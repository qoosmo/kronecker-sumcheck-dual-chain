//! Protocol Pi_dual: commit phase driver and verifier (Protocol 2.2).
use crate::chain_b::{fold_pair, level0_from_values, Leaf};
use crate::field::{domain_point, K};
use crate::poly;
use crate::rng::Rng;

#[derive(Clone, Copy, Debug)]
pub struct Params {
    pub m: usize,
    /// Blowup B (power of two).
    pub b: usize,
}

impl Params {
    pub fn l(&self) -> usize {
        1 << self.m
    }
    /// |D_m| = B L.
    pub fn n(&self) -> usize {
        self.b << self.m
    }
    /// |D_i| = B 2^i.
    pub fn d(&self, i: usize) -> usize {
        self.b << i
    }
}

/// Commitment order. `LateFirstRound` lets the prover see r_1 before committing (U_1, V_1).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Order {
    Correct,
    LateFirstRound,
}

/// `AllLeavesEqual` is check (F1). `OwnFiber` is the under-specified variant Pi^-.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Terminal {
    AllLeavesEqual,
    OwnFiber,
}

#[derive(Clone, Copy, Debug)]
pub struct VerifierConfig {
    /// Number of chain-B queries q.
    pub q_b: usize,
    /// Number of chain-A paths.
    pub q_a: usize,
    pub terminal: Terminal,
}

pub trait Prover {
    /// Level-0 table s_0 on D_m and the claimed sum H.
    fn initial(&mut self) -> (Vec<K>, K);
    /// Tables (U_i, V_i) on D_{i-1}. `r_i` is `Some` only under a late ordering.
    fn round_uv(&mut self, i: usize, r_i: Option<K>) -> (Vec<K>, Vec<K>);
    /// Table P_i on D_i and chain-B level s_i on E_i = D_{m-i}, after r_i.
    fn round_after(&mut self, i: usize, r_i: K) -> (Vec<K>, Vec<Leaf>);
}

/// All oracles; index i in 1..=m for u, v, p (index 0 unused); s has levels 0..=m.
pub struct Transcript {
    pub h: K,
    pub r: Vec<K>,
    pub u: Vec<Vec<K>>,
    pub v: Vec<Vec<K>>,
    pub p: Vec<Vec<K>>,
    pub s: Vec<Vec<Leaf>>,
}

pub fn run<Pr: Prover>(pr: &mut Pr, par: &Params, order: Order, rng: &mut Rng) -> Transcript {
    let (s0, h) = pr.initial();
    assert_eq!(s0.len(), par.n());
    let mut tr = Transcript {
        h,
        r: Vec::new(),
        u: vec![Vec::new()],
        v: vec![Vec::new()],
        p: vec![Vec::new()],
        s: vec![level0_from_values(&s0)],
    };
    for i in 1..=par.m {
        let (u, v, ri) = if order == Order::LateFirstRound && i == 1 {
            let ri = rng.k();
            let (u, v) = pr.round_uv(i, Some(ri));
            (u, v, ri)
        } else {
            let (u, v) = pr.round_uv(i, None);
            (u, v, rng.k())
        };
        tr.r.push(ri);
        let (p, s) = pr.round_after(i, ri);
        tr.u.push(u);
        tr.v.push(v);
        tr.p.push(p);
        tr.s.push(s);
    }
    tr
}

pub fn verify(tr: &Transcript, par: &Params, cfg: &VerifierConfig, rng: &mut Rng) -> Result<(), String> {
    let (m, b) = (par.m, par.b);
    let two = K::from_u64(2);
    for i in 1..=m {
        if tr.u[i].len() != par.d(i - 1) || tr.v[i].len() != par.d(i - 1) || tr.p[i].len() != par.d(i) {
            return Err(format!("chain A: table size, round {i}"));
        }
        if tr.s[i].len() != par.d(m - i) {
            return Err(format!("chain B: table size, level {i}"));
        }
    }
    // Terminal leaves: (F2) format, then (F1) if enabled.
    let leaves = &tr.s[m];
    if leaves.iter().any(|lf| lf.len() != par.l()) {
        return Err("F2: terminal leaf format".into());
    }
    if cfg.terminal == Terminal::AllLeavesEqual && leaves.iter().any(|lf| lf != &leaves[0]) {
        return Err("F1: terminal leaves differ".into());
    }
    // (F3) chain-B queries.
    for _ in 0..cfg.q_b {
        let mut t = rng.below(par.n());
        for i in 0..m {
            let nn = par.d(m - i);
            let half = nn / 2;
            let idx = t % half;
            let (a, bb, node) = (&tr.s[i][idx], &tr.s[i][idx + half], &tr.s[i + 1][idx]);
            let want = 1usize << i;
            if a.len() != want || bb.len() != want || node.len() != 2 * want {
                return Err(format!("F2: leaf format at level {i}"));
            }
            if fold_pair(a, bb, domain_point(nn, idx), tr.r[i]) != *node {
                return Err(format!("chain B: fold check at level {}", i + 1));
            }
            t = idx;
        }
    }
    // (A) chain-A path checks.
    for _ in 0..cfg.q_a {
        let tm = rng.below(par.d(m));
        let mut t = tm;
        for i in (1..=m).rev() {
            let nn = par.d(i);
            let ti = t % (nn / 2);
            let x = domain_point(nn, t);
            let (uu, vv) = (tr.u[i][ti], tr.v[i][ti]);
            if tr.p[i][t] != uu + tr.r[i - 1] * x * vv {
                return Err(format!("chain A: check (b_{i})"));
            }
            let prev = if i == 1 { tr.h } else { tr.p[i - 1][ti] };
            if prev != two * uu + vv {
                return Err(format!("chain A: check (a_{i})"));
            }
            t = ti;
        }
        let leaf = match cfg.terminal {
            Terminal::AllLeavesEqual => &leaves[0],
            Terminal::OwnFiber => &leaves[tm % b],
        };
        if tr.p[m][tm] != poly::eval(leaf, domain_point(par.d(m), tm)) {
            return Err("terminal link P_m(x_m) = T(x_m)".into());
        }
    }
    Ok(())
}

/// Fraction of `trials` independent runs (fresh challenges and queries) that accept.
pub fn acceptance_rate<Pr: Prover, F: FnMut(&mut Rng) -> Pr>(
    mut make: F,
    par: &Params,
    order: Order,
    cfg: &VerifierConfig,
    trials: usize,
    rng: &mut Rng,
) -> f64 {
    let mut ok = 0usize;
    for _ in 0..trials {
        let mut pr = make(rng);
        let tr = run(&mut pr, par, order, rng);
        if verify(&tr, par, cfg, rng).is_ok() {
            ok += 1;
        }
    }
    ok as f64 / trials as f64
}
