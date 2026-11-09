//! Provers: honest, fiber splitting (Prop. 5.1), late first round (Prop. 5.2),
//! and the chain-B tightness prover (Lemma 6.4 is tight at distance theta).
use crate::chain_b::{fold_level, level0_from_values, Leaf};
use crate::field::{domain_point, K};
use crate::mle;
use crate::poly;
use crate::protocol::{Params, Prover};
use crate::rng::Rng;

/// Runs, on each fiber z in D_0, the honest prover of a multilinear g_z.
/// Commits `s0` as level 0 and folds `fold_base` honestly for levels >= 1.
pub struct FiberProver {
    pub par: Params,
    pub h: K,
    pub s0: Vec<K>,
    fold_base: Vec<K>,
    a: Vec<Vec<Vec<K>>>,
    r: Vec<K>,
    level: Vec<Leaf>,
}

impl FiberProver {
    pub fn new(par: Params, g: Vec<Vec<K>>, s0: Vec<K>, fold_base: Vec<K>, h: K) -> FiberProver {
        assert_eq!(g.len(), par.b);
        let a = g.iter().map(|gz| mle::partial_sums(gz, par.m)).collect();
        FiberProver { par, h, s0, level: level0_from_values(&fold_base), fold_base, a, r: Vec::new() }
    }

    pub fn honest(par: Params, c: &[K]) -> FiberProver {
        let n = par.n();
        let s0: Vec<K> = (0..n).map(|t| poly::eval(c, domain_point(n, t))).collect();
        let h = mle::hypercube_sum_brute(c, par.m);
        FiberProver::new(par, vec![c.to_vec(); par.b], s0.clone(), s0, h)
    }

    fn uv_tables(&self, i: usize) -> (Vec<K>, Vec<K>) {
        let polys: Vec<(Vec<K>, Vec<K>)> =
            self.a.iter().map(|az| mle::chain_a_uv(az, &self.r, i)).collect();
        let nn = self.par.d(i - 1);
        let mut u = vec![K::ZERO; nn];
        let mut v = vec![K::ZERO; nn];
        for t in 0..nn {
            let (pu, pv) = &polys[t % self.par.b];
            let y = domain_point(nn, t);
            u[t] = poly::eval(pu, y);
            v[t] = poly::eval(pv, y);
        }
        (u, v)
    }
}

impl Prover for FiberProver {
    fn initial(&mut self) -> (Vec<K>, K) {
        self.level = level0_from_values(&self.fold_base);
        (self.s0.clone(), self.h)
    }
    fn round_uv(&mut self, i: usize, _r_i: Option<K>) -> (Vec<K>, Vec<K>) {
        self.uv_tables(i)
    }
    fn round_after(&mut self, i: usize, r_i: K) -> (Vec<K>, Vec<Leaf>) {
        self.r.push(r_i);
        let polys: Vec<Vec<K>> = self.a.iter().map(|az| mle::chain_a_p(az, &self.r, i)).collect();
        let nn = self.par.d(i);
        let p = (0..nn)
            .map(|t| poly::eval(&polys[t % self.par.b], domain_point(nn, t)))
            .collect();
        self.level = fold_level(&self.level, r_i);
        (p, self.level.clone())
    }
}

/// Output of the fiber-splitting construction (Prop. 5.1).
pub struct FiberAttack {
    pub prover: FiberProver,
    /// Per fiber: chosen point y_z, sigma_z, lambda_z, g_z.
    pub y: Vec<K>,
    pub sigma: Vec<K>,
    pub lambda: Vec<K>,
    pub g: Vec<Vec<K>>,
}

pub fn fiber_attack(par: Params, fstar: &[K], h_false: K) -> FiberAttack {
    let (m, n, b) = (par.m, par.n(), par.b);
    let hstar = mle::hypercube_sum_brute(fstar, m);
    let (mut ys, mut sigmas, mut lambdas, mut gs) = (vec![], vec![], vec![], vec![]);
    for z in 0..b {
        // Fiber of z: indices t = z + B j (omega_n^{tL} = omega_B^t).
        let (y, sigma) = (0..par.l())
            .map(|j| domain_point(n, z + b * j))
            .map(|y| (y, mle::sigma_product(y, m)))
            .find(|(_, s)| !s.is_zero())
            .expect("no admissible y_z");
        let lambda = (h_false - hstar) * sigma.inv();
        let eta = mle::eta_coeffs(y, m);
        let g = poly::add(fstar, &poly::scale(&eta, lambda));
        ys.push(y);
        sigmas.push(sigma);
        lambdas.push(lambda);
        gs.push(g);
    }
    let s0: Vec<K> = (0..n).map(|t| poly::eval(&gs[t % b], domain_point(n, t))).collect();
    let prover = FiberProver::new(par, gs.clone(), s0.clone(), s0, h_false);
    FiberAttack { prover, y: ys, sigma: sigmas, lambda: lambdas, g: gs }
}

/// Honest except: claims `h_false` and commits (U_1, V_1) after seeing r_1 (Prop. 5.2).
pub struct LateProver {
    inner: FiberProver,
    h_false: K,
}

impl LateProver {
    pub fn new(par: Params, c: &[K], h_false: K) -> LateProver {
        LateProver { inner: FiberProver::honest(par, c), h_false }
    }
}

impl Prover for LateProver {
    fn initial(&mut self) -> (Vec<K>, K) {
        let (s0, _) = self.inner.initial();
        (s0, self.h_false)
    }
    fn round_uv(&mut self, i: usize, r_i: Option<K>) -> (Vec<K>, Vec<K>) {
        match (i, r_i) {
            (1, Some(r1)) => {
                let b = self.inner.par.b;
                let p1 = mle::chain_a_p(&self.inner.a[0], &[r1], 1);
                let (two, one) = (K::from_u64(2), K::ONE);
                let mut u = vec![K::ZERO; b];
                let mut v = vec![K::ZERO; b];
                for t in 0..b {
                    // x_y = omega_{2B}^t is a square root of y = omega_B^t; fall back to -x_y.
                    let mut x = domain_point(2 * b, t);
                    if (one - two * r1 * x).is_zero() {
                        x = -x;
                    }
                    let px = poly::eval(&p1, x);
                    v[t] = (self.h_false - two * px) * (one - two * r1 * x).inv();
                    u[t] = px - r1 * x * v[t];
                }
                (u, v)
            }
            _ => self.inner.round_uv(i, r_i),
        }
    }
    fn round_after(&mut self, i: usize, r_i: K) -> (Vec<K>, Vec<Leaf>) {
        self.inner.round_after(i, r_i)
    }
}

/// Chain-B tightness: s_0 = F' except on a negation-closed set of relative size 3/8
/// where it equals F_*; levels >= 1 are the honest butterfly of F'; chain A honest for f'.
/// Then d(s_0, RS) = 3/8 = theta, so F_* is undefined and acceptance is a win.
pub fn tightness_prover(par: Params, fprime: &[K], fstar: &[K], rng: &mut Rng) -> FiberProver {
    let n = par.n();
    let half = n / 2;
    let target = 3 * n / 16; // pairs; 2 * 3n/16 = 3n/8 positions
    let mut idx: Vec<usize> = (0..half).collect();
    for j in (1..half).rev() {
        idx.swap(j, rng.below(j + 1));
    }
    let mut corrupted = vec![false; n];
    for &t in &idx[..target] {
        corrupted[t] = true;
        corrupted[t + half] = true;
    }
    let fold_base: Vec<K> = (0..n).map(|t| poly::eval(fprime, domain_point(n, t))).collect();
    let s0: Vec<K> = (0..n)
        .map(|t| if corrupted[t] { poly::eval(fstar, domain_point(n, t)) } else { fold_base[t] })
        .collect();
    let h = mle::hypercube_sum_brute(fprime, par.m);
    FiberProver::new(par, vec![fprime.to_vec(); par.b], s0, fold_base, h)
}
