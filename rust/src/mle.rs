//! Multilinear polynomials, chain-A honest polynomials (Lemma 3.1), Lambda_r (Prop. 4.1).
use crate::field::K;

fn bit(s: usize, k: usize) -> bool {
    // variable X_k <-> bit k-1
    (s >> (k - 1)) & 1 == 1
}

/// f(pt), with pt[k-1] the value of X_k.
pub fn eval_ml(c: &[K], pt: &[K]) -> K {
    let mut v = c.to_vec();
    for &x in pt {
        let half = v.len() / 2;
        v = (0..half).map(|j| v[2 * j] + x * v[2 * j + 1]).collect();
    }
    assert_eq!(v.len(), 1);
    v[0]
}

/// sum_{b in {0,1}^m} f(b), by brute force.
pub fn hypercube_sum_brute(c: &[K], m: usize) -> K {
    (0..1usize << m)
        .map(|b| {
            let pt: Vec<K> = (1..=m).map(|k| if bit(b, k) { K::ONE } else { K::ZERO }).collect();
            eval_ml(c, &pt)
        })
        .fold(K::ZERO, |a, x| a + x)
}

/// 2^m f(1/2, ..., 1/2)  (Remark 1.1).
pub fn half_point_formula(c: &[K], m: usize) -> K {
    let half = K::from_u64(2).inv();
    K::from_u64(1u64 << m) * eval_ml(c, &vec![half; m])
}

/// f(beta(X)) = sum_S c_S (prod_{k in S} r_k) X^{j'(S)},  j'(S) = sum_{k in S} 2^{m-k}.
pub fn beta_poly(c: &[K], r: &[K]) -> Vec<K> {
    let m = r.len();
    let l = 1usize << m;
    let mut out = vec![K::ZERO; l];
    for s in 0..l {
        let (mut e, mut w) = (0usize, c[s]);
        for k in 1..=m {
            if bit(s, k) {
                e += 1 << (m - k);
                w = w * r[k - 1];
            }
        }
        out[e] += w;
    }
    out
}

/// Partial sums A_i, i = 0..m, as multilinear coefficient vectors in X_1..X_i.
pub fn partial_sums(c: &[K], m: usize) -> Vec<Vec<K>> {
    let two = K::from_u64(2);
    let mut a = vec![Vec::new(); m + 1];
    a[m] = c.to_vec();
    for i in (1..=m).rev() {
        let h = 1usize << (i - 1);
        a[i - 1] = (0..h).map(|s| two * a[i][s] + a[i][s | h]).collect();
    }
    a
}

/// (U_i, V_i) of Q_i(Y,Z) = A_i(r_1 Y^{2^{i-2}}, ..., r_{i-1} Y, Z). Uses r[0..i-1].
pub fn chain_a_uv(a: &[Vec<K>], r: &[K], i: usize) -> (Vec<K>, Vec<K>) {
    let h = 1usize << (i - 1);
    let (mut u, mut v) = (vec![K::ZERO; h], vec![K::ZERO; h]);
    for s in 0..h {
        let (mut e, mut w) = (0usize, K::ONE);
        for k in 1..i {
            if bit(s, k) {
                e += 1 << (i - 1 - k);
                w = w * r[k - 1];
            }
        }
        u[e] += w * a[i][s];
        v[e] += w * a[i][s | h];
    }
    (u, v)
}

/// P_i(X) = A_i(r_1 X^{2^{i-1}}, ..., r_i X). Uses r[0..i]. P_0 = [A_0].
pub fn chain_a_p(a: &[Vec<K>], r: &[K], i: usize) -> Vec<K> {
    let n = 1usize << i;
    let mut out = vec![K::ZERO; n];
    for s in 0..n {
        let (mut e, mut w) = (0usize, K::ONE);
        for k in 1..=i {
            if bit(s, k) {
                e += 1 << (i - k);
                w = w * r[k - 1];
            }
        }
        out[e] += w * a[i][s];
    }
    out
}

/// Lambda_r(P_m): unwind P_{i-1} = 2 E_{P_i} + r_i^{-1} O_{P_i} down to P_0.
pub fn unwind(pm: &[K], r: &[K]) -> K {
    let two = K::from_u64(2);
    let mut p = pm.to_vec();
    for i in (1..=r.len()).rev() {
        let half = p.len() / 2;
        let rinv = r[i - 1].inv();
        p = (0..half).map(|j| two * p[2 * j] + rinv * p[2 * j + 1]).collect();
    }
    p[0]
}

/// Kronecker preimage of (Y^L - y^L)/(Y - y) = sum_t y^{L-1-t} Y^t, and its hypercube sum.
pub fn eta_coeffs(y: K, m: usize) -> Vec<K> {
    let l = 1usize << m;
    (0..l).map(|t| y.pow((l - 1 - t) as u64)).collect()
}

/// sigma = y^{L-1} prod_{k=1}^m (2 + y^{-2^{k-1}})  (Prop. 5.1).
pub fn sigma_product(y: K, m: usize) -> K {
    let l = 1u64 << m;
    let yinv = y.inv();
    (1..=m).fold(y.pow(l - 1), |acc, k| {
        acc * (K::from_u64(2) + yinv.pow(1u64 << (k - 1)))
    })
}
