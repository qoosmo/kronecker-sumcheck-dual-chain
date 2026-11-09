//! Polynomial-valued FRI chain: leaves s_i(z, .) in K[W]_{<2^i} (format F2).
use crate::field::{domain_point, K};

pub type Leaf = Vec<K>;

pub fn level0_from_values(vals: &[K]) -> Vec<Leaf> {
    vals.iter().map(|&x| vec![x]).collect()
}

/// Fold_{i,y}(a,b)(V) = e(V^2) + r V o(V^2),  e = (a+b)/2,  o = (a-b)/(2y).
pub fn fold_pair(a: &Leaf, b: &Leaf, y: K, r: K) -> Leaf {
    assert_eq!(a.len(), b.len());
    let two_inv = K::from_u64(2).inv();
    let inv2y = (K::from_u64(2) * y).inv();
    let mut out = vec![K::ZERO; 2 * a.len()];
    for j in 0..a.len() {
        out[2 * j] = (a[j] + b[j]) * two_inv;
        out[2 * j + 1] = r * ((a[j] - b[j]) * inv2y);
    }
    out
}

/// Inverse of fold_pair (Lemma 2.1), requires r != 0.
pub fn unfold(s: &Leaf, y: K, r: K) -> (Leaf, Leaf) {
    let rinv = r.inv();
    let h = s.len() / 2;
    let e: Vec<K> = (0..h).map(|j| s[2 * j]).collect();
    let o: Vec<K> = (0..h).map(|j| s[2 * j + 1] * rinv).collect();
    let a = (0..h).map(|j| e[j] + y * o[j]).collect();
    let b = (0..h).map(|j| e[j] - y * o[j]).collect();
    (a, b)
}

/// One level: table on mu_N -> table on mu_{N/2}; -y = omega^{t+N/2}, y^2 = omega_{N/2}^t.
pub fn fold_level(prev: &[Leaf], r: K) -> Vec<Leaf> {
    let n = prev.len();
    let half = n / 2;
    (0..half)
        .map(|t| fold_pair(&prev[t], &prev[t + half], domain_point(n, t), r))
        .collect()
}

/// Full honest butterfly from a level-0 table; returns levels 0..=r.len().
pub fn butterfly(vals: &[K], r: &[K]) -> Vec<Vec<Leaf>> {
    let mut levels = vec![level0_from_values(vals)];
    for &ri in r {
        let next = fold_level(levels.last().unwrap(), ri);
        levels.push(next);
    }
    levels
}

/// Closed form of Lemma 3.2: s_i(z,V) = sum_t c_t z^{t>>i} (prod_{k<=i, t_k=1} r_k) V^{rev_i(t mod 2^i)}.
pub fn closed_form_leaf(c: &[K], i: usize, z: K, r: &[K]) -> Leaf {
    let mut out = vec![K::ZERO; 1 << i];
    for (t, &ct) in c.iter().enumerate() {
        let (mut pos, mut w) = (0usize, ct * z.pow((t >> i) as u64));
        for k in 1..=i {
            if (t >> (k - 1)) & 1 == 1 {
                pos += 1 << (i - k);
                w = w * r[k - 1];
            }
        }
        out[pos] += w;
    }
    out
}
