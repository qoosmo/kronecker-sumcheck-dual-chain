//! Dense univariate polynomials over K (coefficient vectors, low degree first).
use crate::field::K;

pub fn eval(c: &[K], x: K) -> K {
    c.iter().rev().fold(K::ZERO, |acc, &a| acc * x + a)
}

/// Equality up to trailing zeros.
pub fn eq(a: &[K], b: &[K]) -> bool {
    let n = a.len().max(b.len());
    (0..n).all(|j| a.get(j).copied().unwrap_or(K::ZERO) == b.get(j).copied().unwrap_or(K::ZERO))
}

pub fn add(a: &[K], b: &[K]) -> Vec<K> {
    let n = a.len().max(b.len());
    (0..n)
        .map(|j| a.get(j).copied().unwrap_or(K::ZERO) + b.get(j).copied().unwrap_or(K::ZERO))
        .collect()
}

pub fn scale(a: &[K], s: K) -> Vec<K> {
    a.iter().map(|&x| x * s).collect()
}

/// a(X^2).
pub fn compose_square(a: &[K]) -> Vec<K> {
    let mut out = vec![K::ZERO; 2 * a.len()];
    for (j, &x) in a.iter().enumerate() {
        out[2 * j] = x;
    }
    out
}

/// X * a(X).
pub fn shift(a: &[K]) -> Vec<K> {
    let mut out = vec![K::ZERO];
    out.extend_from_slice(a);
    out
}

/// Relative Hamming distance between a table and the evaluations of a polynomial on mu_n.
pub fn dist_to_poly(table: &[K], c: &[K]) -> f64 {
    let n = table.len();
    let bad = (0..n)
        .filter(|&t| table[t] != eval(c, crate::field::domain_point(n, t)))
        .count();
    bad as f64 / n as f64
}
