//! Executable companion to `note/dual-chain.tex`.
//!
//! Field `Fp` = Goldilocks, `K = Fp[x]/(x^3 - 2)`. Multilinear polynomials are
//! coefficient vectors indexed by bitmask `S`, bit `k-1` <-> variable `X_k`,
//! so the Kronecker encoding `F(Y) = sum_S c_S Y^{j(S)}` has the same vector.
pub mod chain_b;
pub mod field;
pub mod mle;
pub mod poly;
pub mod protocol;
pub mod provers;
pub mod rng;
