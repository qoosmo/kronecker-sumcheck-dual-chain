# dual-chain (Rust)

Executable checks for `note/dual-chain.tex`, over Goldilocks³ (`K = F_p[x]/(x^3 - 2)`), zero dependencies.

## Tests (`cargo test --release`)

`tests/completeness.rs`, for m = 1..6, B = 4:
- `x^3 - 2` irreducible (2 is not a cube mod p); field axioms in K.
- Σ_b f(b) = 2^m f(1/2,…,1/2) (Remark 1.1).
- Lemma 3.1: P_{i-1} = 2U_i + V_i, P_i(X) = U_i(X²) + r_i X V_i(X²), P_m = f(β) — as polynomial identities.
- Prop. 4.1: Λ_r(P_m) = H.
- Lemma 3.2: closed form of every chain-B leaf; all terminal leaves equal f(β); format F2.
- Lemma 2.1: fold injective; f ↦ f(β) bijective.
- Honest prover accepted.

`tests/attacks.rs`:
- Prop. 5.1 (fiber splitting): Π⁻ accepts a false sum with d(s₀, F⋆) = B/n; (F1) rejects it.
- Prop. 5.2 (late U₁, V₁): pass rate 1/2 per chain-A path; 0 under the correct order.
- Lemma 6.4 tightness: d(s₀, RS) = 3/8 with F⋆ undefined; acceptance ≈ (5/8)^q.

## Report (`cargo run --release -- <m> <trials>`)

Prints measured vs predicted acceptance rates for all provers above.
