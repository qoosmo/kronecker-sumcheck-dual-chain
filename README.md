# Hypercube Sums via a Dual Kronecker Chain

Research note on an IOP for the Boolean-hypercube sum of a committed multilinear polynomial, built from two synchronized chains sharing the challenges r_1, …, r_m:

- **Chain A**: growing-domain Kronecker–Sumcheck on D_0 ⊂ … ⊂ D_m.
- **Chain B**: shrinking-domain polynomial-valued (symbolic) FRI, with leaves in K[X].

Both chains end at f(r_1 X^{2^{m-1}}, …, r_m X).

## Contents of the note

- Completeness for all m.
- Exact-identity model: both chains are deterministic bijections; the sum is the fixed functional Λ_r(P_m).
- Two explicit attacks on under-specified variants (fiber splitting: false sum accepted with probability 1; late first-round commitment).
- Soundness theorem for the repaired protocol: m/|K| + 2B(2^m − 1)/|K| + (1 − θ)^q, θ = (1 − 1/B)/2, with a proximity-gap-free binding argument for the polynomial-valued chain. Goldilocks³, m = 20, B = 4: q = 189.
- Cost analysis (Θ(2^m) proof) and the collapse X := 1 to sumcheck interleaved with scalar FRI, with a self-contained evaluation-binding proof for scalar FRI (elementary line lemma, radius (1 − ρ)/3): error m/|K| + 3n/|K| + (3/4)^q, q = 309.
- Numerical validation: `rust/` reproduces every completeness identity, both attacks, and the tightness of the chain-B bound.

## Files

- `note/dual-chain.tex` — LaTeX source
- `note/dual-chain.pdf` — compiled note
- `rust/` — executable checks (see `rust/README.md`)

Build: `cd note && latexmk -pdf dual-chain.tex`

Author: Abdelali Mkhida (Algorizk)
