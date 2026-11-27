# BASE.md — the zeta23 dependency + credit

## What we stand on (stage 1)

Corpus: **anthropics/formal-math**, package `zeta23` (Lean v4.33.0-rc2, Mathlib 51e6992e).
Board row 3 (Lean Verified): theorem
`montgomery_taylor_simple_on_critical_line_mult_cumulative`:
∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2 − 1/cMT − ε)·Ncount 0 T ≤ N0simple 0 T,
where cMT = √2·tan(1/√2)/(1 + tan(1/√2)/√2), so 2 − 1/cMT = 3/2 − cot(1/√2)/√2
= H₀ = 0.6725007036794116…  Axioms: propext, Classical.choice, Quot.sound only.
Upstream refs: anthropics/formal-math @ `16a5ce41`, directory `zeta23`
(`Challenge.lean`: exact statements + defs IsNontrivialZero, zeroMult, zerosIn,
Ncount, Ndist, N0star, N0simple, cMT — a Mathlib-only definition layer;
`Zeta23.lean`: library root).

## Toolchain mismatch — deliberate

zeta23 pins v4.33.0-rc2/51e6992e; this project builds on v4.34.1 with Mathlib
d13f23b7 (pinned in lake-manifest.json; fetch built oleans with `lake exe cache
get`, or use CI's lean-action mathlib cache). Rebuilding the 250k-line zeta23
corpus on a second toolchain is out of scope, so Theorem D enters as the **parameterized
hypothesis** `CLZCert.Interface.zeta23_theorem_D` (exact statement shape above).
On the board, the bigospeedrun verifier discharges it from the corpus; the axiom
is the ONLY nonstandard assumption, explicitly named in the axcheck.

## What the delta is (per ainta/zeta-simple-zeros, MIT, credited)

Jo keeps the paper's argument through a stability refinement of the rank–trace
step: the equality case allows the simple-zero atoms to be mutually orthogonal,
but their inner products are the kernel k(x) = K(x)/K(0),
K(x) = ½[sinc(πx−1/√2)+sinc(πx+1/√2)] evaluated at zero-gap differences.
3-point certificate: k(u)²+k(v)²+k(u+v)² ≥ ε₄ on u,v ≥ 0, u+v ≤ 4;
assembly S/N ≥ (H₀−ε₄/4)/(1−ε₄/2). Jo certified ε₄ ≥ 221/10⁶ (Arb, G=16000)
⇒ 0.6725197671…. Upstream source: github.com/ainta/zeta-simple-zeros
(MIT; paper/riemann.tex, docs/proof.md, docs/verifier.md, src/).
