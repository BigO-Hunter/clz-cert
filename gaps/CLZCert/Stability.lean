import CLZCert.Kernel

/-!
# CLZ stability lemma — the rank–trace refinement

From ainta/zeta-simple-zeros §2 (MIT; credited). Status: the finite piece
(Ψ nonneg — the convex defect functional) is PROVED. The Hermitian trace
inequalities are NOT yet formalized; their exact statements are recorded
here as documentation with CLZ_GAP tags (they are the analytic core that
`jo_bridge` in Assembly.lean summarizes as one parameterized hypothesis).

## Exact statements to formalize (from docs/proof.md of ainta/zeta-simple-zeros)

Ψ(t) = (t−1)² for 0 ≤ t ≤ 2, 2t−3 for t ≥ 2  (convex, nonneg — proved below).

CLZ_GAP_RANKTRACE (Jo's (2.1)): V ∈ ℂ^{r×m} with columns of norm ≤ 1,
P = V·V*, M = V*·V, Q Hermitian with ≤ b positive eigenvalues:
    ‖P+Q‖²_F ≥ 4 tr(P+Q) − 3r − 4b + tr Ψ(M).
Proof route: Q = Q₊ − Q₋; ‖Q₊‖²_F ≥ 4 tr Q₊ − 4b; von Neumann reduces the
rest to min_n ((p−n)² + 4n) = 2p − 1 + Ψ(p); spectra of VV* / V*V agree;
sum with tr P ≤ r.

CLZ_GAP_DUALFORM (Jo's (3.4)): for a graph E of max degree ≤ 2 on the columns,
    tr Ψ(M) ≥ (3/2) Σ_{ij∈E} |⟨V_i, V_j⟩|²
(a dual form of Ψ; this is where kernel values on zero-gap differences enter).

Consumed in Assembly.lean as the parameterized hypothesis `jo_bridge`
(Sections 2–3: (2.2) + triple partition + (3.5) + (3.6)).
-/

namespace CLZ.Stability

/-- Ψ(t) = (t−1)² for t ≤ 2, 2t−3 for t ≥ 2 — the convex defect functional. -/
noncomputable def Psi (t : ℝ) : ℝ := if t ≤ 2 then (t - 1)^2 else 2*t - 3

/-- Ψ ≥ 0 (PROVED). -/
theorem Psi_nonneg (t : ℝ) : 0 ≤ Psi t := by
  unfold Psi
  split
  · nlinarith
  · nlinarith

/-- Ψ(t) ≥ 2t − 3 on [0,∞) (PROVED — the linear support used in (3.4)). -/
theorem Psi_ge_support (t : ℝ) : 0 ≤ t → 2*t - 3 ≤ Psi t := by
  intro ht
  unfold Psi
  split
  · nlinarith
  · linarith

end CLZ.Stability
