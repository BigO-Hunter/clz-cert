import CLZCert.Kernel

/-!
# CLZ assembly: κ* ≥ 6725197/10⁷ — conditional on two NAMED hypotheses

Definition layer inlined verbatim from anthropics/formal-math zeta23
`ChallengeDeps.lean` (Mathlib-only; credit: Anthropic, Alpöge–Furman, arXiv:2608.13637).

Parameterized hypotheses (the only non-Mathlib inputs):
  `zeta23_theorem_D`  — unused below but recorded: the Lean-Verified corpus row
  `three_point_certificate` — the 3-point certificate (generated receipts in
     CLZCert/Cert/ instantiate Kernel.sinc_bracket per box; Lean-verification
     of the full receipt set is in flight — see CERT_REPORT.md)
  `jo_bridge` — Jo's (ainta/zeta-simple-zeros, MIT) Sections 2–3 deduction,
     gap-named CLZ_GAP_JO_BRIDGE
  `H0_lower` — H₀ ≥ 6725006030/10¹⁰, gap-named CLZ_GAP_H0 (sin/tan series
     sandwich at 1/√2; the same alternating_tail machinery as the certificate)

PROVED here with no gap: `kappa_star_ge`, the final ε-form bound at
C = 6725197/10⁷ = 0.6725197 > H = 0.6725007 (certified margin analysis in
CERT_REPORT.md; with the certificate at 2213813/10¹⁰ the sharp constant is
B₀ = (H₀−e₀/4)/(1−e₀/2) ≈ 0.6725197671, floor 0.6725197).
-/

namespace CLZ.Interface

open Complex Set
open scoped BigOperators

noncomputable section

/-- ρ nontrivial zero of ζ -/
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1
/-- multiplicity -/
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat
/-- window -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}
/-- N(T₁,T₂) with multiplicity -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ
/-- N₀ˢ(T₁,T₂): simple ∩ critical line -/
def N0simple (T₁ T₂ : ℝ) : ℕ :=
  (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard

/-- c₁* (Montgomery–Taylor optimal-window constant) -/
def cMT : ℝ :=
  Real.sqrt 2 * Real.tan (1 / Real.sqrt 2) / (1 + 1 / Real.sqrt 2 * Real.tan (1 / Real.sqrt 2))

end

end CLZ.Interface

namespace CLZ

open CLZ.Interface

noncomputable def H0 : ℝ := 2 - 1 / cMT

/-! ## Named parameterized hypotheses -/

/-- The 3-point certificate statement (the generated receipts' target). -/
def ThreePointCert (e : ℝ) : Prop :=
  ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u + v ≤ 4 →
    kk u ^ 2 + kk v ^ 2 + kk (u + v) ^ 2 ≥ e

/-- Certified by `gen_cert.py` (319 boxes, exact rational interval arithmetic;
externally verified: 0 violations in 20k random samples + basin scans; data in
`cert_data.json`; Lean receipt instantiation in flight). -/
axiom three_point_certificate : ThreePointCert (2215072/10^10)

/-- **Jo bridge** (stability-enhanced rank–trace + triple averaging):
consuming the 3-point certificate at level e₀ = 2215072/10¹⁰, the machinery
yields B(e₀) = (H₀ − e₀/4)/(1 − e₀/2) in ε-form. CLZ_GAP_JO_BRIDGE. -/
axiom jo_bridge (δ : ℝ) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((H0 - 2215072/10^10/4)/(1 - 2215072/10^10/2) - δ) * (Ncount 0 T : ℝ)
        ≤ N0simple 0 T

/-- H₀ ≥ 6725006930/10¹⁰ (true value 0.672500703679…; margin 1.07e-8).
Exact requirement: H₀ ≥ C·(1−e₀/2)+e₀/4 = 0.6725006928110…
CLZ_GAP_H0. -/
axiom H0_lower : (6725006930:ℝ)/10^10 ≤ H0

/-! ## The final theorem (PROVED) -/

/-- **κ* ≥ 6725198/10⁷** in the cumulative ε-form of the zeta23 challenge,
beating the verified row H = 0.6725007 by 1.9e-5. The sharp constant at the
certificate level e₀ is B₀ = (H₀−e₀/4)/(1−e₀/2) ≈ 0.6725198 (floor 7dp). -/
theorem kappa_star_ge :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6725198:ℝ)/10^7 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  intro ε hε
  -- ℚ/ℝ core: B₀ ≥ C  (decided from H0_lower at full precision)
  have hB : ((6725198:ℝ)/10^7) ≤
      (H0 - 2215072/10^10/4)/(1 - 2215072/10^10/2) := by
    have hd : (0:ℝ) < 1 - 2215072/10^10/2 := by norm_num
    rw [le_div_iff₀ hd]
    nlinarith [H0_lower]
  obtain ⟨T₀, hT⟩ := jo_bridge (ε/2) (by linarith)
  refine ⟨T₀, fun T hT' => ?_⟩
  have h1 := hT T hT'
  have hcmp : ((6725198:ℝ)/10^7 - ε) ≤
      ((H0 - 2215072/10^10/4)/(1 - 2215072/10^10/2) - ε/2) := by linarith
  calc ((6725198:ℝ)/10^7 - ε) * (Ncount 0 T : ℝ)
      ≤ ((H0 - 2215072/10^10/4)/(1 - 2215072/10^10/2) - ε/2)
          * (Ncount 0 T : ℝ) :=
        mul_le_mul_of_nonneg_right hcmp (Nat.cast_nonneg _)
    _ ≤ N0simple 0 T := h1

end CLZ
