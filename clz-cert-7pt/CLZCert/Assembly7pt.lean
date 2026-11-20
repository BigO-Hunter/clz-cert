import CLZCert.Assembly

/-!
# CLZ assembly, 7-point stage: κ* ≥ 6730085/10⁷ — conditional on NAMED hypotheses

Board row 2 (Sunghyeon Jo, ainta/zeta-simple-zeros, Aug 10 2026, claimed):
  κ* ≥ (1,345,000·H − 2,680)/1,340,003 = 0.673008527927…  ≥  0.6730085.
This file mirrors `Assembly.lean` (3-point) at the 7-point level, reusing its
Interface layer, `H0`, and the `H0_lower` axiom verbatim (same named gap,
same level — the 7-point requirement is looser).

New named parameterized hypotheses (the only new non-Mathlib inputs):
  `seven_point_certificate` — F₆(g₁,…,g₆) ≥ 19/5000 ∀ gaps ≥ 0, where
     F₆ = Σgᵢ/3000 + Σ_{s=1..6} (2/(7−s))·Σᵢ kk(Σ_{j=i}^{i+s−1} gⱼ)²
     (21 pair-distance terms; Jo docs/proof.md (4.1)).
     Generated receipts: `gen_7pt.py` + `cert_data_7pt.json` (exact rational
     interval arithmetic; one-body components + pressure + interval +
     certified-convexity tangent pruning; independent verification in
     verify_7pt.py). Lean receipt instantiation mirrors the 3-point status
     ("in flight").
  `jo_bridge_7pt` — Jo's §4 deduction (stability-enhanced rank–trace +
     7-window averaging over 269-offset blocks, m = 269, A = 4997/5000 < 1),
     gap-named CLZ_GAP_JO_BRIDGE (7-point branch, paper-tracked to Jo
     docs/proof.md (4.2)–(4.6)).

PROVED here with no new gap: `kappa_star_ge_7pt`, the final ε-form bound at
C = 6730085/10⁷ > H = 6725007/10⁷ (verified row) by 5.08e-6, and above the
3-point stage (6725198/10⁷) by 4.89e-6.
-/

namespace CLZ

open CLZ.Interface

noncomputable section

/-- The gap-indexing helper: all indices used below are < 6, where this is
the identity. -/
def g' (g : Fin 6 → ℝ) (n : ℕ) : ℝ := g ⟨n % 6, Nat.mod_lt _ (by omega)⟩

/-- Pressure form of one 7-point window (Jo docs/proof.md (4.1)):
the span/3000 linear term plus all 21 pair-distance w-terms weighted by
2/(7−s). -/
def F6 (g : Fin 6 → ℝ) : ℝ :=
  (∑ i ∈ Finset.range 6, g' g i) / 3000 +
    ∑ s ∈ Finset.Icc 1 6, (2 / ((7 - s : ℕ) : ℝ)) *
      ∑ i ∈ Finset.range (7 - s), kk (∑ j ∈ Finset.range s, g' g (i + j)) ^ 2

/-- The 7-point certificate statement (the generated receipts' target). -/
def SevenPointCert (e : ℝ) : Prop := ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → e ≤ F6 g

/-- Certified by `gen_7pt.py` (exact rational interval arithmetic; the
search closes every box in the 6-D component product at level 19/5000 via
pressure/interval/tangent pruning; data in `cert_data_7pt.json`). -/
axiom seven_point_certificate : SevenPointCert (19 / 5000)

/-- **Jo bridge, 7-point branch** (stability-enhanced rank–trace + window
averaging, Jo docs/proof.md (4.3)–(4.6)): consuming the 7-point certificate
at level e₇ = 19/5000 (m = 269, A = 19/5000·263 = 4997/5000 < 1), the
machinery yields S/N ≥ (1345000·H₀ − 2680)/1340003 in ε-form.
CLZ_GAP_JO_BRIDGE. -/
axiom jo_bridge_7pt (δ : ℝ) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (((1345000:ℝ) * H0 - 2680) / 1340003 - δ) * (Ncount 0 T : ℝ)
        ≤ N0simple 0 T

/-- **κ* ≥ 6730085/10⁷** in the cumulative ε-form of the zeta23 challenge,
beating the verified row H = 6725007/10⁷ by 5.08e-6. Arithmetic core:
H₀ ≥ 6725006930/10¹⁰ (`H0_lower`, margin 1.07e-8) covers the 7-point exact
requirement H₀ ≥ 1809026818051/2690000000000 = 0.6725006758… (margin
1.7e-8). -/
theorem kappa_star_ge_7pt :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6730085:ℝ)/10^7 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  intro ε hε
  -- ℚ/ℝ core: C ≤ (1345000·H₀ − 2680)/1340003  (from H0_lower)
  have hd : (0:ℝ) < (1340003:ℝ) := by norm_num
  have hB : ((6730085:ℝ)/10^7) ≤ ((1345000:ℝ) * H0 - 2680) / 1340003 := by
    rw [le_div_iff₀ hd]
    nlinarith [H0_lower]
  obtain ⟨T₀, hT⟩ := jo_bridge_7pt (ε/2) (by linarith)
  refine ⟨T₀, fun T hT' => ?_⟩
  have h1 := hT T hT'
  have hcmp : ((6730085:ℝ)/10^7 - ε) ≤
      ((1345000:ℝ) * H0 - 2680) / 1340003 - ε/2 := by linarith
  calc ((6730085:ℝ)/10^7 - ε) * (Ncount 0 T : ℝ)
      ≤ (((1345000:ℝ) * H0 - 2680) / 1340003 - ε/2) * (Ncount 0 T : ℝ) :=
        mul_le_mul_of_nonneg_right hcmp (Nat.cast_nonneg _)
    _ ≤ N0simple 0 T := h1

end

end CLZ
