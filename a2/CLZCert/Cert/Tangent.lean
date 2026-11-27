import Mathlib

/-!
# CLZ convexity layer — ADOPTED VERBATIM from lane CLZ-D

Source: the convex lane's CLZCert/Convexity.lean (vendored under convex/; that lane owns
it; this copy exists so the CLZ-A2 receipts can consume `tangent_lower` /
`tangent_assembly` without depending on their in-flight worktree). The file is
kernel-agnostic (imports Mathlib only): `w w' w''` and the box data enter as
parameters. Their `DerivBounds.lean` supplies the sinc instances -- that is the
in-flight dependency, see CERT_REPORT's tangent section.

The tangent (supporting-hyperplane) majorant for the 7-point certificate, from
second-derivative brackets + an LDL/PSD certificate for the per-box quadratic
form. This file is *kernel-agnostic*: it never mentions `sinc`, `Kfn` or a
particular window; the `w w' w''` triple and the per-box data enter as
parameters. `CLZCert/DerivBounds.lean` supplies the sinc instances.

## The mathematics, in three moves

1. **Second-order Taylor lower bound** (`tangent_lower`): if `μ ≤ w''` on an
   open interval containing `m` and `t`, then
   `w t ≥ w m + w' m * (t − m) + (μ/2) (t − m)²`.
   This is the tangent lemma in per-piece form; `μ` may have either sign, so the
   one statement covers convex pieces (`μ > 0`) and concave ones (`μ < 0`) —
   in the concave case it is the weaker but still sound lower quadratic.

2. **Block assembly** (`tangent_assembly`): the certificate functional is a
   linear part plus `∑_b c_b · w(P_b g)` over blocks (interval sums `P_b`).
   Applying (1) blockwise, bounding each block's linear remainder by its own
   absolute value, and using `0 ≤ ∑_b c_b μ_b (P_b(g) − P_b(mid))²` (move 3)
   yields the certified per-box bound
   `F(g) ≥ ∑_a lin_a mid_a + ∑_b c_b wlo_b − ∑_a lin_a r_a
            − ∑_b c_b |w'(P_b mid)| (∑_{a∈B b} r_a)`
   on the box `|g_a − mid_a| ≤ r_a` — the generator's `tangent_of` `total`,
   certified through per-block bounds (which are equal to its gradient-magnitude
   table) and needing no sum rearrangement.

3. **PSD via exact LDL** (`blockForm_nonneg_of_ldl`): the block quadratic form
   `∑_b w_b (∑_{a∈B b} q_a)²` is the bilinear form of `Aᵀ diag(w) A` for the
   block incidence matrix `A`. If `Aᵀ diag(w) A = L diag(D) Lᵀ` with `D ≥ 0` —
   the finite exact-ℚ check the generator's `ldl_pd` performs — the form is
   nonnegative. This is the only place negative `μ_b` (concave pieces) are
   absorbed, and `hfac` is shared by every box with the same `μ`-tuple.

Axiom footprint: none beyond the Lean/Mathlib kernel (no `sorry`, no `axiom`).
-/

namespace CLZ

open scoped Matrix

/-! ## Move 1 — the tangent lemma -/

/-- `d/dt ((μ/2) * t^2) = μ * t`. -/
theorem hasDerivAt_half_sq (μ x : ℝ) : HasDerivAt (fun s : ℝ => μ / 2 * s ^ 2) (μ * x) x := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
    have h := (hasDerivAt_id x).mul (hasDerivAt_id x)
    convert h using 1
    · ext s; simp [pow_two]
    · simp only [id_eq]; ring
  have h2 := h1.const_mul (μ / 2)
  convert h2 using 1
  ring

/-- `d/dt (μ * t) = μ`. -/
theorem hasDerivAt_mul_id (μ x : ℝ) : HasDerivAt (fun s : ℝ => μ * s) μ x := by
  simpa using (hasDerivAt_id x).const_mul μ

/-- **The tangent lemma.** If `w'' ≥ μ` on an open interval containing both `m`
and `t`, then `w` dominates its `μ`-quadratic tangent at `m`:
`w t ≥ w m + w' m * (t − m) + (μ/2) (t − m)²`.

Route: `ψ := w − (μ/2)·Id²` has `ψ'' = w'' − μ ≥ 0`, hence is convex
(`convexOn_of_hasDerivWithinAt2_nonneg`), hence dominates its tangent line at
`m` on either side (`ConvexOn.slope_le_of_hasDerivAt`,
`ConvexOn.le_slope_of_hasDerivAt`); then expand. -/
theorem tangent_lower {w w' w'' : ℝ → ℝ} {lo hi μ : ℝ}
    (hw : ∀ x ∈ Set.Ioo lo hi, HasDerivAt w (w' x) x)
    (hw' : ∀ x ∈ Set.Ioo lo hi, HasDerivAt w' (w'' x) x)
    (hμ : ∀ x ∈ Set.Ioo lo hi, μ ≤ w'' x)
    {m t : ℝ} (hm : m ∈ Set.Ioo lo hi) (ht : t ∈ Set.Ioo lo hi) :
    w m + w' m * (t - m) + μ / 2 * (t - m) ^ 2 ≤ w t := by
  set ψ : ℝ → ℝ := fun s => w s - μ / 2 * s ^ 2 with hψdef
  have hψ : ConvexOn ℝ (Set.Ioo lo hi) ψ := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Ioo lo hi) (convex_Ioo lo hi)
      (f' := fun s => w' s - μ * s) (f'' := fun s => w'' s - μ) ?_ ?_ ?_ ?_
    · exact ContinuousOn.sub (fun x hx => (hw x hx).continuousAt.continuousWithinAt)
        (by fun_prop)
    · intro x hx
      rw [interior_Ioo] at hx
      exact ((hw x hx).sub (hasDerivAt_half_sq μ x)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact ((hw' x hx).sub (hasDerivAt_mul_id μ x)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      linarith [hμ x hx]
  have hψ' : HasDerivAt ψ (w' m - μ * m) m := by
    have h := (hw m hm).sub (hasDerivAt_half_sq μ m)
    exact h
  rcases lt_trichotomy t m with hlt | heq | hgt
  · have hsl := hψ.slope_le_of_hasDerivAt ht hm hlt hψ'
    rw [slope_def_field] at hsl
    have hpos : (0:ℝ) < m - t := by linarith
    have h := mul_le_mul_of_nonneg_right hsl hpos.le
    rw [div_mul_cancel₀ _ hpos.ne'] at h
    simp only [hψdef] at h
    nlinarith
  · subst heq; simp
  · have hsl := hψ.le_slope_of_hasDerivAt hm ht hgt hψ'
    rw [slope_def_field] at hsl
    have hpos : (0:ℝ) < t - m := by linarith
    have h := mul_le_mul_of_nonneg_right hsl hpos.le
    rw [div_mul_cancel₀ _ hpos.ne'] at h
    simp only [hψdef] at h
    nlinarith

/-! ## Move 2 — the block assembly -/

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The certificate functional: a linear part plus weighted block sums. -/
noncomputable def certFun (B : ι → Finset (Fin n)) (c : ι → ℝ) (lin : Fin n → ℝ)
    (w : ℝ → ℝ) (g : Fin n → ℝ) : ℝ :=
  (∑ a, lin a * g a) + ∑ b, c b * w (∑ a ∈ B b, g a)

/-- **The tangent-box lower bound.** On the box `|g a − mid a| ≤ r a` the
certificate functional is at least
`∑_a lin_a mid_a + ∑_b c_b wlo_b − ∑_a lin_a r_a
   − ∑_b c_b |w'(P_b mid)| (∑_{a∈B b} r_a)`,
where each block's second-derivative bracket `μ_b ≤ w''` holds on an open
interval `(lo b, hi b)` containing both `P_b mid` and `P_b g`. -/
theorem tangent_assembly
    (B : ι → Finset (Fin n)) (c : ι → ℝ) (hc : ∀ b, 0 ≤ c b)
    (lin : Fin n → ℝ) (hlin : ∀ a, 0 ≤ lin a)
    (w w' w'' : ℝ → ℝ) (lo hi : ι → ℝ)
    (hwd : ∀ b, ∀ x ∈ Set.Ioo (lo b) (hi b), HasDerivAt w (w' x) x)
    (hwd2 : ∀ b, ∀ x ∈ Set.Ioo (lo b) (hi b), HasDerivAt w' (w'' x) x)
    (μ : ι → ℝ) (hμ : ∀ b, ∀ x ∈ Set.Ioo (lo b) (hi b), μ b ≤ w'' x)
    (mid r : Fin n → ℝ) (hr : ∀ a, 0 ≤ r a)
    (wlo : ι → ℝ) (hwb : ∀ b, wlo b ≤ w (∑ a ∈ B b, mid a))
    (g : Fin n → ℝ) (hg : ∀ a, |g a - mid a| ≤ r a)
    (hmem : ∀ b, (∑ a ∈ B b, mid a) ∈ Set.Ioo (lo b) (hi b) ∧
      (∑ a ∈ B b, g a) ∈ Set.Ioo (lo b) (hi b))
    (hpsd : 0 ≤ ∑ b, c b * μ b * (∑ a ∈ B b, (g a - mid a)) ^ 2) :
    (∑ a, lin a * mid a) + ∑ b, c b * wlo b
        - (∑ a, lin a * r a) - ∑ b, c b * |w' (∑ a ∈ B b, mid a)| * (∑ a ∈ B b, r a)
      ≤ certFun B c lin w g := by
  -- per-block Taylor bound
  have hblock : ∀ b, c b * w (∑ a ∈ B b, g a)
      ≥ c b * (w (∑ a ∈ B b, mid a) + w' (∑ a ∈ B b, mid a) * (∑ a ∈ B b, (g a - mid a))
          + μ b / 2 * (∑ a ∈ B b, (g a - mid a)) ^ 2) := by
    intro b
    obtain ⟨hmid, hgP⟩ := hmem b
    have hslope : w (∑ a ∈ B b, g a) ≥ w (∑ a ∈ B b, mid a)
        + w' (∑ a ∈ B b, mid a) * ((∑ a ∈ B b, g a) - (∑ a ∈ B b, mid a))
        + μ b / 2 * ((∑ a ∈ B b, g a) - (∑ a ∈ B b, mid a)) ^ 2 :=
      tangent_lower (hwd b) (hwd2 b) (hμ b) hmid hgP
    have hsub : (∑ a ∈ B b, g a) - (∑ a ∈ B b, mid a) = ∑ a ∈ B b, (g a - mid a) := by
      rw [Finset.sum_sub_distrib]
    rw [hsub] at hslope
    exact mul_le_mul_of_nonneg_left hslope (hc b)
  have hsum : ∑ b, c b * w (∑ a ∈ B b, g a)
      ≥ ∑ b, c b * (w (∑ a ∈ B b, mid a)
          + w' (∑ a ∈ B b, mid a) * (∑ a ∈ B b, (g a - mid a))
          + μ b / 2 * (∑ a ∈ B b, (g a - mid a)) ^ 2) :=
    Finset.sum_le_sum fun b _ => hblock b
  -- the quadratic term is nonnegative (the PSD fact)
  have hquad : 0 ≤ ∑ b, c b * (μ b / 2 * (∑ a ∈ B b, (g a - mid a)) ^ 2) := by
    have hhalf : (∑ b, c b * (μ b / 2 * (∑ a ∈ B b, (g a - mid a)) ^ 2))
        = (1 / 2) * (∑ b, c b * μ b * (∑ a ∈ B b, (g a - mid a)) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hhalf]; linarith [hpsd]
  -- per-block linear terms, bounded by their absolute values
  have hlin_b : ∀ b, c b * (w' (∑ a ∈ B b, mid a) * (∑ a ∈ B b, (g a - mid a)))
      ≥ -(c b * |w' (∑ a ∈ B b, mid a)| * (∑ a ∈ B b, r a)) := by
    intro b
    have hQ : |∑ a ∈ B b, (g a - mid a)| ≤ ∑ a ∈ B b, r a := by
      calc |∑ a ∈ B b, (g a - mid a)| ≤ ∑ a ∈ B b, |g a - mid a| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a ∈ B b, r a := Finset.sum_le_sum fun a _ => hg a
    have h1 : w' (∑ a ∈ B b, mid a) * (∑ a ∈ B b, (g a - mid a))
        ≥ -(|w' (∑ a ∈ B b, mid a)| * (∑ a ∈ B b, r a)) := by
      have h2 : |w' (∑ a ∈ B b, mid a) * (∑ a ∈ B b, (g a - mid a))|
          ≤ |w' (∑ a ∈ B b, mid a)| * (∑ a ∈ B b, r a) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hQ (abs_nonneg _)
      have h3 := neg_abs_le (w' (∑ a ∈ B b, mid a) * (∑ a ∈ B b, (g a - mid a)))
      linarith
    have h4 := mul_le_mul_of_nonneg_left h1 (hc b)
    linarith
  have hlinneg : ∑ b, c b * (w' (∑ a ∈ B b, mid a) * (∑ a ∈ B b, (g a - mid a)))
      ≥ -(∑ b, c b * |w' (∑ a ∈ B b, mid a)| * (∑ a ∈ B b, r a)) := by
    have h := Finset.sum_le_sum fun b (_ : b ∈ (Finset.univ : Finset ι)) => hlin_b b
    rw [Finset.sum_neg_distrib] at h
    linarith
  -- the linear part
  have hlin_a : ∀ a, lin a * mid a - lin a * r a ≤ lin a * g a := by
    intro a
    have h1 : mid a - r a ≤ g a := by
      have := (abs_le.mp (hg a)).1; linarith
    nlinarith [hlin a, hr a]
  have hlinsum : ∑ a, lin a * g a ≥ ∑ a, lin a * mid a - ∑ a, lin a * r a := by
    have h := Finset.sum_le_sum fun a (_ : a ∈ (Finset.univ : Finset (Fin n))) => hlin_a a
    have hsplit : (∑ a, (lin a * mid a - lin a * r a))
        = ∑ a, lin a * mid a - ∑ a, lin a * r a := by
      simpa using Finset.sum_sub_distrib (f := fun a => lin a * mid a)
        (g := fun a => lin a * r a) (s := (Finset.univ : Finset (Fin n)))
    linarith
  -- the certified `w` values at the block mid-sums
  have hwmid : ∑ b, c b * wlo b ≤ ∑ b, c b * w (∑ a ∈ B b, mid a) :=
    Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hwb b) (hc b)
  -- split the summed block bound into its three sums
  have hquadne : ∑ b, c b * (w (∑ a ∈ B b, mid a)
      + w' (∑ a ∈ B b, mid a) * (∑ a ∈ B b, (g a - mid a))
      + μ b / 2 * (∑ a ∈ B b, (g a - mid a)) ^ 2)
      = (∑ b, c b * w (∑ a ∈ B b, mid a))
        + (∑ b, c b * (w' (∑ a ∈ B b, mid a) * (∑ a ∈ B b, (g a - mid a))))
        + (∑ b, c b * (μ b / 2 * (∑ a ∈ B b, (g a - mid a)) ^ 2)) := by
    have hpt : ∀ b, c b * (w (∑ a ∈ B b, mid a)
        + w' (∑ a ∈ B b, mid a) * (∑ a ∈ B b, (g a - mid a))
        + μ b / 2 * (∑ a ∈ B b, (g a - mid a)) ^ 2)
        = c b * w (∑ a ∈ B b, mid a)
          + c b * (w' (∑ a ∈ B b, mid a) * (∑ a ∈ B b, (g a - mid a)))
          + c b * (μ b / 2 * (∑ a ∈ B b, (g a - mid a)) ^ 2) := fun b => by ring
    simp only [hpt, Finset.sum_add_distrib]
  simp only [certFun]
  linarith

/-! ## Move 3 — the block quadratic form and its LDL/PSD certificate -/

variable [DecidableEq ι]

/-- Incidence matrix of a family of blocks: `A b a = 1` if `a ∈ B b`. -/
def incMat (B : ι → Finset (Fin n)) : Matrix ι (Fin n) ℝ :=
  fun b a => if a ∈ B b then 1 else 0

/-- The block quadratic form: `∑_b w_b · (∑_{a ∈ B b} q_a)²`. -/
noncomputable def blockForm (B : ι → Finset (Fin n)) (w : ι → ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ b, w b * (∑ a ∈ B b, q a) ^ 2

/-- Entrywise: `(A *ᵥ q) b = ∑_{a ∈ B b} q a`. -/
theorem incMat_mulVec_apply (B : ι → Finset (Fin n)) (q : Fin n → ℝ) (b : ι) :
    (incMat B *ᵥ q) b = ∑ a ∈ B b, q a := by
  simp only [incMat, Matrix.mulVec, dotProduct, ite_mul, one_mul, zero_mul]
  exact (by simpa using
    (Finset.sum_ite_mem (s := (Finset.univ : Finset (Fin n))) (t := B b) (f := q)))

/-- `(diagonal w *ᵥ v) b = w b * v b`. -/
theorem diagonal_mulVec_apply (w : ι → ℝ) (v : ι → ℝ) (b : ι) :
    (Matrix.diagonal w *ᵥ v) b = w b * v b := by
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal]

/-- The bilinear form of `Aᵀ · diag w · A` is the block form. -/
theorem blockForm_eq_qform (B : ι → Finset (Fin n)) (w : ι → ℝ) (q : Fin n → ℝ) :
    blockForm B w q
      = q ⬝ᵥ (((incMat B)ᵀ * Matrix.diagonal w * (incMat B)) *ᵥ q) := by
  have hchain : q ⬝ᵥ (((incMat B)ᵀ * Matrix.diagonal w * (incMat B)) *ᵥ q)
      = (incMat B *ᵥ q) ⬝ᵥ (Matrix.diagonal w *ᵥ (incMat B *ᵥ q)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
      dotProduct_comm]
  have hdiag : (incMat B *ᵥ q) ⬝ᵥ (Matrix.diagonal w *ᵥ (incMat B *ᵥ q))
      = ∑ b, w b * (incMat B *ᵥ q) b ^ 2 := by
    simp only [dotProduct, diagonal_mulVec_apply]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hchain, hdiag]
  exact Finset.sum_congr rfl fun b _ => by rw [incMat_mulVec_apply]

/-- **The LDL/PSD certificate.** If the block matrix factors as `L diag(D) Lᵀ`
with all `D k ≥ 0`, then the block form is nonnegative. The per-box check is the
finite exact-ℚ computation `Aᵀ diag(w) A = L diag(D) Lᵀ` together with `D ≥ 0`;
both are `norm_num` statements about recorded rationals, and `hfac` is shared by
every box whose `w`-tuple agrees (the generator's `μ` values are cell-range
minima, so tuples recur). -/
theorem blockForm_nonneg_of_ldl (B : ι → Finset (Fin n)) (w : ι → ℝ)
    (L : Matrix (Fin n) (Fin n) ℝ) (D : Fin n → ℝ) (hD : ∀ k, 0 ≤ D k)
    (hfac : (incMat B)ᵀ * Matrix.diagonal w * (incMat B) = L * Matrix.diagonal D * Lᵀ)
    (q : Fin n → ℝ) :
    0 ≤ blockForm B w q := by
  rw [blockForm_eq_qform, hfac]
  have hpsd : (L * Matrix.diagonal D * Lᵀ).PosSemidef :=
    (Matrix.PosSemidef.diagonal hD).mul_mul_conjTranspose_same L
  exact hpsd.dotProduct_mulVec_nonneg q

end CLZ
