import CLZCert.Cert.Tangent
import CLZCert.Cert.Const

/-!
# Tangent-box receipts — the parameterized shape (CLZ-A2, Task 3)

The sibling cover decomposes into 131,035 `interval` boxes (the wcell/wrange/box
pipeline in `emit7.py`) and 14,734 `tangent` boxes (exact-LDL convexity
pruning). This file is the tangent half's *receipt shape*: every tangent box is
an instance of the single theorem below, whose convexity engine is lane CLZ-D's
`CLZ.tangent_assembly` (adopted verbatim in `CLZCert/Cert/Tangent.lean`).

What an instance must supply (the named residual — it is CLZ-D's output, not
this lane's):

* `w' w'' : ℝ → ℝ` with `HasDerivAt wfun (w' x) x` and `HasDerivAt w' (w'' x) x`
  on each block window `(lo b, hi b)` — CLZ-D `DerivBounds.hasDerivAt_wfun`,
  `hasDerivAt_wfunD` (IN FLIGHT: no `.olean` in their tree at session end);
* `μ b ≤ w'' x` on that window — CLZ-D `DerivBounds.wfunD2_lb` fed by the
  `sincD_bracket` / `sincD2_bracket` interval brackets (also in flight);
* the per-box midpoint `mid`, radius `r`, and the window data from
  `tangent_boxes.json` (sha256-pinned extraction of the 14,734 boxes);
* the PSD/LDL witness `hpsd` — CLZ-D `blockForm_nonneg_of_ldl`.

Everything else is arithmetic: the block structure `B`, the weights
`c b = 2/(7−s)`, the linear coefficient `1/3000`, and the fact that this is
exactly `F6`.
-/

namespace CLZ.Cert

open Real
open scoped BigOperators

/-- Gap indexing helper (identical to `Assembly7pt.lean`'s: indices < 6). -/
def g' (g : Fin 6 → ℝ) (n : ℕ) : ℝ := g ⟨n % 6, Nat.mod_lt _ (by omega)⟩

/-- The 7-point certificate functional, verbatim from `Assembly7pt.lean`. -/
noncomputable def F6 (g : Fin 6 → ℝ) : ℝ :=
  (∑ i ∈ Finset.range 6, g' g i) / 3000 +
    ∑ s ∈ Finset.Icc 1 6, (2 / ((7 - s : ℕ) : ℝ)) *
      ∑ i ∈ Finset.range (7 - s), CLZ.kk (∑ j ∈ Finset.range s, g' g (i + j)) ^ 2

/-- The certificate's kernel function: `w = kk²` (lane CLZ-D calls it `wfun`). -/
noncomputable def wfun (x : ℝ) : ℝ := CLZ.kk x ^ 2

/-- **Tangent box receipt (one instance per tangent box).** Given the block
decomposition of `F6` (21 blocks), second-derivative data with a `μ` bracket,
per-box midpoint/radius data, and the PSD witness, the box bound holds. -/
theorem tangent_box_receipt
    {ι : Type*} [Fintype ι]
    (B : ι → Finset (Fin 6)) (c : ι → ℝ) (hc : ∀ b, 0 ≤ c b)
    (hF : ∀ g : Fin 6 → ℝ, F6 g = CLZ.certFun B c (fun _ => (1:ℝ)/3000) wfun g)
    (w' w'' : ℝ → ℝ) (lo hi : ι → ℝ)
    (hwd : ∀ b, ∀ x ∈ Set.Ioo (lo b) (hi b), HasDerivAt wfun (w' x) x)
    (hwd2 : ∀ b, ∀ x ∈ Set.Ioo (lo b) (hi b), HasDerivAt w' (w'' x) x)
    (μ : ι → ℝ) (hμ : ∀ b, ∀ x ∈ Set.Ioo (lo b) (hi b), μ b ≤ w'' x)
    (mid r : Fin 6 → ℝ) (hr : ∀ a, 0 ≤ r a)
    (wlo : ι → ℝ) (hwb : ∀ b, wlo b ≤ wfun (∑ a ∈ B b, mid a))
    (g : Fin 6 → ℝ) (hg : ∀ a, |g a - mid a| ≤ r a)
    (hmem : ∀ b, (∑ a ∈ B b, mid a) ∈ Set.Ioo (lo b) (hi b) ∧
      (∑ a ∈ B b, g a) ∈ Set.Ioo (lo b) (hi b))
    (hpsd : 0 ≤ ∑ b, c b * μ b * (∑ a ∈ B b, (g a - mid a)) ^ 2) :
    (∑ a, ((1:ℝ)/3000) * mid a) + ∑ b, c b * wlo b
        - (∑ a, ((1:ℝ)/3000) * r a)
        - ∑ b, c b * |w' (∑ a ∈ B b, mid a)| * (∑ a ∈ B b, r a)
      ≤ F6 g := by
  rw [hF g]
  exact CLZ.tangent_assembly B c hc (fun _ => (1:ℝ)/3000) (fun _ => by norm_num)
    wfun w' w'' lo hi hwd hwd2 μ hμ mid r hr wlo hwb g hg hmem hpsd

/-! ## The receipt's numeric close (CONVEXITY_REPORT §4b) and the hoisted mcert -/

/-- **`tbox_<i>`: one instance per tangent box** (CONVEXITY_REPORT §5(a)).

`hnum` is the *sound* numeric close: it charges the linear-radius term
`∑_a lin_a r_a`, which the generator's recorded `bounds[i]` omits
(`gen_7pt.tangent_of`'s `total` never subtracts `|q_a|/3000`). So the emitted
literal must be `bounds[i] − Σ_a rad_a·GRID/3000`, NOT `bounds[i]`. Measured on
all 14,734 boxes (`emit_tangent.py`, independent re-run of the §4b audit):
min margin 7.000966e-4 after the charge, 0 boxes lost. -/
theorem tangent_box_close
    {ι : Type*} [Fintype ι]
    (B : ι → Finset (Fin 6)) (c : ι → ℝ) (hc : ∀ b, 0 ≤ c b)
    (hF : ∀ g : Fin 6 → ℝ, F6 g = CLZ.certFun B c (fun _ => (1:ℝ)/3000) wfun g)
    (w' w'' : ℝ → ℝ) (lo hi : ι → ℝ)
    (hwd : ∀ b, ∀ x ∈ Set.Ioo (lo b) (hi b), HasDerivAt wfun (w' x) x)
    (hwd2 : ∀ b, ∀ x ∈ Set.Ioo (lo b) (hi b), HasDerivAt w' (w'' x) x)
    (μ : ι → ℝ) (hμ : ∀ b, ∀ x ∈ Set.Ioo (lo b) (hi b), μ b ≤ w'' x)
    (mid r : Fin 6 → ℝ) (hr : ∀ a, 0 ≤ r a)
    (wlo : ι → ℝ) (hwb : ∀ b, wlo b ≤ wfun (∑ a ∈ B b, mid a))
    (g : Fin 6 → ℝ) (hg : ∀ a, |g a - mid a| ≤ r a)
    (hmem : ∀ b, (∑ a ∈ B b, mid a) ∈ Set.Ioo (lo b) (hi b) ∧
      (∑ a ∈ B b, g a) ∈ Set.Ioo (lo b) (hi b))
    (hpsd : 0 ≤ ∑ b, c b * μ b * (∑ a ∈ B b, (g a - mid a)) ^ 2)
    (hnum : (19:ℝ)/5000 ≤ (∑ a, ((1:ℝ)/3000) * mid a) + ∑ b, c b * wlo b
        - (∑ a, ((1:ℝ)/3000) * r a)
        - ∑ b, c b * |w' (∑ a ∈ B b, mid a)| * (∑ a ∈ B b, r a)) :
    (19:ℝ)/5000 ≤ F6 g :=
  le_trans hnum (tangent_box_receipt B c hc hF w' w'' lo hi hwd hwd2 μ hμ
    mid r hr wlo hwb g hg hmem hpsd)

/-- **The hoisted `mcert` (CONVEXITY_REPORT §5, brick 1).** ONE fact per distinct
21-`μ` tuple, shared by every box carrying that tuple — never one per box. `hfac`
is the finite exact-ℚ factorisation `Aᵀ diag(c·μ) A = L diag(D) Lᵀ`, which
depends only on the tuple, and `D ≥ 0` (keep `piv ≥ 0`: `piv > 0` alone drops
the singular boxes). Emit `mcert_<sha256(tuple)>` as this statement and each box
discharges its `hpsd` in one application. -/
theorem mcert_dispatch
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → Finset (Fin 6)) (c μ : ι → ℝ)
    (L : Matrix (Fin 6) (Fin 6) ℝ) (D : Fin 6 → ℝ) (hD : ∀ k, 0 ≤ D k)
    (hfac : Matrix.transpose (CLZ.incMat B) * Matrix.diagonal (fun b => c b * μ b)
      * CLZ.incMat B = L * Matrix.diagonal D * Matrix.transpose L)
    (q : Fin 6 → ℝ) :
    0 ≤ ∑ b, c b * μ b * (∑ a ∈ B b, q a) ^ 2 :=
  CLZ.blockForm_nonneg_of_ldl B (fun b => c b * μ b) L D hD hfac q

end CLZ.Cert
