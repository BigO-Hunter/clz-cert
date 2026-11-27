# CONVEXITY_REPORT — lane CLZ-D (the tangent layer), 2026-11-07

Working clone: `clz-cert-convex` (fresh clone of `clz-cert` at
`886c185`). Files: `CLZCert/Convexity.lean`, `CLZCert/DerivBounds.lean`,
this report, plus the two import lines added to `CLZCert.lean`.

**Headline: the tangent lemma, the block assembly and the LDL/PSD certificate
are PROVED. The 14,734 tangent-evidence boxes are NOT yet discharged — the
per-box emission (the interval lane's job, ~CLZ-A2) is unbuilt, and the `w''`
cell-table bridge is specified but not emitted. `seven_point_certificate` stays
an axiom until that emission runs.**

## 1. The tangent lemma — PROVED (`CLZ.tangent_lower`)

```lean
theorem CLZ.tangent_lower {w w' w'' : ℝ → ℝ} {lo hi μ : ℝ}
    (hw  : ∀ x ∈ Set.Ioo lo hi, HasDerivAt w (w' x) x)
    (hw' : ∀ x ∈ Set.Ioo lo hi, HasDerivAt w' (w'' x) x)
    (hμ  : ∀ x ∈ Set.Ioo lo hi, μ ≤ w'' x)
    {m t : ℝ} (hm : m ∈ Set.Ioo lo hi) (ht : t ∈ Set.Ioo lo hi) :
    w m + w' m * (t - m) + μ / 2 * (t - m) ^ 2 ≤ w t
```

Route: `ψ := w − (μ/2)·Id²` has `ψ'' = w'' − μ ≥ 0`, hence is convex by
`convexOn_of_hasDerivWithinAt2_nonneg` (Mathlib `Analysis/Convex/Deriv.lean`)
with the derivative pair supplied **explicitly** (`f' := w' − μ·Id`,
`f'' := w'' − μ`) — no `deriv` unfolding, so the `HasDerivAt` facts I can prove
are exactly the facts consumed. The tangent line then follows from
`ConvexOn.slope_le_of_hasDerivAt` (t < m) and `ConvexOn.le_slope_of_hasDerivAt`
(m < t), and the `μ`-quadratic is recovered by expanding.

Two properties worth noting:

* **`μ` may have either sign.** The one statement therefore covers convex pieces
  (`μ > 0`, the strict supporting hyperplane) *and* concave pieces (`μ < 0`,
  where the quadratic term is a weaker but sound lower bound). "Convexity /
  concavity per piece" needs no second lemma — the generator's per-cell
  `w''`-minimum *is* `μ`, sign and all.
* It is stated against an **open** interval `Ioo lo hi`; the receipt supplies
  the open window that contains the whole closed cell range.

## 2. The block assembly — PROVED (`CLZ.tangent_assembly`)

`certFun B c lin w g = ∑_a lin_a g_a + ∑_b c_b · w (∑_{a∈B b} g_a)` — the 21
blocks of the 7-point functional (`s = 1..6`, `st = 0..6−s`, `c_b = 2/(7−s)`,
`lin_a = 1/3000`).

```lean
theorem CLZ.tangent_assembly ... :
    (∑ a, lin a * mid a) + ∑ b, c b * wlo b
        - (∑ a, lin a * r a) - ∑ b, c b * |w' (∑ a ∈ B b, mid a)| * (∑ a ∈ B b, r a)
      ≤ certFun B c lin w g
```

given `0 ≤ c_b`, `0 ≤ lin_a`, `|g a − mid a| ≤ r a`, per-block
`μ_b ≤ w''` on `Ioo (lo b) (hi b)` containing both `P_b mid` and `P_b g`,
per-block `wlo_b ≤ w (P_b mid)`, and the PSD fact
`0 ≤ ∑_b c_b μ_b (P_b(g) − P_b(mid))²`.

The right-hand side is **exactly** the generator's `tangent_of` `total`
(`Σ mid/3000 + Σ c·w_lower(P) − Σ_a rad_a·gradmag_a`), because
`Σ_a rad_a · gradmag_a = Σ_b c_b |w'(P_b mid)| · Σ_{a∈B b} r_a`. The equality
is per-block, so the Lean side needs **no sum rearrangement**: each block's
linear remainder is bounded by its own absolute value, and the `(∑|q|)` step is
`Finset.abs_sum_le_sum_abs`. This is the single most emissive detail of the
design — it turns a gradient table into 21 independent per-block facts.

## 3. The LDL / PSD certificate — PROVED, with one caveat for the emitter

```lean
theorem CLZ.blockForm_nonneg_of_ldl (B) (w) (L) (D) (hD : ∀ k, 0 ≤ D k)
    (hfac : (incMat B)ᵀ * Matrix.diagonal w * incMat B = L * Matrix.diagonal D * Lᵀ)
    (q) : 0 ≤ blockForm B w q
```

`blockForm B w q = ∑_b w_b (∑_{a∈B b} q_a)²` is the bilinear form of
`Aᵀ diag(w) A` (`A = incMat B`, `blockForm_eq_qform`), and `D ≥ 0` makes
`L diag(D) Lᵀ` PSD (`Matrix.PosSemidef.mul_mul_conjTranspose_same` →
`dotProduct_mulVec_nonneg`). So the PSD check is a **finite exact-ℚ
factorisation** — exactly what `gen_7pt.py`'s `ldl_pd` computes — and no
eigenvalue reasoning is needed anywhere.

**Caveat (found by the sanity test).** The generator's `ldl_pd` requires strictly
positive pivots (`if piv <= 0: return False`), but the certificate only needs
`D ≥ 0`. `blockForm_negweight_demo` in `Convexity.lean` exhibits a block family
with weights `(2, −1)` whose matrix is PSD and **singular** (`D = (1, 0)`).
Boxes whose `M` is singular are currently *discarded* by the generator (they
fall through to a split). That is sound but wasteful; if the discarded count
matters, relaxing `ldl_pd` to `piv >= 0` recovers them — this layer already
accepts `D ≥ 0`.

**Cost model for the emitter.** Per box, the PSD path needs the 6 `D ≥ 0` facts
plus the 36-entry matrix identity `Aᵀ diag(w) A = L diag(D) Lᵀ`. Both are
`norm_num` statements about recorded rationals. Do **not** emit them per box:
`w` is the 21-tuple of `μ` values, each a **cell-range minimum from a finite
table**, so the tuple recurs across boxes. Emit one `mcert_<hash>` theorem per
*distinct* tuple and have each box cite it. The 21-vector is the natural key.

## 4. The brackets — PROVED (forms + propagation), emission-side data open

`CLZCert/DerivBounds.lean`:

* Exact forms: `sincD u = (u cos u − sin u)/u²`,
  `sincD2 u = ((2 − u²) sin u − 2u cos u)/u³`,
  `KfnD x = (π/2)(sincD(πx−a) + sincD(πx+a))`,
  `KfnD2 x = (π²/2)(sincD2(πx−a) + sincD2(πx+a))`,
  `wfunD x = 2 k k'`, `wfunD2 x = 2(k'² + k k'')` — these are literally the
  generator's `w_point` formulas (`wfunD2_eq` also gives the unnormalized
  `2(K'² + K K'')/K(0)²` form that `w_lower2` computes).
* `HasDerivAt` proved for all six (`hasDerivAt_sinc`, `hasDerivAt_sincD`, the
  affine compositions, `hasDerivAt_Kfn`, `hasDerivAt_KfnD`,
  `hasDerivAt_wfun`, `hasDerivAt_wfunD`), so `tangent_lower` genuinely
  instantiates — `tangent_lower_wfun` is the kernel-level statement.
* `sincD_bracket` / `sincD2_bracket`: numerator bracket + four corner facts ⟹
  derivative bracket, with the division delegated to the Gaps lane's **already
  proved** `CLZ.Cert.corner_div_bracket`. That is the "sin/cos partial-sum
  technique generalizes" claim made concrete — no new division lemma.
* `mul_lb` (corner product lower bound, via `le_mul_of_endpoints`),
  `wfunD2_lb` (`2(sqlo + prlo) ≤ w''` from certified square/product bounds).

**Open on the emission side (honest):** the `w''`-cell table (the analogue of
`wt` for `w'`) is not materialized in Lean. Each block needs
`μ_b ≤ wfunD2 x` for `x` in the closed block range; the receipt gets it from a
`w2`-cell table exactly as the interval lane gets `wt`, via
`sincD2_bracket` + `mul_lb` + `wfunD2_lb`, then a range-min dispatch over the
cells. That dispatch (the `wrange` analogue) is CLZ-A2's machinery and is
**not built here**.

## 4b. AUDIT: the recorded tangent bounds omit one term (harmless, but the
interface must account for it)

`gen_7pt.py`'s `tangent_of` computes

```
total = ⌊Σ mid_a/3000⌋ + Σ_b c_b·wlo_b − Σ_a rad_a · gradmag_a
```

and the recorded `bounds[i]` for the 14,734 tangent boxes **is** that `total`
(verified bit-exact on 5 sampled boxes against the live tables: `match=True`,
`diff=0`). But the sound bound also needs `− Σ_a rad_a/3000` — the `|q_a|/3000`
part of the linear term, which `total` omits (`gradmag` accumulates only
`c_b|w'(P_b)|`, never `lin_a = 1/3000`). So the recorded number is optimistic by
`Σ_a rad_a/3000`.

Measured on the full certified data (all 14,734 tangent boxes):

| quantity | value |
|---|---|
| min margin over target, `bounds[i] − ⌈19·GRID/5000⌉` | **8.15e-4** |
| 1st percentile / median margin | 1.37e-3 / 3.30e-3 |
| max missing linear slack `Σ_a rad_a/3000` | **1.21e-4** |
| boxes whose margin is below the missing slack | **0 / 14,734** |
| worst `margin − slack` | 7.00e-4 (idx 28591) |

So the prune is **sound as certified** — every box still clears 19/5000 by
≥ 7.0e-4 once the omitted term is charged. `tangent_assembly` deliberately uses
the *sound* RHS (it subtracts `Σ_a lin_a r_a`), which is why the receipt cannot
reuse `bounds[i]` verbatim:

> **Instruction for CLZ-A2:** the Lean close must be against
> `bounds[i] − Σ_a rad_a · GRID/3000`, not `bounds[i]`. Since the worst-case
> shortfall (1.21e-4) is 6.7× below the smallest margin (8.15e-4), no box is
> lost and no re-run of the search is needed. Either subtract the slack when
> emitting the numeric close, or add the hypothesis
> `19/5000 + Σ_a lin_a r_a ≤ certFun-at-mid …` — subtracting is cheaper.

## 5. Interface contract for the receipts lane (CLZ-A2)

No tangent receipts exist yet in `clz-cert`, so this defines the shape. A
tangent box receipt for box `mid, r` (6 coordinates) should emit:

```lean
-- (a) the box bound, one per box
theorem tbox_<i> (g : Fin 6 → ℝ) (hg : ∀ a, |g a - mid a| ≤ r a) :
    (19:ℝ)/5000 ≤ CLZ.certFun B c lin CLZ.wfun g
-- (b) its certificate data as hypotheses
--     wlo   : 21 rationals   (certified w(P_b mid) lower bounds)
--     μ     : 21 rationals   (certified w'' cell-range minima)
--     hpsd  : 0 ≤ ∑ b, c b * μ b * (∑ a ∈ B b, (g a - mid a))^2
--             ← from `blockForm_nonneg_of_ldl` with the shared `mcert_<hash>`
--     numeric : Σ mid/3000 + Σ c wlo − Σ lin·r − Σ c|w'(P_b mid)|·Σ r ≥ 19/5000
```

Concretely the three Lean bricks and their exact signatures:

1. `CLZ.blockForm_nonneg_of_ldl B w L D hD hfac q`
   → the `hpsd` fact, with `w := fun b => c b * μ b` and `B, c` the frozen
   21-block family. Hoist `mcert_<hash>` as described in §3.
2. `CLZ.tangent_lower_wfun hwin hμ hm ht`
   (or `CLZ.tangent_lower` directly) → `P_b`-level Taylor facts, instantiating
   `μ := μ b`, `m := P_b mid`, `t := P_b g`. `hμ` is the `w2`-table dispatch;
   `hwin` is `πx ± a ≠ 0`, discharged by `linarith` from the window literals
   (`x ≥ 0.95` ⟹ `πx > a` by `CLZ.pi_lb`, `CLZ.a_ub`).
3. `CLZ.tangent_assembly …` → the final `19/5000 ≤ certFun …`, given
   `hg`, the 21 block facts from (2), `hpsd` from (1), and the numeric close by
   `norm_num`.

Note the mismatch settled in §4b: `tangent_assembly` bounds `∑ c_b wlo_b` minus
the linear-radius term, so the numeric close must charge
`Σ_a rad_a/3000 ≈ 9.4e-5` against the recorded `bounds[i]`; §4b measures that
this never costs a box. Also
`certFun`'s linear part is `∑ lin_a g_a` with `lin_a = 1/3000`; if CLZ-A2's
`bounds` integer is computed against a different linear normalization, align on
this definition rather than re-deriving.

## 6. Axcheck footprint

`#print axioms` on every theorem in both files:
`[propext, Classical.choice, Quot.sound]` — the three stdlib axioms, and
nothing else. No `sorry`, no `axiom`, no `native_decide`. The Gaps-lane
lemmas consumed (`corner_div_bracket`, `Kfn`, `a`, `pi_lb/ub`,
`Kfn_zero_ne`) are themselves stdlib-only, so the tangent layer adds **zero**
new assumptions; the only non-stdlib assumptions of the whole 7pt submission
remain `jo_bridge_7pt` and `seven_point_certificate`.

## 7. What is left (bounded, in priority order)

1. **`w2` cell table + `wrange` dispatch** — per cell `i`:
   `w2lb i ≤ wfunD2 x` for `x` in the cell, assembled from `sincD2_bracket`,
   `mul_lb`, `wfunD2_lb`; then the 21 range-min lookups per box. *This is the
   bulk of the remaining work* and it is mechanical (same shape as `wt`/`wrange`).
2. **Per-box emission** of `tbox_<i>` (14,734 boxes) + shared `mcert_<hash>`.
3. **Relax `ldl_pd` to `piv >= 0`** if the discarded singular boxes matter
   (§3 caveat); this layer already accepts `D ≥ 0`.
4. **Concave/reflected regime note** — the derivative brackets are stated for
   positive windows `0 < ulo ≤ u`. Tangent boxes live at `x ≥ 0.95` so this is
   sufficient today; a `x < 0` tangent box would need the mirrored bracket.
5. Then `Assembly7pt`'s `seven_point_certificate` swap (CLZ-A2's line) and the
   axcheck shrinks to `{jo_bridge_7pt}` + stdlib.
