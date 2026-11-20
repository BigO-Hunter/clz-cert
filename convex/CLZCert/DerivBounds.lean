import CLZCert.Convexity
import CLZCert.Cert.Glue

/-!
# CLZ derivative bounds for the tangent layer (lane CLZ-D)

The kernel side of the convexity layer: exact `sinc'` / `sinc''` forms, their
`HasDerivAt` instances, the resulting `w = k²` first/second derivative forms
(literally the generator's `w_point` formulas), and the interval brackets that
certify them from the Gaps lane's `sin`/`cos` partial-sum enclosures.

## Derivative forms

With `sinc u = sin u / u` (Mathlib `Real.sinc`; `u ≠ 0` on every window used
here — the certificate's `w''` table starts at `x = 0.95`, far from the
removable singularity at `u = 0`):

* `sincD u  = (u * cos u − sin u) / u²`
* `sincD2 u = ((2 − u²) * sin u − 2 u cos u) / u³`

and for `K(x) = ½[sinc(πx−a) + sinc(πx+a)]`, `k = K/K(0)`, `w = k²`:

* `KfnD x  = (π/2)  · (sincD (πx−a) + sincD (πx+a))`
* `KfnD2 x = (π²/2) · (sincD2 (πx−a) + sincD2 (πx+a))`
* `wfunD x  = 2 k(x) k'(x)`
* `wfunD2 x = 2 (k'(x)² + k(x) k''(x))`   (the generator's `wpp`)

`HasDerivAt` is proved for all four, so `tangent_lower` (Convexity.lean) applies
to `wfun` under a `μ ≤ wfunD2` bracket — that is `tangent_lower_wfun`, the
receipt entry point.

## Brackets

`sincD_bracket` / `sincD2_bracket` reduce a derivative bracket to a numerator
bracket plus four corner facts, delegating the division to the Gaps lane's
proved `CLZ.Cert.corner_div_bracket` (the sin/cos partial-sum enclosure
technique generalized from `sinc` to `sinc'`, `sinc''`). `mul_lb` is the corner
product lower bound the numerator bracket needs, and `wfunD2_lb` assembles
`2 (sqlo + prlo) ≤ w''` from certified square and product lower bounds.

Scope note (honest): the derivative brackets are stated for positive windows
`0 < ulo ≤ u`. The certificate's tangent boxes live at `x ≥ 0.95`
(`W2_START = 3800` of `4000` cells), where `πx ± a > 0`; the reflected
`x < 0` regime used by the interval layer is not covered here.

Axiom footprint: none beyond the Lean/Mathlib kernel (no `sorry`, no `axiom`).
-/

namespace CLZ

open Real Filter
open scoped Topology

/-! ## `sinc'` and `sinc''` -/

/-- `sinc u = sin u / u` at nonzero `u`. -/
theorem sinc_eq_div (u : ℝ) (hu : u ≠ 0) : sinc u = sin u / u := by
  simp [Real.sinc, hu]

/-- First derivative form of `sinc`. -/
noncomputable def sincD (u : ℝ) : ℝ := (u * cos u - sin u) / u ^ 2

/-- Second derivative form of `sinc`. -/
noncomputable def sincD2 (u : ℝ) : ℝ := ((2 - u ^ 2) * sin u - 2 * u * cos u) / u ^ 3

/-- `d/du (u²) = 2u`. -/
theorem hasDerivAt_sq (u : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2) (2 * u) u := by
  have h := (hasDerivAt_id u).mul (hasDerivAt_id u)
  convert h using 1
  · ext s; simp [pow_two]
  · simp only [id_eq]; ring

/-- `d/du (u cos u) = cos u − u sin u`. -/
theorem hasDerivAt_mul_cos (u : ℝ) :
    HasDerivAt (fun v : ℝ => v * cos v) (cos u - u * sin u) u := by
  have h := (hasDerivAt_id u).mul (Real.hasDerivAt_cos u)
  convert h using 1
  · ext s; simp
  · simp only [id_eq]; ring

/-- `d/du (u cos u − sin u) = −u sin u`. -/
theorem hasDerivAt_num_sincD (u : ℝ) :
    HasDerivAt (fun v : ℝ => v * cos v - sin v) (-u * sin u) u := by
  have h := (hasDerivAt_mul_cos u).sub (Real.hasDerivAt_sin u)
  convert h using 1
  ring

/-- `HasDerivAt sinc (sincD u) u` for `u ≠ 0`. -/
theorem hasDerivAt_sinc (u : ℝ) (hu : u ≠ 0) : HasDerivAt sinc (sincD u) u := by
  have hev : sinc =ᶠ[𝓝 u] fun v : ℝ => sin v / v := by
    filter_upwards [eventually_ne_nhds hu] with v hv
    exact sinc_eq_div v hv
  have hd : HasDerivAt (fun v : ℝ => sin v / v) ((cos u * u - sin u * 1) / u ^ 2) u :=
    (Real.hasDerivAt_sin u).div (hasDerivAt_id u) hu
  have h := hev.hasDerivAt_iff.mpr hd
  convert h using 1
  all_goals first
    | (ext v; simp [sincD])
    | (simp only [sincD]; ring_nf)

/-- `HasDerivAt sincD (sincD2 u) u` for `u ≠ 0`. -/
theorem hasDerivAt_sincD (u : ℝ) (hu : u ≠ 0) : HasDerivAt sincD (sincD2 u) u := by
  have hd := (hasDerivAt_num_sincD u).div (hasDerivAt_sq u) (pow_ne_zero 2 hu)
  convert hd using 1
  all_goals first
    | (ext v; simp [sincD])
    | (simp only [sincD2]; field_simp; ring)

/-! ## The kernel's derivatives -/

/-- `d/dx sinc (π x + c) = π · sincD (π x + c)`. -/
theorem hasDerivAt_sinc_affine (c x : ℝ) (h : π * x + c ≠ 0) :
    HasDerivAt (fun y : ℝ => sinc (π * y + c)) (π * sincD (π * x + c)) x := by
  have hinner : HasDerivAt (fun y : ℝ => π * y + c) π x := by
    simpa using ((hasDerivAt_id x).const_mul π).add_const c
  have hc := (hasDerivAt_sinc (π * x + c) h).comp x hinner
  convert hc using 1
  all_goals first
    | (ext y; simp [Function.comp])
    | ring

/-- `d/dx sincD (π x + c) = π · sincD2 (π x + c)`. -/
theorem hasDerivAt_sincD_affine (c x : ℝ) (h : π * x + c ≠ 0) :
    HasDerivAt (fun y : ℝ => sincD (π * y + c)) (π * sincD2 (π * x + c)) x := by
  have hinner : HasDerivAt (fun y : ℝ => π * y + c) π x := by
    simpa using ((hasDerivAt_id x).const_mul π).add_const c
  have hc := (hasDerivAt_sincD (π * x + c) h).comp x hinner
  convert hc using 1
  all_goals first
    | (ext y; simp [Function.comp])
    | ring

/-- First derivative form of `K(x) = ½[sinc(πx−a) + sinc(πx+a)]`. -/
noncomputable def KfnD (x : ℝ) : ℝ := π / 2 * (sincD (π * x - a) + sincD (π * x + a))

/-- Second derivative form of `K`. -/
noncomputable def KfnD2 (x : ℝ) : ℝ :=
  π ^ 2 / 2 * (sincD2 (π * x - a) + sincD2 (π * x + a))

/-- `HasDerivAt Kfn (KfnD x) x`, away from `πx = ±a`. -/
theorem hasDerivAt_Kfn (x : ℝ) (h1 : π * x - a ≠ 0) (h2 : π * x + a ≠ 0) :
    HasDerivAt Kfn (KfnD x) x := by
  have h1' : HasDerivAt (fun y : ℝ => sinc (π * y + (-a))) (π * sincD (π * x + (-a))) x :=
    hasDerivAt_sinc_affine (-a) x (by simpa [sub_eq_add_neg] using h1)
  have h2' : HasDerivAt (fun y : ℝ => sinc (π * y + a)) (π * sincD (π * x + a)) x :=
    hasDerivAt_sinc_affine a x h2
  have hhalf := (h1'.add h2').div_const 2
  convert hhalf using 1
  all_goals first
    | (ext y; simp [Kfn, sub_eq_add_neg])
    | (simp only [KfnD, sub_eq_add_neg]; ring)

/-- `HasDerivAt KfnD (KfnD2 x) x`, away from `πx = ±a`. -/
theorem hasDerivAt_KfnD (x : ℝ) (h1 : π * x - a ≠ 0) (h2 : π * x + a ≠ 0) :
    HasDerivAt KfnD (KfnD2 x) x := by
  have h1' : HasDerivAt (fun y : ℝ => sincD (π * y + (-a))) (π * sincD2 (π * x + (-a))) x :=
    hasDerivAt_sincD_affine (-a) x (by simpa [sub_eq_add_neg] using h1)
  have h2' : HasDerivAt (fun y : ℝ => sincD (π * y + a)) (π * sincD2 (π * x + a)) x :=
    hasDerivAt_sincD_affine a x h2
  have hscale := (h1'.add h2').const_mul (π / 2)
  convert hscale using 1
  all_goals first
    | (ext y; simp [KfnD, sub_eq_add_neg])
    | (simp only [KfnD2, sub_eq_add_neg]; ring)

/-! ## The normalized kernel squared: `w = (K/K(0))²` -/

/-- `w(x) = k(x)²` with `k = K/K(0)` — the certificate's kernel weight. -/
noncomputable def wfun (x : ℝ) : ℝ := (Kfn x / Kfn 0) ^ 2

/-- `w'(x) = 2 k(x) k'(x)`. -/
noncomputable def wfunD (x : ℝ) : ℝ := 2 * (Kfn x / Kfn 0) * (KfnD x / Kfn 0)

/-- `w''(x) = 2 (k'(x)² + k(x) k''(x))` — the generator's `wpp`. -/
noncomputable def wfunD2 (x : ℝ) : ℝ :=
  2 * ((KfnD x / Kfn 0) ^ 2 + (Kfn x / Kfn 0) * (KfnD2 x / Kfn 0))

/-- `w''` in the generator's unnormalized form (its `w_lower2`/`w_point`). -/
theorem wfunD2_eq (x : ℝ) :
    wfunD2 x = 2 * ((KfnD x) ^ 2 + Kfn x * KfnD2 x) / (Kfn 0) ^ 2 := by
  have h0 : Kfn 0 ≠ 0 := Kfn_zero_ne
  simp only [wfunD2]
  field_simp

/-- `HasDerivAt wfun (wfunD x) x`. -/
theorem hasDerivAt_wfun (x : ℝ) (h1 : π * x - a ≠ 0) (h2 : π * x + a ≠ 0) :
    HasDerivAt wfun (wfunD x) x := by
  have hk : HasDerivAt (fun y : ℝ => Kfn y / Kfn 0) (KfnD x / Kfn 0) x :=
    (hasDerivAt_Kfn x h1 h2).div_const (Kfn 0)
  have hsq := hk.pow 2
  have hval : ((2:ℕ):ℝ) * (Kfn x / Kfn 0) ^ (2 - 1) * (KfnD x / Kfn 0) = wfunD x := by
    simp only [wfunD]; norm_num
  have hfun : ((fun y : ℝ => Kfn y / Kfn 0) ^ 2) = wfun := by
    funext y; simp [wfun]
  rw [hval, hfun] at hsq
  exact hsq

/-- `HasDerivAt wfunD (wfunD2 x) x`. -/
theorem hasDerivAt_wfunD (x : ℝ) (h1 : π * x - a ≠ 0) (h2 : π * x + a ≠ 0) :
    HasDerivAt wfunD (wfunD2 x) x := by
  have hk : HasDerivAt (fun y : ℝ => Kfn y / Kfn 0) (KfnD x / Kfn 0) x :=
    (hasDerivAt_Kfn x h1 h2).div_const (Kfn 0)
  have hk' : HasDerivAt (fun y : ℝ => KfnD y / Kfn 0) (KfnD2 x / Kfn 0) x :=
    (hasDerivAt_KfnD x h1 h2).div_const (Kfn 0)
  have hprod := (hk.mul hk').const_mul 2
  have hfun : (fun y : ℝ => 2 * ((fun y : ℝ => Kfn y / Kfn 0) *
      fun y : ℝ => KfnD y / Kfn 0) y) = wfunD := by
    funext y; simp only [wfunD, Pi.mul_apply]; ring
  have hval : 2 * ((KfnD x / Kfn 0) * (KfnD x / Kfn 0)
      + (Kfn x / Kfn 0) * (KfnD2 x / Kfn 0)) = wfunD2 x := by
    simp only [wfunD2]; ring
  rw [hfun, hval] at hprod
  exact hprod

/-- **The tangent lemma at the CLZ kernel.** Away from `πx = ±a`, `wfun` has the
derivative pair `(wfunD, wfunD2)`, so a `μ ≤ wfunD2` bracket on a window makes
the `μ`-quadratic tangent at any interior `m` a lower bound for `wfun`. -/
theorem tangent_lower_wfun {lo hi μ : ℝ}
    (hwin : ∀ x ∈ Set.Ioo lo hi, π * x - a ≠ 0 ∧ π * x + a ≠ 0)
    (hμ : ∀ x ∈ Set.Ioo lo hi, μ ≤ wfunD2 x)
    {m t : ℝ} (hm : m ∈ Set.Ioo lo hi) (ht : t ∈ Set.Ioo lo hi) :
    wfun m + wfunD m * (t - m) + μ / 2 * (t - m) ^ 2 ≤ wfun t :=
  tangent_lower (fun x hx => hasDerivAt_wfun x (hwin x hx).1 (hwin x hx).2)
    (fun x hx => hasDerivAt_wfunD x (hwin x hx).1 (hwin x hx).2) hμ hm ht

/-! ## Interval brackets -/

/-- Linear interpolation of a lower bound across an interval: if `plo` is below
both `c * blo` and `c * bhi`, it is below `c * b` for every `b ∈ [blo, bhi]`. -/
theorem le_mul_of_endpoints (c b blo bhi plo : ℝ) (hb1 : blo ≤ b) (hb2 : b ≤ bhi)
    (h1 : plo ≤ c * blo) (h2 : plo ≤ c * bhi) : plo ≤ c * b := by
  rcases le_or_gt 0 c with hc | hc
  · nlinarith [mul_le_mul_of_nonneg_left hb1 hc]
  · nlinarith [mul_le_mul_of_nonpos_left hb2 (le_of_lt hc)]

/-- Corner product lower bound: `a * b` on a rectangle attains its minimum at a
corner, so four corner facts bound it from below. -/
theorem mul_lb (a b alo ahi blo bhi plo : ℝ)
    (ha : alo ≤ a ∧ a ≤ ahi) (hb : blo ≤ b ∧ b ≤ bhi)
    (h1 : plo ≤ alo * blo) (h2 : plo ≤ alo * bhi)
    (h3 : plo ≤ ahi * blo) (h4 : plo ≤ ahi * bhi) :
    plo ≤ a * b := by
  have e1 : plo ≤ alo * b := le_mul_of_endpoints alo b blo bhi plo hb.1 hb.2 h1 h2
  have e2 : plo ≤ ahi * b := le_mul_of_endpoints ahi b blo bhi plo hb.1 hb.2 h3 h4
  rcases le_or_gt 0 b with hb0 | hb0
  · nlinarith [mul_le_mul_of_nonneg_right ha.1 hb0]
  · nlinarith [mul_le_mul_of_nonpos_right ha.2 (le_of_lt hb0)]

/-- `sinc'` bracket on a positive window: the numerator bracket plus four corner
facts for the division by `u²`, delegated to the proved Gaps-lane
`corner_div_bracket`. -/
theorem sincD_bracket (u ulo uhi nlo nhi lo hi : ℝ)
    (hu1 : ulo ≤ u) (hu2 : u ≤ uhi) (hulo : 0 < ulo)
    (hn : nlo ≤ u * cos u - sin u ∧ u * cos u - sin u ≤ nhi)
    (h1 : lo ≤ nlo / uhi ^ 2) (h2 : lo ≤ nlo / ulo ^ 2)
    (h3 : nhi / ulo ^ 2 ≤ hi) (h4 : nhi / uhi ^ 2 ≤ hi) :
    lo ≤ sincD u ∧ sincD u ≤ hi := by
  have ht1 : ulo ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (le_of_lt hulo) hu1 2
  have ht2 : u ^ 2 ≤ uhi ^ 2 := pow_le_pow_left₀ (le_of_lt hulo |>.trans hu1) hu2 2
  have ht0 : 0 < ulo ^ 2 := pow_pos hulo 2
  have h := CLZ.Cert.corner_div_bracket (u ^ 2) (u * cos u - sin u) lo hi
    (ulo ^ 2) (uhi ^ 2) nlo nhi ht0 ht1 ht2 hn h1 h2 h3 h4
  simpa [sincD] using h

/-- `sinc''` bracket on a positive window (division by `u³`). -/
theorem sincD2_bracket (u ulo uhi nlo nhi lo hi : ℝ)
    (hu1 : ulo ≤ u) (hu2 : u ≤ uhi) (hulo : 0 < ulo)
    (hn : nlo ≤ (2 - u ^ 2) * sin u - 2 * u * cos u ∧
      (2 - u ^ 2) * sin u - 2 * u * cos u ≤ nhi)
    (h1 : lo ≤ nlo / uhi ^ 3) (h2 : lo ≤ nlo / ulo ^ 3)
    (h3 : nhi / ulo ^ 3 ≤ hi) (h4 : nhi / uhi ^ 3 ≤ hi) :
    lo ≤ sincD2 u ∧ sincD2 u ≤ hi := by
  have ht1 : ulo ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (le_of_lt hulo) hu1 3
  have ht2 : u ^ 3 ≤ uhi ^ 3 := pow_le_pow_left₀ (le_of_lt hulo |>.trans hu1) hu2 3
  have ht0 : 0 < ulo ^ 3 := pow_pos hulo 3
  have h := CLZ.Cert.corner_div_bracket (u ^ 3) ((2 - u ^ 2) * sin u - 2 * u * cos u) lo hi
    (ulo ^ 3) (uhi ^ 3) nlo nhi ht0 ht1 ht2 hn h1 h2 h3 h4
  simpa [sincD2] using h

/-- `w''` lower bound from certified square and product lower bounds
(`sqlo ≤ k'²`, `prlo ≤ k · k''`), in the generator's normalized form. -/
theorem wfunD2_lb (x sqlo prlo : ℝ)
    (hsq : sqlo ≤ (KfnD x / Kfn 0) ^ 2)
    (hpr : prlo ≤ (Kfn x / Kfn 0) * (KfnD2 x / Kfn 0)) :
    2 * (sqlo + prlo) ≤ wfunD2 x := by
  simp only [wfunD2]
  linarith

end CLZ
