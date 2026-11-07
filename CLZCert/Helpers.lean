import Mathlib
import CLZCert.Gaps

/-!
# CLZ receipts helpers (PROVED — consumes the proved Gaps lemmas, adds no new gaps)

Shared machinery for the generated per-box receipts (`CLZCert.Cert.*`):

- `sin_sub_nat_pi` / `sin_add_nat_pi`: reduction of `sin` by natural
  multiples of π (Mathlib `sin π = 0`, `cos π = -1`). The generated receipts
  instantiate these at literal `j : ℕ` and evaluate the `(-1)^j` sign by
  `norm_num` (literal `ℤ`-exponents evaluate directly).
- `sinc_even`, `sinc_bracket_even_cover`, `sinc_small`: reflection to
  nonnegative arguments; `sinc ∈ [0,1]` on `[0,M]`, `M < π` covers reflected
  windows near zero (including `t = 0`) with ample slack.
- `sin_series_sandwich`: the 10-term alternating sandwich, consuming
  `Kernel.sin_partial_abs_bound` (PROVED in CLZCert.Gaps) at `n = 9` with the
  global tail constant `chiG = (π_hi/2)^21/21! ≈ 2.6e-16`.
- `Kfn0_lb` / `Kfn0_ub`: numeric `Kfn 0 = sinc(1/√2)` interval from
  `CLZ.sin_a_lb` and the mirrored `sin_a_ub` (both via
  `Kernel.sin_partial_abs_bound`).

The generated receipts consume these with frozen ℚ literals only.
-/

namespace CLZ.Cert

open Real
open scoped Nat

/-! ## sin reduction by natural multiples of π -/

theorem sin_sub_nat_pi (t : ℝ) : ∀ n : ℕ, sin (t - n*π) = (-1:ℝ)^n * sin t
  | 0 => by simp
  | n+1 => by
    have ih := sin_sub_nat_pi t n
    have hstep : sin ((t - n*π) - π) = -sin (t - n*π) := by
      rw [Real.sin_sub, Real.sin_pi, Real.cos_pi]
      ring
    have hpow : (-1:ℝ)^(n+1) = -((-1:ℝ)^n) := by rw [pow_succ]; ring
    rw [Nat.cast_succ]
    rw [show t - ((n:ℝ) + 1)*π = (t - n*π) - π by ring, hstep, hpow, ih]
    ring

theorem sin_add_nat_pi (t : ℝ) : ∀ n : ℕ, sin (t + n*π) = (-1:ℝ)^n * sin t
  | 0 => by simp
  | n+1 => by
    have ih := sin_add_nat_pi t n
    have hstep : sin ((t + n*π) + π) = -sin (t + n*π) := by
      rw [Real.sin_add, Real.sin_pi, Real.cos_pi]
      ring
    have hpow : (-1:ℝ)^(n+1) = -((-1:ℝ)^n) := by rw [pow_succ]; ring
    rw [Nat.cast_succ]
    rw [show t + ((n:ℝ) + 1)*π = (t + n*π) + π by ring, hstep, hpow, ih]
    ring

/-! ## sinc evenness and reflection -/

theorem sinc_even (t : ℝ) : sinc (-t) = sinc t := by
  by_cases h : t = 0
  · subst h; simp
  · simp [Real.sinc, h, neg_ne_zero.mpr h, Real.sin_neg, neg_div_neg_eq]

/-- Cover an arbitrary argument interval by a bracket on `|t| ≤ m`. -/
theorem sinc_bracket_even_cover (tl th m lo hi : ℝ)
    (hcov : ∀ t, tl ≤ t → t ≤ th → |t| ≤ m)
    (hbr : ∀ w, 0 ≤ w → w ≤ m → lo ≤ sinc w ∧ sinc w ≤ hi) :
    ∀ t, tl ≤ t → t ≤ th → lo ≤ sinc t ∧ sinc t ≤ hi := by
  intro t h1 h2
  have habs := hcov t h1 h2
  have heven : sinc t = sinc |t| := by
    rcases abs_cases t with h | h
    · rw [h.1]
    · rw [h.1, sinc_even]
  rw [heven]
  exact hbr |t| (abs_nonneg t) habs

/-- `sinc ∈ [0,1]` on `[0,M]` with `M < π` (covers `t = 0`). -/
theorem sinc_small (w : ℝ) (hnn : 0 ≤ w) (hM : w ≤ M) (hMlt : M < π) :
    (0:ℝ) ≤ sinc w ∧ sinc w ≤ 1 := by
  constructor
  · by_cases h0 : w = 0
    · subst h0; simp
    · have hwpos : 0 < w := lt_of_le_of_ne hnn (Ne.symm h0)
      have hsw : sinc w = sin w / w := by simp [Real.sinc, h0]
      rw [hsw]
      exact div_nonneg
        (sin_nonneg_of_nonneg_of_le_pi hnn (le_of_lt (lt_of_le_of_lt hM hMlt)))
        (le_of_lt hwpos)
  · by_cases h0 : w = 0
    · subst h0; simp
    · have hwpos : 0 < w := lt_of_le_of_ne hnn (Ne.symm h0)
      have hsw : sinc w = sin w / w := by simp [Real.sinc, h0]
      rw [hsw]
      exact (div_le_one hwpos).mpr (sin_lt hwpos).le

/-! ## Alternating-series sandwich (consumes CLZ_GAP_TAIL once) -/

/-- Global tail constant: `(π_hi/2)^21 / 21!` ≈ 2.57e-16. -/
noncomputable def chiG : ℝ :=
  ((3.14159265358979323847 : ℝ) / 2) ^ 21 / 51090942171709440000

/-- The 10-term alternating partial sum of `sin` (kept terms `k < 10`). -/
noncomputable def sin9 (x : ℝ) : ℝ :=
  x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880 - x^11/39916800
    + x^13/6227020800 - x^15/1307674368000 + x^17/355687428096000
    - x^19/121645100408832000

/-- The certified sandwich: for `|x| ≤ π_hi/2`,
`sin x ∈ [sin9 x − chiG, sin9 x + chiG]`. Proved once; the per-window
receipts only have to bound the finitely many monomials of `sin9`. -/
theorem sin_series_sandwich (x : ℝ) (habs : |x| ≤ (3.14159265358979323847:ℝ)/2) :
    sin9 x - chiG ≤ sin x ∧ sin x ≤ sin9 x + chiG := by
  have hxabs2 : |x|^2 ≤ ((3.14159265358979323847:ℝ)/2)^2 :=
    pow_le_pow_left₀ (abs_nonneg x) habs 2
  have hlit : ((3.14159265358979323847:ℝ)/2)^2 ≤ 6 := by norm_num
  have hx2 : x^2 ≤ 6 := by
    have h6 : x^2 = |x|^2 := (sq_abs x).symm
    linarith
  have hmono : ∀ k : ℕ, x^2 ≤ (2*k+2)*(2*k+3) := fun k =>
    le_trans hx2 (by
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _
      nlinarith)
  have hchi : |x|^21 / ((21).factorial : ℝ) ≤ chiG := by
    unfold chiG
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg x) habs 21) (by positivity)
  have hsum : (∑ k ∈ Finset.range 10, (-1:ℝ)^k * x^(2*k+1) / ((2*k+1).factorial : ℝ))
      = sin9 x := by
    simp only [Finset.sum_range_succ, sin9]
    norm_num
    ring
  have hodd : (∑ k ∈ Finset.range 10, (-1:ℝ)^k * (-x)^(2*k+1) / ((2*k+1).factorial : ℝ))
      = -(∑ k ∈ Finset.range 10, (-1:ℝ)^k * x^(2*k+1) / ((2*k+1).factorial : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (-x)^(2*k+1) = -(x^(2*k+1)) from by
      rw [show (-x)^(2*k+1) = (-x) * (-x)^(2*k) from by
        rw [show (2*k+1 : ℕ) = (2*k)+1 from rfl, pow_succ]; ring]
      rw [show (-x)^(2*k) = x^(2*k) from by rw [pow_mul, neg_sq, pow_mul]]
      ring]
    ring
  rcases le_or_gt 0 x with hx0 | hx0
  · -- x ≥ 0: direct partial-sum enclosure
    have hb := sin_partial_abs_bound x hx0 9 hmono
    rw [show (9+1 : ℕ) = 10 from rfl] at hb
    have h21 : x^21 = |x|^21 := by rw [abs_of_nonneg hx0]
    have htail : x^21 / ((21).factorial : ℝ) ≤ chiG := by
      rw [h21]; exact hchi
    rw [hsum] at hb
    obtain ⟨hlo, hhi⟩ := abs_le.mp hb
    exact ⟨by linarith, by linarith⟩
  · -- x < 0: apply the enclosure at −x (odd series)
    have hnx : 0 ≤ -x := by linarith
    have hb := sin_partial_abs_bound (-x) hnx 9 (fun k => by
      rw [show (-x)^2 = x^2 from by ring]; exact hmono k)
    rw [show (9+1 : ℕ) = 10 from rfl, show (2*9+3 : ℕ) = 21 from rfl] at hb
    have h21 : (-x)^21 = |x|^21 := by rw [abs_of_nonpos (le_of_lt hx0)]
    have htail : (-x)^21 / ((21).factorial : ℝ) ≤ chiG := by
      rw [h21]; exact hchi
    rw [hodd, Real.sin_neg, hsum] at hb
    have hkey : (-sin x - -sin9 x) = -(sin x - sin9 x) := by ring
    rw [hkey, abs_neg] at hb
    obtain ⟨hlo, hhi⟩ := abs_le.mp hb
    exact ⟨by linarith, by linarith⟩

/-! ## Kfn 0 numeric interval (from the proved sin partial-sum enclosures) -/

/-- The proved upper enclosure for `sin a` (mirror of `CLZ.sin_a_lb`, same
partial-sum interface, `n = 5`, tail `xh^13/13!` on the positive side). -/
theorem sin_a_ub :
    sin a ≤ xh - xl^3/6 + xh^5/120 - xl^7/5040 + xh^9/362880 - xl^11/39916800
      + xh^13/6227020800 := by
  have hmono : ∀ k : ℕ, a^2 ≤ (2*k+2)*(2*k+3) := by
    intro k
    rw [a_sq]
    have hk : ((2*k+2)*(2*k+3) : ℝ) ≥ 6 := by
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _
      nlinarith
    linarith
  have hb := sin_partial_abs_bound a (le_of_lt (a_pos)) 5 hmono
  obtain ⟨-, hhi⟩ := abs_le.1 hb
  have hP5 : (∑ k ∈ Finset.range 6, (-1:ℝ)^k * a^(2*k+1)/((2*k+1)! : ℝ))
      = a - a^3/6 + a^5/120 - a^7/5040 + a^9/362880 - a^11/39916800 := by
    norm_num [Finset.sum_range_succ]; ring
  rw [hP5] at hhi
  rw [show (2*5+3 : ℕ) = 13 from rfl, show ((13 : ℕ)! : ℝ) = 6227020800 from by norm_num] at hhi
  have d6 : 0 < (6:ℝ) := by norm_num
  have d120 : 0 < (120:ℝ) := by norm_num
  have d5040 : 0 < (5040:ℝ) := by norm_num
  have d362880 : 0 < (362880:ℝ) := by norm_num
  have d39916800 : 0 < (39916800:ℝ) := by norm_num
  have d6227020800 : 0 < (6227020800:ℝ) := by norm_num
  have e1 : a ≤ xh := a_le_xh
  have e3 : xl^3/6 ≤ a^3/6 :=
    div_le_div₀ (pow_nonneg (le_of_lt a_pos) 3) (pow_le_pow_left₀ (le_of_lt xl_pos) xl_le_a 3) d6 (le_refl 6)
  have e5 : a^5/120 ≤ xh^5/120 :=
    div_le_div₀ (pow_nonneg (le_of_lt xh_pos) 5) (pow_le_pow_left₀ (le_of_lt a_pos) a_le_xh 5) d120 (le_refl 120)
  have e7 : xl^7/5040 ≤ a^7/5040 :=
    div_le_div₀ (pow_nonneg (le_of_lt a_pos) 7) (pow_le_pow_left₀ (le_of_lt xl_pos) xl_le_a 7) d5040 (le_refl 5040)
  have e9 : a^9/362880 ≤ xh^9/362880 :=
    div_le_div₀ (pow_nonneg (le_of_lt xh_pos) 9) (pow_le_pow_left₀ (le_of_lt a_pos) a_le_xh 9) d362880 (le_refl 362880)
  have e11 : xl^11/39916800 ≤ a^11/39916800 :=
    div_le_div₀ (pow_nonneg (le_of_lt a_pos) 11) (pow_le_pow_left₀ (le_of_lt xl_pos) xl_le_a 11) d39916800 (le_refl 39916800)
  have e13 : a^13/6227020800 ≤ xh^13/6227020800 :=
    div_le_div₀ (pow_nonneg (le_of_lt xh_pos) 13) (pow_le_pow_left₀ (le_of_lt a_pos) a_le_xh 13) d6227020800 (le_refl 6227020800)
  linarith

/-- Lower bound `Kfn 0 ≥ 0.9187253698520…` (interval width ~6e-11,
against the 20-digit `a`-bounds; slack budget is 2.6e-4 — ample). -/
theorem Kfn0_lb : (0.918725369860555949800554150691128408603149501 : ℝ) ≤ Kfn 0 := by
  have hapos : (0:ℝ) < a := by
    show (0:ℝ) < 1 / sqrt 2
    positivity
  have h1 : Kfn 0 = sin a / a := by simp [Kfn_zero, Real.sinc, a_ne]
  rw [h1, le_div_iff₀ hapos]
  calc (0.918725369860555949800554150691128408603149501:ℝ) * a
      ≤ (0.918725369860555949800554150691128408603149501:ℝ) * (0.7071067811865475245:ℝ) :=
        mul_le_mul_of_nonneg_left a_ub (by norm_num)
    _ ≤ xl - xh^3/6 + xl^5/120 - xh^7/5040 + xl^9/362880 - xh^11/39916800
        - xh^13/6227020800 := by simp only [xl, xh]; norm_num
    _ ≤ sin a := sin_a_lb

/-- Upper bound `Kfn 0 ≤ 0.9187253698655744013…`. -/
theorem Kfn0_ub : Kfn 0 ≤ (0.918725369865574401307762900255801616701254273 : ℝ) := by
  have hapos : (0:ℝ) < a := by
    show (0:ℝ) < 1 / sqrt 2
    positivity
  have h1 : Kfn 0 = sin a / a := by simp [Kfn_zero, Real.sinc, a_ne]
  rw [h1, div_le_iff₀ hapos]
  calc sin a
      ≤ xh - xl^3/6 + xh^5/120 - xl^7/5040 + xh^9/362880 - xl^11/39916800
        + xh^13/6227020800 := sin_a_ub
    _ ≤ (0.918725369865574401307762900255801616701254273:ℝ) * (0.7071067811865475244:ℝ) := by
        simp only [xl, xh]; norm_num
    _ ≤ (0.918725369865574401307762900255801616701254273:ℝ) * a :=
        mul_le_mul_of_nonneg_left a_lb (by norm_num)

/-- Near-zero bracket: `sinc ∈ [1 − δ²/6 − δ⁴/120, 1]` on `[0, δ]`, `δ ≤ 1`
(includes `t = 0`; used by the reflected early-cell receipts). -/
theorem sinc_near1 (δ t : ℝ) (hnn : 0 ≤ t) (hδt : t ≤ δ) (hδ1 : δ ≤ 1) :
    (1:ℝ) - δ^2/6 - δ^4/120 ≤ sinc t ∧ sinc t ≤ 1 := by
  by_cases h0 : t = 0
  · subst h0
    have hδ0 : (0:ℝ) ≤ δ^2 := sq_nonneg δ
    have hδ4 : (0:ℝ) ≤ δ^4 := by nlinarith
    have hs0 : sinc 0 = 1 := by simp [Real.sinc]
    constructor
    · linarith
    · linarith
  · have hpos : 0 < t := lt_of_le_of_ne hnn (Ne.symm h0)
    have hmono : ∀ k : ℕ, t^2 ≤ (2*k+2)*(2*k+3) := by
      intro k
      have h1 : t^2 ≤ 1 := by
        nlinarith [hδt.trans hδ1, abs_nonneg t]
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _
      nlinarith
    have hb := sin_partial_abs_bound t (le_of_lt hpos) 1 hmono
    obtain ⟨hlo, -⟩ := abs_le.1 hb
    rw [show (1+1 : ℕ) = 2 from rfl, show (2*1+3 : ℕ) = 5 from rfl,
      show ((5 : ℕ)! : ℝ) = 120 from by norm_num] at hlo
    norm_num [Finset.sum_range_succ] at hlo
    have hsw : sin t ≥ t - t^3/6 - t^5/120 := by linarith
    have hsw' : sinc t = sin t / t := by simp [Real.sinc, h0]
    have hd6 : (0:ℝ) < 6 := by norm_num
    have hd120 : (0:ℝ) < 120 := by norm_num
    have hup : sin t ≤ t := (sin_lt hpos).le
    have hlo1 : (1:ℝ) - t^2/6 - t^4/120 ≤ sinc t := by
      rw [hsw', le_div_iff₀ hpos]
      have h5 : (0:ℝ) ≤ t^5 := by nlinarith [hpos.le]
      linarith [hsw]
    have hup2 : sinc t ≤ 1 := by
      rw [hsw']; exact (div_le_one hpos).mpr hup
    have ht2 : t^2 ≤ δ^2 := by nlinarith [hδt, abs_nonneg t]
    have ht4 : t^4 ≤ δ^4 := by
      have h2 : t^2 ≤ δ^2 := ht2
      nlinarith
    constructor
    · calc (1:ℝ) - δ^2/6 - δ^4/120 ≤ 1 - t^2/6 - t^4/120 := by nlinarith
      _ ≤ sinc t := hlo1
    · exact hup2

end CLZ.Cert
