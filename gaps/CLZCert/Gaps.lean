import CLZCert.Kernel

/-!
# CLZ_GAP_H0 — the H₀ tan-sandwich (PROVED)

H₀ = 2 − 1/cMT with cMT = √2·tan(a)/(1 + a·tan(a)), a = 1/√2. Algebra:
1/cMT = 1/(√2·tan a) + 1/2, so H₀ = 3/2 − 1/(√2·tan a).

Enclosures (exact ℚ, via `sin_partial_abs_bound`/`cos_partial_abs_bound`,
a ∈ [xl, xh], xl = 7071067811865475244/10¹⁹, xh = 7071067811865475245/10¹⁹):
  sin a ≥ xl − xh³/6 + xl⁵/120 − xh⁷/5040 + xl⁹/362880 − xh¹¹/39916800 − xh¹³/13!
  cos a ≤ 1 − xl²/2 + xh⁴/24 − xl⁶/720 + xh⁸/40320 − xl¹⁰/3628800 + xh¹²/12!
  tan a ≥ sin_lb/cos_ub  (div_le_div₀; margin on √2·tan a is 1.56e-8)
Exact-ℚ close: √2_lb·sin_lb/cos_ub ≥ 1/(3/2 − 6725006930/10¹⁰)
  ⟹ H₀ ≥ 6725006930/10¹⁰ (true value 0.672500703679…, margin 1.07e-8).

Axiom footprint after this file: {jo_bridge} + stdlib
(three_point_certificate discharged by sibling lane CLZ-A's receipts).
-/

namespace CLZ

open Real
open scoped Nat
open Set

/-- a² = 1/2. -/
theorem a_sq : a^2 = 1/2 := by
  rw [a, div_pow, sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  norm_num

/-- The reduced-window endpoints for `a = 1/√2`. -/
noncomputable def xl : ℝ := 7071067811865475244/10^19
noncomputable def xh : ℝ := 7071067811865475245/10^19

theorem xl_eq : xl = 0.7071067811865475244 := by simp only [xl]; norm_num
theorem xh_eq : xh = 0.7071067811865475245 := by simp only [xh]; norm_num

theorem xl_le_a : xl ≤ a := by rw [xl_eq]; exact a_lb
theorem a_le_xh : a ≤ xh := by rw [xh_eq]; exact a_ub
theorem xl_pos : 0 < xl := by simp only [xl_eq]; norm_num
theorem xh_pos : 0 < xh := by simp only [xh_eq]; norm_num

theorem a_pos : 0 < a := by
  have := xl_le_a; linarith [xl_pos]

/-- Positivity of `sin a` (CLZ_GAP_SINPOS companion, quantitative). -/
theorem sin_a_pos : 0 < sin a :=
  sin_pos_of_pos_of_lt_pi a_pos (by
    have h12 : (1:ℝ) < sqrt 2 := (lt_sqrt (by norm_num)).2 (by norm_num)
    have hlt1 : a < 1 := by rw [a]; exact (div_lt_one (lt_trans (show (0:ℝ) < 1 by norm_num) h12)).2 h12
    exact lt_of_lt_of_le hlt1 (by linarith [pi_lb]))

/-- Positivity of `cos a`. -/
theorem cos_a_pos : 0 < cos a := by
  have hpi2 : (1:ℝ) < π/2 := by
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]; linarith [pi_lb]
  have h12 : (1:ℝ) < sqrt 2 := (lt_sqrt (by norm_num)).2 (by norm_num)
  have hlt1 : a < 1 := by rw [a]; exact (div_lt_one (lt_trans (show (0:ℝ) < 1 by norm_num) h12)).2 h12
  have hmem : a ∈ Ioo (-(π/2)) (π/2) := ⟨by linarith [a_pos], by linarith⟩
  exact cos_pos_of_mem_Ioo hmem

/-! ## The sin and cos enclosures -/

/-- sin a ≥ xl − xh³/6 + xl⁵/120 − xh⁷/5040 + xl⁹/362880 − xh¹¹/39916800 − xh¹³/13!. -/
theorem sin_a_lb :
    xl - xh^3/6 + xl^5/120 - xh^7/5040 + xl^9/362880 - xh^11/39916800
      - xh^13/6227020800 ≤ sin a := by
  have hmono : ∀ k : ℕ, a^2 ≤ (2*k+2)*(2*k+3) := by
    intro k
    rw [a_sq]
    have hk : ((2*k+2)*(2*k+3) : ℝ) ≥ 6 := by
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _
      nlinarith
    linarith
  have hb := sin_partial_abs_bound a (le_of_lt a_pos) 5 hmono
  obtain ⟨hlo, -⟩ := abs_le.1 hb
  have hP5 : (∑ k ∈ Finset.range 6, (-1:ℝ)^k * a^(2*k+1)/((2*k+1)! : ℝ))
      = a - a^3/6 + a^5/120 - a^7/5040 + a^9/362880 - a^11/39916800 := by
    norm_num [Finset.sum_range_succ]; ring
  rw [hP5] at hlo
  -- divided monomial bounds: positive terms at xl, negative at xh
  have d6 : 0 < (6:ℝ) := by norm_num
  have d120 : 0 < (120:ℝ) := by norm_num
  have d5040 : 0 < (5040:ℝ) := by norm_num
  have d362880 : 0 < (362880:ℝ) := by norm_num
  have d39916800 : 0 < (39916800:ℝ) := by norm_num
  have d6227020800 : 0 < (6227020800:ℝ) := by norm_num
  have e1 : (xl:ℝ) ≤ a := xl_le_a
  have e3 : a^3/6 ≤ xh^3/6 :=
    div_le_div₀ (pow_nonneg (le_of_lt xh_pos) 3) (pow_le_pow_left₀ (le_of_lt a_pos) a_le_xh 3) d6 (le_refl 6)
  have e5 : xl^5/120 ≤ a^5/120 :=
    div_le_div₀ (pow_nonneg (le_of_lt a_pos) 5) (pow_le_pow_left₀ (le_of_lt xl_pos) xl_le_a 5) d120 (le_refl 120)
  have e7 : a^7/5040 ≤ xh^7/5040 :=
    div_le_div₀ (pow_nonneg (le_of_lt xh_pos) 7) (pow_le_pow_left₀ (le_of_lt a_pos) a_le_xh 7) d5040 (le_refl 5040)
  have e9 : xl^9/362880 ≤ a^9/362880 :=
    div_le_div₀ (pow_nonneg (le_of_lt a_pos) 9) (pow_le_pow_left₀ (le_of_lt xl_pos) xl_le_a 9) d362880 (le_refl 362880)
  have e11 : a^11/39916800 ≤ xh^11/39916800 :=
    div_le_div₀ (pow_nonneg (le_of_lt xh_pos) 11) (pow_le_pow_left₀ (le_of_lt a_pos) a_le_xh 11) d39916800 (le_refl 39916800)
  have e13 : a^13/6227020800 ≤ xh^13/6227020800 :=
    div_le_div₀ (pow_nonneg (le_of_lt xh_pos) 13) (pow_le_pow_left₀ (le_of_lt a_pos) a_le_xh 13) d6227020800 (le_refl 6227020800)
  linarith

/-- cos a ≤ 1 − xl²/2 + xh⁴/24 − xl⁶/720 + xh⁸/40320 − xl¹⁰/3628800 + xh¹²/12!. -/
theorem cos_a_ub :
    cos a ≤ 1 - xl^2/2 + xh^4/24 - xl^6/720 + xh^8/40320 - xl^10/3628800
      + xh^12/479001600 := by
  have hmono : ∀ k : ℕ, a^2 ≤ (2*k+1)*(2*k+2) := by
    intro k
    rw [a_sq]
    have hk : ((2*k+1)*(2*k+2) : ℝ) ≥ 2 := by
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _
      nlinarith
    linarith
  have hb := cos_partial_abs_bound a (le_of_lt a_pos) 5 hmono
  obtain ⟨-, hhi⟩ := abs_le.1 hb
  have hQ5 : (∑ k ∈ Finset.range 6, (-1:ℝ)^k * a^(2*k)/((2*k)! : ℝ))
      = 1 - a^2/2 + a^4/24 - a^6/720 + a^8/40320 - a^10/3628800 := by
    norm_num [Finset.sum_range_succ]; ring
  rw [hQ5] at hhi
  have d2 : 0 < (2:ℝ) := by norm_num
  have d24 : 0 < (24:ℝ) := by norm_num
  have d720 : 0 < (720:ℝ) := by norm_num
  have d40320 : 0 < (40320:ℝ) := by norm_num
  have d3628800 : 0 < (3628800:ℝ) := by norm_num
  have d479001600 : 0 < (479001600:ℝ) := by norm_num
  have f2 : xl^2/2 ≤ a^2/2 :=
    div_le_div₀ (pow_nonneg (le_of_lt a_pos) 2) (pow_le_pow_left₀ (le_of_lt xl_pos) xl_le_a 2) d2 (le_refl 2)
  have f4 : a^4/24 ≤ xh^4/24 :=
    div_le_div₀ (pow_nonneg (le_of_lt xh_pos) 4) (pow_le_pow_left₀ (le_of_lt a_pos) a_le_xh 4) d24 (le_refl 24)
  have f6 : xl^6/720 ≤ a^6/720 :=
    div_le_div₀ (pow_nonneg (le_of_lt a_pos) 6) (pow_le_pow_left₀ (le_of_lt xl_pos) xl_le_a 6) d720 (le_refl 720)
  have f8 : a^8/40320 ≤ xh^8/40320 :=
    div_le_div₀ (pow_nonneg (le_of_lt xh_pos) 8) (pow_le_pow_left₀ (le_of_lt a_pos) a_le_xh 8) d40320 (le_refl 40320)
  have f10 : xl^10/3628800 ≤ a^10/3628800 :=
    div_le_div₀ (pow_nonneg (le_of_lt a_pos) 10) (pow_le_pow_left₀ (le_of_lt xl_pos) xl_le_a 10) d3628800 (le_refl 3628800)
  have f12 : a^12/479001600 ≤ xh^12/479001600 :=
    div_le_div₀ (pow_nonneg (le_of_lt xh_pos) 12) (pow_le_pow_left₀ (le_of_lt a_pos) a_le_xh 12) d479001600 (le_refl 479001600)
  linarith

/-! ## The tan sandwich -/

/-- tan a ≥ sin_lb/cos_ub (the tan-sandwich lower bound). -/
theorem tan_a_lb :
    (xl - xh^3/6 + xl^5/120 - xh^7/5040 + xl^9/362880 - xh^11/39916800
        - xh^13/6227020800)
      / (1 - xl^2/2 + xh^4/24 - xl^6/720 + xh^8/40320 - xl^10/3628800
        + xh^12/479001600)
      ≤ tan a := by
  rw [Real.tan_eq_sin_div_cos]
  exact div_le_div₀ (le_of_lt sin_a_pos) sin_a_lb cos_a_pos cos_a_ub

/-- The exact-ℚ closers (isolated so failures are easy to localize). -/
theorem sin_lb_pos : (0:ℝ) < xl - xh^3/6 + xl^5/120 - xh^7/5040 + xl^9/362880
    - xh^11/39916800 - xh^13/6227020800 := by simp only [xl, xh]; norm_num

theorem cos_ub_pos : (0:ℝ) < 1 - xl^2/2 + xh^4/24 - xl^6/720 + xh^8/40320
    - xl^10/3628800 + xh^12/479001600 := by simp only [xl, xh]; norm_num

theorem sqrt2_lb_q : (14142135623730950488:ℝ)/10^19 ≤ sqrt 2 := by
  have h : (14142135623730950488:ℝ)/10^19 = 1.4142135623730950488 := by norm_num
  rw [h]; exact le_of_lt sqrt2_lb

/-- The exact-ℚ numeric close. -/
theorem h0_num : (6725006930:ℝ)/10^10 ≤ 3/2
    - ((14142135623730950488:ℝ)/10^19 * ((xl - xh^3/6 + xl^5/120 - xh^7/5040
        + xl^9/362880 - xh^11/39916800 - xh^13/6227020800)
      / (1 - xl^2/2 + xh^4/24 - xl^6/720 + xh^8/40320 - xl^10/3628800
        + xh^12/479001600)))⁻¹ := by
  simp only [xl, xh]; norm_num

/-- **CLZ_GAP_H0 (PROVED)**: the H₀ lower bound, tan-sandwich form. -/
theorem H0_tan_sandwich : (6725006930:ℝ)/10^10 ≤
    2 - 1/(sqrt 2 * Real.tan (1/sqrt 2) / (1 + 1/sqrt 2 * Real.tan (1/sqrt 2))) := by
  have haeq : (1:ℝ)/sqrt 2 = a := rfl
  have htan : Real.tan (1/sqrt 2) = Real.tan a := by rw [haeq]
  have htanpos : 0 < Real.tan a := by
    rw [Real.tan_eq_sin_div_cos]; exact div_pos sin_a_pos cos_a_pos
  have hsqrt2pos : 0 < sqrt 2 := sqrt_pos.2 (by norm_num)
  -- algebra: 2 − 1/cMT = 3/2 − 1/(√2·tan a)
  have halg : 2 - 1/(sqrt 2 * Real.tan (1/sqrt 2) / (1 + 1/sqrt 2 * Real.tan (1/sqrt 2)))
      = 3/2 - 1/(sqrt 2 * Real.tan (1/sqrt 2)) := by
    rw [htan, one_div_div, add_div]
    have hlast : ((1:ℝ)/sqrt 2 * Real.tan a)/(sqrt 2 * Real.tan a) = 1/2 := by
      field_simp [show sqrt 2 ^ 2 = 2 from sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
      exact (sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)).symm
    rw [hlast]
    ring
  rw [halg]
  -- sandwich: √2_lb·sin_lb/cos_ub ≤ √2·tan a
  have hkey : (14142135623730950488:ℝ)/10^19 * ((xl - xh^3/6 + xl^5/120 - xh^7/5040
        + xl^9/362880 - xh^11/39916800 - xh^13/6227020800)
      / (1 - xl^2/2 + xh^4/24 - xl^6/720 + xh^8/40320 - xl^10/3628800
        + xh^12/479001600))
      ≤ sqrt 2 * Real.tan (1/sqrt 2) := by
    have hstep := tan_a_lb
    rw [← htan] at hstep
    exact mul_le_mul sqrt2_lb_q hstep
      (div_nonneg (le_of_lt sin_lb_pos) (le_of_lt cos_ub_pos))
      (le_of_lt hsqrt2pos)
  -- reciprocal flip: 1/(√2·t) ≤ (√2_lb·q)⁻¹ from q ≤ √2·t... in one step:
  -- inv_anti₀ (hc : 0 < A) (h : A ≤ B) : B⁻¹ ≤ A⁻¹ applied with A := q, B := √2·t
  have hqpos : 0 < (14142135623730950488:ℝ)/10^19 * ((xl - xh^3/6 + xl^5/120
      - xh^7/5040 + xl^9/362880 - xh^11/39916800 - xh^13/6227020800)
    / (1 - xl^2/2 + xh^4/24 - xl^6/720 + xh^8/40320 - xl^10/3628800
      + xh^12/479001600)) :=
    mul_pos (by norm_num : (0:ℝ) < 14142135623730950488/10^19)
      (div_pos sin_lb_pos cos_ub_pos)
  have hrecip : (sqrt 2 * Real.tan (1/sqrt 2))⁻¹
      ≤ ((14142135623730950488:ℝ)/10^19 * ((xl - xh^3/6 + xl^5/120 - xh^7/5040
          + xl^9/362880 - xh^11/39916800 - xh^13/6227020800)
        / (1 - xl^2/2 + xh^4/24 - xl^6/720 + xh^8/40320 - xl^10/3628800
          + xh^12/479001600)))⁻¹ := by
    exact inv_anti₀ hqpos hkey
  rw [inv_eq_one_div] at hrecip
  linarith [hrecip, h0_num]

end CLZ
