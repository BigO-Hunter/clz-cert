import CLZCert.Helpers

/-!
# Receipt glue lemmas (hand-written once; consumed by the generated receipts)

Small proof-shapes that every generated wcell/obcell/box theorem needs:

- `pow2_le_factorial_sq`: the monotonicity hypothesis of the proved
  `sin_series_sandwich_pos/neg`, discharged once from `x^2 ≤ 6`.
- `corner_div_bracket`: the division close of a `sinc_bracket` piece: the
  ratio `num/t` over the box `[tlo,thi] × [P,Q]` is monotone in each
  variable separately, so its extremes sit at the four corners; the four
  emitted corner facts give the bracket.
- `pi_mul_lb` / `pi_mul_ub`: `π*x` outward products from the 20-digit
  constants (nonnegative `x`).
-/

namespace CLZ.Cert

open Real

theorem pow2_le_factorial_sq (x : ℝ) (h : x^2 ≤ 6) :
    ∀ k : ℕ, x^2 ≤ (2*k+2)*(2*k+3) := by
  intro k
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hk : ((2*k+2)*(2*k+3) : ℝ) ≥ 6 := by nlinarith
  linarith

/-- Corner-monotone ratio bracket: for `t ∈ [tlo,thi]`, `num ∈ [P,Q]`,
`tlo > 0`, the four corner facts give the `num/t` bracket. -/
theorem corner_div_bracket (t num lo hi tlo thi P Q : ℝ)
    (htlo : 0 < tlo) (ht1 : tlo ≤ t) (ht2 : t ≤ thi)
    (hnum : P ≤ num ∧ num ≤ Q)
    (h1 : lo ≤ P / thi) (h2 : lo ≤ P / tlo) (h3 : Q / tlo ≤ hi) (h4 : Q / thi ≤ hi) :
    lo ≤ num / t ∧ num / t ≤ hi := by
  have htpos : (0:ℝ) < t := lt_of_lt_of_le htlo ht1
  have hthipos : (0:ℝ) < thi := lt_of_lt_of_le htlo (le_trans ht1 ht2)
  rcases le_or_gt 0 num with hnn | hnn
  · -- num ≥ 0: num/t ∈ [num/thi, num/tlo]
    refine ⟨?_, ?_⟩
    · calc lo ≤ P / thi := h1
        _ ≤ num / thi := by rw [div_le_div_iff₀ hthipos hthipos]; nlinarith
        _ ≤ num / t := by rw [div_le_div_iff₀ hthipos htpos]; nlinarith
    · calc num / t ≤ num / tlo := by rw [div_le_div_iff₀ htpos htlo]; nlinarith
        _ ≤ Q / tlo := by rw [div_le_div_iff₀ htlo htlo]; nlinarith
        _ ≤ hi := h3
  · -- num ≤ 0: num/t ∈ [num/tlo, num/thi]
    have hn0 : num ≤ 0 := le_of_lt hnn
    refine ⟨?_, ?_⟩
    · calc lo ≤ P / tlo := h2
        _ ≤ num / tlo := by rw [div_le_div_iff₀ htlo htlo]; nlinarith
        _ ≤ num / t := by rw [div_le_div_iff₀ htlo htpos]; nlinarith
    · calc num / t ≤ num / thi := by rw [div_le_div_iff₀ htpos hthipos]; nlinarith
        _ ≤ Q / thi := by rw [div_le_div_iff₀ hthipos hthipos]; nlinarith
        _ ≤ hi := h4

/-- `p*lo ≤ π*x` for `0 ≤ lo ≤ x`, `0 < p ≤ π` (20-digit constants). -/
theorem pi_mul_lb (x lo p : ℝ) (hlo : 0 ≤ lo) (hlx : lo ≤ x)
    (_hp : 0 < p) (hple : p ≤ (3.14159265358979323846 : ℝ)) : p * lo ≤ π * x := by
  have h1 : p * lo ≤ π * lo := mul_le_mul_of_nonneg_right (hple.trans CLZ.pi_lb.le) hlo
  have h2 : π * lo ≤ π * x := mul_le_mul_of_nonneg_left hlx (le_of_lt Real.pi_pos)
  exact le_trans h1 h2

/-- `π*x ≤ q*hi` for `0 ≤ x ≤ hi`, `π ≤ q` (20-digit constants). -/
theorem pi_mul_ub (x hi q : ℝ) (hx0 : 0 ≤ x) (hxh : x ≤ hi)
    (hqle : (3.14159265358979323847 : ℝ) ≤ q) : π * x ≤ q * hi := by
  have h1 : π * x ≤ q * x := mul_le_mul_of_nonneg_right (CLZ.pi_ub.le.trans hqle) hx0
  have h2 : q * x ≤ q * hi := mul_le_mul_of_nonneg_left hxh (by positivity)
  exact le_trans h1 h2

/-- `q*lo ≤ π*x` for `lo ≤ 0 ≤ ...`, `lo ≤ x`, `π ≤ q` (negative-side
product bound; `q*lo ≤ π*lo ≤ π*x`). -/
theorem pi_mul_lb_neg (x lo q : ℝ) (hlo : lo ≤ 0) (hlx : lo ≤ x)
    (hqle : (3.14159265358979323847 : ℝ) ≤ q) : q * lo ≤ π * x := by
  have hpq : π ≤ q := CLZ.pi_ub.le.trans hqle
  have h1 : q * lo ≤ π * lo := by nlinarith [hpq, hlo]
  have h2 : π * lo ≤ π * x := mul_le_mul_of_nonneg_left hlx Real.pi_pos.le
  exact le_trans h1 h2

/-- `π*x ≤ p*hi` for `x ≤ hi ≤ 0`, `p ≤ π` (negative-side product bound). -/
theorem pi_mul_ub_neg (x hi p : ℝ) (hhi : hi ≤ 0) (hxh : x ≤ hi)
    (hple : p ≤ (3.14159265358979323846 : ℝ)) : π * x ≤ p * hi := by
  have hpp : p ≤ π := hple.trans CLZ.pi_lb.le
  have h1 : π * hi ≤ p * hi := by nlinarith [hpp, hhi]
  have h2 : π * x ≤ π * hi := mul_le_mul_of_nonneg_left hxh Real.pi_pos.le
  exact le_trans h2 h1

/-- `sin t = (-1)^n sin(π*((t − n*π)/π))` for natural `n` (literal). -/
theorem sin_shift_pos (t : ℝ) (n : ℕ) :
    sin t = (-1 : ℝ)^((n:ℤ)) * sin (π * ((t - (n:ℝ)*π) / π)) := by
  have hstep : π * ((t - (n:ℝ)*π) / π) = t - (n:ℝ)*π := by field_simp
  calc sin t = sin ((t - (n:ℝ)*π) + (n:ℝ)*π) := by congr 1; ring
    _ = (-1:ℝ)^n * sin (t - (n:ℝ)*π) := sin_add_nat_pi _ n
    _ = (-1:ℝ)^((n:ℤ)) * sin (π * ((t - (n:ℝ)*π) / π)) := by rw [hstep, zpow_natCast]

/-- `sin t = (-1)^(-n) sin(π*((t + n*π)/π))` (literal negative shift; note
`(-1)^(-n) = (-1)^n` for the literals `norm_num` evaluates). -/
theorem sin_shift_neg (t : ℝ) (n : ℕ) :
    sin t = (-1 : ℝ)^n * sin (π * ((t + (n:ℝ)*π) / π)) := by
  have hstep : π * ((t + (n:ℝ)*π) / π) = t + (n:ℝ)*π := by field_simp
  calc sin t = sin ((t + (n:ℝ)*π) - (n:ℝ)*π) := by congr 1; ring
    _ = (-1:ℝ)^n * sin (t + (n:ℝ)*π) := sin_sub_nat_pi _ n
    _ = (-1:ℝ)^n * sin (π * ((t + (n:ℝ)*π) / π)) := by rw [hstep]

end CLZ.Cert
