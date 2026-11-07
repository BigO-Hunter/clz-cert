import Mathlib
import CLZCert.Kernel

/-!
# CLZ receipts helpers (PROVED — adds no new gaps)

Shared machinery for the generated per-box receipts (`CLZCert.Cert.*`):

- `sin_sub_nat_pi` / `sin_add_nat_pi`: reduction of `sin` by natural
  multiples of π (Mathlib `sin π = 0`, `cos π = -1`). The generated receipts
  instantiate these at literal `j : ℕ` and evaluate the `(-1)^j` sign by
  `norm_num` (literal `ℤ`-exponents evaluate directly).
- `sinc_even`, `sinc_bracket_even_cover`, `sinc_small`: reflection to
  nonnegative arguments; `sinc ∈ [0,1]` on `[0,M]`, `M < π` covers reflected
  windows near zero (including `t = 0`) with ample slack.
- `sin_series_sandwich`: the 10-term alternating sandwich; the only gap it
  touches is `Kernel.alternating_tail` (`CLZ_GAP_TAIL`), instantiated with
  `c k = x^(2k)/(2k+1)!` at `N = 10` and the global tail constant `chiG`.
- `Kfn0_lb` / `Kfn0_ub`: numeric `Kfn 0 = sinc(1/√2)` interval from
  `CLZ_GAP_SINPOS`.

The generated receipts consume these with frozen ℚ literals only.
-/

namespace CLZ.Cert

open Real

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
  have hx20 : x^20 = |x|^20 := by
    have e1 : x^20 = (x^2)^10 := by
      show x^(2*10) = (x^2)^10
      rw [pow_mul]
    have e2 : |x|^20 = (|x|^2)^10 := by
      show |x|^(2*10) = (|x|^2)^10
      rw [pow_mul]
    rw [e1, e2, sq_abs]
  have hx21 : |x| * x^20 = |x|^21 := by
    rw [hx20, show |x|^21 = |x|^20 * |x| from by
      rw [show ((21:ℕ)) = 20+1 from rfl, pow_succ], mul_comm]
  set c : ℕ → ℝ := fun k => x^(2*k) / ((2*k+1).factorial : ℝ) with hcdef
  have hx0 : ∀ k, 0 ≤ x^(2*k) := fun k => by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg x) k
  have hcpos : ∀ k, 0 ≤ c k := fun k => by
    unfold c
    exact div_nonneg (hx0 k) (by positivity)
  have hdec : ∀ k, 10 ≤ k → c (k+1) ≤ c k := by
    intro k hk
    have hN1 : (6:ℝ) ≤ ((2*k+2 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (show (6:ℕ) ≤ 2*k+2 by omega)
    have hratio : x^2 ≤ ((2*k+2 : ℕ) : ℝ) := le_trans hx2 hN1
    have hpos1 : (0:ℝ) < ((2*k+1).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have key : x^(2*k) * x^2 ≤ x^(2*k) * ((2*k+2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hratio (hx0 k)
    have f_a : x^(2*k+1+1) * ((2*k+1).factorial : ℝ)
        = x^(2*k) * (x^2 * ((2*k+1).factorial : ℝ)) := by
      rw [show x^(2*k+1+1) = x^(2*k) * x^2 from by
        rw [show (2*k+1+1 : ℕ) = (2*k)+2 from rfl, pow_succ, pow_succ]; ring]
      ring
    have hB : x^(2*k) * x^2 * ((2*k+1).factorial : ℝ)
        ≤ x^(2*k) * ((2*k+2 : ℕ) : ℝ) * ((2*k+1).factorial : ℝ) :=
      mul_le_mul_of_nonneg_right key (Nat.cast_nonneg (2*k+1).factorial)
    have h2c : x^(2*k) * (((2*k+2 : ℕ) : ℝ) * ((2*k+1).factorial : ℝ))
        ≤ x^(2*k) * (((2*k+3 : ℕ) : ℝ) * ((2*k+1).factorial : ℝ)) := by
      have hle : ((2*k+2 : ℕ) : ℝ) ≤ ((2*k+3 : ℕ) : ℝ) :=
        Nat.cast_le.mpr (show 2*k+2 ≤ 2*k+3 by omega)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg (2*k+1).factorial)) (hx0 k)
    have h3c : x^(2*k) * (((2*k+3 : ℕ) : ℝ) * ((2*k+1).factorial : ℝ))
        ≤ x^(2*k) * (((2*k+3 : ℕ) : ℝ)
            * (((2*k+2 : ℕ) : ℝ) * ((2*k+1).factorial : ℝ))) := by
      have hE1 : (1:ℝ) ≤ ((2*k+2 : ℕ) : ℝ) :=
        le_trans (by norm_num : (1:ℝ) ≤ 2) (Nat.cast_le.mpr (show 2 ≤ 2*k+2 by omega))
      have hB0 : (0:ℝ) ≤ ((2*k+1).factorial : ℝ) := Nat.cast_nonneg (2*k+1).factorial
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hB0 hE1)
          (Nat.cast_nonneg (2*k+3))) (hx0 k)
    have hbig : (0:ℝ) < ((2*k+2+1 : ℕ) : ℝ)
        * (((2*k+1+1 : ℕ) : ℝ) * ((2*k+1).factorial : ℝ)) := by
      positivity
    have hgoal : c (k+1) ≤ c k := by
      unfold c
      rw [show (2*(k+1) : ℕ) = (2*k+2) from rfl, Nat.factorial_succ,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul,
        div_le_div_iff₀ hbig hpos1]
      linarith [f_a, hB, h2c, h3c]
    exact hgoal
  have h1 := alternating_tail c 10 hdec hcpos
  simp only [hcdef] at h1
  have hsplit : sin x
      = x * ∑' k, (-1:ℝ)^k * (x^(2*k) / ((2*k+1).factorial : ℝ)) := by
    rw [Real.sin_eq_tsum x, ← tsum_mul_left]
    exact tsum_congr fun k => by simp only [pow_succ]; ring
  have hfin : x * (∑ k ∈ Finset.range 10,
      (-1:ℝ)^k * (x^(2*k) / ((2*k+1).factorial : ℝ))) = sin9 x := by
    simp only [Finset.mul_sum, Finset.sum_range_succ, sin9]
    norm_num
    ring
  have hchi : |x| * c 10 ≤ chiG := by
    unfold chiG c
    calc |x| * (x^(2*10) / ((2*10+1).factorial : ℝ))
        = |x|^21 / ((21).factorial : ℝ) := by
          rw [← mul_div_assoc, show ((2*10 : ℕ)) = 20 from rfl, hx21]
      _ ≤ ((3.14159265358979323847:ℝ)/2)^21 / ((21).factorial : ℝ) :=
          div_le_div_of_nonneg_right
            (pow_le_pow_left₀ (abs_nonneg x) habs 21) (by positivity)
  have hcomb : |sin x - sin9 x| ≤ chiG := by
    have h2 : |x * (∑' k, (-1:ℝ)^k * (x^(2*k) / ((2*k+1).factorial : ℝ)))
        - x * (∑ k ∈ Finset.range 10, (-1:ℝ)^k * (x^(2*k) / ((2*k+1).factorial : ℝ)))|
        ≤ |x| * c 10 := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg x)
    rw [← hsplit] at h2
    rw [hfin] at h2
    linarith [h2, hchi]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hcomb
  exact ⟨by linarith, by linarith⟩

/-! ## Kfn 0 numeric interval (consumes CLZ_GAP_SINPOS) -/

/-- Lower bound `Kfn 0 = sinc(1/√2) = sin(1/√2)/(1/√2) ≥ 0.918725369865…`. -/
theorem Kfn0_lb : (0.918725369865568437655401194933773706703841370 : ℝ) ≤ Kfn 0 := by
  have hsa := CLZ_GAP_SINPOS.1
  have haub := a_ub
  have hapos : (0:ℝ) < a := by
    show (0:ℝ) < 1 / sqrt 2
    positivity
  have h1 : Kfn 0 = sin a / a := by simp [Kfn_zero, Real.sinc, a_ne]
  rw [h1, le_div_iff₀ hapos]
  calc (0.918725369865568437655401194933773706703841370:ℝ) * a
      ≤ (0.918725369865568437655401194933773706703841370:ℝ) * (0.7071067811865475245:ℝ) :=
        mul_le_mul_of_nonneg_left haub (by norm_num)
    _ ≤ 0.649636939080062444129478616043121910899028818 := by norm_num
    _ ≤ sin a := hsa

/-- Upper bound `Kfn 0 ≤ 0.918725369865568437785328582752614622636419071`. -/
theorem Kfn0_ub : Kfn 0 ≤ (0.918725369865568437785328582752614622636419071 : ℝ) := by
  have hsa := CLZ_GAP_SINPOS.2
  have ha := a_lb
  have hapos : (0:ℝ) < a := by
    show (0:ℝ) < 1 / sqrt 2
    positivity
  have h1 : Kfn 0 = sin a / a := by simp [Kfn_zero, Real.sinc, a_ne]
  rw [h1, div_le_iff₀ hapos]
  calc sin a
      ≤ 0.649636939080062444129478616045121910899028818 := hsa
    _ ≤ (0.918725369865568437785328582752614622636419071:ℝ) * (0.7071067811865475244:ℝ) := by norm_num
    _ ≤ (0.918725369865568437785328582752614622636419071:ℝ) * a :=
        mul_le_mul_of_nonneg_left ha (by norm_num)

end CLZ.Cert
