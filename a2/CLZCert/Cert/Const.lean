import CLZCert.Helpers

/-!
# Shared literal bounds (emitted once; consumed by all generated receipts)
-/

namespace CLZ.Cert

open Real

theorem a_lo : (0.7071067811865475244 : ℝ) ≤ CLZ.a := by
  have h : (0.7071067811865475244 : ℝ) = CLZ.xl := by simp only [CLZ.xl]; norm_num
  rw [h]
  exact CLZ.xl_le_a

theorem a_hi : CLZ.a ≤ (0.7071067811865475245 : ℝ) := by
  have h : (0.7071067811865475245 : ℝ) = CLZ.xh := by simp only [CLZ.xh]; norm_num
  rw [h]
  exact CLZ.a_le_xh

/-- The tail constant is `≈ 2.57e-16`, comfortably below `1e-15`. -/
theorem chiG_le : chiG ≤ (0.000000000000001 : ℝ) := by
  simp only [chiG]
  norm_num

/-- The series sandwich with a DECIMAL tail constant: the receipts then never
carry the `chiG` atom, so `linarith` needs no numeric value for it. -/
theorem sin_series_sandwich15 (x : ℝ) (h : |x| ≤ (3.14159265358979323847:ℝ)/2) :
    sin9 x - (0.000000000000001:ℝ) ≤ sin x ∧ sin x ≤ sin9 x + (0.000000000000001:ℝ) := by
  obtain ⟨h1, h2⟩ := sin_series_sandwich x h
  constructor <;> linarith [chiG_le]

end CLZ.Cert
