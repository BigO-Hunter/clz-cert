import CLZCert.Gaps

/-!
# Shared literal bounds (emitted once; consumed by all generated receipts)
-/

namespace CLZ.Cert

theorem a_lo : (0.7071067811865475244 : ℝ) ≤ CLZ.a := by
  have h : (0.7071067811865475244 : ℝ) = CLZ.xl := by simp only [CLZ.xl]; norm_num
  rw [h]
  exact CLZ.xl_le_a

theorem a_hi : CLZ.a ≤ (0.7071067811865475245 : ℝ) := by
  have h : (0.7071067811865475245 : ℝ) = CLZ.xh := by simp only [CLZ.xh]; norm_num
  rw [h]
  exact CLZ.a_le_xh

end CLZ.Cert
