import Mathlib

/-!
# Auxiliary lemmas for `FourierFrames/LogExample.lean`: elementary logarithm estimates.
-/

namespace FF.LogEx

open Real

theorem log_sub_log_bounds {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) (h2 : x ≤ 2 * y) :
    0 ≤ Real.log x - Real.log y ∧ Real.log x - Real.log y ≤ Real.log 2 ∧
      Real.log x - Real.log y ≤ (x - y) / y := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  have hlog : Real.log x - Real.log y = Real.log (x / y) := (Real.log_div hx.ne' hy.ne').symm
  refine ⟨?_, ?_, ?_⟩
  · have := Real.log_le_log hy hyx; linarith
  · rw [hlog]
    apply Real.log_le_log (div_pos hx hy)
    rw [div_le_iff₀ hy]; linarith
  · rw [hlog]
    have := Real.log_le_sub_one_of_pos (div_pos hx hy)
    have e : x / y - 1 = (x - y) / y := by field_simp
    linarith

theorem log_two_lt : Real.log 2 < 7 / 10 := by
  have := Real.log_two_lt_d9
  linarith

/-- `log x ≤ x / 2` for `x > 0`. -/
theorem log_le_half {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 2 by positivity)
  have h2 : Real.log (x / 2) = Real.log x - Real.log 2 := Real.log_div hx.ne' (by norm_num)
  have := log_two_lt
  have h3 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  linarith

end FF.LogEx
