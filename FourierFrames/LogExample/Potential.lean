import FourierFrames.Defs

/-!
# Auxiliary integrals for `LogExample.lean`

* `∫_ℝ log(1 + 1/s²) ds = 2π` (used for the strip estimate of the potential).
-/

open MeasureTheory Set Filter Topology

namespace FF.LogEx

/-- `F(s) = s log(1+s²) - 2 s log s + 2 arctan s`, an antiderivative of `log(1 + 1/s²)` on `(0,∞)`. -/
noncomputable def logPrimF (s : ℝ) : ℝ :=
  s * Real.log (1 + s ^ 2) - 2 * (s * Real.log s) + 2 * Real.arctan s

theorem continuous_logPrimF : Continuous logPrimF := by
  unfold logPrimF
  have h1 := Real.continuous_mul_log
  have h2 : Continuous fun s : ℝ ↦ Real.log (1 + s ^ 2) :=
    Continuous.log (by fun_prop) (fun x ↦ by positivity)
  exact (((continuous_id.mul h2).sub (continuous_const.mul h1)).add
    (continuous_const.mul Real.continuous_arctan))

theorem logPrimF_zero : logPrimF 0 = 0 := by simp [logPrimF]

theorem hasDerivAt_logPrimF {s : ℝ} (hs : 0 < s) :
    HasDerivAt logPrimF (Real.log (1 + 1 / s ^ 2)) s := by
  have h1 : HasDerivAt (fun s : ℝ ↦ Real.log (1 + s ^ 2)) (2 * s / (1 + s ^ 2)) s := by
    have := ((hasDerivAt_pow 2 s).const_add 1).log (by positivity)
    convert this using 1; simp
  have h2 : HasDerivAt (fun s : ℝ ↦ s * Real.log (1 + s ^ 2))
      (Real.log (1 + s ^ 2) + s * (2 * s / (1 + s ^ 2))) s := by
    convert (hasDerivAt_id' s).fun_mul h1 using 1; simp
  have h3 : HasDerivAt (fun s : ℝ ↦ s * Real.log s) (Real.log s + s * s⁻¹) s := by
    convert (hasDerivAt_id' s).fun_mul (Real.hasDerivAt_log hs.ne') using 1; simp
  have h4 := Real.hasDerivAt_arctan s
  have h5 := (h2.sub (h3.const_mul 2)).add (h4.const_mul 2)
  have hfun : logPrimF = ((fun s : ℝ ↦ s * Real.log (1 + s ^ 2)) -
      fun y ↦ 2 * (y * Real.log y)) + fun y ↦ 2 * Real.arctan y := by
    ext y; simp [logPrimF]
  rw [hfun]
  convert h5 using 1
  have hs2 : (1 + s ^ 2) ≠ 0 := by positivity
  have : Real.log (1 + 1 / s ^ 2) = Real.log (1 + s ^ 2) - 2 * Real.log s := by
    have : 1 + 1 / s ^ 2 = (1 + s ^ 2) / s ^ 2 := by field_simp; ring
    rw [this, Real.log_div hs2 (by positivity), Real.log_pow]; push_cast; ring
  rw [this]
  field_simp
  ring

theorem tendsto_logPrimF : Tendsto logPrimF atTop (𝓝 Real.pi) := by
  have h1 : Tendsto (fun s : ℝ ↦ s * Real.log (1 + 1 / s ^ 2)) atTop (𝓝 0) := by
    have hup : ∀ s : ℝ, 0 < s → s * Real.log (1 + 1 / s ^ 2) ≤ 1 / s := by
      intro s hs
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / s ^ 2 by positivity)
      calc s * Real.log (1 + 1 / s ^ 2) ≤ s * (1 / s ^ 2) := by
            gcongr; linarith
        _ = 1 / s := by field_simp
    refine squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
    · filter_upwards [eventually_gt_atTop 0] with s hs
      exact mul_nonneg hs.le (Real.log_nonneg (by have : 0 ≤ 1 / s ^ 2 := by positivity
                                                  linarith))
    · filter_upwards [eventually_gt_atTop 0] with s hs
      simpa using hup s hs
  have h2 : Tendsto (fun s : ℝ ↦ 2 * Real.arctan s) atTop (𝓝 (2 * (Real.pi / 2))) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).const_mul 2
  have h3 := h1.add h2
  rw [show (0 : ℝ) + 2 * (Real.pi / 2) = Real.pi by ring] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  unfold logPrimF
  have : Real.log (1 + 1 / s ^ 2) = Real.log (1 + s ^ 2) - 2 * Real.log s := by
    have hs2 : (1 + s ^ 2) ≠ 0 := by positivity
    have : 1 + 1 / s ^ 2 = (1 + s ^ 2) / s ^ 2 := by field_simp; ring
    rw [this, Real.log_div hs2 (by positivity), Real.log_pow]; push_cast; ring
  rw [this]
  ring

theorem integral_Ioi_log_one_add_inv_sq :
    ∫ s in Ioi (0 : ℝ), Real.log (1 + 1 / s ^ 2) = Real.pi := by
  have := integral_Ioi_of_hasDerivAt_of_nonneg (g := logPrimF) (a := 0)
    (g' := fun s ↦ Real.log (1 + 1 / s ^ 2)) (l := Real.pi)
    continuous_logPrimF.continuousWithinAt (fun s hs ↦ hasDerivAt_logPrimF hs)
    (fun s hs ↦ Real.log_nonneg (by
      have : 0 ≤ 1 / s ^ 2 := by positivity
      linarith)) tendsto_logPrimF
  rw [this, logPrimF_zero, sub_zero]

theorem integral_log_one_add_inv_sq :
    ∫ s : ℝ, Real.log (1 + 1 / s ^ 2) = 2 * Real.pi := by
  have := integral_comp_abs (f := fun s ↦ Real.log (1 + 1 / s ^ 2))
  simp only [sq_abs] at this
  rw [this, integral_Ioi_log_one_add_inv_sq]

theorem integrable_log_one_add_inv_sq :
    Integrable (fun s : ℝ ↦ Real.log (1 + 1 / s ^ 2)) := by
  by_contra h
  have := integral_log_one_add_inv_sq
  rw [integral_undef h] at this
  have := Real.pi_pos
  linarith

end FF.LogEx
