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



/-- Antiderivative of `t ↦ log ((t - x)² + y²)` (for `y > 0`). -/
noncomputable def logPrimD (x y t : ℝ) : ℝ :=
  (t - x) * Real.log ((t - x) ^ 2 + y ^ 2) - 2 * (t - x) + 2 * y * Real.arctan ((t - x) / y)

theorem hasDerivAt_logPrimD {x y : ℝ} (hy : 0 < y) (t : ℝ) :
    HasDerivAt (logPrimD x y) (Real.log ((t - x) ^ 2 + y ^ 2)) t := by
  have hD0 : 0 < (t - x) ^ 2 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun t : ℝ ↦ t - x) 1 t := (hasDerivAt_id' t).sub_const x
  have hD : HasDerivAt (fun t : ℝ ↦ (t - x) ^ 2 + y ^ 2) (2 * (t - x) * 1) t := by
    simpa using (h1.pow 2).add_const (y ^ 2)
  have hlog := hD.log hD0.ne'
  have hmul := h1.mul hlog
  have harc := (h1.div_const y).arctan
  have hall := ((hmul.sub (h1.const_mul 2)).add (harc.const_mul (2 * y)))
  have hfun : (((fun t : ℝ ↦ t - x) * fun y_1 ↦ Real.log ((y_1 - x) ^ 2 + y ^ 2)) -
      (fun y' ↦ 2 * (y' - x)) + fun y_1 ↦ 2 * y * Real.arctan ((y_1 - x) / y)) = logPrimD x y := by
    funext s; simp [logPrimD]
  rw [← hfun]
  refine hall.congr_deriv ?_
  field_simp
  ring

/-- The local expansion `u ↦ log (1 + b u + c u²)` has slope `b` at `0⁺`. -/
theorem tendsto_slope_log_quad (b c : ℝ) :
    Tendsto (fun R : ℝ ↦ R * Real.log (1 + b * R⁻¹ + c * R⁻¹ ^ 2)) atTop (𝓝 b) := by
  have hd : HasDerivAt (fun u : ℝ ↦ Real.log (1 + b * u + c * u ^ 2)) b 0 := by
    have h1 : HasDerivAt (fun u : ℝ ↦ 1 + b * u + c * u ^ 2) (b + c * (2 * 0)) 0 := by
      have := (((hasDerivAt_id' (0 : ℝ)).const_mul b).const_add 1).fun_add
        (((hasDerivAt_id' (0 : ℝ)).pow 2).const_mul c)
      simpa using this
    have := h1.log (by norm_num)
    simpa using this
  have h2 := hd.tendsto_slope_zero_right
  simp only [zero_add, smul_eq_mul, mul_zero] at h2
  refine (h2.comp tendsto_inv_atTop_nhdsGT_zero).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  simp [Function.comp]

theorem tendsto_log_quad_zero (b c : ℝ) :
    Tendsto (fun R : ℝ ↦ Real.log (1 + b * R⁻¹ + c * R⁻¹ ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ ↦ 1 + b * R⁻¹ + c * R⁻¹ ^ 2) atTop (𝓝 1) := by
    have := tendsto_inv_atTop_zero (𝕜 := ℝ)
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).add (this.const_mul b)).add
      ((this.pow 2).const_mul c)
    simpa using h
  have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h1
  simpa [Function.comp_def] using this


theorem log_sq_add_sq_eq {x y R : ℝ} (hR : 0 < R) (hy : 0 < y) (s : ℝ) (hs : s = x ∨ s = -x) :
    Real.log ((R - s) ^ 2 + y ^ 2) =
      2 * Real.log R + Real.log (1 + (-2 * s) * R⁻¹ + (x ^ 2 + y ^ 2) * R⁻¹ ^ 2) := by
  have hs2 : s ^ 2 = x ^ 2 := by rcases hs with rfl | rfl <;> ring
  have hpos : 0 < 1 + (-2 * s) * R⁻¹ + (x ^ 2 + y ^ 2) * R⁻¹ ^ 2 := by
    have : 1 + (-2 * s) * R⁻¹ + (x ^ 2 + y ^ 2) * R⁻¹ ^ 2 = ((R - s) ^ 2 + y ^ 2) / R ^ 2 := by
      field_simp
      nlinarith [hs2]
    rw [this]; positivity
  have : (R - s) ^ 2 + y ^ 2 = R ^ 2 * (1 + (-2 * s) * R⁻¹ + (x ^ 2 + y ^ 2) * R⁻¹ ^ 2) := by
    field_simp
    nlinarith [hs2]
  rw [this, Real.log_mul (by positivity) hpos.ne', Real.log_pow]
  push_cast; ring

theorem tendsto_integral_log_norm_sub {x y : ℝ} (hy : 0 < y) :
    Tendsto (fun R : ℝ ↦ (logPrimD x y R - logPrimD x y (-R)) / 2 - (2 * R * Real.log R - 2 * R))
      atTop (𝓝 (Real.pi * y)) := by
  set c : ℝ := x ^ 2 + y ^ 2 with hc
  have h1 := tendsto_slope_log_quad (-2 * x) c
  have h2 := tendsto_slope_log_quad (-2 * -x) c
  have h3 := tendsto_log_quad_zero (-2 * x) c
  have h4 := tendsto_log_quad_zero (-2 * -x) c
  have hE : Tendsto (fun R : ℝ ↦
      ((R * Real.log (1 + (-2 * x) * R⁻¹ + c * R⁻¹ ^ 2) +
        R * Real.log (1 + (-2 * -x) * R⁻¹ + c * R⁻¹ ^ 2)) +
        x * (Real.log (1 + (-2 * -x) * R⁻¹ + c * R⁻¹ ^ 2) -
          Real.log (1 + (-2 * x) * R⁻¹ + c * R⁻¹ ^ 2))) / 2) atTop (𝓝 0) := by
    have := (((h1.add h2).add ((h4.sub h3).const_mul x)).div_const 2)
    simpa using this
  have hA1 : Tendsto (fun R : ℝ ↦ y * Real.arctan ((R - x) / y)) atTop (𝓝 (y * (Real.pi / 2))) := by
    refine ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ?_).const_mul y
    exact (tendsto_atTop_add_const_right _ (-x) tendsto_id).atTop_div_const hy |>.congr
      (fun R ↦ by simp [sub_eq_add_neg])
  have hA2 : Tendsto (fun R : ℝ ↦ y * Real.arctan ((R + x) / y)) atTop (𝓝 (y * (Real.pi / 2))) := by
    refine ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ?_).const_mul y
    exact (tendsto_atTop_add_const_right _ x tendsto_id).atTop_div_const hy
  have := (hE.add (hA1.add hA2))
  rw [show (0 : ℝ) + (y * (Real.pi / 2) + y * (Real.pi / 2)) = Real.pi * y by ring] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  have e1 := log_sq_add_sq_eq (x := x) hR hy x (Or.inl rfl)
  have e2 := log_sq_add_sq_eq (x := x) hR hy (-x) (Or.inr rfl)
  have e3 : Real.log ((-R - x) ^ 2 + y ^ 2) = Real.log ((R - -x) ^ 2 + y ^ 2) := by
    congr 1; ring
  have e4 : Real.arctan ((-R - x) / y) = - Real.arctan ((R + x) / y) := by
    rw [← Real.arctan_neg]; congr 1; ring
  unfold logPrimD
  rw [e3, e4, e1, e2]
  field_simp
  ring

end FF.LogEx

namespace FF.LogEx

theorem integral_oddpart (R : ℝ) :
    ∫ t in (-R)..R, (1 - (Set.Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹ = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
    (fun t : ℝ ↦ (1 - (Set.Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹)
  have hodd : ∀ t : ℝ, (1 - (Set.Icc (-1 : ℝ) 1).indicator 1 (-t)) * (-t)⁻¹ =
      -((1 - (Set.Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹) := by
    intro t
    have : (-t ∈ Set.Icc (-1 : ℝ) 1) ↔ t ∈ Set.Icc (-1 : ℝ) 1 := by
      simp only [Set.mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
    · simp [Set.indicator_of_mem ht, Set.indicator_of_mem (this.2 ht)]
    · simp [Set.indicator_of_notMem ht, Set.indicator_of_notMem (mt this.1 ht), inv_neg]
  simp_rw [hodd] at h
  rw [intervalIntegral.integral_neg, neg_neg] at h
  linarith

end FF.LogEx
