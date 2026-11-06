import FourierFrames.Defs
import OrtegaCerdaSeip.Lemma3.Potential

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


/-- The kernel `K_z(t) = (t - x)/((t - x)² + y²) - 1/t` (same expression as `logKernel`). -/
noncomputable def kern (z : ℂ) (t : ℝ) : ℝ :=
  (t - z.re) / ((t - z.re) ^ 2 + z.im ^ 2) - 1 / t

theorem hasDerivAt_phi {z : ℂ} (hy : 0 < z.im) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ Real.log ((s - z.re) ^ 2 + z.im ^ 2) / 2 - Real.log s) (kern z t) t := by
  have hD0 : 0 < (t - z.re) ^ 2 + z.im ^ 2 := by positivity
  have h1 : HasDerivAt (fun s : ℝ ↦ s - z.re) 1 t := (hasDerivAt_id' t).sub_const z.re
  have hD : HasDerivAt (fun s : ℝ ↦ (s - z.re) ^ 2 + z.im ^ 2) (2 * (t - z.re) * 1) t := by
    simpa using (h1.pow 2).add_const (z.im ^ 2)
  have h2 := (hD.log hD0.ne').div_const 2
  have h3 := h2.sub (Real.hasDerivAt_log ht)
  refine h3.congr_deriv ?_
  unfold kern
  field_simp

theorem kern_continuousOn {z : ℂ} (hy : 0 < z.im) : ContinuousOn (kern z) {t : ℝ | t ≠ 0} := by
  intro t ht
  unfold kern
  have : ∀ s : ℝ, (s - z.re) ^ 2 + z.im ^ 2 ≠ 0 := fun s ↦ by positivity
  exact (((continuous_id.sub continuous_const).div
    ((continuous_id.sub continuous_const).pow 2 |>.add continuous_const) this).continuousAt.sub
    ((continuous_const.continuousAt).div continuousAt_id ht)).continuousWithinAt

theorem measurable_kern (z : ℂ) : Measurable (kern z) := by
  unfold kern
  fun_prop

theorem norm_sub_ge_im {z : ℂ} (t : ℝ) : z.im ≤ ‖(t : ℂ) - z‖ := by
  have := Complex.abs_im_le_norm ((t : ℂ) - z)
  simp at this
  exact (le_abs_self _).trans this

theorem abs_kern_le_aux {z : ℂ} (hy : 0 < z.im) {t : ℝ} (ht : t ≠ 0) :
    |kern z t| ≤ ‖z‖ / (|t| * ‖(t : ℂ) - z‖) := by
  have htz : (t : ℂ) - z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this; linarith
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have e1 : (1 / ((t : ℂ) - z)).re = (t - z.re) / ((t - z.re) ^ 2 + z.im ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]; simp; ring_nf
  have e2 : (1 / (t : ℂ)).re = 1 / t := by simp
  have e3 : kern z t = (z / ((t : ℂ) * ((t : ℂ) - z))).re := by
    have : z / ((t : ℂ) * ((t : ℂ) - z)) = 1 / ((t : ℂ) - z) - 1 / (t : ℂ) := by
      field_simp; ring
    rw [this, Complex.sub_re, e1, e2]; rfl
  rw [e3]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem abs_kern_le_near {z : ℂ} (hy : 0 < z.im) {t : ℝ} (ht : t ≠ 0) :
    |kern z t| ≤ ‖z‖ / (z.im * |t|) := by
  refine (abs_kern_le_aux hy ht).trans ?_
  have h1 := norm_sub_ge_im (z := z) t
  have h2 : 0 < |t| := abs_pos.2 ht
  have h3 : 0 < ‖(t : ℂ) - z‖ := lt_of_lt_of_le hy h1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ ‖z‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg t)]

theorem abs_kern_le_far {z : ℂ} (hy : 0 < z.im) {t : ℝ} (ht : 2 * ‖z‖ ≤ |t|) (h0 : 0 < ‖z‖) :
    |kern z t| ≤ 2 * ‖z‖ / t ^ 2 := by
  have ht0 : t ≠ 0 := by
    intro h; rw [h, abs_zero] at ht; linarith
  refine (abs_kern_le_aux hy ht0).trans ?_
  have h1 : |t| ≤ 2 * ‖(t : ℂ) - z‖ := by
    have := norm_sub_norm_le (t : ℂ) z
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  have h2 : 0 < |t| := abs_pos.2 ht0
  have h3 : 0 < ‖(t : ℂ) - z‖ := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity), ← sq_abs t]
  nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg t), norm_nonneg z]

/-- `|f · K_z|` is integrable if `|f(t)| ≤ c |t|` and `|f(t)| ≤ c (1 + |t|)^{1/2}`. -/
theorem integrable_mul_kern {z : ℂ} (hy : 0 < z.im) {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume)
    {c : ℝ} (hc : 0 ≤ c) (h1 : ∀ t, |f t| ≤ c * |t|)
    (h2 : ∀ t, |f t| ≤ c * (1 + |t|) ^ (1 / 2 : ℝ)) :
    Integrable (fun t ↦ f t * kern z t) := by
  set a : ℝ := ‖z‖ with ha
  have ha0 : 0 < a := lt_of_lt_of_le hy (Complex.im_le_norm z)
  set T : ℝ := max 1 (2 * a) with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  set M : ℝ := max (c * a / z.im * (1 + T) ^ (3 / 2 : ℝ)) (8 * a * c) with hM
  have hint : Integrable (fun t : ℝ ↦ M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (by simp; norm_num)).const_mul M
  refine Integrable.mono' hint (hf.mul (measurable_kern z).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun t ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  have hp : 0 < (1 + |t|) ^ (-(3 / 2 : ℝ)) := by positivity
  by_cases ht0 : t = 0
  · subst ht0
    have := h1 0
    simp at this
    simp [this]
    positivity
  rcases le_or_gt |t| T with hnear | hfar
  · -- near
    have hk := abs_kern_le_near hy ht0
    have ht1 : 0 < |t| := abs_pos.2 ht0
    have : |f t| * |kern z t| ≤ c * a / z.im := by
      calc |f t| * |kern z t| ≤ (c * |t|) * (a / (z.im * |t|)) :=
            mul_le_mul (h1 t) hk (abs_nonneg _) (by positivity)
        _ = c * a / z.im := by field_simp
    have h3 : (1 + T) ^ (3 / 2 : ℝ) * (1 + |t|) ^ (-(3 / 2 : ℝ)) ≥ 1 := by
      rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, ge_iff_le, le_div_iff₀ (by positivity), one_mul]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    calc |f t| * |kern z t| ≤ c * a / z.im := this
      _ ≤ (c * a / z.im * (1 + T) ^ (3 / 2 : ℝ)) * (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
          have : 0 ≤ c * a / z.im := by positivity
          nlinarith
      _ ≤ M * (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
          gcongr; exact le_max_left _ _
  · -- far
    have hk := abs_kern_le_far hy (le_trans (le_max_right _ _) hfar.le) ha0
    have ht1 : 1 ≤ |t| := le_trans hT1 hfar.le
    have hsq : (1 + |t|) ^ 2 ≤ 4 * t ^ 2 := by
      rw [← sq_abs t]; nlinarith
    have hu : 0 < 1 + |t| := by positivity
    have key : (1 + |t|) ^ (1 / 2 : ℝ) * ((1 + |t|) ^ 2)⁻¹ = (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast (1 + |t|) 2, ← Real.rpow_neg hu.le, ← Real.rpow_add hu]
      norm_num
    have hk2 : 2 * a / t ^ 2 ≤ 8 * a * ((1 + |t|) ^ 2)⁻¹ := by
      have e : 8 * a * ((1 + |t|) ^ 2)⁻¹ = 8 * a / (1 + |t|) ^ 2 := by rw [div_eq_mul_inv]
      have : 0 < (1 + |t|) ^ 2 := by positivity
      have ht2 : 0 < t ^ 2 := by positivity
      rw [e, div_le_div_iff₀ ht2 this]
      nlinarith [ha0, hsq]
    calc |f t| * |kern z t| ≤ (c * (1 + |t|) ^ (1 / 2 : ℝ)) * (2 * a / t ^ 2) :=
          mul_le_mul (h2 t) hk (abs_nonneg _) (by positivity)
      _ ≤ (c * (1 + |t|) ^ (1 / 2 : ℝ)) * (8 * a * ((1 + |t|) ^ 2)⁻¹) := by gcongr
      _ = (8 * a * c) * ((1 + |t|) ^ (1 / 2 : ℝ) * ((1 + |t|) ^ 2)⁻¹) := by ring
      _ = (8 * a * c) * (1 + |t|) ^ (-(3 / 2 : ℝ)) := by rw [key]
      _ ≤ M * (1 + |t|) ^ (-(3 / 2 : ℝ)) := by gcongr; exact le_max_right _ _

/-- The primitive `φ_z(t) = ½ log D(t) - log t`, `D(t) = (t - x)² + y²`. -/
noncomputable def phiK (z : ℂ) (t : ℝ) : ℝ :=
  Real.log ((t - z.re) ^ 2 + z.im ^ 2) / 2 - Real.log t

theorem phiK_sub_neg (z : ℂ) (s : ℝ) :
    phiK z s - phiK z (-s) =
      (Real.log ((s - z.re) ^ 2 + z.im ^ 2) - Real.log ((-s - z.re) ^ 2 + z.im ^ 2)) / 2 := by
  unfold phiK
  rw [Real.log_neg_eq_log]
  ring

theorem log_add_sq_sub_le {P Q y2 : ℝ} (hQ : 0 < Q) (hPQ : Q ≤ P) (hy : 0 ≤ y2) :
    0 ≤ Real.log (P + y2) - Real.log (Q + y2) ∧
      Real.log (P + y2) - Real.log (Q + y2) ≤ Real.log P - Real.log Q := by
  have hP : 0 < P := lt_of_lt_of_le hQ hPQ
  constructor
  · have := Real.log_le_log (by positivity) (by linarith : Q + y2 ≤ P + y2)
    linarith
  · rw [← Real.log_div (by positivity) (by positivity), ← Real.log_div hP.ne' hQ.ne']
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by positivity) hQ]
    nlinarith

theorem abs_phiK_sub_neg_le {z : ℂ} {s : ℝ} (hs : 0 < s) (hne : s ≠ |z.re|) :
    |phiK z s - phiK z (-s)| ≤ Real.log ((s + |z.re|) / abs (s - |z.re|)) := by
  set ξ : ℝ := |z.re| with hξ
  have hQ : 0 < (s - ξ) ^ 2 := by
    have : s - ξ ≠ 0 := sub_ne_zero.2 hne
    positivity
  have hPQ : (s - ξ) ^ 2 ≤ (s + ξ) ^ 2 := by nlinarith [abs_nonneg z.re]
  have hy2 : 0 ≤ z.im ^ 2 := sq_nonneg _
  obtain ⟨h1, h2⟩ := log_add_sq_sub_le hQ hPQ hy2
  have hRHS : Real.log ((s + ξ) / |s - ξ|) = (Real.log ((s + ξ) ^ 2) - Real.log ((s - ξ) ^ 2)) / 2 := by
    have hsξ : 0 < s + ξ := by have := abs_nonneg z.re; linarith
    have hab : 0 < |s - ξ| := abs_pos.2 (sub_ne_zero.2 hne)
    rw [Real.log_div hsξ.ne' hab.ne', Real.log_pow, ← sq_abs (s - ξ), Real.log_pow]
    push_cast; ring
  rw [hRHS, phiK_sub_neg]
  have hD : (-s - z.re) ^ 2 = (s + z.re) ^ 2 := by ring
  rw [hD]
  rw [abs_div, abs_two, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2), abs_le]
  rcases le_or_gt 0 z.re with hx | hx
  · have hξx : z.re = ξ := (abs_of_nonneg hx).symm
    rw [hξx]
    constructor <;> linarith
  · have hξx : z.re = -ξ := by rw [hξ, abs_of_neg hx]; ring
    rw [hξx]
    have e1 : (s - -ξ) ^ 2 = (s + ξ) ^ 2 := by ring
    have e2 : (s + -ξ) ^ 2 = (s - ξ) ^ 2 := by ring
    rw [e1, e2]
    constructor <;> linarith

/-- `H(σ) = log((1+σ)/|1-σ|)/σ`. -/
noncomputable def Hrat (σ : ℝ) : ℝ := Real.log ((1 + σ) / |1 - σ|) / σ

theorem Hrat_nonneg {σ : ℝ} (hσ : 0 < σ) : 0 ≤ Hrat σ := by
  unfold Hrat
  apply div_nonneg _ hσ.le
  by_cases h : |1 - σ| = 0
  · rw [h]; simp
  · have hp : 0 < |1 - σ| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h)
    apply Real.log_nonneg
    rw [one_le_div hp]
    rcases abs_cases (1 - σ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith

theorem Hrat_scale {ξ s : ℝ} (hξ : 0 < ξ) (hs : 0 < s) :
    Real.log ((s + ξ) / |s - ξ|) / s = ξ⁻¹ * Hrat (ξ⁻¹ * s) := by
  unfold Hrat
  have e : (1 + ξ⁻¹ * s) / |1 - ξ⁻¹ * s| = (s + ξ) / |s - ξ| := by
    have h1 : 1 + ξ⁻¹ * s = (s + ξ) / ξ := by field_simp; ring
    have h2 : |1 - ξ⁻¹ * s| = |s - ξ| / ξ := by
      have : 1 - ξ⁻¹ * s = (ξ - s) / ξ := by field_simp
      rw [this, abs_div, abs_of_pos hξ, abs_sub_comm]
    rw [h1, h2]
    by_cases h : |s - ξ| = 0
    · simp [h]
    · field_simp
  rw [e]
  field_simp

theorem integral_h_le {ξ : ℝ} (hξ : 0 ≤ ξ) (hH : IntegrableOn Hrat (Ioi 0)) :
    IntegrableOn (fun s : ℝ ↦ Real.log ((s + ξ) / |s - ξ|) / s) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), Real.log ((s + ξ) / |s - ξ|) / s ≤ ∫ s in Ioi (0 : ℝ), Hrat s := by
  rcases hξ.eq_or_lt with h0 | hpos
  · subst h0
    have : ∀ s ∈ Ioi (0 : ℝ), Real.log ((s + 0) / |s - 0|) / s = 0 := by
      intro s hs
      have hs' : 0 < s := hs
      simp [abs_of_pos hs', div_self hs'.ne']
    refine ⟨?_, ?_⟩
    · exact IntegrableOn.congr_fun integrableOn_zero (fun s hs ↦ (this s hs).symm) measurableSet_Ioi
    · rw [setIntegral_congr_fun measurableSet_Ioi this]
      simp only [integral_zero]
      exact setIntegral_nonneg measurableSet_Ioi (fun σ hσ ↦ Hrat_nonneg hσ)
  · have hscale : ∀ s ∈ Ioi (0 : ℝ), Real.log ((s + ξ) / |s - ξ|) / s = ξ⁻¹ * Hrat (ξ⁻¹ * s) :=
      fun s hs ↦ Hrat_scale hpos hs
    have hint : IntegrableOn (fun s : ℝ ↦ Hrat (ξ⁻¹ * s)) (Ioi 0) := by
      rw [integrableOn_Ioi_comp_mul_left_iff Hrat 0 (inv_pos.2 hpos), mul_zero]; exact hH
    refine ⟨?_, ?_⟩
    · exact IntegrableOn.congr_fun (hint.const_mul ξ⁻¹) (fun s hs ↦ (hscale s hs).symm) measurableSet_Ioi
    · rw [setIntegral_congr_fun measurableSet_Ioi hscale, integral_const_mul,
        integral_comp_mul_left_Ioi Hrat 0 (inv_pos.2 hpos), mul_zero, inv_inv, smul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

theorem continuousAt_phiK {z : ℂ} (hy : 0 < z.im) {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (phiK z) t :=
  (hasDerivAt_phi hy ht).continuousAt

theorem integrable_posLog_kern {z : ℂ} (hy : 0 < z.im) :
    Integrable (fun t : ℝ ↦ Real.posLog |t| * kern z t) := by
  refine integrable_mul_kern hy (f := fun t : ℝ ↦ Real.posLog |t|)
    (Real.continuous_posLog.comp continuous_abs).aestronglyMeasurable (c := 2) (by norm_num)
    (fun t ↦ ?_) (fun t ↦ ?_)
  · rw [abs_of_nonneg Real.posLog_nonneg]
    have := Real.posLog_le_abs |t|
    rw [abs_abs] at this
    linarith [abs_nonneg t]
  · rw [abs_of_nonneg Real.posLog_nonneg]
    have h1 := Real.posLog_le_log_one_add (abs_nonneg t)
    have h2 : Real.log (1 + |t|) ≤ 2 * Real.sqrt (1 + |t|) := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (show 0 < 1 + |t| by positivity))
      have h' : Real.log (Real.sqrt (1 + |t|)) = Real.log (1 + |t|) / 2 :=
        Real.log_sqrt (by positivity)
      linarith [Real.sqrt_nonneg (1 + |t|)]
    rw [← Real.sqrt_eq_rpow]
    linarith

/-- Integration by parts for `log t · K_z(t)` on an interval avoiding `0`. -/
theorem integral_log_mul_kern {z : ℂ} (hy : 0 < z.im) {a b : ℝ} (h0 : ∀ t ∈ Set.uIcc a b, t ≠ 0) :
    ∫ t in a..b, Real.log t * kern z t =
      Real.log b * phiK z b - Real.log a * phiK z a - ∫ t in a..b, t⁻¹ * phiK z t := by
  apply intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := Real.log) (u' := fun t ↦ t⁻¹)
    (v := phiK z) (v' := kern z)
  · intro t ht; exact Real.hasDerivAt_log (h0 t ht)
  · intro t ht; exact hasDerivAt_phi hy (h0 t ht)
  · exact (continuousOn_inv₀.mono (fun t ht ↦ h0 t ht)).intervalIntegrable
  · exact ((kern_continuousOn hy).mono (fun t ht ↦ h0 t ht)).intervalIntegrable

theorem integral_posLog_kern_eq {z : ℂ} (hy : 0 < z.im) {R : ℝ} (hR : 1 < R) :
    ∫ t in (-R)..R, Real.posLog |t| * kern z t =
      Real.log R * (phiK z R - phiK z (-R)) -
        ∫ s in (1 : ℝ)..R, (phiK z s - phiK z (-s)) / s := by
  have hg : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ ↦ Real.posLog |t| * kern z t) volume a b :=
    fun a b ↦ (integrable_posLog_kern hy).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (hg (-R) (-1)) (hg (-1) R),
    ← intervalIntegral.integral_add_adjacent_intervals (hg (-1) 1) (hg 1 R)]
  -- middle piece vanishes
  have hmid : ∫ t in (-1 : ℝ)..1, Real.posLog |t| * kern z t = 0 := by
    have : ∀ t ∈ Set.uIcc (-1 : ℝ) 1, Real.posLog |t| * kern z t = 0 := by
      intro t ht
      rw [Set.uIcc_of_le (by norm_num)] at ht
      have : Real.posLog |t| = 0 := by
        rw [Real.posLog_abs]; exact (Real.posLog_eq_zero_iff t).2 (abs_le.2 ht)
      rw [this, zero_mul]
    rw [intervalIntegral.integral_congr this]; simp
  -- right piece
  have hright : ∫ t in (1 : ℝ)..R, Real.posLog |t| * kern z t =
      Real.log R * phiK z R - ∫ t in (1 : ℝ)..R, t⁻¹ * phiK z t := by
    have h1 : ∫ t in (1 : ℝ)..R, Real.posLog |t| * kern z t =
        ∫ t in (1 : ℝ)..R, Real.log t * kern z t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hR.le] at ht
      have : 1 ≤ |t| := by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.1
      simp only []
      rw [Real.posLog_abs, Real.posLog_eq_log this]
    rw [h1, integral_log_mul_kern hy (fun t ht ↦ by
      rw [Set.uIcc_of_le hR.le] at ht; exact (by linarith [ht.1] : (0:ℝ) < t).ne'), Real.log_one]
    ring
  -- left piece
  have hleft : ∫ t in (-R)..(-1 : ℝ), Real.posLog |t| * kern z t =
      -(Real.log R * phiK z (-R)) - ∫ t in (-R)..(-1 : ℝ), t⁻¹ * phiK z t := by
    have h1 : ∫ t in (-R)..(-1 : ℝ), Real.posLog |t| * kern z t =
        ∫ t in (-R)..(-1 : ℝ), Real.log t * kern z t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      have : 1 ≤ |t| := by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2]
      simp only []
      rw [Real.posLog_abs, Real.posLog_eq_log this]
    rw [h1, integral_log_mul_kern hy (fun t ht ↦ by
      rw [Set.uIcc_of_le (by linarith)] at ht; exact (by linarith [ht.2] : t < 0).ne),
      Real.log_neg_eq_log, Real.log_neg_eq_log, Real.log_one]
    ring
  -- reflect the left integral
  have hrefl : ∫ t in (-R)..(-1 : ℝ), t⁻¹ * phiK z t = -∫ s in (1 : ℝ)..R, s⁻¹ * phiK z (-s) := by
    have := intervalIntegral.integral_comp_neg (a := 1) (b := R) (fun t : ℝ ↦ t⁻¹ * phiK z t)
    rw [← this]
    simp only [inv_neg, neg_mul]
    rw [intervalIntegral.integral_neg]
  have hpos : ∀ s ∈ Set.uIcc (1 : ℝ) R, s ≠ 0 := fun s hs ↦ by
    rw [Set.uIcc_of_le hR.le] at hs; exact (by linarith [hs.1] : (0:ℝ) < s).ne'
  have hi1 : IntervalIntegrable (fun s : ℝ ↦ s⁻¹ * phiK z s) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    exact ((continuousAt_inv₀ (hpos s hs)).mul (continuousAt_phiK hy (hpos s hs))).continuousWithinAt
  have hi2 : IntervalIntegrable (fun s : ℝ ↦ s⁻¹ * phiK z (-s)) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    exact ((continuousAt_inv₀ (hpos s hs)).mul
      ((continuousAt_phiK hy (neg_ne_zero.2 (hpos s hs))).comp continuousAt_neg)).continuousWithinAt
  have hsplit : ∫ s in (1 : ℝ)..R, (phiK z s - phiK z (-s)) / s =
      (∫ s in (1 : ℝ)..R, s⁻¹ * phiK z s) - ∫ s in (1 : ℝ)..R, s⁻¹ * phiK z (-s) := by
    rw [← intervalIntegral.integral_sub hi1 hi2]
    apply intervalIntegral.integral_congr
    intro s _
    simp only []
    ring
  rw [hleft, hmid, hright, hrefl, hsplit]
  ring

theorem abs_integral_phiK_le {z : ℂ} (hy : 0 < z.im) (hH : IntegrableOn Hrat (Ioi 0)) {R : ℝ}
    (hR : 1 < R) :
    |∫ s in (1 : ℝ)..R, (phiK z s - phiK z (-s)) / s| ≤ ∫ s in Ioi (0 : ℝ), Hrat s := by
  set ξ : ℝ := |z.re| with hξ
  obtain ⟨hhint, hhle⟩ := integral_h_le (abs_nonneg z.re) hH
  set h : ℝ → ℝ := fun s ↦ Real.log ((s + ξ) / |s - ξ|) / s with hh
  have hpos : ∀ s ∈ Set.uIcc (1 : ℝ) R, s ≠ 0 := fun s hs ↦ by
    rw [Set.uIcc_of_le hR.le] at hs; exact (by linarith [hs.1] : (0:ℝ) < s).ne'
  have hF : IntervalIntegrable (fun s : ℝ ↦ (phiK z s - phiK z (-s)) / s) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    exact (((continuousAt_phiK hy (hpos s hs)).sub
      ((continuousAt_phiK hy (neg_ne_zero.2 (hpos s hs))).comp continuousAt_neg)).div
        continuousAt_id (hpos s hs)).continuousWithinAt
  have hhI : IntervalIntegrable h volume 1 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    exact hhint.mono_set (fun s hs ↦ lt_of_lt_of_le one_pos hs.1.le)
  have hnn : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ h s := by
    intro s hs
    have hs' : 0 < s := hs
    -- `h s = ξ⁻¹ H(ξ⁻¹ s) ≥ 0` for `ξ > 0`, and `0` for `ξ = 0`
    rcases (abs_nonneg z.re).eq_or_lt with h0 | hpos'
    · have : ξ = 0 := h0.symm
      simp only [hh, this, add_zero, sub_zero, abs_of_pos hs', div_self hs'.ne', Real.log_one,
        zero_div, le_refl]
    · simp only [hh]
      rw [Hrat_scale hpos' hs']
      exact mul_nonneg (inv_nonneg.2 hpos'.le) (Hrat_nonneg (by positivity))
  calc |∫ s in (1 : ℝ)..R, (phiK z s - phiK z (-s)) / s|
      = ‖∫ s in (1 : ℝ)..R, (phiK z s - phiK z (-s)) / s‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ s in (1 : ℝ)..R, ‖(phiK z s - phiK z (-s)) / s‖ :=
        intervalIntegral.norm_integral_le_integral_norm hR.le
    _ ≤ ∫ s in (1 : ℝ)..R, h s := by
        apply intervalIntegral.integral_mono_ae_restrict hR.le hF.norm hhI
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
        filter_upwards [OCS.ae_ne_real ξ] with s hs hsI
        have hs1 : 0 < s := by linarith [hsI.1]
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hs1]
        simp only [hh]
        gcongr
        exact abs_phiK_sub_neg_le hs1 hs
    _ = ∫ s in Ioc (1 : ℝ) R, h s := intervalIntegral.integral_of_le hR.le
    _ ≤ ∫ s in Ioi (0 : ℝ), h s := by
        apply setIntegral_mono_set hhint
        · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hnn)
        · exact Filter.Eventually.of_forall (fun s hs ↦ lt_of_lt_of_le one_pos hs.1.le)
    _ ≤ ∫ s in Ioi (0 : ℝ), Hrat s := hhle

theorem tendsto_log_phiK_diff {z : ℂ} (hy : 0 < z.im) :
    Tendsto (fun R : ℝ ↦ Real.log R * (phiK z R - phiK z (-R))) atTop (𝓝 0) := by
  set c : ℝ := z.re ^ 2 + z.im ^ 2 with hc
  have h1 := tendsto_slope_log_quad (-2 * z.re) c
  have h2 := tendsto_slope_log_quad (-2 * -z.re) c
  have h3 : Tendsto (fun R : ℝ ↦ Real.log R / R) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h4 := h3.mul ((h1.sub h2).div_const 2)
  rw [zero_mul] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  have e1 := log_sq_add_sq_eq (x := z.re) (y := z.im) hR hy z.re (Or.inl rfl)
  have e2 := log_sq_add_sq_eq (x := z.re) (y := z.im) hR hy (-z.re) (Or.inr rfl)
  rw [phiK_sub_neg]
  have e3 : (-R - z.re) ^ 2 = (R - -z.re) ^ 2 := by ring
  rw [e3, e1, e2]
  field_simp
  ring

/-- **Hilbert-transform estimate for `log⁺|t|`** (`y > 0`): `|∫ log⁺|t| K_z(t) dt| ≤ ∫_0^∞ H`. -/
theorem abs_integral_posLog_kern_le {z : ℂ} (hy : 0 < z.im) (hH : IntegrableOn Hrat (Ioi 0)) :
    |∫ t : ℝ, Real.posLog |t| * kern z t| ≤ ∫ s in Ioi (0 : ℝ), Hrat s := by
  have hint := integrable_posLog_kern hy
  have hlim := intervalIntegral_tendsto_integral hint (tendsto_neg_atTop_atBot (G := ℝ)) tendsto_id
  have hlim' : Tendsto (fun R : ℝ ↦ |∫ t in (-R)..R, Real.posLog |t| * kern z t|) atTop
      (𝓝 |∫ t : ℝ, Real.posLog |t| * kern z t|) := (continuous_abs.tendsto _).comp hlim
  have hup : Tendsto (fun R : ℝ ↦ |Real.log R * (phiK z R - phiK z (-R))| +
      ∫ s in Ioi (0 : ℝ), Hrat s) atTop (𝓝 (∫ s in Ioi (0 : ℝ), Hrat s)) := by
    have := ((tendsto_log_phiK_diff hy).abs).add_const (∫ s in Ioi (0 : ℝ), Hrat s)
    simpa using this
  refine le_of_tendsto_of_tendsto hlim' hup ?_
  filter_upwards [eventually_gt_atTop 1] with R hR
  rw [integral_posLog_kern_eq hy hR]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (Real.log_nonneg hR.le)] 
  have := abs_integral_phiK_le hy hH hR
  rw [← abs_of_nonneg (Real.log_nonneg hR.le), ← abs_mul]
  linarith

/-- `u(t) = (1+|t|)^{-1/2}`, `v(s) = (1+s²)^{-1/2}`. -/
theorem young_uv (t s : ℝ) :
    (1 + |t|) ^ (-(1 / 2 : ℝ)) * (1 + s ^ 2) ^ (-(1 / 2 : ℝ)) ≤
      (1 + |t|) ^ (-(3 / 2 : ℝ)) / 3 + 2 / 3 * (1 + s ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have hpq : (3 : ℝ).HolderConjugate (3 / 2) :=
    Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have h := Real.young_inequality_of_nonneg (a := (1 + |t|) ^ (-(1 / 2 : ℝ)))
    (b := (1 + s ^ 2) ^ (-(1 / 2 : ℝ))) (by positivity) (by positivity) hpq
  rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)] at h
  have e1 : -(1 / 2 : ℝ) * 3 = -(3 / 2 : ℝ) := by norm_num
  have e2 : -(1 / 2 : ℝ) * (3 / 2) = -(3 / 4 : ℝ) := by norm_num
  rw [e1, e2] at h
  calc _ ≤ _ := h
    _ = _ := by ring

theorem integrable_rpow_three_half : Integrable (fun t : ℝ ↦ (1 + |t|) ^ (-(3 / 2 : ℝ))) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by simp; norm_num)
  simpa using this

theorem integrable_rpow_three_quarter : Integrable (fun s : ℝ ↦ (1 + s ^ 2) ^ (-(3 / 4 : ℝ))) := by
  have := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 3 / 2) (by simp; norm_num)
  have e : -(3 / 2 : ℝ) / 2 = -(3 / 4 : ℝ) := by norm_num
  simpa [e] using this

theorem integrable_uv (x : ℝ) :
    Integrable (fun t : ℝ ↦ (1 + |t|) ^ (-(1 / 2 : ℝ)) * (1 + (t - x) ^ 2) ^ (-(1 / 2 : ℝ))) := by
  have hmaj : Integrable (fun t : ℝ ↦ (1 + |t|) ^ (-(3 / 2 : ℝ)) / 3 +
      2 / 3 * (1 + (t - x) ^ 2) ^ (-(3 / 4 : ℝ))) :=
    (integrable_rpow_three_half.div_const 3).add
      ((integrable_rpow_three_quarter.comp_sub_right x).const_mul _)
  refine Integrable.mono' hmaj ?_ (Filter.Eventually.of_forall fun t ↦ ?_)
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact young_uv t (t - x)

theorem integral_uv_le (x : ℝ) :
    ∫ t : ℝ, (1 + |t|) ^ (-(1 / 2 : ℝ)) * (1 + (t - x) ^ 2) ^ (-(1 / 2 : ℝ)) ≤
      (∫ t : ℝ, (1 + |t|) ^ (-(3 / 2 : ℝ))) / 3 +
        2 / 3 * ∫ s : ℝ, (1 + s ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have hmaj : Integrable (fun t : ℝ ↦ (1 + |t|) ^ (-(3 / 2 : ℝ)) / 3 +
      2 / 3 * (1 + (t - x) ^ 2) ^ (-(3 / 4 : ℝ))) :=
    (integrable_rpow_three_half.div_const 3).add
      ((integrable_rpow_three_quarter.comp_sub_right x).const_mul _)
  calc _ ≤ ∫ t : ℝ, ((1 + |t|) ^ (-(3 / 2 : ℝ)) / 3 + 2 / 3 * (1 + (t - x) ^ 2) ^ (-(3 / 4 : ℝ))) :=
        integral_mono (integrable_uv x) hmaj (fun t ↦ young_uv t (t - x))
    _ = _ := by
        rw [integral_add (integrable_rpow_three_half.div_const 3)
          ((integrable_rpow_three_quarter.comp_sub_right x).const_mul _), integral_div,
          integral_const_mul]
        congr 2
        exact integral_sub_right_eq_self (fun s : ℝ ↦ (1 + s ^ 2) ^ (-(3 / 4 : ℝ))) x

theorem abs_div_sq_add_le {s y : ℝ} (hy : 1 ≤ y) :
    |s| / (s ^ 2 + y ^ 2) ≤ (1 + s ^ 2) ^ (-(1 / 2 : ℝ)) := by
  have hy2 : 1 ≤ y ^ 2 := by nlinarith
  have hD : 0 < s ^ 2 + y ^ 2 := by positivity
  have hsq : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ← one_div, div_le_div_iff₀ hD hsq]
  have h1 : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  nlinarith [sq_nonneg (|s| - Real.sqrt (1 + s ^ 2)), sq_abs s]

theorem abs_kern_le_uv {z : ℂ} (hy : 1 ≤ z.im) (t : ℝ) :
    |kern z t| ≤ (1 + (t - z.re) ^ 2) ^ (-(1 / 2 : ℝ)) + |t⁻¹| := by
  unfold kern
  have h1 := abs_div_sq_add_le (s := t - z.re) hy
  have h2 := abs_sub ((t - z.re) / ((t - z.re) ^ 2 + z.im ^ 2)) (1 / t)
  rw [abs_div, abs_of_pos (by positivity : 0 < (t - z.re) ^ 2 + z.im ^ 2), one_div] at h2
  rw [one_div]
  linarith

end FF.LogEx
