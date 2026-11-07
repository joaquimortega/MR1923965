import FourierFrames.Cited.JohnNirenberg

/-!
# Second moments from the John–Nirenberg tail estimate
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace FF.Pavlov

/-- Layer cake for the square of a nonnegative real-valued function. -/
theorem lintegral_sq_eq_tail {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ} (hf : AEMeasurable f μ) (hpos : 0 ≤ᵐ[μ] f) :
    (∫⁻ x, ENNReal.ofReal ((f x)^2) ∂μ) =
      ∫⁻ s in Ioi (0:ℝ), μ {x | s ≤ f x} * ENNReal.ofReal (2*s) := by
  have he := lintegral_comp_eq_lintegral_meas_le_mul μ hpos hf
    (g := fun s : ℝ ↦ 2*s)
    (fun _ _ ↦ (continuous_const.mul continuous_id).intervalIntegrable _ _)
    (by filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
        exact mul_nonneg (by norm_num) hs.le)
  have hi (z : ℝ) : (∫ s in (0:ℝ)..z, 2*s) = z^2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  simpa only [hi] using he

/-- Exponential decay of superlevel sets implies a finite second moment. -/
theorem integrable_sq_of_exp_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hpos : 0 ≤ᵐ[μ] f) {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (htail : ∀ s : ℝ, 0 < s →
      μ {x | s ≤ f x} ≤ ENNReal.ofReal (A * Real.exp (-c*s))) :
    Integrable (fun x ↦ (f x)^2) μ := by
  have hbase : IntegrableOn (fun s : ℝ ↦ s * Real.exp (-c*s)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1)
        (by norm_num) (by norm_num) hc
  have hi : IntegrableOn (fun s : ℝ ↦ 2*A*(s*Real.exp (-c*s))) (Ioi 0) :=
    hbase.const_mul _
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun s : ℝ ↦ 2*A*(s*Real.exp (-c*s))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (mul_nonneg (by norm_num) hA)
      (mul_nonneg hs.le (Real.exp_pos _).le)
  have hle : (∫⁻ x, ENNReal.ofReal ((f x)^2) ∂μ) ≤
      ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (2*A*(s*Real.exp (-c*s))) := by
    rw [lintegral_sq_eq_tail μ hf.aemeasurable hpos]
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    calc
      _ ≤ ENNReal.ofReal (A*Real.exp (-c*s)) * ENNReal.ofReal (2*s) := by
        exact mul_le_mul_left (htail s hs) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hA (Real.exp_pos _).le)]
        congr 1
        ring
  refine ⟨hf.pow 2, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x ↦ sq_nonneg (f x))).mpr
  exact lt_of_le_of_lt hle ((hasFiniteIntegral_iff_ofReal hnn).mp hi.2)

/-- Evaluation of the elementary exponential moment used in the BMO bound. -/
theorem integral_linear_exp_neg {c : ℝ} (hc : 0 < c) :
    (∫ s : ℝ in Ioi 0, s*Real.exp (-c*s)) = c⁻¹^2 := by
  have he := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := c)
    (by norm_num) hc
  norm_num [Real.rpow_two, Real.Gamma_nat_eq_factorial] at he
  simpa only [neg_mul, inv_pow] using he

/-- Quantitative second-moment estimate from an exponential superlevel bound. -/
theorem integral_sq_le_of_exp_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hpos : 0 ≤ᵐ[μ] f) {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (htail : ∀ s : ℝ, 0 < s →
      μ {x | s ≤ f x} ≤ ENNReal.ofReal (A * Real.exp (-c*s))) :
    (∫ x, (f x)^2 ∂μ) ≤ 2*A*c⁻¹^2 := by
  have hbase : IntegrableOn (fun s : ℝ ↦ s * Real.exp (-c*s)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1)
        (by norm_num) (by norm_num) hc
  have hi : IntegrableOn (fun s : ℝ ↦ 2*A*(s*Real.exp (-c*s))) (Ioi 0) :=
    hbase.const_mul _
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun s : ℝ ↦ 2*A*(s*Real.exp (-c*s))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (mul_nonneg (by norm_num) hA)
      (mul_nonneg hs.le (Real.exp_pos _).le)
  have hi₂ := integrable_sq_of_exp_tail μ hf hpos hA hc htail
  have heval : (∫ s : ℝ in Ioi 0, 2*A*(s*Real.exp (-c*s))) = 2*A*c⁻¹^2 := by
    rw [integral_const_mul, integral_linear_exp_neg hc]
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2*A*c⁻¹^2)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi₂
    (Eventually.of_forall fun x ↦ sq_nonneg (f x)), ← heval,
    ofReal_integral_eq_lintegral_ofReal hi hnn,
    lintegral_sq_eq_tail μ hf.aemeasurable hpos]
  apply lintegral_mono_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  calc
    _ ≤ ENNReal.ofReal (A*Real.exp (-c*s)) * ENNReal.ofReal (2*s) :=
      mul_le_mul_left (htail s hs) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hA (Real.exp_pos _).le)]
      congr 1
      ring

/-- Centered BMO oscillation is square integrable on every compact interval. -/
theorem bmo_osc_integrableOn_sq {u : ℝ → ℝ} (hu : LocallyIntegrable u)
    {M : ℝ} (hM : 0 < M)
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M)
    {a b : ℝ} (hab : a < b) :
    IntegrableOn (fun t ↦ (u t-intervalMean u a b)^2) (Icc a b) := by
  obtain ⟨C, c, hC, hc, hJN⟩ := FF.johnNirenberg_holds
  have hi : IntegrableOn (fun t ↦ |u t-intervalMean u a b|) (Icc a b) := by
    have he : IntegrableOn (fun t ↦ u t-intervalMean u a b) (Icc a b) :=
      (hu.integrableOn_isCompact isCompact_Icc).sub
        (integrableOn_const isCompact_Icc.measure_lt_top.ne)
    exact he.abs
  have hsq := integrable_sq_of_exp_tail (volume.restrict (Icc a b))
    hi.aestronglyMeasurable (Eventually.of_forall fun t ↦ abs_nonneg _)
    (A := C*(b-a)) (c := c/M) (mul_pos hC (sub_pos.mpr hab)).le (div_pos hc hM)
    (fun s hs ↦ ?_)
  · simpa only [IntegrableOn, sq_abs] using hsq
  · rw [Measure.restrict_apply' measurableSet_Icc]
    have he : {x : ℝ | s ≤ |u x-intervalMean u a b|} ∩ Icc a b =
        {x ∈ Icc a b | s ≤ |u x-intervalMean u a b|} := by ext x; simp [and_comm]
    rw [he]
    have he₂ : C*(b-a)*Real.exp (-(c/M)*s) =
        C*Real.exp (-(c*s/M))*(b-a) := by
      rw [show -(c/M)*s = -(c*s/M) by ring]
      ring
    rw [he₂]
    exact hJN u hu M hM hosc a b hab s hs

/-- The uniform local square estimate for BMO needed in the near-field argument. -/
theorem bmo_local_square_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ), LocallyIntegrable u →
      ∀ M : ℝ, 0 < M →
      (∀ a b : ℝ, a < b → meanOsc u a b ≤ M) →
      ∀ a b : ℝ, a < b →
        IntegrableOn (fun t ↦ (u t-intervalMean u a b)^2) (Icc a b) ∧
        (∫ t in a..b, (u t-intervalMean u a b)^2) ≤ C*M^2*(b-a) := by
  obtain ⟨C, c, hC, hc, hJN⟩ := FF.johnNirenberg_holds
  refine ⟨2*C/c^2, by positivity, ?_⟩
  intro u hu M hM hosc a b hab
  have hi : IntegrableOn (fun t ↦ |u t-intervalMean u a b|) (Icc a b) := by
    have he : IntegrableOn (fun t ↦ u t-intervalMean u a b) (Icc a b) :=
      (hu.integrableOn_isCompact isCompact_Icc).sub
        (integrableOn_const isCompact_Icc.measure_lt_top.ne)
    exact he.abs
  refine ⟨bmo_osc_integrableOn_sq hu hM hosc hab, ?_⟩
  have hb := integral_sq_le_of_exp_tail (volume.restrict (Icc a b))
    hi.aestronglyMeasurable (Eventually.of_forall fun t ↦ abs_nonneg _)
    (A := C*(b-a)) (c := c/M) (mul_pos hC (sub_pos.mpr hab)).le (div_pos hc hM)
    (fun s hs ↦ ?_)
  · rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]
    simp only [sq_abs] at hb
    apply hb.trans_eq
    field_simp
  · rw [Measure.restrict_apply' measurableSet_Icc]
    have he : {x : ℝ | s ≤ |u x-intervalMean u a b|} ∩ Icc a b =
        {x ∈ Icc a b | s ≤ |u x-intervalMean u a b|} := by ext x; simp [and_comm]
    rw [he]
    have he₂ : C*(b-a)*Real.exp (-(c/M)*s) =
        C*Real.exp (-(c*s/M))*(b-a) := by
      rw [show -(c/M)*s = -(c*s/M) by ring]
      ring
    rw [he₂]
    exact hJN u hu M hM hosc a b hab s hs

end FF.Pavlov
