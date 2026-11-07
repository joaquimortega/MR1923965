import FourierFrames.Cited.Pavlov.Schwarz

/-!
# Poisson extension of the logarithm of distance to a real point

The tangent substitution reduces the integral to the difference of two translates
of the periodic, integrable function `log |cos θ|`. See `P5_LogPoissonKernel.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace FF.Pavlov

private def angleInterval : Set ℝ := Ioo (-(Real.pi / 2)) (Real.pi / 2)

private lemma log_cos_periodic : Function.Periodic (fun t : ℝ ↦ Real.log (Real.cos t)) Real.pi := by
  intro t
  simp only [Real.cos_add_pi, Real.log_neg_eq_log]

private lemma integral_log_cos_sub (α : ℝ) :
    (∫ t in -(Real.pi / 2)..Real.pi / 2, Real.log (Real.cos (t-α))) =
      ∫ t in -(Real.pi / 2)..Real.pi / 2, Real.log (Real.cos t) := by
  rw [intervalIntegral.integral_comp_sub_right (f := fun t ↦ Real.log (Real.cos t))]
  convert log_cos_periodic.intervalIntegral_add_eq (-(Real.pi / 2) - α) (-(Real.pi / 2)) using 1 <;>
    congr 1 <;> ring

private lemma log_tan_identity {c y θ : ℝ} (hy : 0 < y) (hθ : θ ∈ angleInterval)
    (hn : c + y * Real.tan θ ≠ 0) :
    Real.log |c + y * Real.tan θ| =
      Real.log ‖(c : ℂ) + (y : ℂ) * I‖ +
        Real.log (Real.cos (θ - ((c : ℂ) + (y : ℂ) * I).arg)) - Real.log (Real.cos θ) := by
  let w : ℂ := (c : ℂ) + (y : ℂ) * I
  have hw : w ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [w] at this
    linarith
  have hR : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
  have hnum : c * Real.cos θ + y * Real.sin θ = ‖w‖ * Real.cos (θ-w.arg) := by
    rw [Real.cos_sub, Complex.cos_arg hw, Complex.sin_arg]
    simp only [w, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, zero_add, add_zero, mul_one]
    field_simp [show ‖(c : ℂ) + (y : ℂ) * I‖ ≠ 0 from hR.ne']
  have hdiv : c + y * Real.tan θ = ‖w‖ * Real.cos (θ-w.arg) / Real.cos θ := by
    rw [← hnum, Real.tan_eq_sin_div_cos]
    field_simp
  have hcos : Real.cos (θ-w.arg) ≠ 0 := by
    intro h
    rw [hdiv, h, mul_zero, zero_div] at hn
    exact hn rfl
  rw [hdiv, Real.log_abs, Real.log_div (mul_ne_zero hR.ne' hcos) hc.ne',
    Real.log_mul hR.ne' hcos]

private lemma affine_tan_deriv (x : ℝ) {y θ : ℝ} (hθ : θ ∈ angleInterval) :
    HasDerivAt (fun t ↦ x + y * Real.tan t) (y / Real.cos θ ^ 2) θ := by
  simpa only [one_div, div_eq_mul_inv, one_mul] using
    ((Real.hasDerivAt_tan_of_mem_Ioo hθ).const_mul y).const_add x

private lemma affine_tan_inj (x : ℝ) {y : ℝ} (hy : 0 < y) :
    InjOn (fun t ↦ x + y * Real.tan t) angleInterval := by
  intro θ hθ φ hφ he
  apply Real.injOn_tan hθ hφ
  exact mul_left_cancel₀ hy.ne' (add_left_cancel he)

private lemma affine_tan_image (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (fun t ↦ x + y * Real.tan t) '' angleInterval = univ := by
  apply eq_univ_of_forall
  intro t
  refine ⟨Real.arctan ((t-x)/y), Real.arctan_mem_Ioo _, ?_⟩
  dsimp
  rw [Real.tan_arctan]
  field_simp
  ring

private lemma tan_poisson_jacobian (x : ℝ) {y θ : ℝ} (hy : 0 < y)
    (hθ : θ ∈ angleInterval) :
    |y / Real.cos θ ^ 2| *
      (y / (Real.pi * ((x+y*Real.tan θ-x)^2+y^2))) = Real.pi⁻¹ := by
  have hc : Real.cos θ ≠ 0 := (Real.cos_pos_of_mem_Ioo hθ).ne'
  rw [abs_of_pos (div_pos hy (sq_pos_of_ne_zero hc)), Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq θ]

private def logTanModel (c y θ : ℝ) : ℝ :=
  Real.log ‖(c : ℂ) + (y : ℂ)*I‖ +
    Real.log (Real.cos (θ - ((c : ℂ) + (y : ℂ)*I).arg)) - Real.log (Real.cos θ)

private lemma log_tan_ae (c : ℝ) {y : ℝ} (hy : 0 < y) :
    (fun θ ↦ Real.log |c+y*Real.tan θ|) =ᵐ[volume.restrict angleInterval]
      logTanModel c y := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    (volume.ae_ne (Real.arctan (-c/y))).filter_mono ae_restrict_le] with θ hθ hne
  apply log_tan_identity hy hθ
  intro he
  have ht : Real.tan θ = Real.tan (Real.arctan (-c/y)) := by
    rw [Real.tan_arctan]
    apply (eq_div_iff hy.ne').2
    nlinarith
  exact hne (Real.injOn_tan hθ (Real.arctan_mem_Ioo _) ht)

private lemma log_cos_sub_intervalIntegrable (α a b : ℝ) :
    IntervalIntegrable (fun θ ↦ Real.log (Real.cos (θ-α))) volume a b := by
  simpa only [Function.comp_apply, sub_add_cancel] using
    (intervalIntegrable_log_cos (a := a-α) (b := b-α)).comp_sub_right α

private lemma logTanModel_intervalIntegrable (c y : ℝ) :
    IntervalIntegrable (logTanModel c y) volume (-(Real.pi/2)) (Real.pi/2) := by
  exact (intervalIntegrable_const.add
    (log_cos_sub_intervalIntegrable _ _ _)).sub intervalIntegrable_log_cos

private lemma integrableOn_log_tan (c : ℝ) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun θ ↦ Real.log |c+y*Real.tan θ|) angleInterval := by
  have hi : IntegrableOn (logTanModel c y) angleInterval :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])).mp
      (logTanModel_intervalIntegrable c y)
  exact hi.congr (log_tan_ae c hy).symm

private lemma integral_log_tan (c : ℝ) {y : ℝ} (hy : 0 < y) :
    (∫ θ in angleInterval, Real.log |c+y*Real.tan θ|) =
      Real.pi * Real.log ‖(c : ℂ) + (y : ℂ)*I‖ := by
  rw [integral_congr_ae (log_tan_ae c hy)]
  change (∫ θ in Ioo (-(Real.pi/2)) (Real.pi/2), logTanModel c y θ) = _
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  change (∫ θ in -(Real.pi/2)..Real.pi/2,
    (Real.log ‖(c : ℂ)+(y : ℂ)*I‖ +
      Real.log (Real.cos (θ-((c : ℂ)+(y : ℂ)*I).arg))) - Real.log (Real.cos θ)) = _
  have hs := intervalIntegral.integral_sub
      ((intervalIntegrable_const (c := Real.log ‖(c : ℂ)+(y : ℂ)*I‖)).add (log_cos_sub_intervalIntegrable
        (((c : ℂ)+(y : ℂ)*I).arg) (-(Real.pi/2)) (Real.pi/2)))
      (intervalIntegrable_log_cos (a := -(Real.pi/2)) (b := Real.pi/2))
  have ha := intervalIntegral.integral_add
      (intervalIntegrable_const (c := Real.log ‖(c : ℂ)+(y : ℂ)*I‖))
      (log_cos_sub_intervalIntegrable (((c : ℂ)+(y : ℂ)*I).arg)
        (-(Real.pi/2)) (Real.pi/2))
  simp only [Function.comp_apply] at hs ha
  rw [hs, ha, intervalIntegral.integral_const, integral_log_cos_sub]
  simp only [smul_eq_mul]
  ring

private lemma poisson_log_aux (a x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (fun t : ℝ ↦ y / (Real.pi * ((t-x)^2+y^2)) * Real.log |t-a|) ∧
    (∫ t : ℝ, y / (Real.pi * ((t-x)^2+y^2)) * Real.log |t-a|) =
      Real.log ‖((x-a : ℝ) : ℂ) + (y : ℂ)*I‖ := by
  let g : ℝ → ℝ := fun t ↦ y / (Real.pi * ((t-x)^2+y^2)) * Real.log |t-a|
  let φ : ℝ → ℝ := fun θ ↦ x + y * Real.tan θ
  let φ' : ℝ → ℝ := fun θ ↦ y / Real.cos θ ^ 2
  have hder : ∀ θ ∈ angleInterval, HasDerivWithinAt φ (φ' θ) angleInterval θ :=
    fun θ hθ ↦ (affine_tan_deriv x hθ).hasDerivWithinAt
  have hjac : ∀ θ ∈ angleInterval,
      |φ' θ| • g (φ θ) = Real.pi⁻¹ * Real.log |(x-a)+y*Real.tan θ| := by
    intro θ hθ
    dsimp [φ', φ, g]
    rw [← mul_assoc, tan_poisson_jacobian x hy hθ]
    congr 1
    have he : x + y * Real.tan θ - a = x-a+y*Real.tan θ := by ring
    rw [he]
  have hint : IntegrableOn (fun θ ↦ |φ' θ| • g (φ θ)) angleInterval := by
    apply ((integrableOn_log_tan (x-a) hy).const_mul Real.pi⁻¹).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact (hjac θ hθ).symm
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo hder (affine_tan_inj x hy) g).mpr hint
  have he := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hder (affine_tan_inj x hy) g
  have himage : φ '' Ioo (-(Real.pi/2)) (Real.pi/2) = univ := affine_tan_image x hy
  rw [himage, integrableOn_univ] at hi
  rw [himage, setIntegral_univ] at he
  refine ⟨hi, ?_⟩
  change (∫ t, g t) = _
  rw [he]
  have hcongr := setIntegral_congr_fun (μ := volume) measurableSet_Ioo hjac
  rw [hcongr, integral_const_mul]
  have ht := integral_log_tan (x-a) hy
  dsimp [angleInterval] at ht
  rw [ht]
  field_simp

theorem integrable_poisson_log_abs_sub (a x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (fun t : ℝ ↦ y / (Real.pi * ((t-x)^2+y^2)) * Real.log |t-a|) :=
  (poisson_log_aux a x hy).1

theorem poissonIntegral_log_abs_sub (a x : ℝ) {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ, y / (Real.pi * ((t-x)^2+y^2)) * Real.log |t-a|) =
      Real.log ‖((x-a : ℝ) : ℂ) + (y : ℂ)*I‖ :=
  (poisson_log_aux a x hy).2

theorem logIntegrable_log_abs_sub (a : ℝ) :
    LogIntegrable (fun t ↦ Real.log |t-a|) := by
  have hi := (integrable_poisson_log_abs_sub a 0 (y := 1) zero_lt_one).const_mul Real.pi
  unfold LogIntegrable
  apply hi.congr
  filter_upwards [] with t
  field_simp
  ring

theorem schwarzIntegral_re_log_abs_sub (a : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (schwarzIntegral (fun t ↦ Real.log |t-a|) z).re = Real.log ‖z-(a:ℂ)‖ := by
  rw [schwarzIntegral_re (logIntegrable_log_abs_sub a) hz,
    poissonIntegral_log_abs_sub a z.re hz]
  congr 1
  congr 1
  apply Complex.ext <;> simp

end FF.Pavlov
