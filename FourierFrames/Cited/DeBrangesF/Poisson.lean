import FourierFrames.Cited.DeBrangesF.Herglotz
import FourierFrames.Cited.DeBrangesF.Cauchy
import FourierFrames.Cited.DeBrangesF.Transforms

/-!
# Returning from a normalized finite measure to the Poisson integral

See `blueprint/P4F_Elementary.md`, §4, independently reviewed in
`reviews/R11_TheoremF.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section
namespace FF

/-- The finite measure obtained from `μ` by the standard Cayley weight. -/
def poissonWeightedMeasure (μ : Measure ℝ) : Measure ℝ :=
  μ.withDensity (fun t ↦ ENNReal.ofReal (1 / (Real.pi * (1 + t ^ 2))))

lemma measurable_poissonWeight :
    Measurable (fun t : ℝ ↦ ENNReal.ofReal (1 / (Real.pi * (1 + t ^ 2)))) := by
  exact (measurable_const.div (measurable_const.mul
    (measurable_const.add (measurable_id.pow_const 2)))).ennreal_ofReal

lemma poissonWeight_integrable {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞) :
    Integrable (fun t : ℝ ↦ 1 / (Real.pi * (1 + t ^ 2))) μ := by
  convert (Herglotz.moment_integrable hm).const_mul Real.pi⁻¹ using 1
  ext t
  simp only [one_div, mul_inv_rev]
  ring

lemma poissonWeightedMeasure_finite {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞) :
    IsFiniteMeasure (poissonWeightedMeasure μ) := by
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable (poissonWeight_integrable hm).aestronglyMeasurable
    (Eventually.of_forall fun t ↦ by positivity)).2 (poissonWeight_integrable hm)

lemma integral_poissonWeightedMeasure (μ : Measure ℝ) (f : ℝ → ℂ) :
    ∫ t, f t ∂poissonWeightedMeasure μ =
      ∫ t, ((1 / (Real.pi * (1 + t ^ 2)) : ℝ) : ℂ) * f t ∂μ := by
  rw [poissonWeightedMeasure, integral_withDensity_eq_integral_toReal_smul
    measurable_poissonWeight (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with t
  rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]

lemma integral_poissonWeightedMeasure_real (μ : Measure ℝ) (f : ℝ → ℝ) :
    ∫ t, f t ∂poissonWeightedMeasure μ =
      ∫ t, (1 / (Real.pi * (1 + t ^ 2))) * f t ∂μ := by
  rw [poissonWeightedMeasure, integral_withDensity_eq_integral_toReal_smul
    measurable_poissonWeight (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with t
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

namespace FPoisson

lemma add_I_ne_zero {z : ℂ} (hz : 0 ≤ z.im) : z + I ≠ 0 := by
  intro he
  have := congrArg Complex.im he
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at this
  linarith

lemma real_sub_I_ne_zero (t : ℝ) : (t : ℂ) - I ≠ 0 := by
  exact Herglotz.real_sub_ne_zero (by simp) t

/-- The disk Cauchy kernel in half-plane coordinates. -/
lemma cayley_kernel_eq {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    diskCauchyKernel (fun t : ℝ ↦ ((t : ℂ) - I) / ((t : ℂ) + I))
      ((z - I) / (z + I)) t = (z + I) * ((t : ℂ) - I) / (2 * I * ((t : ℂ) - z)) := by
  have ht := real_sub_I_ne_zero t
  have hzI := add_I_ne_zero hz.le
  have htz := Herglotz.real_sub_ne_zero hz t
  have hi : (I : ℂ) ≠ 0 := by simp
  unfold diskCauchyKernel
  simp only [map_div₀, map_sub, map_add, Complex.conj_ofReal, Complex.conj_I,
    sub_neg_eq_add]
  have hinner : 1 - (z - I) / (z + I) * (((t : ℂ) + I) / ((t : ℂ) - I)) =
      2 * I * ((t : ℂ) - z) / ((z + I) * ((t : ℂ) - I)) := by
    field_simp [hzI, ht]
    ring
  change (1 - (z - I) / (z + I) * (((t : ℂ) + I) / ((t : ℂ) - I)))⁻¹ = _
  rw [hinner]
  field_simp [hzI, ht, htz]

/-- The Poisson kernel under the Cayley change of variables. -/
lemma cayley_poisson_identity {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    2 * (diskCauchyKernel (fun t : ℝ ↦ ((t : ℂ) - I) / ((t : ℂ) + I))
      ((z - I) / (z + I)) t).re - 1 =
        z.im * (1 + t ^ 2) / ((t - z.re) ^ 2 + z.im ^ 2) := by
  have hd : (t - z.re) ^ 2 + z.im ^ 2 ≠ 0 := by positivity
  have hden : Complex.normSq (2 * I * ((t : ℂ) - z)) =
      4 * ((t - z.re) ^ 2 + z.im ^ 2) := by
    norm_num [Complex.normSq_mul, Complex.normSq_apply]
    ring
  rw [cayley_kernel_eq hz t, Complex.div_re, hden]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  norm_num
  field_simp [hd]
  ring

lemma circle_weight_expand (a p : ℂ) (hp : ‖p‖ = 1) :
    ((‖1 + conj a * p‖ ^ 2 : ℝ) : ℂ) =
      (1 + (‖a‖ ^ 2 : ℝ) : ℂ) + conj a * p + a * conj p := by
  have ha : ((‖a‖ ^ 2 : ℝ) : ℂ) = a * conj a := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hpp : p * conj p = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]
    norm_num
  have hq : ((‖1 + conj a * p‖ ^ 2 : ℝ) : ℂ) =
      (1 + conj a * p) * conj (1 + conj a * p) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hq, ha, map_add, map_one, map_mul, Complex.conj_conj]
  linear_combination a * conj a * hpp

/-- Integration under a bounded circle weight, expanded into three linear terms. -/
lemma integral_circle_weight {ν : Measure ℝ} {p f : ℝ → ℂ} (hp : Measurable p)
    (hpn : ∀ t, ‖p t‖ = 1) (hf : Integrable f ν)
    (hpf : Integrable (fun t ↦ p t * f t) ν)
    (hpcf : Integrable (fun t ↦ conj (p t) * f t) ν)
    (a : ℂ) {d : ℝ} (hd : 0 < d) :
    (d : ℂ) * ∫ t, f t ∂ν.withDensity (fun t ↦ ENNReal.ofReal (‖1 + conj a * p t‖ ^ 2 / d)) =
      (1 + (‖a‖ ^ 2 : ℝ) : ℂ) * ∫ t, f t ∂ν +
        conj a * ∫ t, p t * f t ∂ν + a * ∫ t, conj (p t) * f t ∂ν := by
  have hm : Measurable (fun t ↦ ENNReal.ofReal (‖1 + conj a * p t‖ ^ 2 / d)) := by fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top), ← integral_const_mul]
  calc
    _ = ∫ t, ((1 + (‖a‖ ^ 2 : ℝ) : ℂ) * f t +
        conj a * (p t * f t) + a * (conj (p t) * f t)) ∂ν := by
      apply integral_congr_ae
      filter_upwards with t
      rw [ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) hd.le), Complex.real_smul]
      push_cast
      have he := circle_weight_expand a (p t) (hpn t)
      push_cast at he
      have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
      field_simp
      linear_combination f t * he
    _ = _ := by
      have h₁ := (hf.const_mul (1 + (‖a‖ ^ 2 : ℝ) : ℂ)).add (hpf.const_mul (conj a))
      calc
        _ = (∫ t, ((1 + (‖a‖ ^ 2 : ℝ) : ℂ) * f t + conj a * (p t * f t)) ∂ν) +
            ∫ t, a * (conj (p t) * f t) ∂ν := integral_add h₁ (hpcf.const_mul a)
        _ = _ := by
          rw [integral_add (hf.const_mul (1 + (‖a‖ ^ 2 : ℝ) : ℂ)) (hpf.const_mul (conj a))]
          simp only [integral_const_mul]

end FPoisson

namespace FMeasure

/-- The unnormalized Cauchy transform for the finite Cayley-weighted measure. -/
def originalCauchyF (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t, diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t
    ∂poissonWeightedMeasure μ

/-- Total mass of the finite Cayley-weighted measure. -/
def originalMass (μ : Measure ℝ) : ℝ := (poissonWeightedMeasure μ Set.univ).toReal

lemma normalizedDensity_mul_inverse {E : ℂ → ℂ} (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) (t : ℝ) :
    (‖baseKernel E t / E t‖ ^ 2 / baseNorm E) *
      (‖1 + conj (anchor E) * theta E t‖ ^ 2 / defect E) =
        1 / (Real.pi * (1 + t ^ 2)) := by
  rw [baseKernel_div_norm_sq hE h0, baseNorm_eq hE,
    one_add_conj_anchor_mul_theta hE (by simp) (h0 t), norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (defect_pos hE), div_pow]
  have he : ‖E I‖ ≠ 0 := norm_ne_zero_iff.mpr (hE.1.2.1 I (by simp))
  have hd : ‖denom E t‖ ≠ 0 := norm_ne_zero_iff.mpr (denom_real_ne_zero hE h0 t)
  have hdef := (defect_pos hE).ne'
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [he, hd, hdef, ht, Real.pi_ne_zero]

/-- Undoing the normalized kernel density gives the Cayley weight. -/
theorem poissonWeightedMeasure_eq {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0) :
    poissonWeightedMeasure μ = (normalizedKernelMeasure μ E).withDensity
      (fun t ↦ ENNReal.ofReal (‖1 + conj (anchor E) * theta E t‖ ^ 2 / defect E)) := by
  have hm : Measurable (fun t : ℝ ↦
      ENNReal.ofReal (‖1 + conj (anchor E) * theta E t‖ ^ 2 / defect E)) := by
    have hp := measurable_theta_real hE.1
    fun_prop
  rw [normalizedKernelMeasure, ← withDensity_mul _ (measurable_normalizedKernelDensity hE.1) hm]
  apply withDensity_congr_ae
  filter_upwards with t
  rw [Pi.mul_apply, normalizedKernelDensity_eq hE t, ← ENNReal.ofReal_mul
    (div_nonneg (sq_nonneg _) (kernel_i_re_pos hE).le)]
  congr 1
  exact (normalizedDensity_mul_inverse hE h0 t).symm

/-- The inverse circle weight expands the original transform into `F`, `J`, and `H`. -/
theorem originalCauchyF_expand {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : 0 < z.im) :
    (defect E : ℂ) * originalCauchyF μ z =
      (1 + (‖anchor E‖ ^ 2 : ℝ) : ℂ) * cauchyF μ E z +
        conj (anchor E) * cauchyJ μ E z + anchor E * cauchyH μ E z := by
  unfold originalCauchyF
  rw [poissonWeightedMeasure_eq hE h0]
  simpa only [cauchyF, cauchyJ, cauchyH, diskCauchyTransform, one_mul] using
    FPoisson.integral_circle_weight (measurable_theta_real hE.1) (norm_theta_real hE h0)
      (integrable_cauchyF hE h0 hμ hz) (integrable_cauchyJ hE h0 hμ hz)
      (integrable_cauchyH hE h0 hμ hz) (anchor E) (defect_pos hE)

/-- The same inverse circle weight expands the original total mass. -/
theorem originalMass_expand {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) :
    (defect E : ℂ) * (originalMass μ : ℂ) =
      (1 + (‖anchor E‖ ^ 2 : ℝ) : ℂ) +
        conj (anchor E) * boundaryMean μ E + anchor E * conj (boundaryMean μ E) := by
  let := normalizedKernelMeasure_probability hE h0 hμ
  have hic : Integrable (fun t : ℝ ↦ conj (theta E t)) (normalizedKernelMeasure μ E) := by
    exact (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp
      (integrable_boundaryMean hE h0 hμ)
  have hc := FPoisson.integral_circle_weight (measurable_theta_real hE.1)
    (norm_theta_real hE h0) (integrable_const (1 : ℂ))
    (by simpa only [mul_one] using integrable_boundaryMean hE h0 hμ)
    (by simpa only [mul_one] using hic)
    (anchor E) (defect_pos hE)
  rw [← poissonWeightedMeasure_eq hE h0] at hc
  simpa [originalMass, boundaryMean, integral_conj, measureReal_def] using hc

/-- The real part of the original Cauchy transform is the half-plane Poisson integral. -/
theorem poissonInt_cayley_spec {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞)
    {z : ℂ} (hz : 0 < z.im) :
    poissonInt μ z ≠ ∞ ∧
      (poissonInt μ z).toReal = 2 * (originalCauchyF μ z).re - originalMass μ := by
  let := poissonWeightedMeasure_finite hm
  have hi : Integrable (diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z))
      (poissonWeightedMeasure μ) :=
    diskCauchyKernel_integrable measurable_cayley_real norm_cayley_real (norm_cayley_lt_one hz)
  have hip : Integrable (fun t : ℝ ↦ z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2))) μ := by
    have hir := ((Herglotz.kernel_integrable hm hz).const_mul (-I / Real.pi)).re
    simp only [RCLike.re_eq_complex_re, Herglotz.re_scaled_kernel] at hir
    exact hir
  have hpos : ∀ t : ℝ, 0 ≤ z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2)) :=
    fun t ↦ div_nonneg hz.le (mul_nonneg Real.pi_pos.le (by positivity))
  refine ⟨(herglotzG_spec hm 0).2 z hz |>.1, ?_⟩
  calc
    (poissonInt μ z).toReal =
        ∫ t : ℝ, z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2)) ∂μ := by
      symm
      exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hpos) hip.aestronglyMeasurable
    _ = ∫ t : ℝ, (2 * (diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t).re - 1)
        ∂poissonWeightedMeasure μ := by
      rw [integral_poissonWeightedMeasure_real]
      apply integral_congr_ae
      filter_upwards with t
      change _ = _ * (2 * (diskCauchyKernel (fun t : ℝ ↦ ((t : ℂ)-I)/((t : ℂ)+I))
        ((z-I)/(z+I)) t).re - 1)
      rw [FPoisson.cayley_poisson_identity hz t]
      have ht : 1 + t ^ 2 ≠ 0 := by positivity
      field_simp
    _ = 2 * (originalCauchyF μ z).re - originalMass μ := by
      have hir : Integrable (fun t ↦ (diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t).re)
          (poissonWeightedMeasure μ) := by simpa only [RCLike.re_eq_complex_re] using hi.re
      rw [integral_sub (hir.const_mul 2) (integrable_const (1 : ℝ)), integral_const_mul,
        show (∫ t, (diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t).re
          ∂poissonWeightedMeasure μ) = (originalCauchyF μ z).re from
          by simpa only [RCLike.re_eq_complex_re, originalCauchyF] using integral_re hi]
      simp [originalCauchyF, originalMass, measureReal_def]

end FMeasure
end FF
