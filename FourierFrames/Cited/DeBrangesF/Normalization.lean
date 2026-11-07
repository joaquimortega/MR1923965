import FourierFrames.Cited.DeBrangesF.Moment
import FourierFrames.Cited.DeBrangesF.Isometry

/-!
# A probability measure obtained from an isometric measure

Weight an isometric measure by the squared normalized reproducing kernel at `i`.
The resulting measure has mass one. See `blueprint/P4F_Normalization.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section
namespace FF

/-- The diagonal kernel at `i` is strictly positive. -/
theorem kernel_i_re_pos {E : ℂ → ℂ} (hE : IsStrictHB E) :
    0 < (deBrangesKernel E I I).re := by
  rw [deBrangesKernel_diag E (by simp)]
  simp only [Complex.ofReal_re, Complex.I_im, mul_one]
  apply div_pos _ (by positivity)
  have h := hE.2 I (by simp)
  nlinarith [norm_nonneg (E (conj I)), norm_nonneg (E I)]

/-- The squared kernel norm, as an extended nonnegative real. -/
theorem heNormSq_kernel_i {E : ℂ → ℂ} (hE : IsHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) :
    heNormSq E (deBrangesKernel E I) = ENNReal.ofReal (deBrangesKernel E I I).re := by
  rw [← heNormSq_kernel hE h0 I]
  exact (ENNReal.ofReal_toReal
    ((memHE_deBrangesKernel hE h0 I).heNormSq_lt_top hE.1 h0).ne).symm

/-- The probability measure used to normalize the two kernel identities. -/
def normalizedKernelMeasure (μ : Measure ℝ) (E : ℂ → ℂ) : Measure ℝ :=
  μ.withDensity (fun t ↦ ‖deBrangesKernel E I t / E t‖ₑ ^ 2 /
    ENNReal.ofReal (deBrangesKernel E I I).re)

/-- The kernel density expressed using ordinary real-valued squares. -/
theorem normalizedKernelDensity_eq {E : ℂ → ℂ} (hE : IsStrictHB E) (t : ℝ) :
    ‖deBrangesKernel E I t / E t‖ₑ ^ 2 / ENNReal.ofReal (deBrangesKernel E I I).re =
      ENNReal.ofReal (‖deBrangesKernel E I t / E t‖ ^ 2 /
        (deBrangesKernel E I I).re) := by
  rw [ENNReal.ofReal_div_of_pos (kernel_i_re_pos hE), enorm_sq_eq_ofReal]

/-- The normalizing density is measurable. -/
theorem measurable_normalizedKernelDensity {E : ℂ → ℂ} (hE : IsHB E) :
    Measurable (fun t : ℝ ↦ ‖deBrangesKernel E I t / E t‖ₑ ^ 2 /
      ENNReal.ofReal (deBrangesKernel E I I).re) := by
  have hm := measurable_div_real hE (differentiable_deBrangesKernel hE.1 I)
  exact (hm.enorm.pow_const 2).div_const _

/-- Normalizing an isometric measure at `i` gives a probability measure. -/
theorem normalizedKernelMeasure_probability {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) :
    IsProbabilityMeasure (normalizedKernelMeasure μ E) := by
  apply isProbabilityMeasure_iff.mpr
  rw [normalizedKernelMeasure, withDensity_apply _ MeasurableSet.univ]
  simp only [setLIntegral_univ]
  change (∫⁻ t : ℝ, ‖deBrangesKernel E I t / E t‖ₑ ^ 2 *
    (ENNReal.ofReal (deBrangesKernel E I I).re)⁻¹ ∂μ) = 1
  rw [lintegral_mul_const _
    ((measurable_div_real hE.1 (differentiable_deBrangesKernel hE.1.1 I)).enorm.pow_const 2)]
  rw [hμ _ (memHE_deBrangesKernel hE.1 h0 I), heNormSq_kernel_i hE.1 h0]
  exact ENNReal.mul_inv_cancel (by simpa using (kernel_i_re_pos hE))
    ENNReal.ofReal_ne_top

/-- Integration against the normalized measure, in real scalar form. -/
theorem integral_normalizedKernelMeasure {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (f : ℝ → ℂ) :
    ∫ t, f t ∂normalizedKernelMeasure μ E =
      ∫ t, ((‖deBrangesKernel E I t / E t‖ ^ 2 /
        (deBrangesKernel E I I).re : ℝ) : ℂ) * f t ∂μ := by
  unfold normalizedKernelMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_normalizedKernelDensity hE.1)]
  · apply integral_congr_ae
    filter_upwards with t
    rw [normalizedKernelDensity_eq hE t,
      ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) (kernel_i_re_pos hE).le),
      Complex.real_smul]
  · filter_upwards with t
    rw [normalizedKernelDensity_eq hE t]
    exact ENNReal.ofReal_lt_top

/-- The kernel at `i` has no real zeros. -/
theorem kernel_i_real_ne_zero {E : ℂ → ℂ} (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) (t : ℝ) : deBrangesKernel E I t ≠ 0 := by
  intro h
  have hb := momentWeight_le_kernel hE h0 t
  simp only [h, zero_div, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero] at hb
  have hp : 0 < 1 / (1 + t ^ 2) := by positivity
  linarith

/-- The weighted normalized pairing reduces pointwise to the original pairing. -/
theorem normalizedKernel_pair_density {E : ℂ → ℂ} (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) (f g : ℂ → ℂ) (t : ℝ) :
    ((‖deBrangesKernel E I t / E t‖ ^ 2 /
      (deBrangesKernel E I I).re : ℝ) : ℂ) *
        (f t / deBrangesKernel E I t * conj (g t / deBrangesKernel E I t)) =
      ((deBrangesKernel E I I).re : ℂ)⁻¹ * (f t / E t * conj (g t / E t)) := by
  have hn : ((‖deBrangesKernel E I t / E t‖ ^ 2 : ℝ) : ℂ) =
      (deBrangesKernel E I t / E t) * conj (deBrangesKernel E I t / E t) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [Complex.ofReal_div, hn]
  simp only [map_div₀]
  have hk := kernel_i_real_ne_zero hE h0 t
  have hkc : conj (deBrangesKernel E I t) ≠ 0 := (map_ne_zero _).mpr hk
  field_simp

/-- Integrability transfers through the normalizing density. -/
theorem integrable_normalizedKernelMeasure_iff {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (f : ℝ → ℂ) :
    Integrable f (normalizedKernelMeasure μ E) ↔
      Integrable (fun t : ℝ ↦ ((‖deBrangesKernel E I t / E t‖ ^ 2 /
        (deBrangesKernel E I I).re : ℝ) : ℂ) * f t) μ := by
  unfold normalizedKernelMeasure
  rw [integrable_withDensity_iff_integrable_smul' (measurable_normalizedKernelDensity hE.1)]
  · simp only [normalizedKernelDensity_eq hE,
      ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) (kernel_i_re_pos hE).le),
      Complex.real_smul]
  · filter_upwards with t
    rw [normalizedKernelDensity_eq hE t]
    exact ENNReal.ofReal_lt_top

/-- Pairings of normalized elements of `H(E)` are integrable. -/
theorem integrable_normalizedKernel_pair {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    Integrable (fun t : ℝ ↦ f t / deBrangesKernel E I t *
      conj (g t / deBrangesKernel E I t)) (normalizedKernelMeasure μ E) := by
  rw [integrable_normalizedKernelMeasure_iff hE]
  simpa only [normalizedKernel_pair_density hE h0] using
    (hμ.integrable_pair hE.1 hf hg).const_mul ((deBrangesKernel E I I).re : ℂ)⁻¹

/-- The normalized measure preserves pairings up to the factor `1/κ`. -/
theorem integral_normalizedKernel_pair {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    ∫ t : ℝ, f t / deBrangesKernel E I t *
      conj (g t / deBrangesKernel E I t) ∂normalizedKernelMeasure μ E =
        heInner E f g / (deBrangesKernel E I I).re := by
  rw [integral_normalizedKernelMeasure hE]
  simp only [normalizedKernel_pair_density hE h0]
  rw [integral_const_mul, hμ.integral_pair hE.1 hf hg]
  ring

/-- Normalized elements of `H(E)` are integrable. -/
theorem integrable_normalizedKernel {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f : ℂ → ℂ} (hf : MemHE E f) :
    Integrable (fun t : ℝ ↦ f t / deBrangesKernel E I t) (normalizedKernelMeasure μ E) := by
  simpa only [div_self (kernel_i_real_ne_zero hE h0 _), map_one, mul_one] using
    integrable_normalizedKernel_pair hE h0 hμ hf (memHE_deBrangesKernel hE.1 h0 I)

/-- The mean of a normalized element is its value at `i`, divided by `κ`. -/
theorem integral_normalizedKernel {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f : ℂ → ℂ} (hf : MemHE E f) :
    ∫ t : ℝ, f t / deBrangesKernel E I t ∂normalizedKernelMeasure μ E =
      f I / (deBrangesKernel E I I).re := by
  have h := integral_normalizedKernel_pair hE h0 hμ hf (memHE_deBrangesKernel hE.1 h0 I)
  simpa only [div_self (kernel_i_real_ne_zero hE h0 _), map_one, mul_one,
    heInner_kernel hE.1 h0 hf I] using h

/-- The squared normalized modulus is integrable. -/
theorem integrable_normalizedKernel_norm_sq {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f : ℂ → ℂ} (hf : MemHE E f) :
    Integrable (fun t : ℝ ↦ ‖f t / deBrangesKernel E I t‖ ^ 2)
      (normalizedKernelMeasure μ E) := by
  refine (integrable_normalizedKernel_pair hE h0 hμ hf hf).re.congr
    (Eventually.of_forall fun t ↦ ?_)
  change (f t / deBrangesKernel E I t * conj (f t / deBrangesKernel E I t)).re = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- The normalized squared norm is the original squared norm divided by `κ`. -/
theorem integral_normalizedKernel_norm_sq {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f : ℂ → ℂ} (hf : MemHE E f) :
    ∫ t : ℝ, ‖f t / deBrangesKernel E I t‖ ^ 2 ∂normalizedKernelMeasure μ E =
      (heNormSq E f).toReal / (deBrangesKernel E I I).re := by
  have h := integral_normalizedKernel_pair hE h0 hμ hf hf
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  rw [integral_complex_ofReal, heInner_self hE.1 hf] at h
  exact_mod_cast h

/-- Normalized elements are square integrable for the probability measure. -/
theorem memLp_normalizedKernel {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f : ℂ → ℂ} (hf : MemHE E f) :
    MemLp (fun t : ℝ ↦ f t / deBrangesKernel E I t) 2
      (normalizedKernelMeasure μ E) := by
  have hm : Measurable (fun t : ℝ ↦ f t / deBrangesKernel E I t) :=
    (hf.1.continuous.measurable.comp Complex.measurable_ofReal).div
      ((differentiable_deBrangesKernel hE.1.1 I).continuous.measurable.comp
        Complex.measurable_ofReal)
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
    (integrable_normalizedKernel_norm_sq hE h0 hμ hf)

end FF
