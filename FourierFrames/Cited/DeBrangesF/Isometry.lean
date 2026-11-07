import FourierFrames.Cited.DeBrangesF.Basic

/-!
# Polarization for an isometric measure

The norm identity defining an isometric measure gives square integrability and preserves
the full sesquilinear pairing, by complex polarization.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace FF

variable {μ : Measure ℝ} {E : ℂ → ℂ}

/-- Every element of `H(E)` remains square integrable for an isometric measure. -/
theorem IsIsometricMeasure.memLp (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f : ℂ → ℂ} (hf : MemHE E f) : MemLp (fun t : ℝ ↦ f t / E t) 2 μ := by
  unfold MemLp
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
    (measurable_div_real hE hf.1).aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hμ f hf] using
    hf.heNormSq_lt_top_of_isHB hE

/-- The pairing integrand is integrable for an isometric measure. -/
theorem IsIsometricMeasure.integrable_pair (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    Integrable (fun t : ℝ ↦ f t / E t * conj (g t / E t)) μ :=
  (hμ.memLp hE hf).integrable_mul (hμ.memLp hE hg).star

/-- The norm identity, expressed as an ordinary real integral. -/
theorem IsIsometricMeasure.integral_norm_sq (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f : ℂ → ℂ} (hf : MemHE E f) :
    ∫ t : ℝ, ‖f t / E t‖ ^ 2 ∂μ = (heNormSq E f).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t ↦ by positivity)
    ((measurable_div_real hE hf.1).norm.pow_const 2).aestronglyMeasurable]
  congr 1
  simpa only [← enorm_sq_eq_ofReal] using hμ f hf

/-- The sesquilinear pairing computed with the measure `μ`. -/
def measurePair (μ : Measure ℝ) (E f g : ℂ → ℂ) : ℂ :=
  ∫ t : ℝ, f t / E t * conj (g t / E t) ∂μ

theorem measurePair_smul_left (μ : Measure ℝ) (E f g : ℂ → ℂ) (c : ℂ) :
    measurePair μ E (fun z ↦ c * f z) g = c * measurePair μ E f g := by
  unfold measurePair
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

theorem measurePair_smul_right (μ : Measure ℝ) (E f g : ℂ → ℂ) (c : ℂ) :
    measurePair μ E f (fun z ↦ c * g z) = conj c * measurePair μ E f g := by
  unfold measurePair
  rw [← integral_const_mul]
  congr 1
  funext t
  simp only [mul_div_assoc, map_mul]
  ring

theorem IsIsometricMeasure.measurePair_self (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f : ℂ → ℂ} (hf : MemHE E f) : measurePair μ E f f = heInner E f f := by
  rw [heInner_self hE hf]
  unfold measurePair
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [integral_complex_ofReal, hμ.integral_norm_sq hE hf]

theorem IsIsometricMeasure.measurePair_add_left (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f g k : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) (hk : MemHE E k) :
    measurePair μ E (fun z ↦ f z + g z) k =
      measurePair μ E f k + measurePair μ E g k := by
  unfold measurePair
  simp_rw [add_div, add_mul]
  exact integral_add (hμ.integrable_pair hE hf hk) (hμ.integrable_pair hE hg hk)

theorem IsIsometricMeasure.measurePair_add_right (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f g k : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) (hk : MemHE E k) :
    measurePair μ E f (fun z ↦ g z + k z) =
      measurePair μ E f g + measurePair μ E f k := by
  unfold measurePair
  simp_rw [add_div, map_add, mul_add]
  exact integral_add (hμ.integrable_pair hE hf hg) (hμ.integrable_pair hE hf hk)

/-- Polarization of the isometry preserves the complex inner product. -/
theorem IsIsometricMeasure.measurePair_eq (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    measurePair μ E f g = heInner E f g := by
  have hadd {u v : ℂ → ℂ} (hu : MemHE E u) (hv : MemHE E v) :
      measurePair μ E u v + measurePair μ E v u = heInner E u v + heInner E v u := by
    have h := hμ.measurePair_self hE (hu.add hv)
    rw [hμ.measurePair_add_left hE hu hv (hu.add hv),
      hμ.measurePair_add_right hE hu hu hv, hμ.measurePair_add_right hE hv hu hv,
      heInner_add_left_of_isHB hE hu hv (hu.add hv),
      heInner_add_right_of_isHB hE hu hu hv, heInner_add_right_of_isHB hE hv hu hv,
      hμ.measurePair_self hE hu, hμ.measurePair_self hE hv] at h
    linear_combination h
  have h₁ := hadd hf hg
  have h₂ := hadd hf (hg.const_mul I)
  rw [measurePair_smul_right, measurePair_smul_left,
    heInner_smul_right, heInner_smul_left, Complex.conj_I] at h₂
  linear_combination (norm := (ring_nf; simp [Complex.I_sq])) h₁ / 2 + I * h₂ / 2

/-- Integral form of the polarized isometry. -/
theorem IsIsometricMeasure.integral_pair (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    ∫ t : ℝ, f t / E t * conj (g t / E t) ∂μ = heInner E f g :=
  hμ.measurePair_eq hE hf hg

/-- Reproducing kernels retain their reproducing property under an isometric measure. -/
theorem IsIsometricMeasure.integral_kernel (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    (h0 : ∀ x : ℝ, E x ≠ 0) {f : ℂ → ℂ} (hf : MemHE E f) (w : ℂ) :
    ∫ t : ℝ, f t / E t * conj (deBrangesKernel E w t / E t) ∂μ = f w := by
  rw [hμ.integral_pair hE hf (memHE_deBrangesKernel hE h0 w), heInner_kernel hE h0 hf w]

end FF
