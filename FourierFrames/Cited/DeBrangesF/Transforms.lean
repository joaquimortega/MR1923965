import FourierFrames.Cited.DeBrangesF.Kernel
import FourierFrames.Cited.DeBrangesF.Normalization
import FourierFrames.Cited.DeBrangesF.Cauchy

/-!
# The three Cauchy transforms used in Theorem F

The measure is normalized at the reproducing kernel at `i`. The two weighted
transforms use the normalized inner function and its complex conjugate.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF.FMeasure

/-- The unweighted Cauchy transform of the normalized measure. -/
def cauchyF (μ : Measure ℝ) (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  diskCauchyTransform (normalizedKernelMeasure μ E) (fun t ↦ cayley t)
    (fun _ ↦ 1) (cayley z)

/-- The transform weighted by the conjugate normalized inner function. -/
def cauchyH (μ : Measure ℝ) (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  diskCauchyTransform (normalizedKernelMeasure μ E) (fun t ↦ cayley t)
    (fun t ↦ conj (theta E t)) (cayley z)

/-- The transform weighted by the normalized inner function. -/
def cauchyJ (μ : Measure ℝ) (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  diskCauchyTransform (normalizedKernelMeasure μ E) (fun t ↦ cayley t)
    (fun t ↦ theta E t) (cayley z)

/-- The boundary mean of the normalized inner function. -/
def boundaryMean (μ : Measure ℝ) (E : ℂ → ℂ) : ℂ :=
  ∫ t, theta E t ∂normalizedKernelMeasure μ E

theorem measurable_cayley_real : Measurable (fun t : ℝ ↦ cayley t) := by
  unfold cayley
  fun_prop

theorem measurable_theta_real {E : ℂ → ℂ} (hE : IsHB E) :
    Measurable (fun t : ℝ ↦ theta E t) := by
  have h₁ : Measurable (fun t : ℝ ↦ thetaFn E t) := by
    unfold thetaFn
    exact ((FF.Differentiable.fstar hE.1).continuous.measurable.comp Complex.measurable_ofReal).div
      (hE.1.continuous.measurable.comp Complex.measurable_ofReal)
  exact (h₁.sub_const _).div (measurable_const.sub (h₁.const_mul _))

variable {μ : Measure ℝ} {E : ℂ → ℂ}

theorem integrable_cauchyF (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    Integrable (diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z))
      (normalizedKernelMeasure μ E) := by
  let := normalizedKernelMeasure_probability hE h0 hμ
  exact diskCauchyKernel_integrable measurable_cayley_real norm_cayley_real
    (norm_cayley_lt_one hz)

theorem integrable_cauchyH (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    Integrable (fun t : ℝ ↦ conj (theta E t) *
      diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t)
      (normalizedKernelMeasure μ E) := by
  let := normalizedKernelMeasure_probability hE h0 hμ
  exact diskCauchyTransform_integrable measurable_cayley_real norm_cayley_real
    ((Complex.continuous_conj.measurable.comp (measurable_theta_real hE.1))) (M := 1)
    (fun t ↦ by simp [norm_theta_real hE h0]) (norm_cayley_lt_one hz)

theorem integrable_cauchyJ (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    Integrable (fun t : ℝ ↦ theta E t *
      diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t)
      (normalizedKernelMeasure μ E) := by
  let := normalizedKernelMeasure_probability hE h0 hμ
  exact diskCauchyTransform_integrable measurable_cayley_real norm_cayley_real
    (measurable_theta_real hE.1) (M := 1)
    (fun t ↦ (norm_theta_real hE h0 t).le) (norm_cayley_lt_one hz)

theorem integrable_boundaryMean (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) :
    Integrable (fun t : ℝ ↦ theta E t) (normalizedKernelMeasure μ E) := by
  let := normalizedKernelMeasure_probability hE h0 hμ
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_theta_real hE.1).aestronglyMeasurable ?_
  exact Eventually.of_forall fun t ↦ (norm_theta_real hE h0 t).le

theorem cauchyF_ne_zero (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) : cauchyF μ E z ≠ 0 := by
  let := normalizedKernelMeasure_probability hE h0 hμ
  exact diskCauchyTransform_ne_zero measurable_cayley_real norm_cayley_real
    (norm_cayley_lt_one hz)

@[simp] theorem cauchyF_I (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) : cauchyF μ E I = 1 := by
  let := normalizedKernelMeasure_probability hE h0 hμ
  simp [cauchyF, diskCauchyTransform, diskCauchyKernel]

@[simp] theorem cauchyJ_I : cauchyJ μ E I = boundaryMean μ E := by
  simp [cauchyJ, boundaryMean, diskCauchyTransform, diskCauchyKernel]

@[simp] theorem cauchyH_I : cauchyH μ E I = conj (boundaryMean μ E) := by
  simp [cauchyH, boundaryMean, diskCauchyTransform, diskCauchyKernel, integral_conj]

theorem differentiableOn_cauchyF (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) : DifferentiableOn ℂ (cauchyF μ E) UHP := by
  let := normalizedKernelMeasure_probability hE h0 hμ
  exact (diskCauchyTransform_differentiableOn measurable_cayley_real norm_cayley_real
    measurable_const (M := 1) (fun _ ↦ by simp)).comp differentiableOn_cayley
      (fun _ hz ↦ norm_cayley_lt_one hz)

theorem differentiableOn_cauchyH (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) : DifferentiableOn ℂ (cauchyH μ E) UHP := by
  let := normalizedKernelMeasure_probability hE h0 hμ
  exact (diskCauchyTransform_differentiableOn measurable_cayley_real norm_cayley_real
    ((Complex.continuous_conj.measurable.comp (measurable_theta_real hE.1))) (M := 1)
    (fun t ↦ by simp [norm_theta_real hE h0])).comp differentiableOn_cayley
      (fun _ hz ↦ norm_cayley_lt_one hz)

theorem differentiableOn_cauchyJ (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) : DifferentiableOn ℂ (cauchyJ μ E) UHP := by
  let := normalizedKernelMeasure_probability hE h0 hμ
  exact (diskCauchyTransform_differentiableOn measurable_cayley_real norm_cayley_real
    (measurable_theta_real hE.1) (M := 1)
    (fun t ↦ (norm_theta_real hE h0 t).le)).comp differentiableOn_cayley
      (fun _ hz ↦ norm_cayley_lt_one hz)

end FF.FMeasure
