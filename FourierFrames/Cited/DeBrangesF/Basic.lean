import FourierFrames.Cited.DeBrangesFC

/-!
# Isometric measures for de Branges spaces

Shared definitions for the proof of Theorem F. The statement `TheoremF` remains the
one in `FourierFrames/Defs.lean`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- `μ` embeds `H(E)` isometrically in `L²(μ/|E|²)`. -/
def IsIsometricMeasure (μ : Measure ℝ) (E : ℂ → ℂ) : Prop :=
  ∀ f : ℂ → ℂ, MemHE E f → ∫⁻ t, ‖f t / E t‖ₑ ^ 2 ∂μ = heNormSq E f

/-- The regularized Herglotz transform of a measure on the real line. -/
def herglotzG (μ : Measure ℝ) (c : ℝ) (z : ℂ) : ℂ :=
  -(I / Real.pi) * ∫ t : ℝ, (((t : ℂ) - z)⁻¹ - ((t / (1 + t ^ 2) : ℝ) : ℂ)) ∂μ + I * c

end FF
