import FourierFrames.Defs

/-!
# Normalized integrals for the proof of Pavlov's theorem

The real and imaginary parts of the regularized Schwarz integral are the
Poisson and conjugate Poisson integrals. The subtraction is kept inside the
integrand; its two terms need not be separately integrable.
-/

open MeasureTheory Complex

noncomputable section

namespace FF.Pavlov

/-- Absolute integrability with the standard half-plane boundary weight. -/
def LogIntegrable (u : ℝ → ℝ) : Prop :=
  Integrable (fun t ↦ u t / (1 + t ^ 2)) volume

/-- The Schwarz integral normalized to have zero imaginary part at `i`. -/
def schwarzIntegral (u : ℝ → ℝ) (z : ℂ) : ℂ :=
  (-I / Real.pi) * ∫ t : ℝ,
    (((t : ℂ) - z)⁻¹ - ((t / (1 + t ^ 2) : ℝ) : ℂ)) * (u t : ℂ)

/-- The regularized conjugate Poisson integral. -/
def conjugatePoisson (u : ℝ → ℝ) (y x : ℝ) : ℝ :=
  Real.pi⁻¹ * ∫ t : ℝ,
    ((x - t) / ((x - t) ^ 2 + y ^ 2) + t / (1 + t ^ 2)) * u t

end FF.Pavlov
