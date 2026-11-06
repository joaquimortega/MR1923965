import FourierFrames.PW.Basic

/-!
# M10 — Fourier frames and sampling

See `blueprint/M10_Frames.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- The Fourier coefficient `∫_{-π}^{π} g(x) e^{-iλx} dx` of `IsFourierFrame`. -/
def fourierCoeff (g : ℝ → ℂ) (l : ℝ) : ℂ :=
  ∫ x in (-Real.pi)..Real.pi, g x * Complex.exp (-(I * (l : ℂ) * x))

/-- `fourierCoeff g l = pwFT (reflect g) l`. -/
theorem fourierCoeff_eq_pwFT_reflect (g : ℝ → ℂ) (l : ℝ) :
    fourierCoeff g l = pwFT (reflect g) (l : ℂ) := by
  sorry

/-- The sum `∑_{λ ∈ Λ} |∫ g e^{-iλx}|²` of `IsFourierFrame` equals `sampleSum Λ (pwFT (reflect g))`. -/
theorem tsum_fourierCoeff_eq_sampleSum (Λ : Set ℝ) (g : ℝ → ℂ) :
    ∑' l : Λ, ‖∫ x in (-Real.pi)..Real.pi, g x * Complex.exp (-(I * ((l : ℝ) : ℂ) * x))‖ₑ ^ 2 =
      sampleSum Λ (pwFT (reflect g)) := by
  sorry

/-- **The Paley–Wiener reduction** (p. 790): `{e^{iλx}}_{λ ∈ Λ}` is a Fourier frame if and only if
`Λ` is sampling for `PW`.  Frame bounds `(A, B)` correspond to sampling bounds `(A/2π, B/2π)`. -/
theorem isFourierFrame_iff_isSampling (hPW : PaleyWienerThm) (Λ : Set ℝ) :
    IsFourierFrame Λ ↔ IsSampling Λ := by
  sorry

end FF
