import FourierFrames.Defs

/-!
# P1 — the `L²` Fourier transform agrees with the integral on `L¹ ∩ L²`

Mathlib has the `L²` Fourier transform `Lp.fourierTransformₗᵢ` (Plancherel) and the `L¹` integral
`𝓕 φ`, but (as of Mathlib v4.35) no lemma identifying them on `L¹ ∩ L²`.  We prove it by testing
against Schwartz functions, using only `inner_fourier_eq`, `SchwartzMap.toLp_fourier_eq` and the
Fubini identity `VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip`.

See `blueprint/P1_PaleyWiener.md`, §2.
-/

open MeasureTheory Set Complex Filter Topology SchwartzMap
open scoped ENNReal NNReal ComplexConjugate FourierTransform

noncomputable section

namespace FF.PW1

/-- The `L²` Fourier transform on `ℝ`, as a linear isometry equivalence of `Lp ℂ 2`. -/
abbrev F2 : Lp (α := ℝ) ℂ 2 ≃ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 := Lp.fourierTransformₗᵢ ℝ ℂ

/-- **The `L²` transform agrees with the integral on `L¹ ∩ L²`.** -/
theorem F2_toLp_ae_eq {φ : ℝ → ℂ} (h1 : Integrable φ) (h2 : MemLp φ 2) :
    (F2 (h2.toLp φ) : ℝ → ℂ) =ᵐ[volume] 𝓕 φ := by
  sorry

/-- On `L²`, the inverse transform is the transform followed by reflection. -/
theorem F2_symm_ae_eq (Φ : Lp (α := ℝ) ℂ 2) :
    ((F2.symm Φ : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) =ᵐ[volume] fun x ↦ (F2 Φ : ℝ → ℂ) (-x) := by
  sorry

/-- Inverse transform on `L¹ ∩ L²`. -/
theorem F2_symm_toLp_ae_eq {φ : ℝ → ℂ} (h1 : Integrable φ) (h2 : MemLp φ 2) :
    ((F2.symm (h2.toLp φ) : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ φ := by
  sorry

end FF.PW1
