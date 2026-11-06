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
  rw [pwFT_reflect]
  rfl

/-- The sum `∑_{λ ∈ Λ} |∫ g e^{-iλx}|²` of `IsFourierFrame` equals `sampleSum Λ (pwFT (reflect g))`. -/
theorem tsum_fourierCoeff_eq_sampleSum (Λ : Set ℝ) (g : ℝ → ℂ) :
    ∑' l : Λ, ‖∫ x in (-Real.pi)..Real.pi, g x * Complex.exp (-(I * ((l : ℝ) : ℂ) * x))‖ₑ ^ 2 =
      sampleSum Λ (pwFT (reflect g)) := by
  unfold sampleSum
  refine tsum_congr fun l ↦ ?_
  have := fourierCoeff_eq_pwFT_reflect g (l : ℝ)
  unfold fourierCoeff at this
  rw [this]

/-- **The Paley–Wiener reduction** (p. 790): `{e^{iλx}}_{λ ∈ Λ}` is a Fourier frame if and only if
`Λ` is sampling for `PW`.  Frame bounds `(A, B)` correspond to sampling bounds `(A/2π, B/2π)`. -/
theorem isFourierFrame_iff_isSampling (hPW : PaleyWienerThm) (Λ : Set ℝ) :
    IsFourierFrame Λ ↔ IsSampling Λ := by
  set K : ℝ≥0 := (2 * Real.pi).toNNReal with hK
  have hK0 : 0 < K := by
    rw [hK]; exact Real.toNNReal_pos.2 (by positivity)
  have hKκ : ENNReal.ofReal (2 * Real.pi) = (K : ℝ≥0∞) := rfl
  constructor
  · rintro ⟨A, B, hA, h⟩
    refine ⟨A / K, B / K, div_pos hA hK0, fun f hf ↦ ?_⟩
    obtain ⟨h0, hh0, hfh, hn⟩ := exists_pwFT hPW hf
    have hg : MemL2pi (reflect h0) := memL2pi_reflect hh0
    have hfg : f = pwFT (reflect (reflect h0)) := by
      rw [hfh]; congr 1; funext t; simp [reflect]
    obtain ⟨h1, h2⟩ := h (reflect h0) hg
    have e : ∫⁻ x in Ioc (-Real.pi) Real.pi, ‖reflect h0 x‖ₑ ^ 2 = l2piSq h0 := l2piSq_reflect h0
    rw [tsum_fourierCoeff_eq_sampleSum, e, ← hfg] at h1 h2
    have hcancel : ((A / K : ℝ≥0) : ℝ≥0∞) * (K : ℝ≥0∞) = (A : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul, div_mul_cancel₀ _ hK0.ne']
    have hcancel' : ((B / K : ℝ≥0) : ℝ≥0∞) * (K : ℝ≥0∞) = (B : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul, div_mul_cancel₀ _ hK0.ne']
    rw [hn, hKκ]
    refine ⟨?_, ?_⟩
    · rw [← mul_assoc, hcancel]; exact h1
    · rw [← mul_assoc, hcancel']; exact h2
  · rintro ⟨A, B, hA, h⟩
    refine ⟨K * A, K * B, mul_pos hK0 hA, fun g hg ↦ ?_⟩
    obtain ⟨hmem, hnorm⟩ := memPW_pwFT hPW (memL2pi_reflect hg)
    rw [l2piSq_reflect] at hnorm
    obtain ⟨h1, h2⟩ := h _ hmem
    rw [tsum_fourierCoeff_eq_sampleSum]
    rw [hnorm, hKκ] at h1 h2
    refine ⟨?_, ?_⟩
    · calc ((K * A : ℝ≥0) : ℝ≥0∞) * ∫⁻ x in Ioc (-Real.pi) Real.pi, ‖g x‖ₑ ^ 2
          = (A : ℝ≥0∞) * ((K : ℝ≥0∞) * l2piSq g) := by
            rw [ENNReal.coe_mul]; unfold l2piSq; ring
        _ ≤ _ := h1
    · calc _ ≤ (B : ℝ≥0∞) * ((K : ℝ≥0∞) * l2piSq g) := h2
        _ = ((K * B : ℝ≥0) : ℝ≥0∞) * ∫⁻ x in Ioc (-Real.pi) Real.pi, ‖g x‖ₑ ^ 2 := by
            rw [ENNReal.coe_mul]; unfold l2piSq; ring

end FF
