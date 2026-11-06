import FourierFrames.Defs

/-!
# P1 — Paley–Wiener, part (1): the transform of an `L²(-π, π)` function

See `blueprint/P1_PaleyWiener.md`, §1.  For `g ∈ L²(-π, π)` the function
`f(z) = ∫_{-π}^{π} g(t) e^{izt} dt` is entire, of exponential type `≤ π`, square integrable on `ℝ`,
and `∫_ℝ |f|² = 2π ∫ |g|²`.  The norm identity is proved by Parseval for Fourier series on
`[-π, π]` applied to `g(t) e^{ixt}` for *every* `x`, followed by integration of
`∑_k |f(x + k)|²` over `x ∈ [0, 1)` (no Fourier transform on `ℝ` is needed).
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF.PW1

/-- `g ∈ L²(-π, π)`. -/
abbrev L2pi (g : ℝ → ℂ) : Prop :=
  MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))

/-- The transform `z ↦ ∫_{-π}^{π} g(t) e^{izt} dt`. -/
def ft (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)

/-! ### 1.1 Entire, exponential type -/

theorem L2pi.integrable {g : ℝ → ℂ} (hg : L2pi g) :
    IntegrableOn g (Ioc (-Real.pi) Real.pi) := by
  sorry

theorem differentiable_ft {g : ℝ → ℂ} (hg : L2pi g) : Differentiable ℂ (ft g) := by
  sorry

theorem norm_ft_le {g : ℝ → ℂ} (hg : L2pi g) (z : ℂ) :
    ‖ft g z‖ ≤ (∫ t in Ioc (-Real.pi) Real.pi, ‖g t‖) * Real.exp (Real.pi * ‖z‖) := by
  sorry

theorem isExpTypeLE_ft {g : ℝ → ℂ} (hg : L2pi g) : IsExpTypeLE Real.pi (ft g) := by
  sorry

/-! ### 1.2 The norm identity via Parseval on `[-π, π]` -/

/-- Multiplying by `e^{ixt}` (`x` real) preserves `L²(-π, π)`. -/
theorem L2pi.mul_cexp {g : ℝ → ℂ} (hg : L2pi g) (x : ℝ) :
    L2pi (fun t ↦ g t * Complex.exp (I * x * t)) := by
  sorry

/-- `f(x + k) = ∫ (g e^{ix·}) e^{ik·}`. -/
theorem ft_add_intCast {g : ℝ → ℂ} (x : ℝ) (k : ℤ) :
    ft g ((x : ℂ) + k) = ft (fun t ↦ g t * Complex.exp (I * x * t)) k := by
  sorry

/-- The Fourier coefficient of `g` on `[-π, π]` (period `2π`) is `(2π)⁻¹ ft g (-n)`. -/
theorem ft_intCast_eq_fourierCoeffOn {g : ℝ → ℂ} (n : ℤ) :
    ft g (n : ℂ) =
      (2 * Real.pi : ℂ) * fourierCoeffOn (by linarith [Real.pi_pos] : -Real.pi < Real.pi) g (-n) := by
  sorry

/-- Parseval for the samples `f(x + k)`, `k ∈ ℤ`, for every real `x`. -/
theorem hasSum_sq_ft_add_intCast {g : ℝ → ℂ} (hg : L2pi g) (x : ℝ) :
    HasSum (fun k : ℤ ↦ ‖ft g ((x : ℂ) + k)‖ ^ 2)
      (2 * Real.pi * ∫ t in (-Real.pi)..Real.pi, ‖g t‖ ^ 2) := by
  sorry

/-- The same in `ℝ≥0∞`. -/
theorem tsum_enorm_sq_ft_add_intCast {g : ℝ → ℂ} (hg : L2pi g) (x : ℝ) :
    ∑' k : ℤ, ‖ft g ((x : ℂ) + k)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2 := by
  sorry

/-- Unit-interval decomposition of `∫_ℝ |F|²` for measurable `F`. -/
theorem lintegral_enorm_sq_eq_lintegral_tsum {F : ℝ → ℂ} (hF : Measurable F) :
    ∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 = ∫⁻ x in Ico (0 : ℝ) 1, ∑' k : ℤ, ‖F (x + k)‖ₑ ^ 2 := by
  sorry

theorem pwNormSq_ft {g : ℝ → ℂ} (hg : L2pi g) :
    ∫⁻ x : ℝ, ‖ft g x‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2 := by
  sorry

theorem memLp_ft_real {g : ℝ → ℂ} (hg : L2pi g) : MemLp (fun x : ℝ ↦ ft g x) 2 := by
  sorry

/-- **Paley–Wiener, part (1)**, in the shape of `FF.PaleyWienerThm`. -/
theorem paleyWiener_part1 : ∀ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) →
      MemPW (fun z ↦ ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)) ∧
      pwNormSq (fun z ↦ ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)) =
        ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2 := by
  sorry

end FF.PW1
