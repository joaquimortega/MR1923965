import FourierFrames.Cited.PaleyWiener.Part1
import FourierFrames.Cited.PaleyWiener.Spectrum
import OrtegaCerdaSeip.Bernstein.PhragmenLindelof

/-!
# P1 — Paley–Wiener, part (2): every `f ∈ PW` is a transform of an `L²(-π, π)` function

See `blueprint/P1_PaleyWiener.md`, §4.  Chain:
crude spectrum bound (`spectrum_vanish`, `a = b = π + 1`) ⇒ `f` bounded on `ℝ` (inversion on a
compact spectrum) ⇒ Phragmén–Lindelöf `|f(z)| ≤ M e^{π|Im z|}` (`OCS.norm_le_mul_exp_abs_im`)
⇒ sharp spectrum bound (`spectrum_vanish`, `a = 0`, `b = π`) ⇒ inversion ⇒ identity theorem.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform

noncomputable section

namespace FF.PW1

/-- The `L²` Fourier transform of `f|ℝ` (a chosen representative). -/
def specOf {f : ℂ → ℂ} (hL2 : MemLp (fun x : ℝ ↦ f x) 2) : ℝ → ℂ :=
  (F2 (hL2.toLp (fun x : ℝ ↦ f x)) : ℝ → ℂ)

theorem memLp_specOf {f : ℂ → ℂ} (hL2 : MemLp (fun x : ℝ ↦ f x) 2) :
    MemLp (specOf hL2) 2 := by
  sorry

/-- Inversion for a spectrum contained in `[-ρ, ρ]`: for *every* real `x`
(a.e. equality of two continuous functions). -/
theorem eq_integral_of_spectrum {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hL2 : MemLp (fun x : ℝ ↦ f x) 2) {ρ : ℝ} (hρ : 0 < ρ)
    (hsp : ∀ᵐ w : ℝ, ρ < |w| → specOf hL2 w = 0) (x : ℝ) :
    f x = ∫ w in (-ρ)..ρ, specOf hL2 w * Complex.exp (2 * Real.pi * I * w * x) := by
  sorry

theorem bounded_of_spectrum {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hL2 : MemLp (fun x : ℝ ↦ f x) 2) {ρ : ℝ} (hρ : 0 < ρ)
    (hsp : ∀ᵐ w : ℝ, ρ < |w| → specOf hL2 w = 0) :
    ∃ M : ℝ, ∀ x : ℝ, ‖f x‖ ≤ M := by
  sorry

/-- Step A: `f ∈ PW` is bounded on `ℝ`. -/
theorem pw_bounded {f : ℂ → ℂ} (hd : Differentiable ℂ f) (he : IsExpTypeLE Real.pi f)
    (hL2 : MemLp (fun x : ℝ ↦ f x) 2) : ∃ M : ℝ, ∀ x : ℝ, ‖f x‖ ≤ M := by
  sorry

/-- Step B: sharp spectrum, using Phragmén–Lindelöf. -/
theorem pw_spectrum {f : ℂ → ℂ} (hd : Differentiable ℂ f) (he : IsExpTypeLE Real.pi f)
    (hL2 : MemLp (fun x : ℝ ↦ f x) 2) :
    ∀ᵐ w : ℝ, (1 / 2 : ℝ) < |w| → specOf hL2 w = 0 := by
  sorry

/-- Step C: the representation on `ℝ`, with `g(t) = Φ(t/2π)/2π`. -/
theorem pw_representation_real {f : ℂ → ℂ} (hd : Differentiable ℂ f) (he : IsExpTypeLE Real.pi f)
    (hL2 : MemLp (fun x : ℝ ↦ f x) 2) :
    ∃ g : ℝ → ℂ, L2pi g ∧ ∀ x : ℝ, f x = ft g x := by
  sorry

/-- Identity theorem: entire functions agreeing on `ℝ` agree on `ℂ`. -/
theorem eq_of_eq_on_real {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h : ∀ x : ℝ, F x = G x) : ∀ z : ℂ, F z = G z := by
  sorry

/-- **Paley–Wiener, part (2)**, in the shape of `FF.PaleyWienerThm`. -/
theorem paleyWiener_part2 : ∀ f : ℂ → ℂ, MemPW f →
    ∃ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) ∧
      ∀ z : ℂ, f z = ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t) := by
  sorry

end FF.PW1
