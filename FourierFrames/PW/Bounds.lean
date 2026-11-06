import FourierFrames.PW.Basic
import OrtegaCerdaSeip.Bernstein.Sinc

/-!
# M01 — Paley–Wiener space toolkit: pointwise and line bounds

See `blueprint/M01_PW.md`, §2.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- Imaginary translate of a transform: `pwFT g (z + i y) = pwFT (g e^{-y·}) z`. -/
theorem pwFT_add_mul_I (g : ℝ → ℂ) (y : ℝ) (z : ℂ) :
    pwFT g (z + y * I) = pwFT (fun t ↦ g t * ((Real.exp (-(y * t)) : ℝ) : ℂ)) z := by
  sorry

/-- `g ∈ L²(-π,π)` implies `g e^{-y·} ∈ L²(-π,π)` with `‖g e^{-y·}‖² ≤ e^{2π|y|} ‖g‖²`. -/
theorem memL2pi_mul_exp {g : ℝ → ℂ} (hg : MemL2pi g) (y : ℝ) :
    MemL2pi (fun t ↦ g t * ((Real.exp (-(y * t)) : ℝ) : ℂ)) ∧
      l2piSq (fun t ↦ g t * ((Real.exp (-(y * t)) : ℝ) : ℂ)) ≤
        ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * l2piSq g := by
  sorry

/-- Imaginary translates of `f ∈ PW` are in `PW` (`z ↦ f(z + i y)` corresponds to `g e^{-y t}`),
and `‖f(· + iy)‖² = 2π ∫ |g|² e^{-2yt}`. -/
theorem pw_translate_I (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (y : ℝ) :
    MemPW (fun z ↦ f (z + y * I)) := by
  sorry

/-- The exact norm of an imaginary translate: if `f = pwFT g` then
`‖f(· + iy)‖² = 2π ∫ e^{-2yt} |g(t)|² dt`. -/
theorem pwNormSq_translate_I (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (y : ℝ) :
    ∃ g : ℝ → ℂ, MemL2pi g ∧ f = pwFT g ∧
      pwNormSq f = ENNReal.ofReal (2 * Real.pi) * l2piSq g ∧
      pwNormSq (fun z ↦ f (z + y * I)) = ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ t in Set.Ioc (-Real.pi) Real.pi, ENNReal.ofReal (Real.exp (-(2 * y * t))) * ‖g t‖ₑ ^ 2 := by
  sorry

/-- **Pointwise bound** `|f(z)|² ≤ e^{2π|Im z|} ‖f‖²` (constant exactly `1`). -/
theorem pw_norm_sq_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (z : ℂ) :
    ‖f z‖ ^ 2 ≤ Real.exp (2 * Real.pi * |z.im|) * (pwNormSq f).toReal := by
  sorry

/-- **Line integrals** `∫ |f(x + iy)|² dx ≤ e^{2π|y|} ‖f‖²`. -/
theorem pw_line_integral_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (y : ℝ) :
    ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * pwNormSq f := by
  sorry

/-- `f(z) e^{iπz} ∈ H²(ℂ₊)`. -/
theorem MemPW.isH2Upper_mul_exp (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) :
    IsH2Upper (fun z ↦ f z * Complex.exp (I * Real.pi * z)) := by
  sorry

/-- The `H²` norm bound, with constant `1`: for `y > 0`,
`∫ |f(x+iy) e^{iπ(x+iy)}|² dx ≤ ‖f‖²_{PW}`. -/
theorem MemPW.lintegral_mul_exp_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) {y : ℝ}
    (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I) * Complex.exp (I * Real.pi * ((x : ℂ) + (y : ℂ) * I))‖ₑ ^ 2
      ≤ pwNormSq f := by
  sorry

/-- **Derivative bound on `ℝ`**: `|f'(x)|² ≤ π² e² ‖f‖²` (Cauchy estimate on the circle of radius
`1/π`; the constant is absolute). -/
theorem pw_deriv_bound (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (x : ℝ) :
    ‖deriv f x‖ ^ 2 ≤ (Real.pi * Real.exp 1) ^ 2 * (pwNormSq f).toReal := by
  sorry

/-! ## A fixed function with `g(0) = 1` -/

/-- `((sin (π z / 2)) / (π z / 2))²`. -/
def pwBump (z : ℂ) : ℂ :=
  OCS.csinc (((Real.pi / 2 : ℝ) : ℂ) * z) ^ 2

theorem pwBump_zero : pwBump 0 = 1 := by
  sorry

theorem memPW_pwBump : MemPW pwBump := by
  sorry

theorem pwNormSq_pwBump_pos : 0 < pwNormSq pwBump := by
  sorry

theorem exists_memPW_eval_ne_zero : ∃ g : ℂ → ℂ, MemPW g ∧ g 0 = 1 := by
  exact ⟨pwBump, memPW_pwBump, pwBump_zero⟩

/-- A uniform lower bound for point evaluations: for every real `x` there is `f ∈ PW`, namely a
translate of `pwBump`, with `0 < ‖f‖² < ∞` and `c ‖f‖² ≤ |f(x)|²`; the constant is
`c = ‖pwBump‖⁻²` (absolute), `‖pwBump‖² = pwNormSq pwBump`. -/
theorem pw_eval_lower : ∃ c : ℝ≥0, 0 < c ∧ ∀ x : ℝ, ∃ f : ℂ → ℂ, MemPW f ∧
    (c : ℝ≥0∞) * pwNormSq f ≤ ‖f (x : ℂ)‖ₑ ^ 2 ∧ pwNormSq f ≠ 0 ∧ pwNormSq f ≠ ⊤ := by
  sorry

end FF
