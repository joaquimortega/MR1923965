import FourierFrames.Cited.PaleyWiener.L2Fourier

/-!
# P1 — Gaussian regularisation and the spectrum of an entire function of exponential type

Key estimate (blueprint §3).  Let `f` be entire, `f|ℝ ∈ L²`, and
`|f(x + iy)| ≤ C e^{a|x| + b|y|}`.  Then the `L²` Fourier transform of `f|ℝ` vanishes a.e. on
`{w : 2π|w| > a + b}`.

Proof idea: `f_η(x) = f(x) e^{-ηx²} ∈ L¹ ∩ L²`; shift the contour of
`∫ f_η(x) e^{-iξx} dx` to `Im z = ∓Y`, `Y = (|ξ| - b)/(2η)`, giving
`|𝓕 f_η| ≲ η^{-1/2} exp((a² - (|ξ|-b)²)/(4η)) → 0`; and `𝓕 f_η → 𝓕 f` in `L²` (Plancherel +
dominated convergence), so a subsequence converges a.e.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform

noncomputable section

namespace FF.PW1

/-! ### 3.1 Contour shift for entire functions with Gaussian decay -/

theorem integral_line_shift {H : ℂ → ℂ} (hH : Differentiable ℂ H) (y : ℝ)
    (hint0 : Integrable (fun x : ℝ ↦ H x))
    (hinty : Integrable (fun x : ℝ ↦ H (x + y * I)))
    (hR : Tendsto (fun R : ℝ ↦ ∫ s in (0 : ℝ)..y, ‖H (R + s * I)‖) atTop (𝓝 0))
    (hR' : Tendsto (fun R : ℝ ↦ ∫ s in (0 : ℝ)..y, ‖H (-R + s * I)‖) atTop (𝓝 0)) :
    ∫ x : ℝ, H x = ∫ x : ℝ, H (x + y * I) := by
  sorry

/-! ### 3.2 Gaussian integrals -/

theorem integral_exp_abs_sub_sq_le {a : ℝ} (ha : 0 ≤ a) {η : ℝ} (hη : 0 < η) :
    ∫ x : ℝ, Real.exp (a * |x| - η * x ^ 2) ≤
      2 * Real.sqrt (Real.pi / η) * Real.exp (a ^ 2 / (4 * η)) := by
  sorry

theorem integrable_exp_abs_sub_sq {a : ℝ} {η : ℝ} (hη : 0 < η) :
    Integrable (fun x : ℝ ↦ Real.exp (a * |x| - η * x ^ 2)) := by
  sorry

/-! ### 3.3 The pointwise bound on `∫ f(x) e^{-ηx²} e^{-iξx} dx` -/

theorem norm_integral_gauss_mul_le {f : ℂ → ℂ} (hd : Differentiable ℂ f) {C a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (a * |z.re| + b * |z.im|))
    {η : ℝ} (hη : 0 < η) {ξ : ℝ} (hξ : b ≤ |ξ|) :
    ‖∫ x : ℝ, f x * Complex.exp (-(η : ℂ) * (x : ℂ) ^ 2) * Complex.exp (-I * ξ * x)‖ ≤
      2 * |C| * Real.sqrt (Real.pi / η) * Real.exp ((a ^ 2 - (|ξ| - b) ^ 2) / (4 * η)) := by
  sorry

theorem tendsto_gauss_bound {a κ : ℝ} (ha : 0 ≤ a) (hκ : a < κ) (C : ℝ) :
    Tendsto (fun η : ℝ ↦
      2 * |C| * Real.sqrt (Real.pi / η) * Real.exp ((a ^ 2 - κ ^ 2) / (4 * η)))
      (𝓝[>] 0) (𝓝 0) := by
  sorry

/-! ### 3.4 `f e^{-η·²} → f` in `L²` and the a.e. limit -/

theorem memLp_mul_gauss {f : ℝ → ℂ} (hf : MemLp f 2) {η : ℝ} (hη : 0 < η) :
    MemLp (fun x : ℝ ↦ f x * ((Real.exp (-η * x ^ 2) : ℝ) : ℂ)) 2 ∧
    Integrable (fun x : ℝ ↦ f x * ((Real.exp (-η * x ^ 2) : ℝ) : ℂ)) := by
  sorry

theorem tendsto_eLpNorm_mul_gauss {f : ℝ → ℂ} (hf : MemLp f 2) :
    Tendsto (fun n : ℕ ↦ eLpNorm (fun x : ℝ ↦ f x * ((Real.exp (-(1 / ((n : ℝ) + 1)) * x ^ 2) : ℝ) : ℂ)
      - f x) 2 volume) atTop (𝓝 0) := by
  sorry

/-- **Spectrum lemma.** -/
theorem spectrum_vanish {f : ℂ → ℂ} (hd : Differentiable ℂ f) (hL2 : MemLp (fun x : ℝ ↦ f x) 2)
    {C a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (a * |z.re| + b * |z.im|)) :
    ∀ᵐ w : ℝ, a + b < 2 * Real.pi * |w| →
      (F2 (hL2.toLp (fun x : ℝ ↦ f x)) : ℝ → ℂ) w = 0 := by
  sorry

end FF.PW1
