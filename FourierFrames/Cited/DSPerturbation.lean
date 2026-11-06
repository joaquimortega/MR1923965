import FourierFrames.PW.PlancherelPolya

/-!
# P2a — Duffin–Schaeffer perturbation lemma (`DSPerturbation`)

See `blueprint/P2_DS_JN.md`, Part A.  Route: Bernstein in `L²` (`‖f'‖ ≤ π ‖f‖`, from
`f' = pwFT (i t g)`) + Cauchy–Schwarz on `f(γ+δ) - f(γ) = ∫ f'` + finite overlap of the intervals
`[γ-L, γ+L]` for a separated `Γ`.  No Taylor series, no higher derivatives.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Bernstein's inequality in `L²` -/

/-- `t ↦ i t g(t)` stays in `L²(-π, π)` and `‖i t g‖² ≤ π² ‖g‖²`. -/
theorem memL2pi_mul_t {g : ℝ → ℂ} (hg : MemL2pi g) :
    MemL2pi (fun t ↦ I * (t : ℂ) * g t) ∧
      l2piSq (fun t ↦ I * (t : ℂ) * g t) ≤ ENNReal.ofReal (Real.pi ^ 2) * l2piSq g := by
  sorry

/-- Differentiation under the integral sign: `(pwFT g)' = pwFT (i t g)` on all of `ℂ`. -/
theorem hasDerivAt_pwFT {g : ℝ → ℂ} (hg : MemL2pi g) (z : ℂ) :
    HasDerivAt (pwFT g) (pwFT (fun t ↦ I * (t : ℂ) * g t) z) z := by
  sorry

/-- **Bernstein's inequality in `L²`**: `f ∈ PW ⇒ f' ∈ PW` and `‖f'‖² ≤ π² ‖f‖²`. -/
theorem pw_bernstein (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) :
    MemPW (deriv f) ∧ pwNormSq (deriv f) ≤ ENNReal.ofReal (Real.pi ^ 2) * pwNormSq f := by
  sorry

/-! ## Increments of `f ∈ PW` -/

/-- `|f(γ+δ) - f(γ)|² ≤ |δ| ∫_{γ-|δ|}^{γ+|δ|} |f'|²` (FTC + Cauchy–Schwarz). -/
theorem enorm_sq_sub_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (γ δ : ℝ) :
    ‖f ((γ + δ : ℝ) : ℂ) - f (γ : ℂ)‖ₑ ^ 2 ≤
      ENNReal.ofReal |δ| * ∫⁻ x in Icc (γ - |δ|) (γ + |δ|), ‖deriv f (x : ℂ)‖ₑ ^ 2 := by
  sorry

/-- A `d`-separated set has at most `2L/d + 1` points in any interval of length `2L`. -/
theorem IsSepBy.ncard_Icc_le {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ) (x L : ℝ)
    (hL : 0 ≤ L) : ((Γ ∩ Icc (x - L) (x + L)).ncard : ℝ) ≤ 2 * L / d + 1 := by
  sorry

/-- Finite overlap: `∑_{γ ∈ Γ} ∫_{γ-L}^{γ+L} φ ≤ (2L/d + 1) ∫ φ` for `φ ≥ 0` measurable. -/
theorem tsum_lintegral_Icc_le {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ) {L : ℝ}
    (hL : 0 ≤ L) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∑' γ : Γ, ∫⁻ x in Icc ((γ : ℝ) - L) ((γ : ℝ) + L), φ x ≤
      ENNReal.ofReal (2 * L / d + 1) * ∫⁻ x, φ x := by
  sorry

/-- The key estimate: `∑_γ |f(γ+δ_γ) - f(γ)|² ≤ π² L (2L/d + 1) ‖f‖²` when `|δ_γ| ≤ L`. -/
theorem tsum_sub_le (hPW : PaleyWienerThm) {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ)
    {L : ℝ} (hL : 0 ≤ L) {δ : ℝ → ℝ} (hδ : ∀ x ∈ Γ, |δ x| ≤ L) {f : ℂ → ℂ} (hf : MemPW f) :
    ∑' γ : Γ, ‖f (((γ : ℝ) + δ γ : ℝ) : ℂ) - f ((γ : ℝ) : ℂ)‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.pi ^ 2 * L * (2 * L / d + 1)) * pwNormSq f := by
  sorry

/-! ## Sampling sums over an injective image -/

theorem sampleSum_image {φ : ℝ → ℝ} {Γ : Set ℝ} (hφ : InjOn φ Γ) (f : ℂ → ℂ) :
    sampleSum (φ '' Γ) f = ∑' γ : Γ, ‖f ((φ γ : ℝ) : ℂ)‖ₑ ^ 2 := by
  sorry

/-- `(a+b)² ≤ 2a² + 2b²` in `ℝ≥0∞`, summed. -/
theorem tsum_enorm_sq_add_le {ι : Type*} (a b : ι → ℂ) :
    ∑' i, ‖a i + b i‖ₑ ^ 2 ≤ 2 * ∑' i, ‖a i‖ₑ ^ 2 + 2 * ∑' i, ‖b i‖ₑ ^ 2 := by
  sorry

/-! ## Main result -/

theorem dsPerturbation_of_paleyWiener (hPW : PaleyWienerThm) : DSPerturbation := by
  sorry

end FF
