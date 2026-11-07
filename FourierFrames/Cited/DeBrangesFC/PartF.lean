import FourierFrames.Cited.DeBrangesFC

/-!
# de Branges' Theorem F (deferred scaffold)

Part F of `blueprint/P4_DeBrangesFC.md`: the statements of the route to `TheoremF` (de Branges
1960 / [dB68, Theorem 32]), all `sorry`.  It is **deferred** (estimated 5–8k lines; see
`blueprint/PHASE2.md`), and `division_lemma` is **false as stated** (reviews/R10_TheoremC.md, with a
Lean disproof); its hypotheses must be strengthened as described there before any attempt.
This file is not in the default target `FourierFrames`; it is built by `FourierFramesScaffold`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace FF

section PartF

/-- `μ` embeds `H(E)` isometrically in `L²(μ/|E|²)`. -/
def IsIsometricMeasure (μ : Measure ℝ) (E : ℂ → ℂ) : Prop :=
  ∀ f : ℂ → ℂ, MemHE E f → ∫⁻ t, ‖f t / E t‖ₑ ^ 2 ∂μ = heNormSq E f

/-- The Herglotz transform of `μ`: `g(z) = (−i/π) ∫ (1/(t − z) − t/(1+t²)) dμ(t) + i c`;
`Re g` is the Poisson integral of `μ`. -/
def herglotzG (μ : Measure ℝ) (c : ℝ) (z : ℂ) : ℂ :=
  -(I / Real.pi) * ∫ t : ℝ, (((t : ℂ) - z)⁻¹ - ((t / (1 + t ^ 2) : ℝ) : ℂ)) ∂μ + I * c

variable {μ : Measure ℝ} {E : ℂ → ℂ}

/-- F.1 `∫ dμ/(1+t²) < ∞` (test the isometry on `K(i,·)`; uses `|E(i)| > |E^*(i)|`). -/
theorem isometric_moment (hD : TheoremD) (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0)
    (hμ : IsIsometricMeasure μ E) : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞ := by
  sorry

/-- F.2 Herglotz representation, constructive: `g` is holomorphic with `Re g = P[μ]`. -/
theorem herglotzG_spec (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞) (c : ℝ) :
    DifferentiableOn ℂ (herglotzG μ c) UHP ∧
      ∀ z ∈ UHP, poissonInt μ z ≠ ∞ ∧ (herglotzG μ c z).re = (poissonInt μ z).toReal := by
  sorry

/-- F.3 Pairing of two kernels at zeros of `E^*` in the upper half-plane (formula (67)):
`∫ dμ / ((t - v̄)(t - w)) = 2πi/(w - v̄)`. -/
theorem cauchy_pairing_zero (hD : TheoremD) (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0)
    (hμ : IsIsometricMeasure μ E) {w v : ℂ} (hw : 0 < w.im) (hv : 0 < v.im)
    (hw0 : fstar E w = 0) (hv0 : fstar E v = 0) :
    ∫ t : ℝ, (((t : ℂ) - conj v)⁻¹ * ((t : ℂ) - w)⁻¹) ∂μ = 2 * Real.pi * I / (w - conj v) := by
  sorry

/-- F.4 General pairing of the kernel at a zero `w₀` of `E^*` with `K(z,·)`, `z ∈ ℂ₊`:
`∫ dμ/((t - w̄₀)(t - z))` equals `2πi/(z - w̄₀)` up to an error `≤ ‖Θ(z)‖ · C(w₀)/√Im z`.
(R7-11: only where `‖Θ(z)‖ ≤ 1/2`, which F.5 needs for `P[μ](z) ≤ 3`; F.9 uses it only as
`Im z → ∞`, where `‖Θ(z)‖ ≤ e^{-a Im z}`.) -/
theorem cauchy_pairing_general (hD : TheoremD) (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0)
    (hμ : IsIsometricMeasure μ E) {w₀ : ℂ} (hw₀ : 0 < w₀.im) (hz0 : fstar E w₀ = 0) :
    ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im → ‖thetaFn E z‖ ≤ 1 / 2 →
      ‖∫ t : ℝ, (((t : ℂ) - conj w₀)⁻¹ * ((t : ℂ) - z)⁻¹) ∂μ - 2 * Real.pi * I / (z - conj w₀)‖ ≤
        C * ‖thetaFn E z‖ / Real.sqrt z.im := by
  sorry

/-- F.5 Diagonal estimate (isometry on `K(z,·)`): `|P[μ](z) − 1| ≤ 4 |Θ(z)|` when `|Θ(z)| ≤ 1/2`. -/
theorem poisson_diag_estimate (hD : TheoremD) (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : 0 < z.im) (hθ : ‖thetaFn E z‖ ≤ 1 / 2) :
    |(poissonInt μ z).toReal - 1| ≤ 4 * ‖thetaFn E z‖ := by
  sorry

/-- F.6 (Cauchy–Riemann argument) If `g` is holomorphic on `ℂ₊` and `|Re g − 1| ≤ C e^{−a y}` on
`y ≥ 1`, then there is `c ∈ ℝ` with `|g − 1 − i c| ≤ C' e^{−a' y}` on `y ≥ 2`, for every `a' < a`
(local uniformity in `x` is not needed, uniformity is assumed). -/
theorem exists_imag_limit {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g UHP) {C a : ℝ} (ha : 0 < a)
    (h : ∀ z : ℂ, 1 ≤ z.im → |(g z).re - 1| ≤ C * Real.exp (-(a * z.im))) {a' : ℝ} (ha' : a' < a) :
    ∃ c C' : ℝ, ∀ z : ℂ, 2 ≤ z.im → ‖g z - 1 - I * c‖ ≤ C' * Real.exp (-(a' * z.im)) := by
  sorry

/-- F.7 Factorization of the meromorphic inner function `Θ = E^*/E` (`E` strict, no real zeros):
`Θ = e^{i(az+θ)} B` with `a ≥ 0` and `B` a Blaschke product, together with the Blaschke division
property: a bounded holomorphic `Ψ` vanishing (with multiplicity) where `Θ` does satisfies
`|Ψ| ≤ ‖Ψ‖_∞ |B|`. -/
theorem inner_factorization (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0) :
    ∃ (a θ : ℝ) (B : ℂ → ℂ), 0 ≤ a ∧ DifferentiableOn ℂ B UHP ∧ (∀ z ∈ UHP, ‖B z‖ ≤ 1) ∧
      (∀ z ∈ UHP, thetaFn E z = Complex.exp (I * (a * z + θ)) * B z) ∧
      ∀ (Ψ : ℂ → ℂ) (M : ℝ), DifferentiableOn ℂ Ψ UHP → (∀ z ∈ UHP, ‖Ψ z‖ ≤ M) →
        (∀ z ∈ UHP, thetaFn E z = 0 → analyticOrderAt (thetaFn E) z ≤ analyticOrderAt Ψ z) →
        ∀ z ∈ UHP, ‖Ψ z‖ ≤ M * ‖B z‖ := by
  sorry

/-- F.8 Division lemma: if `Ξ` is holomorphic, `|Ξ| ≤ 1` on `ℂ₊`, vanishes where `Θ` does (with
multiplicity) and decays like `e^{−a' y}` for all `a' < a` (`a` from F.7), then `|Ξ| ≤ |Θ|`. -/
theorem division_lemma (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0) {a θ : ℝ} {B : ℂ → ℂ}
    (hfac : ∀ z ∈ UHP, thetaFn E z = Complex.exp (I * (a * z + θ)) * B z) {Ξ : ℂ → ℂ}
    (hΞ : DifferentiableOn ℂ Ξ UHP) (h1 : ∀ z ∈ UHP, ‖Ξ z‖ ≤ 1)
    (hz : ∀ z ∈ UHP, thetaFn E z = 0 → analyticOrderAt (thetaFn E) z ≤ analyticOrderAt Ξ z)
    (hdec : ∀ a' : ℝ, a' < a → ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im → ‖Ξ z‖ ≤ C * Real.exp (-(a' * z.im))) :
    ∀ z ∈ UHP, ‖Ξ z‖ ≤ ‖thetaFn E z‖ := by
  -- FALSE: see reviews/R10_TheoremC.md (needs 0 ≤ a, ‖B‖ ≤ 1 on ℂ₊ and the Blaschke-division
  -- clause as hypotheses); counterexample E = exp(-iz/2), Θ = e^{iz}, a = θ = 0, B = Θ, Ξ ≡ 1/2.
  sorry

end PartF

/-- **Theorem F** (de Branges, Theorem 32; with `p = 0`). -/
theorem theoremF_holds : TheoremF := by
  sorry

end FF
