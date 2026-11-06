import FourierFrames.HB.Basic

/-!
# M02 — Phase functions of `E ∈ \overline{HB}`

See `blueprint/M02_HB.md`, §4–§5.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Existence, uniqueness and derivative of phase functions -/

theorem continuous_phaseDeriv {E : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0) :
    Continuous (phaseDeriv E) := by
  sorry

/-- `phaseDeriv` is multiplicative-to-additive: `φ_{EF}' = φ_E' + φ_F'`. -/
theorem phaseDeriv_mul {E F : ℂ → ℂ} (hE : Differentiable ℂ E) (hF : Differentiable ℂ F)
    {x : ℝ} (hEx : E x ≠ 0) (hFx : F x ≠ 0) :
    phaseDeriv (fun z ↦ E z * F z) x = phaseDeriv E x + phaseDeriv F x := by
  sorry

/-- **Existence of a phase function** with `φ' = phaseDeriv E`. -/
theorem exists_isPhaseFunction {E : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0) :
    ∃ φ : ℝ → ℝ, IsPhaseFunction E φ ∧ ∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x := by
  sorry

/-- **Uniqueness up to `2π ℤ`.** -/
theorem IsPhaseFunction.exists_int_eq_add {E : ℂ → ℂ} (h0 : ∀ x : ℝ, E x ≠ 0) {φ ψ : ℝ → ℝ}
    (hφ : IsPhaseFunction E φ) (hψ : IsPhaseFunction E ψ) :
    ∃ k : ℤ, ∀ x : ℝ, ψ x = φ x + 2 * Real.pi * k := by
  sorry

/-- Every phase function of `E` (without real zeros) is differentiable with derivative
`phaseDeriv E`. -/
theorem IsPhaseFunction.hasDerivAt {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (h0 : ∀ x : ℝ, E x ≠ 0) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) (x : ℝ) :
    HasDerivAt φ (phaseDeriv E x) x := by
  sorry

/-- Phase functions add under products. -/
theorem IsPhaseFunction.mul {E F : ℂ → ℂ} {φ ψ : ℝ → ℝ} (hφ : IsPhaseFunction E φ)
    (hψ : IsPhaseFunction F ψ) :
    IsPhaseFunction (fun z ↦ E z * F z) (fun x ↦ φ x + ψ x) := by
  sorry

/-- `Re E(x) = |E(x)| cos φ(x)` on the real axis. -/
theorem IsPhaseFunction.re_eq {E : ℂ → ℂ} {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) (x : ℝ) :
    (E x).re = ‖E x‖ * Real.cos (φ x) := by
  sorry

/-! ## Sign of the phase derivative -/

/-- **`φ_F' ≥ 0`** for `F ∈ \overline{HB}` (the non-strict class) at real points where `F ≠ 0`. -/
theorem IsHB.phaseDeriv_nonneg {F : ℂ → ℂ} (hF : IsHB F) {x : ℝ} (hx : F x ≠ 0) :
    0 ≤ phaseDeriv F x := by
  sorry

/-- **`φ_E' > 0`** if `E ∈ \overline{HB}` is strict at a single point of `Im z > 0`
(i.e. `E^*/E` is not constant). -/
theorem IsHB.phaseDeriv_pos_of_exists_lt {E : ℂ → ℂ} (hE : IsHB E) {x : ℝ} (hx : E x ≠ 0)
    (h : ∃ z : ℂ, 0 < z.im ∧ ‖E (conj z)‖ < ‖E z‖) : 0 < phaseDeriv E x := by
  sorry

theorem IsStrictHB.phaseDeriv_pos {E : ℂ → ℂ} (hE : IsStrictHB E) {x : ℝ} (hx : E x ≠ 0) :
    0 < phaseDeriv E x := by
  sorry

/-- A phase function of a strict `E` without real zeros is strictly increasing. -/
theorem IsPhaseFunction.strictMono_of_isStrictHB {E : ℂ → ℂ} (hE : IsStrictHB E)
    (h0 : ∀ x : ℝ, E x ≠ 0) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) : StrictMono φ := by
  sorry

/-! ## Zeros of `EF + E^*F^*` -/

/-- **Zero set of `EF + E^*F^*`** (p. 796): for `E` strict and `F ∈ \overline{HB}`, both without
real zeros, the zeros of `EF + E^*F^*` are exactly the real points where the total phase
`φ_E + φ_F` is `≡ π/2 (mod π)`. -/
theorem zero_set_eq_phaseLevel {E F : ℂ → ℂ} (hE : IsStrictHB E) (hF : IsHB F)
    (hE0 : ∀ x : ℝ, E x ≠ 0) (hF0 : ∀ x : ℝ, F x ≠ 0) {φE φF : ℝ → ℝ}
    (hφE : IsPhaseFunction E φE) (hφF : IsPhaseFunction F φF) (z : ℂ) :
    E z * F z + fstar E z * fstar F z = 0 ↔
      z ∈ Complex.ofReal '' phaseLevel (fun t ↦ φE t + φF t) (Real.pi / 2) := by
  sorry

/-- Added at assembly (moved from `Corollary1.lean` / `Corollary2.lean`): a phase function of
`e^{iθ} E` is `φ_E - θ`. -/
theorem IsPhaseFunction.rotate {E : ℂ → ℂ} {φ : ℝ → ℝ} (h : IsPhaseFunction E φ) (θ : ℝ) :
    IsPhaseFunction (fun z ↦ Complex.exp (I * θ) * E z) (fun x ↦ φ x - θ) := by
  sorry

end FF
