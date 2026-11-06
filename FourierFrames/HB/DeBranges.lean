import FourierFrames.HB.Phase
import FourierFrames.HB.H2

/-!
# M02 — de Branges spaces `H(E)`: basic facts

See `blueprint/M02_HB.md`, §6–§8.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Upstream interface (temporary, replaced by imports at assembly)

All of these are exported by M01 (`FourierFrames/PW/*.lean`, see `blueprint/M01_PW.md`); the
statements below copy the M01 scaffold at the time of writing. -/

theorem exists_memPW_eval_ne_zero : ∃ g : ℂ → ℂ, MemPW g ∧ g 0 = 1 := by
  sorry

theorem MemPW.comp_sub_ofReal {f : ℂ → ℂ} (hf : MemPW f) (a : ℝ) :
    MemPW (fun z ↦ f (z - a)) := by
  sorry

theorem pwNormSq_comp_sub_ofReal (f : ℂ → ℂ) (a : ℝ) :
    pwNormSq (fun z ↦ f (z - a)) = pwNormSq f := by
  sorry

theorem MemPW.fstar {f : ℂ → ℂ} (hf : MemPW f) : MemPW (FF.fstar f) := by
  sorry

theorem pwNormSq_ne_top {f : ℂ → ℂ} (hf : MemPW f) : pwNormSq f ≠ ⊤ := by
  sorry

theorem pw_eval_lower : ∃ c : ℝ≥0, 0 < c ∧ ∀ x : ℝ, ∃ f : ℂ → ℂ, MemPW f ∧
    (c : ℝ≥0∞) * pwNormSq f ≤ ‖f (x : ℂ)‖ₑ ^ 2 ∧ pwNormSq f ≠ 0 ∧ pwNormSq f ≠ ⊤ := by
  sorry

theorem pw_norm_sq_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (z : ℂ) :
    ‖f z‖ ^ 2 ≤ Real.exp (2 * Real.pi * |z.im|) * (pwNormSq f).toReal := by
  sorry

theorem pw_line_integral_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (y : ℝ) :
    ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * pwNormSq f := by
  sorry

/-! ## Multiplication by `F ∈ \overline{HB}` -/

/-- `F f ∈ H(E F)` for `f ∈ H(E)` and `F ∈ \overline{HB}`. -/
theorem MemHE.mul_isHB {E F f : ℂ → ℂ} (hF : IsHB F) (hf : MemHE E f) :
    MemHE (fun z ↦ E z * F z) (fun z ↦ F z * f z) := by
  sorry

/-- `‖F f‖_{EF} = ‖f‖_E`. -/
theorem heNormSq_mul {E F f : ℂ → ℂ} (hF : IsHB F) :
    heNormSq (fun z ↦ E z * F z) (fun z ↦ F z * f z) = heNormSq E f := by
  sorry

/-! ## The functions `S_α = e^{iα} E - e^{-iα} E^*` -/

/-- `S_α = e^{iα} E - e^{-iα} E^*` (the function of Theorem E). -/
def sAlpha (E : ℂ → ℂ) (α : ℝ) : ℂ → ℂ :=
  fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z

/-- At most one `α` (mod `π`) has `S_α ∈ H(E)`. -/
theorem memHE_sAlpha_unique {E : ℂ → ℂ} (hE : IsHB E) {α β : ℝ}
    (hα : MemHE E (sAlpha E α)) (hβ : MemHE E (sAlpha E β)) :
    ∃ k : ℤ, β - α = k * Real.pi := by
  sorry

/-! ## `H(E) = PW` forces `E` to be strict without real zeros -/

/-- If `H(E) = PW` (as sets), `E ∈ \overline{HB}` has no real zeros. -/
theorem HEEqPW.ne_zero_ofReal {E : ℂ → ℂ} (hE : IsHB E) (h : HEEqPW E) (x : ℝ) : E x ≠ 0 := by
  sorry

/-- If `H(E) = PW`, then `E ∈ \overline{HB}` is strict: `H(E) = {0}` when `E^* = cE`. -/
theorem HEEqPW.isStrictHB {E : ℂ → ℂ} (hE : IsHB E) (h : HEEqPW E) : IsStrictHB E := by
  sorry

/-! ## `φ_E' |E|² ≃ 1` when `H(E) = PW` -/

/-- Lower bound: `φ_E'(x) |E(x)|² ≥ c > 0` on `ℝ` when `H(E) = PW`
(`c = π / (C₁ ‖g‖²_{PW})`, `C₁` the upper norm-equivalence constant, `g(0) = 1`). -/
theorem HEEqPW.phaseDeriv_mul_sq_ge (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hHB : IsHB E) (h : HEEqPW E) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, c ≤ phaseDeriv E x * ‖E x‖ ^ 2 := by
  sorry

/-- Upper bound: `φ_E'(x) |E(x)|² ≤ C` on `ℝ` when `H(E) = PW` (`C = π / c₁`, `c₁` the lower
norm-equivalence constant). -/
theorem HEEqPW.phaseDeriv_mul_sq_le (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hHB : IsHB E) (h : HEEqPW E) :
    ∃ C : ℝ, ∀ x : ℝ, phaseDeriv E x * ‖E x‖ ^ 2 ≤ C := by
  sorry

end FF
