import FourierFrames.HB.DeBranges

/-!
# M02 — the "evident fact" of p. 799: `|E| ≃ e^{π Im z}` on `Im z ≥ 0` implies `H(E) = PW`

See `blueprint/M02_HB.md`, §9.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- `PW ⊆ H(E)` with `‖f‖²_E ≤ c⁻² ‖f‖²` and `‖f‖²_E ≥ C⁻² ‖f‖²`. -/
theorem memHE_of_memPW (hPW : PaleyWienerThm) {E : ℂ → ℂ} (hE : IsHB E) {c C : ℝ} (hc : 0 < c)
    (hcomp : ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im))
    {f : ℂ → ℂ} (hf : MemPW f) :
    MemHE E f ∧ heNormSq E f ≤ ENNReal.ofReal (c ^ 2)⁻¹ * pwNormSq f ∧
      ENNReal.ofReal (C ^ 2)⁻¹ * pwNormSq f ≤ heNormSq E f := by
  sorry

/-- `H(E) ⊆ PW` with `‖f‖²_{PW} ≤ C² ‖f‖²_E`. -/
theorem memPW_of_memHE (hPW : PaleyWienerThm) {E : ℂ → ℂ} (hE : IsHB E) {c C : ℝ} (hc : 0 < c)
    (hcomp : ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im))
    {f : ℂ → ℂ} (hf : MemHE E f) :
    MemPW f ∧ pwNormSq f ≤ ENNReal.ofReal (C ^ 2) * heNormSq E f := by
  sorry

/-- **The "evident fact"** (p. 799): if `E ∈ \overline{HB}` and `|E(z)| ≃ e^{π Im z}` for
`Im z ≥ 0`, then `H(E) = PW`. -/
theorem heEqPW_of_comparable (hPW : PaleyWienerThm) {E : ℂ → ℂ} (hE : IsHB E)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) :
    HEEqPW E := by
  sorry

end FF
