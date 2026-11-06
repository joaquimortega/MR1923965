import FourierFrames.Theorem2i.Product

/-!
# M08 helper: U_psi as a sum over cells

See `blueprint/M08_Theorem2i.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

/-! ## §4. `U_ψ` as a sum over cells -/

theorem RegData.integrable_UPsi (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    Integrable fun s : ℝ =>
      (Real.log ‖1 - z / s‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 s) * (z / s).re) * deriv ψ s := by
  sorry

theorem RegData.hasSum_UPsi (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    HasSum (fun n : ℕ => ∫ s in cell t (n + 1),
        (Real.log ‖1 - z / s‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 s) * (z / s).re) * deriv ψ s)
      (UPsi ψ z) := by
  sorry

/-- `U_ψ - log|f| = ∑ j_n`. -/
theorem RegData.hasSum_cellTerm (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    HasSum (fun n : ℕ => cellTerm ψ t C (n + 1) z)
      (UPsi ψ z - Real.log ‖fProd ψ t C z‖) := by
  sorry


end FF
