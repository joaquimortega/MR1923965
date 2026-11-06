import FourierFrames.Theorem2i.Basic

/-!
# M08 helper: the product f, phase derivative

See `blueprint/M08_Theorem2i.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

/-! ## §3. The function `f` -/

theorem RegData.differentiable_fProd (h : RegData ψ t C M) : Differentiable ℂ (fProd ψ t C) := by
  sorry

theorem RegData.fProd_ne_zero (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    fProd ψ t C z ≠ 0 := by
  sorry

theorem RegData.isHB_fProd (h : RegData ψ t C M) : IsHB (fProd ψ t C) := by
  sorry

theorem RegData.hasSum_log_fProd (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    HasSum (fun n : ℕ => Real.log ‖1 - z / zPt ψ t C (n + 1)‖ + z.re * convFac ψ t (n + 1))
      (Real.log ‖fProd ψ t C z‖) := by
  sorry

/-- `φ_f'(x) = ∑ |Im z_n| / |x - z_n|²`. -/
theorem RegData.hasSum_phaseDeriv_fProd (h : RegData ψ t C M) (x : ℝ) :
    HasSum (fun n : ℕ => -(zPt ψ t C (n + 1)).im / ‖(x : ℂ) - zPt ψ t C (n + 1)‖ ^ 2)
      (phaseDeriv (fProd ψ t C) x) := by
  sorry

theorem RegData.tendsto_phaseDeriv_fProd (h : RegData ψ t C M) :
    Tendsto (phaseDeriv (fProd ψ t C)) (cocompact ℝ) (𝓝 0) := by
  sorry


end FF
