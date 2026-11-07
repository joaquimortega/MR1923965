import FourierFrames.Cited.Pavlov.LogDistanceCore
import FourierFrames.Cited.Pavlov.LogSingularity
import FourierFrames.Cited.Pavlov.LogDistanceLarge
import FourierFrames.Cited.Pavlov.LogDistanceTransfer

/-! # BMO of logarithmic distance to a bounded-gap separated grid -/

open MeasureTheory Metric Set Filter Topology Complex
noncomputable section
namespace FF.Pavlov
variable {Γ : Set ℝ}

/-- Short intervals near the grid reduce to one logarithmic singularity. -/
theorem Grid.meanOsc_log_infDist_le_of_near (g : Grid Γ) {a b : ℝ}
    (hab : a < b) (hsmall : b-a < g.lower/8)
    (hnear : Metric.infDist a Γ < 2*(b-a)) :
    meanOsc (fun x ↦ Real.log (Metric.infDist x Γ)) a b ≤ 2*logSingularityBound := by
  obtain ⟨k, hk, he⟩ := g.exists_nearest_on_short_interval hab hsmall hnear
  rw [meanOsc_congr_on_Icc hab.le (show EqOn
    (fun x ↦ Real.log (Metric.infDist x Γ))
    (fun x ↦ Real.log |x-g.point k|) (Icc a b) from
      fun x hx ↦ congrArg Real.log (he x hx))]
  apply (meanOsc_le_twice_comparison (locallyIntegrable_log_abs_sub (g.point k))
    hab (Real.log (b-a))).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply log_singularity_comparison hab
  linarith

/-- Logarithmic distance to a separated bounded-gap real grid belongs to BMO. -/
theorem Grid.memBMO_log_infDist (g : Grid Γ) :
    MemBMO (fun x ↦ Real.log (Metric.infDist x Γ)) := by
  obtain ⟨K, hK⟩ := g.exists_large_interval_log_infDist_bound
  refine ⟨g.locallyIntegrable_log_infDist,
    max (2*K) (max (2*Real.log 2) (2*logSingularityBound)), ?_⟩
  intro a b hab
  by_cases hlarge : g.lower/8 ≤ b-a
  · apply le_trans _ (le_max_left _ _)
    exact (meanOsc_le_twice_comparison g.locallyIntegrable_log_infDist hab 0).trans
      (by simpa only [sub_zero] using
        mul_le_mul_of_nonneg_left (hK a b hab hlarge) (show (0:ℝ) ≤ 2 by norm_num))
  · apply le_trans _ (le_max_right _ _)
    by_cases hfar : 2*(b-a) ≤ Metric.infDist a Γ
    · exact (g.meanOsc_log_infDist_le_of_far hab hfar).trans (le_max_left _ _)
    · exact (g.meanOsc_log_infDist_le_of_near hab (not_le.mp hlarge) (not_le.mp hfar)).trans
        (le_max_right _ _)

/-- Cell comparison transfers BMO from a horizontal line to the boundary. -/
theorem memBMO_boundary_log_of_cell_comparison
    (g : Grid Γ) (G : ℂ → ℂ) (ε C : ℝ)
    (hboundary : LocallyIntegrable (fun x : ℝ ↦ Real.log ‖G x‖))
    (hshift : MemBMO (fun x : ℝ ↦ Real.log ‖G ((x:ℂ)+(ε:ℂ)*I)‖))
    (hcmp : ∀ k x, x ∈ cell g k → x ≠ g.point k →
      |Real.log ‖G x‖ - Real.log ‖G ((x:ℂ)+(ε:ℂ)*I)‖ -
        Real.log (abs (x-g.point k))| ≤ C) :
    MemBMO (fun x : ℝ ↦ Real.log ‖G x‖) :=
  memBMO_boundary_log_of_distance g G ε C g.memBMO_log_infDist hboundary hshift hcmp

/-- A cardinal generator admits a height at which shifted BMO implies boundary BMO. -/
theorem exists_boundary_log_BMO_transfer (g : Grid Γ) (d : CardinalData Γ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < g.lower/8 ∧
      (MemBMO (fun x : ℝ ↦ Real.log ‖d.G ((x:ℂ)+(ε:ℂ)*I)‖) →
        MemBMO (fun x : ℝ ↦ Real.log ‖d.G x‖)) := by
  obtain ⟨ε, C, hε, hεq, _, hcmp⟩ := generating_log_cell_comparison g d
  refine ⟨ε, hε, hεq, fun hshift ↦ ?_⟩
  exact memBMO_boundary_log_of_cell_comparison g d.G ε C
    (locallyIntegrable_boundary_log_of_entire d.entire) hshift hcmp

end FF.Pavlov
