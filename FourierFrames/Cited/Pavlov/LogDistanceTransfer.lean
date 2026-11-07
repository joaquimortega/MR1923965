import FourierFrames.Cited.Pavlov.LogDistanceCore
import FourierFrames.Cited.Pavlov.CellBounds

/-! # Transfer from a shifted generator logarithm to its boundary logarithm -/

open MeasureTheory Metric Set Filter Topology Complex
noncomputable section
namespace FF.Pavlov
variable {Γ : Set ℝ}

/-- The cell comparison transfers BMO once logarithmic distance is known to lie in BMO. -/
theorem memBMO_boundary_log_of_distance
    (g : Grid Γ) (G : ℂ → ℂ) (ε C : ℝ)
    (hdistance : MemBMO (fun x ↦ Real.log (Metric.infDist x Γ)))
    (hboundary : LocallyIntegrable (fun x : ℝ ↦ Real.log ‖G x‖))
    (hshift : MemBMO (fun x : ℝ ↦ Real.log ‖G ((x:ℂ)+(ε:ℂ)*I)‖))
    (hcmp : ∀ k x, x ∈ cell g k → x ≠ g.point k →
      |Real.log ‖G x‖ - Real.log ‖G ((x:ℂ)+(ε:ℂ)*I)‖ -
        Real.log (abs (x-g.point k))| ≤ C) :
    MemBMO (fun x : ℝ ↦ Real.log ‖G x‖) := by
  let f : ℝ → ℝ := fun x ↦ Real.log ‖G ((x:ℂ)+(ε:ℂ)*I)‖ +
    Real.log (Metric.infDist x Γ)
  have hf : MemBMO f := memBMO_add hshift hdistance
  let e : ℝ → ℝ := fun x ↦ Real.log ‖G x‖ - f x
  have he : LocallyIntegrable e := hboundary.sub hf.1
  have heC : ∀ᵐ x : ℝ, |e x| ≤ C := by
    filter_upwards [g.ae_not_mem] with x hx
    obtain ⟨k, hk⟩ := g.exists_cell x
    have hxk : x ≠ g.point k := fun h ↦ hx (h ▸ g.point_mem k)
    have hc := hcmp k x hk hxk
    rw [← g.infDist_eq_abs_sub hk] at hc
    dsimp [e, f]
    convert hc using 1
    congr 1
    ring
  have hsum := memBMO_add_ae_bounded hf he heC
  convert hsum using 1
  funext x
  dsimp [e]
  ring

/-- The logarithmic boundary modulus of an entire function is locally integrable. -/
theorem locallyIntegrable_boundary_log_of_entire {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) : LocallyIntegrable (fun x : ℝ ↦ Real.log ‖G x‖) := by
  intro x
  refine ⟨Icc (x-1) (x+1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro y _
  have hreal : AnalyticAt ℝ (fun t : ℝ ↦ G (t : ℂ)) y :=
    (hG.analyticAt (y : ℂ)).restrictScalars.comp (Complex.ofRealCLM.analyticAt y)
  exact hreal.meromorphicAt

end FF.Pavlov
