import FourierFrames.Defs

/-! # A real-valued Fatou upper-bound helper -/

open MeasureTheory Filter Topology

noncomputable section
namespace FF.Pavlov

/-- A common integral upper bound survives an a.e. limit of nonnegative functions. -/
theorem integral_le_of_ae_tendsto_nonneg {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ} {K : ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hfn : ∀ n, 0 ≤ᵐ[μ] f n) (hgn : 0 ≤ᵐ[μ] g)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    (hbound : ∀ n, ∫ x, f n x ∂μ ≤ K) :
    ∫ x, g x ∂μ ≤ K := by
  have hK : 0 ≤ K := (integral_nonneg_of_ae (hfn 0)).trans (hbound 0)
  apply (ENNReal.ofReal_le_ofReal_iff hK).mp
  rw [ofReal_integral_eq_lintegral_ofReal hg hgn]
  calc
    ∫⁻ x, ENNReal.ofReal (g x) ∂μ =
        ∫⁻ x, liminf (fun n ↦ ENNReal.ofReal (f n x)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with x hx
      exact (ENNReal.tendsto_ofReal hx).liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) atTop :=
      lintegral_liminf_le' fun n ↦ (hf n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    _ ≤ ENNReal.ofReal K := by
      apply liminf_le_of_frequently_le
      · apply Filter.Eventually.frequently
        exact Filter.Eventually.of_forall fun n ↦ by
          rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (hfn n)]
          exact ENNReal.ofReal_le_ofReal (hbound n)
      · exact ⟨0, Filter.Eventually.of_forall fun _ ↦ bot_le⟩

end FF.Pavlov
