import FourierFrames.Cited.Pavlov.BMO

/-!
# Uniform interval bounds for a logarithmic singularity

Scaling an interval to unit length turns a nearby translated logarithm into
`log |u|` on a subinterval of `[-4,4]`. The exceptional node is a null singleton.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace FF.Pavlov

/-- A translated logarithm is integrable even across its single zero. -/
theorem intervalIntegrable_log_abs_sub (γ a b : ℝ) :
    IntervalIntegrable (fun x ↦ Real.log |x-γ|) volume a b := by
  have hi := (intervalIntegral.intervalIntegrable_log' (a := a-γ) (b := b-γ)).comp_sub_right γ
  simpa only [sub_add_cancel, Real.log_abs] using hi

/-- Local integrability of the logarithm of distance to one point. -/
theorem locallyIntegrable_log_abs_sub (γ : ℝ) :
    LocallyIntegrable (fun x ↦ Real.log |x-γ|) := by
  intro x
  refine ⟨Icc (x-1) (x+1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
    (intervalIntegrable_log_abs_sub γ (x-1) (x+1))

/-- A fixed finite comparison constant for all nearby logarithmic singularities. -/
def logSingularityBound : ℝ := ∫ u in (-4 : ℝ)..4, |Real.log (|u|)|

theorem logSingularityBound_nonneg : 0 ≤ logSingularityBound := by
  exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ abs_nonneg _)

/-- A nearby node has uniformly bounded normalized logarithmic oscillation
around the logarithm of the interval length. -/
theorem log_singularity_comparison {a b γ : ℝ} (hab : a < b)
    (hγ : |γ-a| ≤ 3*(b-a)) :
    (b-a)⁻¹ * ∫ x in a..b, |Real.log |x-γ| - Real.log (b-a)| ≤
      logSingularityBound := by
  let L := b-a
  have hL : 0 < L := sub_pos.mpr hab
  have hne : ∀ᵐ x : ℝ, x ≠ γ := by
    rw [ae_iff]
    simp
  have he : (∫ x in a..b, |Real.log |x-γ| - Real.log L|) =
      ∫ x in a..b, |Real.log (|x/L-γ/L|)| := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with x hx _
    rw [Real.log_abs, Real.log_abs, ← Real.log_div (sub_ne_zero.mpr hx) hL.ne', sub_div]
  have heq : L⁻¹ * (∫ x in a..b, |Real.log (|x/L-γ/L|)|) =
      ∫ u in a/L-γ/L..b/L-γ/L, |Real.log (|u|)| := by
    rw [intervalIntegral.integral_comp_div_sub (fun u ↦ |Real.log (|u|)|) hL.ne' (γ/L)]
    simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
  have hlo : (-4 : ℝ) ≤ a/L-γ/L := by
    have hg := (abs_le.mp hγ).2
    rw [← sub_div, le_div_iff₀ hL]
    dsimp [L] at *
    linarith
  have hhi : b/L-γ/L ≤ (4 : ℝ) := by
    have hg := (abs_le.mp hγ).1
    rw [← sub_div, div_le_iff₀ hL]
    dsimp [L] at *
    linarith
  have hab' : a/L-γ/L ≤ b/L-γ/L := by
    exact sub_le_sub_right ((div_le_div_iff_of_pos_right hL).mpr hab.le) _
  rw [he, heq]
  apply intervalIntegral.integral_mono_interval hlo hab' hhi
    (Eventually.of_forall fun _ ↦ abs_nonneg _)
  simpa only [Real.log_abs] using
    (intervalIntegral.intervalIntegrable_log' (a := -4) (b := 4)).abs

/-- A single absolute constant works for every interval and nearby point. -/
theorem exists_log_singularity_comparison : ∃ C : ℝ, 0 ≤ C ∧
    ∀ a b γ : ℝ, a < b → |γ-a| ≤ 3*(b-a) →
      (b-a)⁻¹ * ∫ x in a..b, |Real.log |x-γ| - Real.log (b-a)| ≤ C := by
  exact ⟨logSingularityBound, logSingularityBound_nonneg,
    fun _ _ _ hab hγ ↦ log_singularity_comparison hab hγ⟩

end FF.Pavlov
