import FourierFrames.Defs

/-!
# M08 helper (D2): the logarithmic lower bound `∫ log|s - x| dν ≥ log d - 2K` (blueprint §6.7)

Pure real analysis, independent of the partition data.
-/

open MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

namespace FF.D2

theorem intervalIntegrable_log_abs_sub (x a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => Real.log |s - x|) volume a b := by
  have h := (intervalIntegrable_log' (a := a - x) (b := b - x)).comp_sub_right x
  simpa [Real.log_abs] using h

theorem integrableOn_log_abs_sub (x a b : ℝ) :
    IntegrableOn (fun s : ℝ => Real.log |s - x|) (Ioc a b) :=
  (intervalIntegrable_log_abs_sub x a b).1

theorem integral_log_ball (x : ℝ) {d : ℝ} (hd : 0 < d) :
    ∫ s in (x - d)..(x + d), (Real.log d - Real.log |s - x|) = 2 * d := by
  have hab : x - d ≤ x + d := by linarith
  rw [integral_sub intervalIntegrable_const (intervalIntegrable_log_abs_sub x _ _)]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  have : ∫ s in (x - d)..(x + d), Real.log |s - x| = ∫ s in (x - d)..(x + d), Real.log (s - x) := by
    simp [Real.log_abs]
  rw [this, intervalIntegral.integral_comp_sub_right (fun s => Real.log s) x]
  simp only [integral_log]
  have h1 : x + d - x = d := by ring
  have h2 : x - d - x = -d := by ring
  rw [h1, h2, Real.log_neg_eq_log]
  ring

/-- The deficit function. -/
def deficit (x d : ℝ) : ℝ → ℝ :=
  (Ioo (x - d) (x + d)).indicator (fun s => Real.log d - Real.log |s - x|)

theorem deficit_integrable (x d : ℝ) : Integrable (deficit x d) := by
  unfold deficit
  rw [integrable_indicator_iff measurableSet_Ioo]
  have : IntegrableOn (fun s : ℝ => Real.log d - Real.log |s - x|) (Ioc (x - d) (x + d)) :=
    (integrableOn_const (by simp)).sub (integrableOn_log_abs_sub x _ _)
  exact this.mono_set Ioo_subset_Ioc_self

theorem deficit_integral (x : ℝ) {d : ℝ} (hd : 0 < d) : ∫ s, deficit x d s = 2 * d := by
  unfold deficit
  rw [MeasureTheory.integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]
  exact integral_log_ball x hd

theorem deficit_nonneg (x : ℝ) {d : ℝ} (s : ℝ) (hs : s ≠ x) : 0 ≤ deficit x d s := by
  unfold deficit
  by_cases h : s ∈ Ioo (x - d) (x + d)
  · rw [indicator_of_mem h]
    obtain ⟨h1, h2⟩ := h
    have hpos : 0 < |s - x| := abs_pos.mpr (sub_ne_zero.mpr hs)
    have hlt : |s - x| < d := abs_lt.mpr ⟨by linarith, by linarith⟩
    have := Real.log_le_log hpos hlt.le
    linarith
  · rw [indicator_of_notMem h]

theorem log_abs_ge_deficit (x : ℝ) {d : ℝ} (hd : 0 < d) (s : ℝ) (hs : s ≠ x) :
    Real.log d - deficit x d s ≤ Real.log |s - x| := by
  unfold deficit
  have hpos : 0 < |s - x| := abs_pos.mpr (sub_ne_zero.mpr hs)
  by_cases h : s ∈ Ioo (x - d) (x + d)
  · rw [indicator_of_mem h]; linarith
  · rw [indicator_of_notMem h]
    have : d ≤ |s - x| := by
      by_contra hc
      replace hc := not_le.mp hc
      obtain ⟨h1, h2⟩ := abs_lt.mp hc
      exact h ⟨by linarith, by linarith⟩
    have := Real.log_le_log hd this
    linarith

theorem lower_log_integral {a b K x : ℝ} (hab : a < b) {p : ℝ → ℝ} (hp : Continuous p)
    (hp0 : ∀ s, 0 ≤ p s) (hpK : ∀ s ∈ Ioc a b, p s ≤ K / (b - a))
    (hint : ∫ s in Ioc a b, p s = 1) :
    Real.log (b - a) - 2 * K ≤ ∫ s in Ioc a b, Real.log |s - x| * p s := by
  set d := b - a with hd_def
  have hd : 0 < d := by linarith
  have hK0 : 0 ≤ K := by
    have := hpK b ⟨hab, le_rfl⟩
    have h0 := hp0 b
    have : 0 ≤ K / d := le_trans h0 this
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith [h.2, hd])
  have hpint : IntegrableOn p (Ioc a b) := hp.integrableOn_Ioc
  have hmint : IntegrableOn (deficit x d) (Ioc a b) := (deficit_integrable x d).integrableOn
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ x := by
    simpa using (Set.countable_singleton x).ae_notMem volume
  have hRint : IntegrableOn (fun s => Real.log d * p s - K / d * deficit x d s) (Ioc a b) :=
    (hpint.const_mul _).sub (hmint.const_mul _)
  have hLint : IntegrableOn (fun s => Real.log |s - x| * p s) (Ioc a b) :=
    (integrableOn_log_abs_sub x a b).mul_continuousOn_of_subset hp.continuousOn
      measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  have hm_cell : ∫ s in Ioc a b, deficit x d s ≤ 2 * d := by
    rw [← deficit_integral x hd]
    exact setIntegral_le_integral (deficit_integrable x d)
      (hae.mono fun s hs => deficit_nonneg x s hs)
  have hmain : ∫ s in Ioc a b, (Real.log d * p s - K / d * deficit x d s) ≤
      ∫ s in Ioc a b, Real.log |s - x| * p s := by
    refine integral_mono_ae hRint hLint ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hae] with s hs hsc
    have h1 := log_abs_ge_deficit x hd s hs
    have h2 := deficit_nonneg (d := d) x s hs
    have h3 := hpK s hsc
    have h4 := hp0 s
    nlinarith [mul_le_mul_of_nonneg_left h3 h2, mul_le_mul_of_nonneg_right h1 h4]
  refine le_trans ?_ hmain
  · rw [integral_sub (hpint.const_mul _) (hmint.const_mul _), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, hint]
    have : K / d * ∫ s in Ioc a b, deficit x d s ≤ K / d * (2 * d) :=
      mul_le_mul_of_nonneg_left hm_cell (by positivity)
    have e : K / d * (2 * d) = 2 * K := by field_simp
    linarith

end FF.D2
