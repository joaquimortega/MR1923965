import FourierFrames.Defs

/-!
# M07 -- helper lemmas for `Corollary2.lean`: modification of a density on a compact set

Weighted Cesaro means, the sign/cutoff functions, and the modified density `modDens`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

theorem weighted_cesaro {ρ u : ℝ → ℝ} (hρ0 : ∀ t, 0 ≤ ρ t) (hρ : ∀ R : ℝ, IntegrableOn ρ (Icc (-R) R))
    (hum : Measurable u) {B : ℝ} (hB : ∀ t, |u t| ≤ B)
    (hu0 : Tendsto u (cocompact ℝ) (𝓝 0))
    (hP : Tendsto (fun R : ℝ ↦ ∫ t in Icc (-R) R, ρ t) atTop atTop) :
    Tendsto (fun R : ℝ ↦ (∫ t in Icc (-R) R, ρ t * u t) / ∫ t in Icc (-R) R, ρ t) atTop
      (𝓝 0) := by
  have hint := hρ
  have hintu : ∀ R : ℝ, IntegrableOn (fun t ↦ ρ t * u t) (Icc (-R) R) := fun R ↦
    (hint R).mul_bdd (c := B) hum.aestronglyMeasurable (ae_of_all _ fun t ↦ by simpa using hB t)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- tail threshold
  have h1 : {t : ℝ | |u t| < ε / 2} ∈ cocompact ℝ := by
    have := hu0.eventually (Metric.ball_mem_nhds 0 (half_pos hε))
    filter_upwards [this] with t ht
    simpa using ht
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.mp h1
  obtain ⟨X, hX⟩ := hK.isBounded.subset_closedBall 0
  set Y : ℝ := |X| + 1 with hY
  have hY0 : 0 < Y := by positivity
  set B₀ : ℝ := ∫ t in Icc (-Y) Y, ρ t * |u t| with hB₀
  have hB₀0 : 0 ≤ B₀ := setIntegral_nonneg measurableSet_Icc fun t _ ↦ mul_nonneg (hρ0 t) (abs_nonneg _)
  have htail : ∀ t, Y ≤ |t| → |u t| < ε / 2 := by
    intro t ht
    have : t ∉ K := fun h ↦ by
      have := hX h
      simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      linarith [le_abs_self X, abs_nonneg X]
    exact hKs this
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (hP.eventually (eventually_gt_atTop (max 1 (2 * B₀ / ε + 1))))
  refine ⟨max R₀ Y, fun R hR ↦ ?_⟩
  have hRX : Y ≤ R := (le_max_right _ _).trans hR
  have hPR := hR₀ R ((le_max_left _ _).trans hR)
  set P := ∫ t in Icc (-R) R, ρ t with hPdef
  have hP1 : 1 < P := lt_of_le_of_lt (le_max_left _ _) hPR
  have hP2 : 2 * B₀ / ε + 1 < P := lt_of_le_of_lt (le_max_right _ _) hPR
  have hPpos : 0 < P := by linarith
  -- bound
  have hbound : |∫ t in Icc (-R) R, ρ t * u t| ≤ ε / 2 * P + B₀ := by
    refine (abs_integral_le_integral_abs).trans ?_
    have hpt : ∀ t, |ρ t * u t| ≤ ε / 2 * ρ t + (Icc (-Y) Y).indicator (fun t ↦ ρ t * |u t|) t := by
      intro t
      rw [abs_mul, abs_of_nonneg (hρ0 t)]
      by_cases ht : t ∈ Icc (-Y) Y
      · rw [indicator_of_mem ht]; nlinarith [hρ0 t]
      · rw [indicator_of_notMem ht]
        have : Y ≤ |t| := by
          simp only [mem_Icc, not_and_or, not_le] at ht
          rcases ht with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        have := htail t this
        nlinarith [hρ0 t]
    have hI1 : IntegrableOn (fun t ↦ ρ t * |u t|) (Icc (-Y) Y) := by
      exact IntegrableOn.congr_fun (f := fun t ↦ ‖ρ t * u t‖) (hintu Y).norm (fun t _ ↦ by simp [abs_of_nonneg (hρ0 t)]) measurableSet_Icc
    have hI2 : IntegrableOn (fun t ↦ (Icc (-Y) Y).indicator (fun t ↦ ρ t * |u t|) t) (Icc (-R) R) :=
      ((integrable_indicator_iff measurableSet_Icc).mpr hI1).integrableOn
    calc ∫ t in Icc (-R) R, |ρ t * u t|
        ≤ ∫ t in Icc (-R) R, (ε / 2 * ρ t + (Icc (-Y) Y).indicator (fun t ↦ ρ t * |u t|) t) := by
          refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun t _ ↦ hpt t
          · exact IntegrableOn.congr_fun (f := fun t ↦ ‖ρ t * u t‖) (hintu R).norm (fun t _ ↦ by simp) measurableSet_Icc
          · exact ((hint R).const_mul _).add hI2
      _ = ε / 2 * P + ∫ t in Icc (-R) R, (Icc (-Y) Y).indicator (fun t ↦ ρ t * |u t|) t := by
          rw [integral_add ((hint R).const_mul _) hI2, integral_const_mul]
      _ ≤ ε / 2 * P + B₀ := by
          gcongr
          calc ∫ t in Icc (-R) R, (Icc (-Y) Y).indicator (fun t ↦ ρ t * |u t|) t
              ≤ ∫ t, (Icc (-Y) Y).indicator (fun t ↦ ρ t * |u t|) t := by
                refine setIntegral_le_integral ((integrable_indicator_iff measurableSet_Icc).mpr hI1) ?_
                exact Eventually.of_forall fun t ↦ indicator_nonneg (fun t _ ↦ mul_nonneg (hρ0 t) (abs_nonneg _)) t
            _ = B₀ := integral_indicator measurableSet_Icc
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hPpos, div_lt_iff₀ hPpos]
  have : 2 * B₀ / ε < P - 1 := by linarith
  rw [div_lt_iff₀ hε] at this
  nlinarith


/-- The cutoff `1 - 1_{[-1,1]}`. -/
def chi (t : ℝ) : ℝ := 1 - (Icc (-1 : ℝ) 1).indicator 1 t

theorem chi_eq (t : ℝ) : chi t = if |t| ≤ 1 then 0 else 1 := by
  unfold chi
  by_cases h : |t| ≤ 1
  · have : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp h
    simp [indicator_of_mem this, h]
  · have : t ∉ Icc (-1 : ℝ) 1 := fun h' ↦ h (abs_le.mpr h')
    simp [indicator_of_notMem this, h]

/-- The sign off `[-1,1]`. -/
def sig (t : ℝ) : ℝ := if 1 < t then 1 else if t < -1 then -1 else 0

/-- `1_{|t|>1} / |t|`. -/
def rho (t : ℝ) : ℝ := chi t / |t|

theorem integral_Icc_odd {F : ℝ → ℝ} (hF : ∀ t, F (-t) = -F t) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in Icc (-R) R, F t = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have := intervalIntegral.integral_comp_neg (a := -R) (b := R) F
  simp only [hF, neg_neg, intervalIntegral.integral_neg] at this
  linarith

theorem measurable_chi : Measurable chi := by
  unfold chi
  exact measurable_const.sub (measurable_const.indicator measurableSet_Icc)

theorem measurable_sig : Measurable sig := by
  unfold sig
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const

theorem measurable_rho : Measurable rho := by
  unfold rho
  exact measurable_chi.div measurable_id.abs

theorem abs_sig_le (t : ℝ) : |sig t| ≤ 1 := by
  unfold sig; split_ifs <;> simp

theorem chi_nonneg (t : ℝ) : 0 ≤ chi t := by
  rw [chi_eq]; split_ifs <;> norm_num

theorem chi_le_one (t : ℝ) : chi t ≤ 1 := by
  rw [chi_eq]; split_ifs <;> norm_num

theorem rho_nonneg (t : ℝ) : 0 ≤ rho t := div_nonneg (chi_nonneg t) (abs_nonneg t)

theorem rho_le_one (t : ℝ) : rho t ≤ 1 := by
  unfold rho
  rw [chi_eq]
  split_ifs with h
  · simp
  · push Not at h
    rw [div_le_one (by linarith)]; exact h.le

theorem rho_of_one_lt {t : ℝ} (ht : 1 < t) : rho t = t⁻¹ := by
  unfold rho
  have h1 : ¬ |t| ≤ 1 := by rw [abs_of_pos (by linarith)]; linarith
  simp [chi_eq, abs_of_pos (show 0 < t by linarith), ht.not_ge]

theorem integrableOn_of_abs_le {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ t, |f t| ≤ B)
    (R : ℝ) : IntegrableOn f (Icc (-R) R) :=
  Measure.integrableOn_of_bounded (M := B) (by simp) hf.aestronglyMeasurable
    (ae_of_all _ fun t ↦ by simpa using hB t)

theorem integrableOn_rho (R : ℝ) : IntegrableOn rho (Icc (-R) R) :=
  integrableOn_of_abs_le measurable_rho (B := 1) (fun t ↦ by
    rw [abs_of_nonneg (rho_nonneg t)]; exact rho_le_one t) R

theorem rho_tendsto : Tendsto (fun R : ℝ ↦ ∫ t in Icc (-R) R, rho t) atTop atTop := by
  have h1 : ∀ R : ℝ, 1 ≤ R → Real.log R ≤ ∫ t in Icc (-R) R, rho t := by
    intro R hR
    have h2 : ∫ t in Ioc 1 R, rho t = Real.log R := by
      rw [← intervalIntegral.integral_of_le hR]
      rw [intervalIntegral.integral_congr_ae (g := fun t ↦ t⁻¹)]
      · rw [integral_inv_of_pos (by norm_num) (by linarith)]; simp
      · refine Eventually.of_forall fun t ht ↦ ?_
        rw [uIoc_of_le hR] at ht
        exact rho_of_one_lt ht.1
    rw [← h2]
    refine setIntegral_mono_set (integrableOn_rho R) (Eventually.of_forall fun t ↦ rho_nonneg t) ?_
    refine Eventually.of_forall fun t ht ↦ ?_
    exact ⟨by linarith [ht.1], ht.2⟩
  exact tendsto_atTop_mono' atTop (eventually_atTop.mpr ⟨1, h1⟩) Real.tendsto_log_atTop


theorem bounded_of_tendsto_cocompact {g : ℝ → ℝ} (hg : Continuous g)
    (h : Tendsto g (cocompact ℝ) (𝓝 0)) : ∃ M : ℝ, ∀ x, |g x| ≤ M := by
  have h1 : {x | g x ∈ Metric.closedBall (0 : ℝ) 1} ∈ cocompact ℝ :=
    h.eventually (Metric.closedBall_mem_nhds 0 one_pos)
  obtain ⟨t, ht, hts⟩ := Filter.mem_cocompact.mp h1
  obtain ⟨C, hC⟩ := ht.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 1, fun x ↦ ?_⟩
  by_cases hx : x ∈ t
  · exact (hC x hx).trans (le_max_left _ _)
  · have := hts hx
    simp only [mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact this.trans (le_max_right _ _)

theorem sig_neg (t : ℝ) : sig (-t) = -sig t := by
  unfold sig
  by_cases h1 : 1 < t
  · have : ¬ (1 < -t) := by linarith
    have h2 : -t < -1 := by linarith
    simp [h1, this, h2]
  · by_cases h2 : t < -1
    · have : 1 < -t := by linarith
      simp [h1, h2, this]
    · have h3 : ¬ (1 < -t) := by linarith
      have h4 : ¬ (-t < -1) := by linarith
      simp [h1, h2, h3, h4]

/-- The modified density. -/
def modDens (w : ℝ → ℝ) (R c s : ℝ) (t : ℝ) : ℝ := if |t| ≤ R then c + s * sig t else 1 + w t

theorem modDens_sub (w : ℝ → ℝ) (R c s : ℝ) (t : ℝ) :
    modDens w R c s t - (1 + w t) =
      (Icc (-R) R).indicator (fun t ↦ (c - 1) + s * sig t - w t) t := by
  unfold modDens
  by_cases h : |t| ≤ R
  · have : t ∈ Icc (-R) R := abs_le.mp h
    rw [indicator_of_mem this]; simp only [h, ↓reduceIte]; ring
  · have : t ∉ Icc (-R) R := fun h' ↦ h (abs_le.mpr h')
    rw [indicator_of_notMem this]; simp only [h, ↓reduceIte]; ring

theorem pw_identity (c s : ℝ) (w : ℝ → ℝ) (t : ℝ) :
    chi t * (((c - 1) + s * sig t - w t) / t) =
      (c - 1) * (chi t / t) + s * rho t - rho t * (sig t * w t) := by
  rw [chi_eq]
  unfold rho
  rw [chi_eq]
  by_cases h : |t| ≤ 1
  · simp [h]
  · push Not at h
    simp only [h.not_ge, ↓reduceIte]
    rcases lt_abs.mp h with h1 | h1
    · have : 0 < t := by linarith
      rw [abs_of_pos this]; unfold sig; simp only [h1, ↓reduceIte]; field_simp
    · have : t < 0 := by linarith
      have h2 : t < -1 := by linarith
      rw [abs_of_neg this]; unfold sig; simp only [show ¬ (1 < t) by linarith, h2, ↓reduceIte]; field_simp

theorem integral_modDens_sub_zero {w : ℝ → ℝ} (hw : Continuous w) {R c s : ℝ} (hR : 0 < R)
    (hc : (c - 1) * (2 * R) = ∫ t in Icc (-R) R, w t) :
    ∫ t, (modDens w R c s t - (1 + w t)) = 0 := by
  simp_rw [modDens_sub]
  rw [integral_indicator measurableSet_Icc]
  have i1 : IntegrableOn (fun _ : ℝ ↦ c - 1) (Icc (-R) R) := integrableOn_const (by simp)
  have i2 : IntegrableOn (fun t ↦ s * sig t) (Icc (-R) R) :=
    (integrableOn_of_abs_le measurable_sig (B := 1) abs_sig_le R).const_mul s
  have i3 : IntegrableOn w (Icc (-R) R) := hw.integrableOn_Icc
  have i12 : IntegrableOn (fun x ↦ (c - 1) + s * sig x) (Icc (-R) R) := i1.add i2
  rw [integral_sub i12 i3, integral_add i1 i2, integral_const_mul,
    integral_Icc_odd sig_neg hR.le, ← hc]
  simp only [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith : -R ≤ R)]
  ring


theorem chi_div_odd (t : ℝ) : chi (-t) / (-t) = -(chi t / t) := by
  rw [chi_eq, chi_eq, abs_neg, div_neg]

theorem abs_chi_div_le (t : ℝ) : |chi t / t| ≤ 1 := by
  rw [chi_eq]
  split_ifs with h
  · simp
  · push Not at h
    rw [abs_div, abs_one, div_le_one (by linarith)]; exact h.le

theorem measurable_chi_div : Measurable fun t : ℝ ↦ chi t / t := measurable_chi.div measurable_id

theorem integral_modDens_moment {w : ℝ → ℝ} (hw : Continuous w) {B : ℝ} (hB : ∀ t, |w t| ≤ B)
    {R c s β : ℝ} (hR : 0 < R)
    (hs : s * (∫ t in Icc (-R) R, rho t) = (∫ t in Icc (-R) R, rho t * (sig t * w t)) - β) :
    ∫ t, chi t * ((modDens w R c s t - (1 + w t)) / t) = -β := by
  have key : ∀ t, chi t * ((modDens w R c s t - (1 + w t)) / t) =
      (Icc (-R) R).indicator (fun t ↦ (c - 1) * (chi t / t) + s * rho t - rho t * (sig t * w t)) t := by
    intro t
    rw [modDens_sub]
    by_cases h : t ∈ Icc (-R) R
    · rw [indicator_of_mem h, indicator_of_mem h, pw_identity]
    · rw [indicator_of_notMem h, indicator_of_notMem h]; simp
  simp_rw [key]
  rw [integral_indicator measurableSet_Icc]
  have i1 : IntegrableOn (fun t ↦ (c - 1) * (chi t / t)) (Icc (-R) R) :=
    (integrableOn_of_abs_le measurable_chi_div (B := 1) abs_chi_div_le R).const_mul _
  have i2 : IntegrableOn (fun t ↦ s * rho t) (Icc (-R) R) := (integrableOn_rho R).const_mul s
  have i3 : IntegrableOn (fun t ↦ rho t * (sig t * w t)) (Icc (-R) R) := by
    refine integrableOn_of_abs_le (measurable_rho.mul (measurable_sig.mul hw.measurable)) (B := B)
      (fun t ↦ ?_) R
    show |rho t * (sig t * w t)| ≤ B
    rw [abs_mul, abs_mul, abs_of_nonneg (rho_nonneg t)]
    calc rho t * (|sig t| * |w t|) ≤ 1 * (1 * B) := by
          gcongr <;> first | exact rho_le_one t | exact abs_sig_le t | exact hB t
      _ = B := by ring
  have i12 : IntegrableOn (fun t ↦ (c - 1) * (chi t / t) + s * rho t) (Icc (-R) R) := i1.add i2
  rw [integral_sub i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_Icc_odd chi_div_odd hR.le]
  linarith


end FF
