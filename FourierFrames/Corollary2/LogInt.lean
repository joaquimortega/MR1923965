import FourierFrames.Corollary2.Kernel
import FourierFrames.Corollary2.Density

/-!
# M07 -- helper lemmas for `Corollary2.lean`: integrals of `log |t - z|` and kernel bounds
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF



/-- The negative part of the logarithm near `0`: `L(u) = -log|u|` for `|u| < 1`, else `0`. -/
def logNeg (u : ℝ) : ℝ := (Ioo (-1 : ℝ) 1).indicator (fun u ↦ -Real.log u) u

theorem logNeg_nonneg (u : ℝ) : 0 ≤ logNeg u := by
  unfold logNeg
  by_cases h : u ∈ Ioo (-1 : ℝ) 1
  · rw [indicator_of_mem h, ← Real.log_abs]
    have : |u| < 1 := abs_lt.mpr ⟨h.1, h.2⟩
    have := Real.log_nonpos (abs_nonneg u) this.le
    linarith
  · rw [indicator_of_notMem h]

theorem integrable_logNeg : Integrable logNeg := by
  unfold logNeg
  rw [integrable_indicator_iff measurableSet_Ioo]
  have : IntervalIntegrable Real.log volume (-1) 1 := intervalIntegral.intervalIntegrable_log'
  have h2 := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp this
  exact h2.neg

theorem integral_logNeg : ∫ u, logNeg u = 2 := by
  unfold logNeg
  rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num)]
  rw [intervalIntegral.integral_neg, integral_log]
  simp
  norm_num


theorem abs_log_norm_sub_le {T : ℝ} (z : ℂ) {t : ℝ} (ht : |t| ≤ T) (hne : t ≠ z.re) :
    |Real.log ‖(t : ℂ) - z‖| ≤ Real.log (1 + T + ‖z‖) + logNeg (t - z.re) := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have h1 : |t - z.re| ≤ ‖(t : ℂ) - z‖ := by
    have := Complex.abs_re_le_norm ((t : ℂ) - z)
    simpa using this
  have hpos : 0 < |t - z.re| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have h2 : ‖(t : ℂ) - z‖ ≤ T + ‖z‖ := by
    calc ‖(t : ℂ) - z‖ ≤ ‖(t : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ T + ‖z‖ := by simp [ht]
  have hs : 0 < ‖(t : ℂ) - z‖ := hpos.trans_le h1
  have hlog1 : 0 ≤ Real.log (1 + T + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  have hLn := logNeg_nonneg (t - z.re)
  by_cases hs1 : 1 ≤ ‖(t : ℂ) - z‖
  · rw [abs_of_nonneg (Real.log_nonneg hs1)]
    have : Real.log ‖(t : ℂ) - z‖ ≤ Real.log (1 + T + ‖z‖) :=
      Real.log_le_log hs (by linarith)
    linarith
  · push Not at hs1
    rw [abs_of_nonpos (Real.log_nonpos hs.le hs1.le)]
    have hmem : t - z.re ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp (h1.trans_lt hs1)
    have : logNeg (t - z.re) = -Real.log |t - z.re| := by
      unfold logNeg; rw [indicator_of_mem hmem, Real.log_abs]
    have h3 : Real.log |t - z.re| ≤ Real.log ‖(t : ℂ) - z‖ := Real.log_le_log hpos h1
    linarith

theorem measurable_log_norm_sub (z : ℂ) : Measurable fun t : ℝ ↦ Real.log ‖(t : ℂ) - z‖ :=
  Real.measurable_log.comp (by fun_prop)

theorem integrableOn_log_norm_sub (z : ℂ) (T : ℝ) :
    IntegrableOn (fun t : ℝ ↦ Real.log ‖(t : ℂ) - z‖) (Icc (-T) T) := by
  have hdom : Integrable (fun t : ℝ ↦ Real.log (1 + |T| + ‖z‖) + logNeg (t - z.re)) (volume.restrict (Icc (-T) T)) := by
    refine (integrable_const _).add ?_
    exact (integrable_logNeg.comp_sub_right z.re).integrableOn
  refine Integrable.mono' hdom (measurable_log_norm_sub z).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_of_ae ((Set.countable_singleton z.re).ae_notMem volume),
    ae_restrict_mem measurableSet_Icc] with t ht1 ht2
  have hne : t ≠ z.re := by simpa using ht1
  have hTt : |t| ≤ |T| := by
    rw [abs_le]; constructor <;> cases abs_cases T <;> linarith [ht2.1, ht2.2]
  exact abs_log_norm_sub_le z hTt hne |>.trans_eq' (by simp [Real.norm_eq_abs]) |>.trans_eq (by rfl)


theorem integral_abs_log_norm_sub_le (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in Icc (-T) T, |Real.log ‖(t : ℂ) - z‖| ≤ 2 * T * Real.log (1 + T + ‖z‖) + 2 := by
  have hLn : Integrable (fun t : ℝ ↦ logNeg (t - z.re)) := integrable_logNeg.comp_sub_right z.re
  have hdom : IntegrableOn (fun t : ℝ ↦ Real.log (1 + T + ‖z‖) + logNeg (t - z.re)) (Icc (-T) T) :=
    (integrableOn_const (by simp)).add hLn.integrableOn
  calc ∫ t in Icc (-T) T, |Real.log ‖(t : ℂ) - z‖|
      ≤ ∫ t in Icc (-T) T, (Real.log (1 + T + ‖z‖) + logNeg (t - z.re)) := by
        refine integral_mono_ae (integrableOn_log_norm_sub z T).abs hdom ?_
        filter_upwards [ae_restrict_of_ae ((Set.countable_singleton z.re).ae_notMem volume),
          ae_restrict_mem measurableSet_Icc] with t ht1 ht2
        have hne : t ≠ z.re := by simpa using ht1
        exact abs_log_norm_sub_le z (abs_le.mpr ⟨ht2.1, ht2.2⟩) hne
    _ = Real.log (1 + T + ‖z‖) * (2 * T) + ∫ t in Icc (-T) T, logNeg (t - z.re) := by
        rw [integral_add (integrableOn_const (by simp)) hLn.integrableOn]
        simp only [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith : -T ≤ T)]
        ring
    _ ≤ Real.log (1 + T + ‖z‖) * (2 * T) + 2 := by
        gcongr
        calc ∫ t in Icc (-T) T, logNeg (t - z.re) ≤ ∫ t, logNeg (t - z.re) :=
              setIntegral_le_integral hLn (Eventually.of_forall fun t ↦ logNeg_nonneg _)
          _ = 2 := by rw [integral_sub_right_eq_self (fun t ↦ logNeg t) z.re]; exact integral_logNeg
    _ = _ := by ring



theorem rho_eq (t : ℝ) : rho t = if 1 < |t| then |t|⁻¹ else 0 := by
  unfold rho
  rw [chi_eq]
  by_cases h : |t| ≤ 1
  · simp [h, not_lt.mpr h]
  · simp [h, not_le.mp h, div_eq_mul_inv]

theorem integral_rho_Icc {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in Icc (-T) T, rho t = 2 * Real.log T := by
  rw [← integral_indicator measurableSet_Icc]
  have hF : ∀ t : ℝ, (Icc (-T) T).indicator rho t =
      (fun r : ℝ ↦ (Ioc (1 : ℝ) T).indicator (fun r ↦ r⁻¹) r) |t| := by
    intro t
    dsimp only
    by_cases h : t ∈ Icc (-T) T
    · rw [indicator_of_mem h, rho_eq]
      have hab : |t| ≤ T := abs_le.mpr ⟨h.1, h.2⟩
      by_cases h1 : 1 < |t|
      · simp only [h1, ↓reduceIte]; rw [indicator_of_mem (show |t| ∈ Ioc (1 : ℝ) T from ⟨h1, hab⟩)]
      · simp only [h1, ↓reduceIte]; rw [indicator_of_notMem (show |t| ∉ Ioc (1 : ℝ) T from fun h' ↦ h1 h'.1)]
    · rw [indicator_of_notMem h]
      have : ¬ |t| ≤ T := fun h' ↦ h (abs_le.mp h')
      rw [indicator_of_notMem (show |t| ∉ Ioc (1 : ℝ) T from fun h' ↦ this h'.2)]
  simp_rw [hF]
  rw [integral_comp_abs (f := fun r : ℝ ↦ (Ioc (1 : ℝ) T).indicator (fun r ↦ r⁻¹) r)]
  have this : ∫ r in Ioi (0 : ℝ), (Ioc (1 : ℝ) T).indicator (fun r ↦ r⁻¹) r = ∫ r in Ioc (1 : ℝ) T, r⁻¹ := by
    rw [setIntegral_indicator measurableSet_Ioc]
    have hs : Ioi (0 : ℝ) ∩ Ioc (1 : ℝ) T = Ioc (1 : ℝ) T :=
      inter_eq_right.mpr fun r hr ↦ by simp only [mem_Ioi]; linarith [hr.1]
    rw [hs]
  rw [this, ← intervalIntegral.integral_of_le hT, integral_inv_of_pos one_pos (by linarith)]
  simp


theorem potKernel_eq_of_ne (z : ℂ) {t : ℝ} (ht : t ≠ 0) (hz : t ≠ z.re) :
    potKernel z t = Real.log ‖(t : ℂ) - z‖ - Real.log |t| + chi t * (z.re / t) := by
  unfold potKernel chi
  have h1 : ‖1 - z / (t : ℂ)‖ = ‖(t : ℂ) - z‖ / |t| := by
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have : (1 : ℂ) - z / t = ((t : ℂ) - z) / t := by field_simp
    rw [this, norm_div]; simp
  have hnz : ‖(t : ℂ) - z‖ ≠ 0 := by
    intro h
    have := norm_eq_zero.mp h
    have := congrArg Complex.re this
    simp at this
    exact hz (by linarith)
  rw [h1, Real.log_div hnz (abs_ne_zero.mpr ht)]
  have : (z / (t : ℂ)).re = z.re / t := Complex.div_ofReal_re z t
  rw [this]

theorem abs_potKernel_le_far (z : ℂ) {t : ℝ} (ht1 : 1 < |t|) (hz : ‖z‖ ≤ |t| / 2) :
    |potKernel z t| ≤ ‖z‖ ^ 2 / t ^ 2 := by
  have ht0 : t ≠ 0 := fun h ↦ by rw [h] at ht1; norm_num at ht1
  have hχ : chi t = 1 := by rw [chi_eq]; simp [not_le.mpr ht1]
  show |Real.log ‖1 - z / t‖ + chi t * (z / t).re| ≤ _
  rw [hχ, one_mul]
  set w : ℂ := z / t with hw
  have hwn : ‖w‖ = ‖z‖ / |t| := by rw [hw, norm_div]; simp
  have hwn2 : ‖w‖ ≤ 1 / 2 := by
    rw [hwn, div_le_iff₀ (by linarith)]; linarith
  have hlog : Real.log ‖1 - w‖ = (Complex.log (1 + (-w))).re := by
    rw [Complex.log_re, ← sub_eq_add_neg]
  have hb := Complex.norm_log_one_add_sub_self_le (z := -w) (by rw [norm_neg]; linarith)
  rw [norm_neg] at hb
  have h1 : |Real.log ‖1 - w‖ + w.re| ≤ ‖w‖ ^ 2 := by
    have e : Real.log ‖1 - w‖ + w.re = (Complex.log (1 + (-w)) - (-w)).re := by
      rw [hlog]; simp
    rw [e]
    refine (Complex.abs_re_le_norm _).trans (hb.trans ?_)
    have : (1 - ‖w‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    nlinarith [sq_nonneg ‖w‖]
  refine h1.trans ?_
  rw [hwn, div_pow, sq_abs]



theorem far_inv_sq {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Icc (-T) T)ᶜ ∧
      ∫ t in (Icc (-T) T)ᶜ, (t ^ 2)⁻¹ = 2 / T := by
  have hcompl : (Icc (-T) T)ᶜ = Iio (-T) ∪ Ioi T := by
    ext t; simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
  have hf : ∀ t : ℝ, 0 < t → (t ^ 2)⁻¹ = t ^ (-2 : ℝ) := fun t ht ↦ by
    rw [Real.rpow_neg ht.le]; norm_cast
  have hI : IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Ioi T) := by
    have := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hT
    refine this.congr_fun (fun t ht ↦ (hf t (hT.trans ht)).symm) measurableSet_Ioi
  have hJ : ∫ t in Ioi T, (t ^ 2)⁻¹ = T⁻¹ := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ hf t (hT.trans ht)),
      integral_Ioi_rpow_of_lt (by norm_num) hT]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]; field_simp
  have hI' : IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Iio (-T)) := by
    have h1 : IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Ioi (-(-T))) := by rwa [neg_neg]
    have := h1.comp_neg_Iio (c := -T)
    simpa using this
  have hJ' : ∫ t in Iio (-T), (t ^ 2)⁻¹ = T⁻¹ := by
    rw [← integral_Iic_eq_integral_Iio]
    have := integral_comp_neg_Iic (-T) (fun t : ℝ ↦ (t ^ 2)⁻¹)
    simp only [neg_sq, neg_neg] at this
    rw [this, hJ]
  rw [hcompl]
  refine ⟨hI'.union hI, ?_⟩
  rw [setIntegral_union (Iio_disjoint_Ioi_of_le ?_ ) measurableSet_Ioi hI' hI]
  · rw [hJ, hJ']; field_simp; ring
  · linarith




theorem abs_potKernel_le_near (z : ℂ) {t : ℝ} (ht0 : t ≠ 0) (hz : t ≠ z.re) :
    |potKernel z t| ≤ |Real.log ‖(t : ℂ) - z‖| + |Real.log ‖(t : ℂ) - 0‖| + ‖z‖ * rho t := by
  rw [potKernel_eq_of_ne z ht0 hz]
  have h1 : Real.log ‖(t : ℂ) - 0‖ = Real.log |t| := by simp
  rw [h1]
  have h2 : |chi t * (z.re / t)| ≤ ‖z‖ * rho t := by
    rw [abs_mul, abs_of_nonneg (chi_nonneg t), abs_div]
    unfold rho
    have : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    calc chi t * (|z.re| / |t|) = (chi t / |t|) * |z.re| := by ring
      _ ≤ (chi t / |t|) * ‖z‖ := by gcongr; exact div_nonneg (chi_nonneg t) (abs_nonneg t)
      _ = ‖z‖ * (chi t / |t|) := by ring
  calc |Real.log ‖(t : ℂ) - z‖ - Real.log |t| + chi t * (z.re / t)|
      ≤ |Real.log ‖(t : ℂ) - z‖ - Real.log (|t|)| + |chi t * (z.re / t)| := abs_add_le _ _
    _ ≤ (|Real.log ‖(t : ℂ) - z‖| + |Real.log (|t|)|) + ‖z‖ * rho t := by
        gcongr; exact abs_sub _ _
    _ = _ := by ring


/-- Explicit bound for the potential of a bounded density. -/
def potBound (z : ℂ) : ℝ :=
  (2 * (2 * ‖z‖ + 2) * Real.log (1 + (2 * ‖z‖ + 2) + ‖z‖) + 2) +
    (2 * (2 * ‖z‖ + 2) * Real.log (1 + (2 * ‖z‖ + 2)) + 2) +
    ‖z‖ * (2 * Real.log (2 * ‖z‖ + 2)) + ‖z‖ ^ 2 * (2 / (2 * ‖z‖ + 2))

theorem abs_multU_le_potBound {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M)
    (z : ℂ) : |OCS.multU g 0 z| ≤ M * potBound z := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set T : ℝ := 2 * ‖z‖ + 2 with hT
  have hT2 : 2 ≤ T := by linarith [norm_nonneg z]
  have hT0 : 0 < T := by linarith
  have hint := integrable_potKernel_mul hg hM z
  rw [multU_eq_integral, ← integral_add_compl (s := Icc (-T) T) measurableSet_Icc hint]
  have hnear : |∫ t in Icc (-T) T, potKernel z t * g t| ≤
      M * ((2 * T * Real.log (1 + T + ‖z‖) + 2) + (2 * T * Real.log (1 + T) + 2) +
        ‖z‖ * (2 * Real.log T)) := by
    have hD1 := (integrableOn_log_norm_sub z T).abs
    have hD2 := (integrableOn_log_norm_sub 0 T).abs
    have hD3 := (integrableOn_rho T).const_mul ‖z‖
    have hD : IntegrableOn (fun t : ℝ ↦ M * (|Real.log ‖(t : ℂ) - z‖| + |Real.log ‖(t : ℂ) - 0‖| +
        ‖z‖ * rho t)) (Icc (-T) T) := ((hD1.add hD2).add hD3).const_mul M
    have e1 := integral_abs_log_norm_sub_le z hT0.le
    have e2 := integral_abs_log_norm_sub_le 0 hT0.le
    have e3 := integral_rho_Icc (by linarith : 1 ≤ T)
    simp only [norm_zero, add_zero] at e2
    calc |∫ t in Icc (-T) T, potKernel z t * g t|
        ≤ ∫ t in Icc (-T) T, |potKernel z t * g t| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Icc (-T) T, M * (|Real.log ‖(t : ℂ) - z‖| + |Real.log ‖(t : ℂ) - 0‖| +
            ‖z‖ * rho t) := by
          refine integral_mono_ae hint.abs.integrableOn hD ?_
          have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({0, z.re} : Set ℝ) :=
            (Set.toFinite _).countable.ae_notMem volume
          filter_upwards [ae_restrict_of_ae hnull] with t ht
          simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
          have h1 := abs_potKernel_le_near z ht.1 ht.2
          rw [abs_mul]
          calc |potKernel z t| * |g t| ≤ (|Real.log ‖(t : ℂ) - z‖| + |Real.log ‖(t : ℂ) - 0‖| +
                ‖z‖ * rho t) * M := mul_le_mul h1 (hM t) (abs_nonneg _) (by
                  have := abs_nonneg (Real.log ‖(t : ℂ) - z‖)
                  have := abs_nonneg (Real.log ‖(t : ℂ) - 0‖)
                  have := mul_nonneg (norm_nonneg z) (rho_nonneg t)
                  linarith)
            _ = _ := by ring
      _ = M * ((∫ t in Icc (-T) T, |Real.log ‖(t : ℂ) - z‖|) +
            (∫ t in Icc (-T) T, |Real.log ‖(t : ℂ) - 0‖|) + ‖z‖ * ∫ t in Icc (-T) T, rho t) := by
          rw [integral_const_mul, integral_add (f := fun t : ℝ ↦ |Real.log ‖(t : ℂ) - z‖| + |Real.log ‖(t : ℂ) - 0‖|) (g := fun t ↦ ‖z‖ * rho t) (hD1.add hD2) hD3, integral_add hD1 hD2,
            integral_const_mul]
      _ ≤ _ := by
          rw [e3]
          gcongr
  have hfar : |∫ t in (Icc (-T) T)ᶜ, potKernel z t * g t| ≤ M * (‖z‖ ^ 2 * (2 / T)) := by
    obtain ⟨hI, hJ⟩ := far_inv_sq hT0
    have hI2 : IntegrableOn (fun t : ℝ ↦ M * (‖z‖ ^ 2 * (t ^ 2)⁻¹)) (Icc (-T) T)ᶜ :=
      (hI.const_mul (‖z‖ ^ 2)).const_mul M
    calc |∫ t in (Icc (-T) T)ᶜ, potKernel z t * g t|
        ≤ ∫ t in (Icc (-T) T)ᶜ, |potKernel z t * g t| := abs_integral_le_integral_abs
      _ ≤ ∫ t in (Icc (-T) T)ᶜ, M * (‖z‖ ^ 2 * (t ^ 2)⁻¹) := by
          refine setIntegral_mono_on hint.abs.integrableOn hI2 measurableSet_Icc.compl fun t ht ↦ ?_
          have htT : T < |t| := by
            simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at ht
            rcases ht with h | h
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; linarith
          have h1 := abs_potKernel_le_far z (by linarith) (by linarith : ‖z‖ ≤ |t| / 2)
          rw [abs_mul]
          calc |potKernel z t| * |g t| ≤ (‖z‖ ^ 2 / t ^ 2) * M :=
                mul_le_mul h1 (hM t) (abs_nonneg _) (by positivity)
            _ = M * (‖z‖ ^ 2 * (t ^ 2)⁻¹) := by ring
      _ = M * (‖z‖ ^ 2 * (2 / T)) := by
          rw [integral_const_mul, integral_const_mul, hJ]
  calc _ ≤ |∫ t in Icc (-T) T, potKernel z t * g t| + |∫ t in (Icc (-T) T)ᶜ, potKernel z t * g t| :=
        abs_add_le _ _
    _ ≤ _ := by
        unfold potBound
        rw [← hT]
        linarith


theorem rpow_three_halves_eq {y : ℝ} (hy : 0 ≤ y) :
    y ^ (3 / 2 : ℝ) = Real.sqrt y ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

theorem potBound_le (z : ℂ) : potBound z ≤ 45 * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
  set x : ℝ := ‖z‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg z
  set y : ℝ := 1 + x with hy
  have hy1 : 1 ≤ y := by linarith
  set s : ℝ := Real.sqrt y with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hy1
  have hss : s * s = y := Real.mul_self_sqrt (by linarith)
  have hlogy : Real.log y ≤ 2 * s := by
    have : Real.log y = 2 * Real.log s := by
      rw [← hss, ← sq, Real.log_pow]; norm_num
    rw [this]
    have := Real.log_le_sub_one_of_pos (show 0 < s by linarith)
    linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have h3y : Real.log (3 * y) ≤ 4 * s := by
    rw [Real.log_mul (by norm_num) (by linarith)]; linarith
  have e1 : 1 + (2 * x + 2) + x = 3 * y := by rw [hy]; ring
  have e2 : 1 + (2 * x + 2) ≤ 3 * y := by rw [hy]; linarith
  have e3 : 2 * x + 2 = 2 * y := by rw [hy]; ring
  have hlog1 : Real.log (1 + (2 * x + 2)) ≤ 4 * s := by
    refine (Real.log_le_log (by linarith) e2).trans h3y
  have hlog2' : Real.log (2 * y) ≤ 3 * s := by
    rw [Real.log_mul (by norm_num) (by linarith)]; linarith
  unfold potBound
  rw [← hx, e1, e3]
  rw [e3] at hlog1
  rw [rpow_three_halves_eq (by linarith)]
  rw [← hs]
  have hs3 : s ^ 3 = y * s := by rw [← hss]; ring
  have hy0 : 0 ≤ y := by linarith
  have A1 : 2 * (2 * y) * Real.log (3 * y) ≤ 16 * s ^ 3 := by
    have := mul_le_mul_of_nonneg_left h3y (by linarith : 0 ≤ 2 * (2 * y))
    rw [hs3]; nlinarith
  have A2 : 2 * (2 * y) * Real.log (1 + 2 * y) ≤ 16 * s ^ 3 := by
    have := mul_le_mul_of_nonneg_left hlog1 (by linarith : 0 ≤ 2 * (2 * y))
    rw [hs3]; nlinarith
  have A3 : x * (2 * Real.log (2 * y)) ≤ 6 * s ^ 3 := by
    have := mul_le_mul_of_nonneg_left hlog2' hx0
    have hxy : x ≤ y := by linarith
    rw [hs3]
    nlinarith [mul_le_mul_of_nonneg_right hxy (by linarith : 0 ≤ s)]
  have A4 : x ^ 2 * (2 / (2 * y)) ≤ s ^ 3 := by
    have : x ^ 2 * (2 / (2 * y)) = x ^ 2 / y := by field_simp
    rw [this, div_le_iff₀ (by linarith)]
    have hxy : x ≤ y := by linarith
    rw [hs3]
    nlinarith [mul_le_mul_of_nonneg_right hxy hx0, mul_le_mul_of_nonneg_right hxy hy0, mul_le_mul_of_nonneg_right (show 1 ≤ s from hs1) hy0, mul_le_mul_of_nonneg_left hs1 hy0]
  have hs3' : 1 ≤ s ^ 3 := one_le_pow₀ hs1
  linarith


end FF
