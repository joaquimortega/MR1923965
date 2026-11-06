import FourierFrames.Defs
import OrtegaCerdaSeip.Lemma3.Main

/-!
# M09 helper: the ramp potential estimate

`|(1/a) ∫_a^{2a} log|1 - x/t| dt - log max(1, |x|/a)| ≤ 4`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped Interval

noncomputable section

namespace FF

namespace T2ii

/-- `V(v) = min(0, log |v|)`, supported in `[-1, 1]`. -/
def Vneg (v : ℝ) : ℝ := min 0 (Real.log |v|)

lemma Vneg_eq_indicator : Vneg = (Icc (-1 : ℝ) 1).indicator (fun v ↦ Real.log |v|) := by
  funext v
  by_cases h : v ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem h]
    have : |v| ≤ 1 := abs_le.2 ⟨h.1, h.2⟩
    have : Real.log |v| ≤ 0 := by
      rcases (abs_nonneg v).eq_or_lt with h0 | h0
      · rw [← h0]; simp
      · exact Real.log_nonpos h0.le this
    unfold Vneg; rw [min_eq_right this]
  · rw [indicator_of_notMem h]
    have : 1 < |v| := by
      simp only [mem_Icc, not_and_or, not_le] at h
      rcases h with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    unfold Vneg; rw [min_eq_left (Real.log_nonneg this.le)]

lemma intervalIntegrable_log_abs (u v : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ Real.log |s|) volume u v := by
  simp

lemma integrable_Vneg : Integrable Vneg := by
  rw [Vneg_eq_indicator]
  refine (integrable_indicator_iff measurableSet_Icc).2 ?_
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).1
    (intervalIntegrable_log_abs _ _))

lemma integral_Vneg : ∫ v, Vneg v = -2 := by
  rw [Vneg_eq_indicator, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (intervalIntegrable_log_abs _ _) (intervalIntegrable_log_abs _ _)]
  have h1 : ∫ v in (-1 : ℝ)..0, Real.log |v| = ∫ v in (0 : ℝ)..1, Real.log v := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (fun v : ℝ ↦ Real.log |v|)
    simp only [abs_neg, neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr (fun v hv ↦ ?_)
    have : v ∈ Icc (0 : ℝ) 1 := by simpa using hv
    simp [abs_of_nonneg this.1]
  have h2 : ∫ v in (0 : ℝ)..1, Real.log |v| = ∫ v in (0 : ℝ)..1, Real.log v := by
    refine intervalIntegral.integral_congr (fun v hv ↦ ?_)
    have : v ∈ Icc (0 : ℝ) 1 := by simpa using hv
    simp [abs_of_nonneg this.1]
  rw [h1, h2, integral_log]
  norm_num

/-- Any unit interval carries `∫ log|v| ≥ -2`. -/
lemma neg_two_le_integral_log_abs (c : ℝ) : -2 ≤ ∫ v in c..(c + 1), Real.log |v| := by
  have hle : ∫ v in c..(c + 1), Vneg v ≤ ∫ v in c..(c + 1), Real.log |v| := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_ (intervalIntegrable_log_abs _ _) ?_
    · exact integrable_Vneg.intervalIntegrable
    · intro v _; exact min_le_right _ _
  refine le_trans ?_ hle
  rw [intervalIntegral.integral_of_le (by linarith)]
  have h := integral_add_compl (μ := volume) (measurableSet_Ioc (a := c) (b := c + 1))
    integrable_Vneg
  have h2 : ∫ v in (Ioc c (c + 1))ᶜ, Vneg v ≤ 0 := by
    refine setIntegral_nonpos measurableSet_Ioc.compl (fun v _ ↦ min_le_left _ _)
  rw [integral_Vneg] at h
  linarith

lemma log_three_lt : Real.log 3 < 1.11 := by
  have he := Real.exp_one_gt_d9
  have h1 : Real.log (3 / Real.exp 1) ≤ 3 / Real.exp 1 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at h1
  have h2 : 3 / Real.exp 1 < 1.11 := by
    rw [div_lt_iff₀ (Real.exp_pos 1)]; linarith
  linarith

lemma log_le_log_of_nonneg {y z : ℝ} (hy : 0 ≤ y) (hz : 1 ≤ z) (h : y ≤ z) :
    Real.log y ≤ Real.log z := by
  rcases hy.eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]; exact Real.log_nonneg hz
  · exact Real.log_le_log h0 h

/-- The normalised ramp potential `∫_1^2 log|1 - ξ/s| ds`. -/
def rampInt (ξ : ℝ) : ℝ := ∫ s in (1 : ℝ)..2, Real.log ‖1 - (ξ : ℂ) / (s : ℂ)‖

lemma intervalIntegrable_log_abs_sub (ξ u v : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ Real.log |s - ξ|) volume u v := by
  have := (intervalIntegrable_log_abs (u - ξ) (v - ξ)).comp_sub_right ξ
  simpa using this

lemma log_norm_one_sub_div_real (ξ s : ℝ) (hs : 0 < s) (hne : s ≠ ξ) :
    Real.log ‖1 - (ξ : ℂ) / (s : ℂ)‖ = Real.log |s - ξ| - Real.log s := by
  have h : (1 : ℂ) - (ξ : ℂ) / (s : ℂ) = (((s - ξ) / s : ℝ) : ℂ) := by
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast; field_simp
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hs,
    Real.log_div (abs_ne_zero.2 (sub_ne_zero.2 hne)) hs.ne']

lemma rampInt_eq (ξ : ℝ) :
    rampInt ξ = (∫ s in (1 : ℝ)..2, Real.log |s - ξ|) - ∫ s in (1 : ℝ)..2, Real.log s := by
  unfold rampInt
  rw [← intervalIntegral.integral_sub (intervalIntegrable_log_abs_sub _ _ _)
    (by simp)]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [OCS.ae_ne_real ξ] with s hs hs'
  have : 0 < s := by
    rw [Set.uIoc_of_le (by norm_num)] at hs'; linarith [hs'.1]
  exact log_norm_one_sub_div_real ξ s this hs

lemma integral_log_one_two_nonneg : 0 ≤ ∫ s in (1 : ℝ)..2, Real.log s := by
  refine intervalIntegral.integral_nonneg (by norm_num) (fun s hs ↦ Real.log_nonneg hs.1)

lemma integral_log_one_two_le : ∫ s in (1 : ℝ)..2, Real.log s ≤ Real.log 2 := by
  have := intervalIntegral.integral_mono_on (a := 1) (b := 2) (by norm_num)
    (f := fun s ↦ Real.log s) (g := fun _ ↦ Real.log 2) (intervalIntegral.intervalIntegrable_log' ) intervalIntegrable_const
    (fun s hs ↦ Real.log_le_log (by linarith [hs.1]) hs.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

lemma neg_two_le_P (ξ : ℝ) : -2 ≤ ∫ s in (1 : ℝ)..2, Real.log |s - ξ| := by
  have h := intervalIntegral.integral_comp_sub_right (a := 1) (b := 2)
    (fun v : ℝ ↦ Real.log |v|) ξ
  beta_reduce at h
  rw [h]
  have := neg_two_le_integral_log_abs (1 - ξ)
  have e : 1 - ξ + 1 = 2 - ξ := by ring
  rwa [e] at this

lemma P_le (ξ : ℝ) : ∫ s in (1 : ℝ)..2, Real.log |s - ξ| ≤ Real.log (|ξ| + 2) := by
  have := intervalIntegral.integral_mono_on (a := 1) (b := 2) (by norm_num)
    (f := fun s ↦ Real.log |s - ξ|) (g := fun _ ↦ Real.log (|ξ| + 2))
    (intervalIntegrable_log_abs_sub _ _ _) intervalIntegrable_const
    (fun s hs ↦ by
      refine log_le_log_of_nonneg (abs_nonneg _) (by linarith [abs_nonneg ξ]) ?_
      rw [abs_le]
      constructor <;> cases abs_cases ξ <;> linarith [hs.1, hs.2])
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

lemma le_P_of_large {ξ : ℝ} (hξ : 3 ≤ |ξ|) :
    Real.log |ξ| - Real.log 3 ≤ ∫ s in (1 : ℝ)..2, Real.log |s - ξ| := by
  have := intervalIntegral.integral_mono_on (a := 1) (b := 2) (by norm_num)
    (f := fun _ ↦ Real.log |ξ| - Real.log 3) (g := fun s ↦ Real.log |s - ξ|)
    intervalIntegrable_const (intervalIntegrable_log_abs_sub _ _ _)
    (fun s hs ↦ by
      have h3 : |ξ| / 3 ≤ |s - ξ| := by
        have : |ξ| ≤ |s - ξ| + |s| := by
          have := abs_sub_abs_le_abs_sub ξ s
          rw [abs_sub_comm ξ s] at this
          have := abs_sub (s - ξ) s
          rw [show s - ξ - s = -ξ by ring, abs_neg] at this
          linarith
        rw [abs_of_pos (by linarith [hs.1] : 0 < s)] at this
        linarith [hs.2]
      have hpos : 0 < |ξ| / 3 := by linarith
      calc Real.log |ξ| - Real.log 3 = Real.log (|ξ| / 3) := by
            rw [Real.log_div (by linarith) (by norm_num)]
        _ ≤ Real.log |s - ξ| := Real.log_le_log hpos h3)
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

theorem rampInt_estimate (ξ : ℝ) : |rampInt ξ - Real.log (max 1 |ξ|)| ≤ 4 := by
  rw [rampInt_eq]
  have h2 := Real.log_two_lt_d9
  have h3 := log_three_lt
  have hP := neg_two_le_P ξ
  have hPu := P_le ξ
  have hL0 := integral_log_one_two_nonneg
  have hL1 := integral_log_one_two_le
  have hℓ0 : 0 ≤ Real.log (max 1 |ξ|) := Real.log_nonneg (le_max_left _ _)
  rw [abs_le]
  constructor
  · by_cases hξ : |ξ| ≤ 3
    · have : Real.log (max 1 |ξ|) ≤ Real.log 3 :=
        Real.log_le_log (by positivity) (max_le (by norm_num) hξ)
      linarith
    · rw [not_le] at hξ
      have hl := le_P_of_large hξ.le
      rw [max_eq_right (by linarith)]
      linarith
  · have : Real.log (|ξ| + 2) ≤ Real.log (3 * max 1 |ξ|) := by
      refine Real.log_le_log (by positivity) ?_
      rcases le_total 1 |ξ| with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith [abs_nonneg ξ]
    rw [Real.log_mul (by norm_num) (by positivity)] at this
    linarith

lemma intervalIntegrable_g {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ Real.log ‖1 - (x : ℂ) / t‖) volume a b := by
  have h1 := (intervalIntegrable_log_abs_sub x a b).sub
    (intervalIntegral.intervalIntegrable_log' (a := a) (b := b))
  refine h1.congr_ae ?_
  have hae : ∀ᵐ t ∂(volume.restrict (Ι a b)), t ≠ x := ae_restrict_of_ae (OCS.ae_ne_real x)
  filter_upwards [hae, ae_restrict_mem measurableSet_uIoc] with t ht1 ht2
  have : 0 < t := by
    rw [Set.mem_uIoc] at ht2
    rcases ht2 with h | h <;> linarith [h.1]
  exact (log_norm_one_sub_div_real x t this ht1).symm

theorem rampPot_estimate' {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |(1 / a) * (∫ t in a..2 * a, Real.log ‖1 - (x : ℂ) / t‖) - Real.log (max 1 (|x| / a))| ≤ 4 := by
  have h := intervalIntegral.integral_comp_mul_left (a := 1) (b := 2)
    (fun t : ℝ ↦ Real.log ‖1 - (x : ℂ) / t‖) ha.ne'
  have e : (1 / a) * (∫ t in a..2 * a, Real.log ‖1 - (x : ℂ) / t‖) = rampInt (x / a) := by
    unfold rampInt
    have h' : ∫ s in (1 : ℝ)..2, Real.log ‖1 - (x / a : ℝ) / (s : ℂ)‖ =
        ∫ s in (1 : ℝ)..2, Real.log ‖1 - (x : ℂ) / ((a * s : ℝ) : ℂ)‖ := by
      refine intervalIntegral.integral_congr (fun s hs ↦ ?_)
      have : (x : ℂ) / ((a * s : ℝ) : ℂ) = ((x / a : ℝ) : ℂ) / (s : ℂ) := by
        push_cast; rcases eq_or_ne (s : ℂ) 0 with h0 | h0
        · simp [h0]
        · field_simp
      rw [this]
    rw [h']
    rw [mul_one] at h
    simp only [smul_eq_mul] at h ⊢
    rw [h]
    field_simp
  rw [e]
  have := rampInt_estimate (x / a)
  rwa [abs_div, abs_of_pos ha] at this

/-- **Ramp potential** (as stated in the scaffold: the binder of `∫` swallows `- log max ..`). -/
theorem rampPot_estimate {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |(1 / a) * ∫ t in a..2 * a, Real.log ‖1 - (x : ℂ) / t‖ - Real.log (max 1 (|x| / a))| ≤ 4 := by
  have hg := intervalIntegrable_g ha (by linarith : 0 < 2 * a) x
  rw [intervalIntegral.integral_sub hg intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul]
  have := rampPot_estimate' ha x
  have e : (1 / a) * ((∫ t in a..2 * a, Real.log ‖1 - (x : ℂ) / t‖) -
      (2 * a - a) * Real.log (max 1 (|x| / a))) =
      (1 / a) * (∫ t in a..2 * a, Real.log ‖1 - (x : ℂ) / t‖) - Real.log (max 1 (|x| / a)) := by
    field_simp; ring
  rw [e]; exact this

end T2ii

end FF
