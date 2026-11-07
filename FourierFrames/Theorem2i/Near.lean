import FourierFrames.Theorem2i.Riemann
import FourierFrames.Theorem2i.NearAux

/-!
# M08 helper (D2): the near cells (blueprint §6.7)
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

namespace D2

theorem norm_sub_real (z : ℂ) (s : ℝ) (hz : z.im = 0) : ‖(s : ℂ) - z‖ = |s - z.re| := by
  have hzr : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  have : (s : ℂ) - z = ((s - z.re : ℝ) : ℂ) := by rw [Complex.ofReal_sub, ← hzr]
  rw [this, Complex.norm_real, Real.norm_eq_abs]

theorem integrableOn_log_norm_sub (z : ℂ) (a b : ℝ) :
    IntegrableOn (fun s : ℝ => Real.log ‖(s : ℂ) - z‖) (Ioc a b) := by
  by_cases hz : z.im = 0
  · have : (fun s : ℝ => Real.log ‖(s : ℂ) - z‖) = fun s => Real.log |s - z.re| := by
      funext s; rw [norm_sub_real z s hz]
    rw [this]
    exact integrableOn_log_abs_sub z.re a b
  · have hc : ContinuousOn (fun s : ℝ => Real.log ‖(s : ℂ) - z‖) (Icc a b) := by
      refine ContinuousOn.log (by fun_prop) fun s _ => ?_
      intro h0
      have := congrArg Complex.im (norm_eq_zero.mp h0)
      simp at this
      exact hz this
    exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self

/-- `log ‖1 - w / a‖ = log ‖a - w‖ - log ‖a‖`. -/
theorem log_norm_one_sub_div {w a : ℂ} (ha : a ≠ 0) (hwa : a - w ≠ 0) :
    Real.log ‖1 - w / a‖ = Real.log ‖a - w‖ - Real.log ‖a‖ := by
  have : 1 - w / a = (a - w) / a := by field_simp
  rw [this, norm_div, Real.log_div (norm_ne_zero_iff.mpr hwa) (norm_ne_zero_iff.mpr ha)]

end D2

/-- Near cells (blueprint §6.7) for an arbitrary distance constant `k > 0`
(`abs_cellTerm_near` is the case `k = K0 C`). -/
theorem RegData.abs_cellTerm_near_gen (h : RegData ψ t C M) (hK : DensBound ψ t K) {n : ℕ}
    (hn : 1 ≤ n) {z : ℂ} (hz : 0 ≤ z.im) {k : ℝ} (hk : 0 < k)
    (hnear : ‖z - (rCentre ψ t n : ℂ)‖ < k * cellLen t n) :
    |cellTerm ψ t C n z| ≤ 2 * K + Real.log (k + 1) +
      Real.log (Real.pi / (2 * cAngle ψ t C)) := by
  have hd := D2.cellLen_pos h hn
  obtain ⟨hr1, hr2⟩ := h.rCentre_mem hn
  have ht0 := D2.t_nonneg h (n - 1)
  have hr0 : 0 < rCentre ψ t n := lt_of_le_of_lt ht0 hr1
  have hc0 := h.cAngle_pos
  have hc1 := h.cAngle_lt
  have hpi := Real.pi_pos
  set d := cellLen t n with hd_def
  set r := rCentre ψ t n with hr_def
  set c := cAngle ψ t C with hc_def
  set zn := zPt ψ t C n with hzn_def
  have hznorm : ‖zn‖ = r := h.norm_zPt hn
  have him : zn.im ≤ -(2 / Real.pi * (c * d)) := h.im_zPt_le hn
  have hdist : ‖zn - (r : ℂ)‖ ≤ c * d := h.norm_zPt_sub_le hn
  have hcd : 0 < 2 / Real.pi * (c * d) := by positivity
  have hzn0 : zn ≠ 0 := by
    intro h0; rw [h0] at hznorm; simp at hznorm; linarith
  -- derivative facts
  have hp : Continuous (deriv ψ) := h.adm.1.continuous_deriv le_rfl
  have hp0 : ∀ s, 0 ≤ deriv ψ s := fun s => h.adm.2.1.deriv_nonneg
  have hpK : ∀ s ∈ Ioc (t (n - 1)) (t n), deriv ψ s ≤ K / (t n - t (n - 1)) :=
    fun s hs => hK n hn s (Ioc_subset_Icc_self hs)
  have hint : ∫ s in Ioc (t (n - 1)) (t n), deriv ψ s = 1 := h.integral_cell hn
  have hab : t (n - 1) < t n := by
    have := h.mono (show n - 1 < n by omega); exact this
  have hK0 : 0 ≤ K := by
    have h1 := hpK (t n) ⟨hab, le_rfl⟩
    have h2 := hp0 (t n)
    have h3 : 0 ≤ K / d := le_trans h2 h1
    exact (div_nonneg_iff.mp h3).elim (fun h => h.1) (fun h => by linarith [h.2, hd])
  -- the distance from z_n to z
  have hznz_lo : 2 / Real.pi * (c * d) ≤ ‖zn - z‖ := by
    have h1 : |(zn - z).im| ≤ ‖zn - z‖ := Complex.abs_im_le_norm _
    have h2 : (zn - z).im = zn.im - z.im := by simp
    have h3 : -(2 / Real.pi * (c * d)) ≥ zn.im := him
    rw [abs_of_neg (by rw [h2]; linarith)] at h1
    rw [h2] at h1; linarith
  have hzz : 0 < ‖zn - z‖ := lt_of_lt_of_le hcd hznz_lo
  have hznz_hi : ‖zn - z‖ ≤ (k + 1) * d := by
    have h1 : ‖zn - z‖ ≤ ‖zn - (r : ℂ)‖ + ‖z - (r : ℂ)‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub zn (r : ℂ) z
      rwa [norm_sub_rev (r : ℂ) z] at this
    have : c < 1 := by linarith [Real.pi_lt_four]
    nlinarith
  set L' := Real.log ‖zn - z‖ with hL'
  -- integrability
  have hG : IntegrableOn (fun s : ℝ => Real.log ‖(s : ℂ) - z‖) (Ioc (t (n - 1)) (t n)) :=
    D2.integrableOn_log_norm_sub z _ _
  have hI1 : IntegrableOn (fun s : ℝ => (Real.log ‖(s : ℂ) - z‖ - L') * deriv ψ s)
      (Ioc (t (n - 1)) (t n)) :=
    (hG.sub (integrableOn_const (by simp))).mul_continuousOn_of_subset hp.continuousOn
      measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  have hlog : IntegrableOn Real.log (Ioc (t (n - 1)) (t n)) :=
    (intervalIntegral.intervalIntegrable_log' (a := t (n - 1)) (b := t n)).1
  have hI2 : IntegrableOn (fun s : ℝ => (Real.log s - Real.log r) * deriv ψ s)
      (Ioc (t (n - 1)) (t n)) :=
    (hlog.sub (integrableOn_const (by simp))).mul_continuousOn_of_subset hp.continuousOn
      measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ z.re := by
    simpa using (Set.countable_singleton z.re).ae_notMem volume
  -- Step A: `cellTerm = B`
  set B := ∫ s in Ioc (t (n - 1)) (t n), (Real.log ‖(s : ℂ) - z‖ - L') * deriv ψ s with hB
  have hA : cellTerm ψ t C n z = B := by
    have h0 : ∫ s in Ioc (t (n - 1)) (t n), (Real.log s - Real.log r) * deriv ψ s = 0 :=
      h.integral_log_sub_centre hn
    have : cellTerm ψ t C n z = ∫ s in Ioc (t (n - 1)) (t n),
        ((Real.log ‖(s : ℂ) - z‖ - L') * deriv ψ s - (Real.log s - Real.log r) * deriv ψ s) := by
      unfold cellTerm
      refine setIntegral_congr_ae measurableSet_Ioc ?_
      filter_upwards [hae] with s hs hsc
      have hs0 : 0 < s := lt_of_le_of_lt ht0 hsc.1
      have hsz : (s : ℂ) - z ≠ 0 := by
        intro h0; apply hs
        have := congrArg Complex.re h0; simp at this; linarith
      have e1 := D2.log_norm_one_sub_div (w := z) (a := (s : ℂ)) (by exact_mod_cast hs0.ne') hsz
      have e2 := D2.log_norm_one_sub_div (w := z) (a := zn) hzn0 (sub_ne_zero.mpr (by
        intro h0; rw [h0] at hzz; simp at hzz))
      have e3 : Real.log ‖(s : ℂ)‖ = Real.log s := by
        rw [Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
      rw [e1, e2, e3, hznorm]
      ring
    rw [this, integral_sub hI1 hI2, h0, sub_zero]
  rw [hA]
  have hpint : IntegrableOn (deriv ψ) (Ioc (t (n - 1)) (t n)) := hp.integrableOn_Ioc
  have hsr : ∀ s ∈ Ioc (t (n - 1)) (t n), ‖(s : ℂ) - z‖ ≤ (k + 1) * d := by
    intro s hsc
    have h1 : ‖(s : ℂ) - (r : ℂ)‖ ≤ d := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact D2.abs_sub_centre_le h hn hsc
    have h2 : ‖(s : ℂ) - z‖ ≤ ‖(s : ℂ) - (r : ℂ)‖ + ‖(r : ℂ) - z‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev (r : ℂ) z] at h2
    nlinarith
  have hpos : ∀ s : ℝ, s ≠ z.re → 0 < ‖(s : ℂ) - z‖ := by
    intro s hs
    refine norm_pos_iff.mpr fun h0 => hs ?_
    have := congrArg Complex.re h0; simp at this; linarith
  have hUe : Real.log ((k + 1) * d) - Real.log (2 / Real.pi * (c * d)) =
      Real.log (k + 1) + Real.log (Real.pi / (2 * c)) := by
    rw [← Real.log_div (by positivity) hcd.ne']
    have : (k + 1) * d / (2 / Real.pi * (c * d)) = (k + 1) * (Real.pi / (2 * c)) := by
      field_simp
    rw [this, Real.log_mul (by positivity) (by positivity)]
  have hup : B ≤ Real.log (k + 1) + Real.log (Real.pi / (2 * c)) := by
    have hmono : B ≤ ∫ s in Ioc (t (n - 1)) (t n),
        (Real.log (k + 1) + Real.log (Real.pi / (2 * c))) * deriv ψ s := by
      refine integral_mono_ae hI1 (hpint.const_mul _) ?_
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hae] with s hs hsc
      have h1 := Real.log_le_log (hpos s hs) (hsr s hsc)
      have h2 := Real.log_le_log hcd hznz_lo
      refine mul_le_mul_of_nonneg_right ?_ (hp0 s)
      rw [← hUe]; simp only [hL']; linarith
    rwa [MeasureTheory.integral_const_mul, hint, mul_one] at hmono
  have hlogabs : IntegrableOn (fun s : ℝ => Real.log |s - z.re|) (Ioc (t (n - 1)) (t n)) :=
    D2.integrableOn_log_abs_sub z.re _ _
  have hlow : -(2 * K) - Real.log (k + 1) ≤ B := by
    set E := Real.log ((k + 1) * d) with hE
    have hlogp : IntegrableOn (fun s : ℝ => Real.log |s - z.re| * deriv ψ s)
        (Ioc (t (n - 1)) (t n)) :=
      hlogabs.mul_continuousOn_of_subset hp.continuousOn measurableSet_Ioc isCompact_Icc
        Ioc_subset_Icc_self
    have hI3 : IntegrableOn (fun s : ℝ => (Real.log |s - z.re| - E) * deriv ψ s)
        (Ioc (t (n - 1)) (t n)) :=
      (hlogabs.sub (integrableOn_const (by simp))).mul_continuousOn_of_subset hp.continuousOn
        measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
    have hmono : ∫ s in Ioc (t (n - 1)) (t n), (Real.log |s - z.re| - E) * deriv ψ s ≤ B := by
      refine integral_mono_ae hI3 hI1 ?_
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hae] with s hs hsc
      have hxs : 0 < |s - z.re| := abs_pos.mpr (sub_ne_zero.mpr hs)
      have h1 : |s - z.re| ≤ ‖(s : ℂ) - z‖ := by
        have := Complex.abs_re_le_norm ((s : ℂ) - z)
        simpa using this
      have h2 := Real.log_le_log hxs h1
      have h3 := Real.log_le_log hzz hznz_hi
      refine mul_le_mul_of_nonneg_right ?_ (hp0 s)
      simp only [hL'] at *; linarith
    have heq : ∫ s in Ioc (t (n - 1)) (t n), (Real.log |s - z.re| - E) * deriv ψ s =
        (∫ s in Ioc (t (n - 1)) (t n), Real.log |s - z.re| * deriv ψ s) - E := by
      simp_rw [sub_mul]
      rw [integral_sub hlogp (hpint.const_mul E), MeasureTheory.integral_const_mul, hint, mul_one]
    have hlowI := D2.lower_log_integral hab hp hp0 hpK hint (x := z.re)
    have hE2 : E = Real.log (k + 1) + Real.log d := by
      rw [hE, Real.log_mul (by positivity) hd.ne']
    have hdd : t n - t (n - 1) = d := rfl
    rw [hdd] at hlowI
    linarith
  have hl0 : 0 ≤ Real.log (Real.pi / (2 * c)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_four, Real.pi_gt_three]
  have hk0 : 0 ≤ Real.log (k + 1) := Real.log_nonneg (by linarith)
  rw [abs_le]
  constructor <;> linarith

end FF
