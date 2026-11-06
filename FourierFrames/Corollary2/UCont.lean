import FourierFrames.Corollary2.LogInt

/-!
# M07 -- helper lemmas for `Corollary2.lean`: continuity of the potential of a continuous density

For a continuous bounded `g`, `z ↦ ∫ potKernel z t * g t dt` is continuous on `ℂ`.  The integral is
split as `a + b + c` according to the window `|t - Re z| ≤ 1`; the logarithmic singularity (`b`) is
handled in the translated variable `s = t - Re z`, where it becomes `log |s - i y|`, dominated by a
fixed integrable function, while `g (s + x)` varies continuously.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF


/-- Indicator of the window `|t - x| ≤ 1`. -/
def win (x t : ℝ) : ℝ := (Icc (x - 1) (x + 1)).indicator (fun _ ↦ (1 : ℝ)) t

theorem win_nonneg (x t : ℝ) : 0 ≤ win x t := by
  unfold win; exact indicator_nonneg (fun _ _ ↦ zero_le_one) t

theorem win_le_one (x t : ℝ) : win x t ≤ 1 := by
  unfold win
  by_cases h : t ∈ Icc (x - 1) (x + 1)
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h]; exact zero_le_one

theorem win_eq_zero {x t : ℝ} (h : 1 < |t - x|) : win x t = 0 := by
  unfold win
  apply indicator_of_notMem
  intro hm
  have := abs_le.mpr (⟨by linarith [hm.1], by linarith [hm.2]⟩ : -1 ≤ t - x ∧ t - x ≤ 1)
  linarith

theorem abs_sub_le_of_win_ne {x t : ℝ} (h : win x t ≠ 0) : |t - x| ≤ 1 := by
  by_contra hc
  exact h (win_eq_zero (not_le.mp hc))

theorem win_eq_one {x t : ℝ} (h : |t - x| ≤ 1) : win x t = 1 := by
  unfold win
  have := abs_le.mp h
  rw [indicator_of_mem (show t ∈ Icc (x - 1) (x + 1) from ⟨by linarith [this.1], by linarith [this.2]⟩)]

theorem measurable_win (x : ℝ) : Measurable (win x) :=
  measurable_const.indicator measurableSet_Icc

theorem continuousAt_win {x₀ t : ℝ} (h1 : t ≠ x₀ - 1) (h2 : t ≠ x₀ + 1) :
    ContinuousAt (fun x : ℝ ↦ win x t) x₀ := by
  rcases lt_or_ge (|t - x₀|) 1 with h | h
  · have hn : {x : ℝ | |t - x| < 1} ∈ 𝓝 x₀ :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using h)
    refine (continuousAt_const (y := (1 : ℝ))).congr ?_
    filter_upwards [hn] with x hx
    exact (win_eq_one (le_of_lt hx)).symm
  · have h' : 1 < |t - x₀| := by
      rcases eq_or_lt_of_le h with h | h
      · exfalso
        have := (abs_eq (zero_le_one)).mp h.symm
        rcases this with h | h
        · exact h2 (by linarith)
        · exact h1 (by linarith)
      · exact h
    have hn : {x : ℝ | 1 < |t - x|} ∈ 𝓝 x₀ :=
      (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simpa [abs_sub_comm] using h')
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [hn] with x hx
    exact (win_eq_zero hx).symm


/-- Piece `a`: outside the window. -/
def aF (g : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℝ := (1 - win z.re t) * (potKernel z t * g t)

/-- Piece `b`: the logarithmic singularity inside the window. -/
def bF (g : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℝ := win z.re t * (Real.log ‖(t : ℂ) - z‖ * g t)

/-- Piece `c`: the smooth remainder inside the window. -/
def cF (g : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  win z.re t * ((-Real.log (|t|) + chi t * (z.re / t)) * g t)

theorem potKernel_mul_eq_abc (g : ℝ → ℝ) (z : ℂ) {t : ℝ} (ht0 : t ≠ 0) (ht : t ≠ z.re) :
    potKernel z t * g t = aF g z t + bF g z t + cF g z t := by
  unfold aF bF cF
  rw [potKernel_eq_of_ne z ht0 ht]
  ring

theorem measurable_aF {g : ℝ → ℝ} (hg : Measurable g) (z : ℂ) : Measurable (aF g z) := by
  unfold aF
  exact (measurable_const.sub (measurable_win z.re)).mul ((measurable_potKernel z).mul hg)

theorem measurable_bF {g : ℝ → ℝ} (hg : Measurable g) (z : ℂ) : Measurable (bF g z) := by
  unfold bF
  exact (measurable_win z.re).mul ((measurable_log_norm_sub z).mul hg)

theorem measurable_cF {g : ℝ → ℝ} (hg : Measurable g) (z : ℂ) : Measurable (cF g z) := by
  unfold cF
  refine (measurable_win z.re).mul (Measurable.mul (Measurable.add ?_ ?_) hg)
  · exact (Real.measurable_log.comp measurable_id.abs).neg
  · exact measurable_chi.mul (measurable_const.div measurable_id)

/-- Bound for piece `c`. -/
def cBound (M R : ℝ) (t : ℝ) : ℝ :=
  (Icc (-(R + 1)) (R + 1)).indicator (fun t ↦ (|Real.log ‖(t : ℂ) - 0‖| + R) * M) t

theorem integrable_cBound (M R : ℝ) : Integrable (cBound M R) := by
  unfold cBound
  rw [integrable_indicator_iff measurableSet_Icc]
  exact (((integrableOn_log_norm_sub 0 (R + 1)).abs).add (integrableOn_const (by simp))).mul_const M

theorem abs_cF_le {g : ℝ → ℝ} {M : ℝ} (hM : ∀ t, |g t| ≤ M) {R : ℝ} {z : ℂ} (hzR : ‖z‖ ≤ R)
    (t : ℝ) : ‖cF g z t‖ ≤ cBound M R t := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hzR
  unfold cBound
  rw [Real.norm_eq_abs]
  by_cases hw : win z.re t = 0
  · unfold cF; rw [hw, zero_mul, abs_zero]
    exact indicator_nonneg (fun s _ ↦ by positivity) t
  · have h1 := abs_sub_le_of_win_ne hw
    have hx : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hzR
    have ht : t ∈ Icc (-(R + 1)) (R + 1) := by
      have := abs_le.mp h1
      have := abs_le.mp hx
      constructor <;> linarith
    rw [indicator_of_mem ht]
    unfold cF
    rw [abs_mul, abs_of_nonneg (win_nonneg _ _), abs_mul]
    have h2 : |(-Real.log (|t|) + chi t * (z.re / t))| ≤ |Real.log ‖(t : ℂ) - 0‖| + R := by
      calc |(-Real.log (|t|) + chi t * (z.re / t))| ≤ |(-Real.log (|t|))| + |chi t * (z.re / t)| := abs_add_le _ _
        _ ≤ |Real.log ‖(t : ℂ) - 0‖| + R := by
            rw [abs_neg]
            have e : Real.log ‖(t : ℂ) - 0‖ = Real.log (|t|) := by simp
            rw [e]
            have : |chi t * (z.re / t)| ≤ |z.re| := by
              have : chi t * (z.re / t) = (chi t / t) * z.re := by ring
              rw [this, abs_mul]
              calc |chi t / t| * |z.re| ≤ 1 * |z.re| :=
                    mul_le_mul_of_nonneg_right (abs_chi_div_le t) (abs_nonneg _)
                _ = |z.re| := one_mul _
            linarith
    calc win z.re t * (|(-Real.log (|t|) + chi t * (z.re / t))| * |g t|)
        ≤ 1 * ((|Real.log ‖(t : ℂ) - 0‖| + R) * M) := by
          gcongr
          · exact win_le_one _ _
          · exact hM t
        _ = _ := one_mul _

theorem continuousAt_integral_cF {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M)
    (z₀ : ℂ) : ContinuousAt (fun z ↦ ∫ t, cF g z t) z₀ := by
  set R : ℝ := ‖z₀‖ + 1 with hR
  refine continuousAt_of_dominated (bound := cBound M R) ?_ ?_ (integrable_cBound M R) ?_
  · exact Eventually.of_forall fun z ↦ (measurable_cF hg z).aestronglyMeasurable
  · have : ∀ᶠ z in 𝓝 z₀, ‖z‖ ≤ R := by
      filter_upwards [ball_mem_nhds z₀ one_pos] with z hz
      have h1 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ R := by rw [hR]; linarith
    filter_upwards [this] with z hz
    exact ae_of_all _ fun t ↦ abs_cF_le hM hz t
  · have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({z₀.re - 1, z₀.re + 1} : Set ℝ) :=
      (Set.toFinite _).countable.ae_notMem volume
    filter_upwards [hnull] with t ht
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
    unfold cF
    have h1 : ContinuousAt (fun z : ℂ ↦ win z.re t) z₀ :=
      (continuousAt_win ht.1 ht.2).comp (f := fun z : ℂ ↦ z.re) Complex.continuous_re.continuousAt
    have h2 : Continuous fun z : ℂ ↦ (-Real.log (|t|) + chi t * (z.re / t)) * g t := by fun_prop
    exact h1.mul h2.continuousAt


/-- Bound for piece `a`. -/
def aBound (M R : ℝ) (t : ℝ) : ℝ :=
  (Icc (-(2 * R + 2)) (2 * R + 2)).indicator
      (fun t ↦ (Real.log (2 * R + 2 + R) + |Real.log ‖(t : ℂ) - 0‖| + R) * M) t +
    ((Icc (-(2 * R + 2)) (2 * R + 2))ᶜ).indicator (fun t ↦ M * R ^ 2 * (t ^ 2)⁻¹) t

theorem integrable_aBound (M : ℝ) {R : ℝ} (hR : 0 ≤ R) : Integrable (aBound M R) := by
  have hT : 0 < 2 * R + 2 := by linarith
  unfold aBound
  refine Integrable.add ?_ ?_
  · rw [integrable_indicator_iff measurableSet_Icc]
    exact ((((integrableOn_const (by simp)).add ((integrableOn_log_norm_sub 0 (2 * R + 2)).abs)).add
      (integrableOn_const (by simp)))).mul_const M
  · rw [integrable_indicator_iff measurableSet_Icc.compl]
    exact (far_inv_sq hT).1.const_mul _

theorem potKernel_zero (z : ℂ) : potKernel z 0 = 0 := by
  simp [potKernel]

theorem abs_aF_le {g : ℝ → ℝ} {M : ℝ} (hM : ∀ t, |g t| ≤ M) {R : ℝ} {z : ℂ} (hzR : ‖z‖ ≤ R)
    (t : ℝ) : ‖aF g z t‖ ≤ aBound M R t := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hzR
  have hlogT : 0 ≤ Real.log (2 * R + 2 + R) := Real.log_nonneg (by linarith)
  unfold aBound
  rw [Real.norm_eq_abs]
  by_cases hw : |t - z.re| ≤ 1
  · unfold aF; rw [win_eq_one hw, sub_self, zero_mul, abs_zero]
    exact add_nonneg (indicator_nonneg (fun s _ ↦ by positivity) t)
      (indicator_nonneg (fun s _ ↦ by positivity) t)
  · push Not at hw
    unfold aF
    rw [win_eq_zero hw, sub_zero, one_mul, abs_mul]
    by_cases ht : t ∈ Icc (-(2 * R + 2)) (2 * R + 2)
    · rw [indicator_of_mem ht, indicator_of_notMem (by simpa using ht), add_zero]
      by_cases h0 : t = 0
      · subst h0; rw [potKernel_zero]; simp
        exact mul_nonneg (by positivity) hM0
      · have hne : t ≠ z.re := by
          intro h; rw [h, sub_self, abs_zero] at hw; linarith
        have hk := potKernel_eq_of_ne z h0 hne
        have hge : 1 < ‖(t : ℂ) - z‖ := by
          refine lt_of_lt_of_le hw ?_
          have := Complex.abs_re_le_norm ((t : ℂ) - z)
          simpa using this
        have hle : ‖(t : ℂ) - z‖ ≤ 2 * R + 2 + R := by
          calc ‖(t : ℂ) - z‖ ≤ ‖(t : ℂ)‖ + ‖z‖ := norm_sub_le _ _
            _ ≤ 2 * R + 2 + R := by
                have : ‖(t : ℂ)‖ = |t| := by simp
                rw [this]; linarith [abs_le.mpr ⟨ht.1, ht.2⟩]
        have hl1 : 0 ≤ Real.log ‖(t : ℂ) - z‖ := Real.log_nonneg hge.le
        have hl2 : Real.log ‖(t : ℂ) - z‖ ≤ Real.log (2 * R + 2 + R) :=
          Real.log_le_log (by linarith) hle
        have hchi : |chi t * (z.re / t)| ≤ R := by
          have e : chi t * (z.re / t) = (chi t / t) * z.re := by ring
          rw [e, abs_mul]
          calc |chi t / t| * |z.re| ≤ 1 * |z.re| :=
                mul_le_mul_of_nonneg_right (abs_chi_div_le t) (abs_nonneg _)
            _ ≤ R := by rw [one_mul]; exact (Complex.abs_re_le_norm z).trans hzR
        have hk' : |potKernel z t| ≤ Real.log (2 * R + 2 + R) + |Real.log ‖(t : ℂ) - 0‖| + R := by
          rw [hk]
          have e : Real.log ‖(t : ℂ) - 0‖ = Real.log (|t|) := by simp
          rw [e]
          calc |Real.log ‖(t : ℂ) - z‖ - Real.log (|t|) + chi t * (z.re / t)|
              ≤ |Real.log ‖(t : ℂ) - z‖ - Real.log (|t|)| + |chi t * (z.re / t)| := abs_add_le _ _
            _ ≤ (|Real.log ‖(t : ℂ) - z‖| + |Real.log (|t|)|) + R := by
                gcongr; exact abs_sub _ _
            _ ≤ _ := by rw [abs_of_nonneg hl1]; linarith
        exact mul_le_mul hk' (hM t) (abs_nonneg _) (by positivity)
    · rw [indicator_of_notMem ht, indicator_of_mem (by simpa using ht), zero_add]
      have htT : 2 * R + 2 < |t| := by
        simp only [mem_Icc, not_and_or, not_le] at ht
        rcases ht with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have h1 := abs_potKernel_le_far z (by linarith) (by linarith : ‖z‖ ≤ |t| / 2)
      calc |potKernel z t| * |g t| ≤ (‖z‖ ^ 2 / t ^ 2) * M :=
            mul_le_mul h1 (hM t) (abs_nonneg _) (by positivity)
        _ ≤ (R ^ 2 / t ^ 2) * M := by gcongr
        _ = M * R ^ 2 * (t ^ 2)⁻¹ := by ring


theorem continuousAt_potKernel {z₀ : ℂ} {t : ℝ} (ht : t ≠ 0) (hne : z₀ ≠ (t : ℂ)) :
    ContinuousAt (fun z ↦ potKernel z t) z₀ := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hne' : (1 : ℂ) - z₀ / (t : ℂ) ≠ 0 := by
    intro h; apply hne
    have : z₀ / (t : ℂ) = 1 := by linear_combination -h
    field_simp at this; exact this
  unfold potKernel
  refine ContinuousAt.add ?_ ?_
  · refine (Real.continuousAt_log ?_).comp (f := fun z : ℂ ↦ ‖1 - z / (t : ℂ)‖) ?_
    · simpa using hne'
    · exact (continuous_norm.comp (by fun_prop : Continuous fun z : ℂ ↦ 1 - z / (t : ℂ))).continuousAt
  · exact (continuous_const.mul (Complex.continuous_re.comp
      (continuous_id.div_const (t : ℂ)))).continuousAt

theorem continuousAt_integral_aF {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M)
    (z₀ : ℂ) : ContinuousAt (fun z ↦ ∫ t, aF g z t) z₀ := by
  set R : ℝ := ‖z₀‖ + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  refine continuousAt_of_dominated (bound := aBound M R) ?_ ?_ (integrable_aBound M hR0) ?_
  · exact Eventually.of_forall fun z ↦ (measurable_aF hg z).aestronglyMeasurable
  · have : ∀ᶠ z in 𝓝 z₀, ‖z‖ ≤ R := by
      filter_upwards [ball_mem_nhds z₀ one_pos] with z hz
      have h1 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ R := by rw [hR]; linarith
    filter_upwards [this] with z hz
    exact ae_of_all _ fun t ↦ abs_aF_le hM hz t
  · have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({0, z₀.re - 1, z₀.re + 1} : Set ℝ) :=
      (Set.toFinite _).countable.ae_notMem volume
    filter_upwards [hnull] with t ht
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
    obtain ⟨ht0, h1, h2⟩ := ht
    rcases lt_or_gt_of_ne (show |t - z₀.re| ≠ 1 from fun h ↦ by
        rcases (abs_eq zero_le_one).mp h with h | h
        · exact h2 (by linarith)
        · exact h1 (by linarith)) with h | h
    · -- inside the window: eventually zero
      have hn : {z : ℂ | |t - z.re| < 1} ∈ 𝓝 z₀ :=
        (isOpen_lt (by fun_prop) continuous_const).mem_nhds h
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hn] with z hz
      unfold aF
      rw [win_eq_one (le_of_lt hz), sub_self, zero_mul]
    · -- outside the window: eventually the kernel
      have hn : {z : ℂ | 1 < |t - z.re|} ∈ 𝓝 z₀ :=
        (isOpen_lt continuous_const (by fun_prop)).mem_nhds h
      have hne : z₀ ≠ (t : ℂ) := by
        intro hc; rw [hc] at h; simp at h; linarith
      have hc : ContinuousAt (fun z ↦ potKernel z t * g t) z₀ :=
        (continuousAt_potKernel ht0 hne).mul continuousAt_const
      refine hc.congr ?_
      filter_upwards [hn] with z hz
      unfold aF
      rw [win_eq_zero hz, sub_zero, one_mul]




/-- The window of the singular kernel: `-log |t - x|` on `|t - x| ≤ a`. -/
def sing (x a : ℝ) (t : ℝ) : ℝ := (Icc (x - a) (x + a)).indicator (fun t ↦ -Real.log |t - x|) t

theorem sing_nonneg {x a : ℝ} (ha : a ≤ 1) (t : ℝ) : 0 ≤ sing x a t := by
  unfold sing
  by_cases h : t ∈ Icc (x - a) (x + a)
  · rw [indicator_of_mem h]
    have : |t - x| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [h.1, h.2]
    have := Real.log_nonpos (abs_nonneg _) this
    linarith
  · rw [indicator_of_notMem h]

theorem integral_sing {x a : ℝ} (ha : 0 < a) :
    ∫ t, sing x a t = 2 * a * (1 - Real.log a) := by
  unfold sing
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h1 : ∀ t : ℝ, -Real.log |t - x| = (fun u : ℝ ↦ -Real.log u) (t - x) := fun t ↦ by
    simp [Real.log_abs]
  simp_rw [h1]
  rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ ↦ -Real.log u) x]
  simp only [sub_sub_cancel_left, add_sub_cancel_left]
  rw [intervalIntegral.integral_neg, integral_log]
  simp [Real.log_neg_eq_log]
  ring


theorem integrable_sing (x : ℝ) {a : ℝ} (ha : 0 ≤ a) : Integrable (sing x a) := by
  unfold sing
  rw [integrable_indicator_iff measurableSet_Icc]
  have h1 : IntervalIntegrable (fun t : ℝ ↦ Real.log (t - x)) volume (x - a) (x + a) := by
    have := (intervalIntegral.intervalIntegrable_log' (a := x - a - x) (b := x + a - x)).comp_sub_right x
    simpa only [sub_add_cancel] using this
  have h2 := (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : x - a ≤ x + a)).mp h1
  refine h2.neg.congr_fun (fun t _ ↦ ?_) measurableSet_Icc
  simp [Real.log_abs]

/-- Pointwise: on the tail set the kernel is bounded by `M * sing`. -/
theorem abs_bF_le_sing {g : ℝ → ℝ} {M : ℝ} (hM : ∀ t, |g t| ≤ M) {R : ℝ} {z : ℂ}
    (hzR : ‖z‖ ≤ R) {C : ℝ} (hC : M * Real.log (1 + R) < C) (hC0 : 0 < C) (hM0 : 0 < M)
    {t : ℝ} (ht : t ≠ z.re) (hS : C ≤ |bF g z t|) :
    |bF g z t| ≤ M * sing z.re (Real.exp (-C / M)) t := by
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hzR
  unfold bF at hS ⊢
  have hw : win z.re t ≠ 0 := by
    intro h; rw [h, zero_mul, abs_zero] at hS; linarith
  have hwin := abs_sub_le_of_win_ne hw
  rw [win_eq_one hwin, one_mul] at hS ⊢
  have hlogt : C ≤ |Real.log ‖(t : ℂ) - z‖| * M := by
    refine hS.trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg _)
  have hs0 : 0 < ‖(t : ℂ) - z‖ := by
    rcases (norm_nonneg ((t : ℂ) - z)).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, Real.log_zero, abs_zero, zero_mul] at hlogt; linarith
  have hx : |t - z.re| ≤ ‖(t : ℂ) - z‖ := by
    have := Complex.abs_re_le_norm ((t : ℂ) - z)
    simpa using this
  have hup : ‖(t : ℂ) - z‖ ≤ 1 + R := by
    calc ‖(t : ℂ) - z‖ = ‖((t : ℂ) - (z.re : ℂ)) + ((z.re : ℂ) - z)‖ := by ring_nf
      _ ≤ ‖(t : ℂ) - (z.re : ℂ)‖ + ‖(z.re : ℂ) - z‖ := norm_add_le _ _
      _ ≤ 1 + R := by
          have h1 : ‖(t : ℂ) - (z.re : ℂ)‖ ≤ 1 := by
            rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hwin
          have h2 : ‖(z.re : ℂ) - z‖ ≤ ‖z‖ := by
            have : (z.re : ℂ) - z = -(z.im : ℂ) * Complex.I := by
              apply Complex.ext <;> simp
            rw [this, norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
            exact Complex.abs_im_le_norm z
          linarith
  have hneg : Real.log ‖(t : ℂ) - z‖ < 0 := by
    by_contra hnn
    push Not at hnn
    rw [abs_of_nonneg hnn] at hlogt
    have : Real.log ‖(t : ℂ) - z‖ ≤ Real.log (1 + R) := Real.log_le_log hs0 hup
    nlinarith
  rw [abs_of_neg hneg] at hlogt
  have hle : ‖(t : ℂ) - z‖ ≤ Real.exp (-C / M) := by
    rw [← Real.log_le_iff_le_exp hs0]
    rw [le_div_iff₀ hM0]
    linarith
  have hmem : t ∈ Icc (z.re - Real.exp (-C / M)) (z.re + Real.exp (-C / M)) := by
    have := abs_le.mp (hx.trans hle)
    constructor <;> linarith [this.1, this.2]
  have hpos : 0 < |t - z.re| := abs_pos.mpr (sub_ne_zero.mpr ht)
  unfold sing
  rw [indicator_of_mem hmem]
  have hlt : Real.log |t - z.re| ≤ Real.log ‖(t : ℂ) - z‖ := Real.log_le_log hpos hx
  rw [abs_mul]
  calc |Real.log ‖(t : ℂ) - z‖| * |g t| ≤ |Real.log ‖(t : ℂ) - z‖| * M :=
        mul_le_mul_of_nonneg_left (hM t) (abs_nonneg _)
    _ = (-Real.log ‖(t : ℂ) - z‖) * M := by rw [abs_of_neg hneg]
    _ ≤ (-Real.log |t - z.re|) * M := by gcongr
    _ = M * -Real.log |t - z.re| := by ring


theorem tendsto_decay (M : ℝ) : Tendsto (fun u : ℝ ↦ 2 * M * ((1 + u) * Real.exp (-u))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ ↦ Real.exp (-u)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun u : ℝ ↦ u * Real.exp (-u)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have := (h1.add h2)
  simp only [add_zero] at this
  have h3 : Tendsto (fun u : ℝ ↦ (1 + u) * Real.exp (-u)) atTop (𝓝 0) := by
    refine this.congr fun u ↦ ?_
    ring
  simpa using h3.const_mul (2 * M)

theorem tail_eLpNorm {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) (hM0 : 0 < M)
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ z : ℂ, ‖z‖ ≤ R →
      eLpNorm ({t | C ≤ ‖bF g z t‖₊}.indicator (bF g z)) 1 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨U₀, hU₀⟩ := (tendsto_decay M).eventually (gt_mem_nhds hε) |> eventually_atTop.mp
  set C₀ : ℝ := M * |Real.log (1 + R)| + M * |U₀| + 1 with hC₀
  have hC₀pos : 0 < C₀ := by
    have : 0 ≤ M * |Real.log (1 + R)| := by positivity
    have : 0 ≤ M * |U₀| := by positivity
    linarith
  have hC₀log : M * Real.log (1 + R) < C₀ := by
    have : M * Real.log (1 + R) ≤ M * |Real.log (1 + R)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hM0.le
    have : 0 ≤ M * |U₀| := by positivity
    linarith
  have hu : U₀ ≤ C₀ / M := by
    rw [le_div_iff₀ hM0]
    have : M * |U₀| ≥ U₀ * M := by nlinarith [le_abs_self U₀]
    have : 0 ≤ M * |Real.log (1 + R)| := by positivity
    linarith
  refine ⟨C₀.toNNReal, fun z hzR ↦ ?_⟩
  have hCcoe : ((C₀.toNNReal : ℝ≥0) : ℝ) = C₀ := Real.coe_toNNReal _ hC₀pos.le
  set a : ℝ := Real.exp (-C₀ / M) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := by
    rw [ha, Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hM0.le
  have hdec : M * (2 * a * (1 - Real.log a)) ≤ ε := by
    have := hU₀ (C₀ / M) hu
    have e : M * (2 * a * (1 - Real.log a)) = 2 * M * ((1 + C₀ / M) * Real.exp (-(C₀ / M))) := by
      rw [ha, Real.log_exp, neg_div]; ring
    rw [e]; exact this.le
  have hmeas : Measurable (bF g z) := measurable_bF hg z
  set S : Set ℝ := {t | C₀.toNNReal ≤ ‖bF g z t‖₊} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const hmeas.nnnorm
  rw [eLpNorm_one_eq_lintegral_enorm (hmeas.indicator hSm).aestronglyMeasurable]
  have hint : Integrable (fun t ↦ M * sing z.re a t) := (integrable_sing z.re ha0.le).const_mul M
  calc ∫⁻ t, ‖S.indicator (bF g z) t‖ₑ ≤ ∫⁻ t, ENNReal.ofReal (M * sing z.re a t) := by
        refine lintegral_mono_ae ?_
        filter_upwards [(Set.countable_singleton z.re).ae_notMem volume] with t ht
        have htx : t ≠ z.re := by simpa using ht
        by_cases hts : t ∈ S
        · rw [indicator_of_mem hts]
          have hCle : C₀ ≤ |bF g z t| := by
            have h' := NNReal.coe_le_coe.mpr hts
            rw [hCcoe, coe_nnnorm, Real.norm_eq_abs] at h'
            exact h'
          have := abs_bF_le_sing hM hzR (hC := hC₀log) hC₀pos hM0 htx hCle
          rw [← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal this
        · rw [indicator_of_notMem hts]; simp
    _ = ENNReal.ofReal (∫ t, M * sing z.re a t) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        exact Eventually.of_forall fun t ↦ mul_nonneg hM0.le (sing_nonneg ha1 t)
    _ ≤ ENNReal.ofReal ε := by
        rw [integral_const_mul, integral_sing ha0]
        exact ENNReal.ofReal_le_ofReal hdec


theorem bF_eq_zero_of_far {g : ℝ → ℝ} {z : ℂ} {t : ℝ} (h : 1 < |t - z.re|) : bF g z t = 0 := by
  unfold bF; rw [win_eq_zero h, zero_mul]

theorem integrable_bF {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) (z : ℂ) :
    Integrable (bF g z) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set T : ℝ := |z.re| + 1 with hT
  have hint : IntegrableOn (bF g z) (Icc (-T) T) := by
    have hdom := ((integrableOn_log_norm_sub z T).abs).const_mul M
    refine hdom.mono' (measurable_bF hg z).aestronglyMeasurable ?_
    refine Eventually.of_forall fun t ↦ ?_
    unfold bF
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (win_nonneg _ _)]
    calc win z.re t * (|Real.log ‖(t : ℂ) - z‖| * |g t|) ≤ 1 * (|Real.log ‖(t : ℂ) - z‖| * M) := by
          gcongr
          · exact win_le_one _ _
          · exact hM t
      _ = M * |Real.log ‖(t : ℂ) - z‖| := by ring
  refine hint.integrable_of_forall_notMem_eq_zero fun t ht ↦ bF_eq_zero_of_far ?_
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith [abs_nonneg z.re, le_abs_self z.re, neg_abs_le z.re])]
    linarith [le_abs_self z.re, neg_abs_le z.re]
  · rw [abs_of_pos (by linarith [abs_nonneg z.re, le_abs_self z.re])]
    linarith [le_abs_self z.re, neg_abs_le z.re]


theorem tendsto_integral_bF {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M)
    (hM0 : 0 < M) {R : ℝ} {z₀ : ℂ} (hz₀ : ‖z₀‖ ≤ R) (w : ℕ → ℂ) (hw : Tendsto w atTop (𝓝 z₀))
    (hbd : ∀ n, ‖w n‖ ≤ R) :
    Tendsto (fun n ↦ ∫ t, bF g (w n) t) atTop (𝓝 (∫ t, bF g z₀ t)) := by
  have hR0 : 0 ≤ R := (norm_nonneg z₀).trans hz₀
  set μ : Measure ℝ := volume.restrict (Icc (-(R + 1)) (R + 1)) with hμ
  -- supports
  have hsupp : ∀ z : ℂ, ‖z‖ ≤ R → ∀ t, t ∉ Icc (-(R + 1)) (R + 1) → bF g z t = 0 := by
    intro z hz t ht
    refine bF_eq_zero_of_far ?_
    have hx : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hz
    simp only [mem_Icc, not_and_or, not_le] at ht
    have := abs_le.mp hx
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hint : ∀ z : ℂ, Integrable (bF g z) := integrable_bF hg hM
  have hV := tendsto_Lp_finite_of_tendsto_ae (μ := μ) (p := 1) le_rfl ENNReal.one_ne_top
    (f := fun n ↦ bF g (w n)) (g := bF g z₀)
    (fun n ↦ (measurable_bF hg (w n)).aestronglyMeasurable)
    (memLp_one_iff_integrable.mpr (hint z₀).integrableOn) ?_ ?_
  · have hconv := tendsto_integral_of_L1' (μ := μ) (bF g z₀) (F := fun n ↦ bF g (w n))
      (Eventually.of_forall fun n ↦ (hint (w n)).integrableOn) hV
    have e : ∀ z : ℂ, ‖z‖ ≤ R → ∫ t, bF g z t ∂μ = ∫ t, bF g z t := fun z hz ↦
      setIntegral_eq_integral_of_forall_compl_eq_zero (hsupp z hz)
    simp only [e _ hz₀, e _ (hbd _)] at hconv
    exact hconv
  · refine unifIntegrable_of le_rfl ENNReal.one_ne_top
      (fun n ↦ (measurable_bF hg (w n)).aestronglyMeasurable) ?_
    intro ε hε
    by_cases hεt : ε = ∞
    · exact ⟨0, fun i ↦ by rw [hεt]; exact le_top⟩
    · obtain ⟨C, hC⟩ := tail_eLpNorm hg hM hM0 R (ε := ε.toReal) (ENNReal.toReal_pos hε.ne' hεt)
      refine ⟨C, fun i ↦ ?_⟩
      refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
      refine (hC (w i) (hbd i)).trans ?_
      rw [ENNReal.ofReal_toReal hεt]
  · -- almost everywhere convergence
    have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({z₀.re - 1, z₀.re + 1, z₀.re} : Set ℝ) :=
      (Set.toFinite _).countable.ae_notMem volume
    filter_upwards [ae_restrict_of_ae hnull] with t ht
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
    obtain ⟨h1, h2, h3⟩ := ht
    unfold bF
    have hwin : Tendsto (fun n ↦ win (w n).re t) atTop (𝓝 (win z₀.re t)) :=
      ((continuousAt_win h1 h2).tendsto).comp ((Complex.continuous_re.tendsto z₀).comp hw)
    have hne : (t : ℂ) - z₀ ≠ 0 := by
      intro h; apply h3
      have := congrArg Complex.re h
      simpa [sub_eq_zero] using this
    have hlog : Tendsto (fun n ↦ Real.log ‖(t : ℂ) - w n‖) atTop (𝓝 (Real.log ‖(t : ℂ) - z₀‖)) := by
      have hc : Tendsto (fun n ↦ (t : ℂ) - w n) atTop (𝓝 ((t : ℂ) - z₀)) :=
        tendsto_const_nhds.sub hw
      exact ((Real.continuousAt_log (by simpa using hne)).tendsto).comp (hc.norm)
    exact hwin.mul (hlog.mul_const _)


theorem continuousAt_integral_bF {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M)
    (z₀ : ℂ) : ContinuousAt (fun z ↦ ∫ t, bF g z t) z₀ := by
  have hM' : ∀ t, |g t| ≤ |M| + 1 := fun t ↦ (hM t).trans (by linarith [le_abs_self M])
  have hM0 : 0 < |M| + 1 := by positivity
  set R : ℝ := ‖z₀‖ + 1 with hR
  rw [ContinuousAt, Filter.tendsto_iff_seq_tendsto]
  intro x hx
  have hev : ∀ᶠ n in atTop, ‖x n‖ ≤ R := by
    have := hx.eventually (ball_mem_nhds z₀ one_pos)
    filter_upwards [this] with n hn
    have h1 : ‖x n - z₀‖ < 1 := by simpa [dist_eq_norm] using hn
    calc ‖x n‖ = ‖(x n - z₀) + z₀‖ := by ring_nf
      _ ≤ ‖x n - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ R := by rw [hR]; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hw : Tendsto (fun n ↦ x (n + N)) atTop (𝓝 z₀) := hx.comp (tendsto_add_atTop_nat N)
  have := tendsto_integral_bF hg hM' hM0 (R := R) (z₀ := z₀) (by rw [hR]; linarith) (fun n ↦ x (n + N)) hw
    (fun n ↦ hN _ (by omega))
  exact (tendsto_add_atTop_iff_nat (f := fun n ↦ ∫ t, bF g (x n) t) N).mp this

theorem continuous_multU_of_bdd_aux {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ t, |g t| ≤ M) : Continuous (OCS.multU g 0) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  set R : ℝ := ‖z₀‖ + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hnear : ∀ᶠ z in 𝓝 z₀, ‖z‖ ≤ R := by
    filter_upwards [ball_mem_nhds z₀ one_pos] with z hz
    have h1 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
    calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
      _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ R := by rw [hR]; linarith
  have hsum : (fun z ↦ OCS.multU g 0 z) =ᶠ[𝓝 z₀]
      fun z ↦ (∫ t, aF g z t) + (∫ t, bF g z t) + ∫ t, cF g z t := by
    filter_upwards [hnear] with z hzR
    have ha : Integrable (aF g z) :=
      (integrable_aBound M hR0).mono' (measurable_aF hg z).aestronglyMeasurable
        (ae_of_all _ fun t ↦ abs_aF_le hM hzR t)
    have hc : Integrable (cF g z) :=
      (integrable_cBound M R).mono' (measurable_cF hg z).aestronglyMeasurable
        (ae_of_all _ fun t ↦ abs_cF_le hM hzR t)
    have hb : Integrable (bF g z) := integrable_bF hg hM z
    have hab : Integrable (fun t ↦ aF g z t + bF g z t) := ha.add hb
    rw [multU_eq_integral]
    rw [← integral_add ha hb, ← integral_add hab hc]
    refine integral_congr_ae ?_
    filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume,
      (Set.countable_singleton z.re).ae_notMem volume] with t h0 h1
    have h0' : t ≠ 0 := by simpa using h0
    have h1' : t ≠ z.re := by simpa using h1
    exact potKernel_mul_eq_abc g z h0' h1'
  refine ContinuousAt.congr ?_ hsum.symm
  exact ((continuousAt_integral_aF hg hM z₀).add (continuousAt_integral_bF hg hM z₀)).add
    (continuousAt_integral_cF hg hM z₀)


end FF
