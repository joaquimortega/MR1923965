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


theorem win_add (x s : ℝ) : win x (s + x) = win 0 s := by
  by_cases h : |s| ≤ 1
  · rw [win_eq_one (by simpa using h), win_eq_one (by simpa using h)]
  · push Not at h
    rw [win_eq_zero (by simpa using h), win_eq_zero (by simpa using h)]

/-- Piece `b` in the translated variable `s = t - Re z`. -/
def bT (g : ℝ → ℝ) (z : ℂ) (s : ℝ) : ℝ :=
  win 0 s * (Real.log ‖(s : ℂ) - (z.im : ℂ) * Complex.I‖ * g (s + z.re))

theorem integral_bF_eq (g : ℝ → ℝ) (z : ℂ) : ∫ t, bF g z t = ∫ s, bT g z s := by
  rw [← integral_add_right_eq_self (fun t ↦ bF g z t) z.re]
  congr 1; funext s
  unfold bF bT
  rw [win_add]
  congr 3
  have : ((s + z.re : ℝ) : ℂ) - z = (s : ℂ) - (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [this]

theorem bT_sub (g : ℝ → ℝ) (z : ℂ) (t : ℝ) : bT g z (t - z.re) = bF g z t := by
  unfold bT bF
  have h1 := win_add z.re (t - z.re)
  rw [sub_add_cancel] at h1
  rw [sub_add_cancel, ← h1]
  congr 3
  have : (((t - z.re : ℝ) : ℂ) - (z.im : ℂ) * Complex.I) = (t : ℂ) - z := by
    apply Complex.ext <;> simp
  rw [this]

theorem abs_log_norm_sub_im_le {s y Y : ℝ} (hs : |s| ≤ 1) (hs0 : s ≠ 0) (hy : |y| ≤ Y) :
    |Real.log ‖(s : ℂ) - (y : ℂ) * Complex.I‖| ≤ |Real.log (|s|)| + Real.log (1 + Y) := by
  have hY : 0 ≤ Y := (abs_nonneg _).trans hy
  have h1 : |s| ≤ ‖(s : ℂ) - (y : ℂ) * Complex.I‖ := by
    have := Complex.abs_re_le_norm ((s : ℂ) - (y : ℂ) * Complex.I)
    simpa using this
  have h2 : ‖(s : ℂ) - (y : ℂ) * Complex.I‖ ≤ 1 + Y := by
    calc ‖(s : ℂ) - (y : ℂ) * Complex.I‖ ≤ ‖(s : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_sub_le _ _
      _ ≤ 1 + Y := by simp; linarith
  have hpos : 0 < |s| := abs_pos.mpr hs0
  have hlog1 : 0 ≤ Real.log (1 + Y) := Real.log_nonneg (by linarith)
  by_cases hn : 1 ≤ ‖(s : ℂ) - (y : ℂ) * Complex.I‖
  · rw [abs_of_nonneg (Real.log_nonneg hn)]
    have := Real.log_le_log (by linarith) h2
    linarith [abs_nonneg (Real.log (|s|))]
  · push Not at hn
    rw [abs_of_nonpos (Real.log_nonpos (by linarith) hn.le)]
    have h3 : Real.log (|s|) ≤ Real.log ‖(s : ℂ) - (y : ℂ) * Complex.I‖ := Real.log_le_log hpos h1
    have h4 : Real.log (|s|) ≤ 0 := Real.log_nonpos (abs_nonneg _) hs
    rw [abs_of_nonpos h4]
    linarith

/-- Bound for the translated piece `b`. -/
def bBound (M Y : ℝ) (s : ℝ) : ℝ :=
  (Icc (-1 : ℝ) 1).indicator (fun s ↦ (|Real.log ‖(s : ℂ) - 0‖| + Real.log (1 + Y)) * M) s

theorem integrable_bBound (M Y : ℝ) : Integrable (bBound M Y) := by
  unfold bBound
  rw [integrable_indicator_iff measurableSet_Icc]
  exact (((integrableOn_log_norm_sub 0 1).abs).add (integrableOn_const (by simp))).mul_const M


theorem measurable_bT {g : ℝ → ℝ} (hg : Continuous g) (z : ℂ) : Measurable (bT g z) := by
  unfold bT
  refine (measurable_win 0).mul (Measurable.mul ?_ (hg.measurable.comp (measurable_id.add_const _)))
  exact Real.measurable_log.comp (by fun_prop)

theorem abs_bT_le {g : ℝ → ℝ} {M : ℝ} (hM : ∀ t, |g t| ≤ M) {Y : ℝ} (hY0 : 0 ≤ Y) {z : ℂ}
    (hz : |z.im| ≤ Y) : ∀ᵐ s ∂(volume : Measure ℝ), ‖bT g z s‖ ≤ bBound M Y s := by
  filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with s hs0
  have hs0' : s ≠ 0 := by simpa using hs0
  unfold bBound bT
  rw [Real.norm_eq_abs]
  by_cases hs : s ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hs]
    have hw : win 0 s = 1 := win_eq_one (by simpa using abs_le.mpr ⟨hs.1, hs.2⟩)
    rw [hw, one_mul, abs_mul]
    have := abs_log_norm_sub_im_le (abs_le.mpr ⟨hs.1, hs.2⟩) hs0' hz
    have e : Real.log ‖(s : ℂ) - 0‖ = Real.log (|s|) := by simp
    simp only [e]
    have hl : 0 ≤ Real.log (1 + Y) := Real.log_nonneg (by linarith)
    exact mul_le_mul this (hM _) (abs_nonneg _) (by positivity)
  · rw [indicator_of_notMem hs]
    have hw : win 0 s = 0 := by
      have : 1 < |s| := by
        by_contra hc
        exact hs (abs_le.mp (not_lt.mp hc))
      exact win_eq_zero (by simpa using this)
    rw [hw]; simp

theorem continuousAt_integral_bT {g : ℝ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ t, |g t| ≤ M)
    (z₀ : ℂ) : ContinuousAt (fun z ↦ ∫ s, bT g z s) z₀ := by
  set Y : ℝ := |z₀.im| + 1 with hY
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine continuousAt_of_dominated (bound := bBound M Y) ?_ ?_ (integrable_bBound M Y) ?_
  · exact Eventually.of_forall fun z ↦ (measurable_bT hg z).aestronglyMeasurable
  · have : ∀ᶠ z in 𝓝 z₀, |z.im| ≤ Y := by
      filter_upwards [ball_mem_nhds z₀ one_pos] with z hz
      have h1 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
      have h2 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
        simpa using Complex.abs_im_le_norm (z - z₀)
      calc |z.im| = |(z.im - z₀.im) + z₀.im| := by ring_nf
        _ ≤ |z.im - z₀.im| + |z₀.im| := abs_add_le _ _
        _ ≤ Y := by rw [hY]; linarith
    filter_upwards [this] with z hz
    exact abs_bT_le hM (by rw [hY]; positivity) hz
  · filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with s hs0
    have hs0' : s ≠ 0 := by simpa using hs0
    unfold bT
    refine continuousAt_const.mul (ContinuousAt.mul ?_ ?_)
    · refine (Real.continuousAt_log ?_).comp (f := fun z : ℂ ↦ ‖(s : ℂ) - (z.im : ℂ) * Complex.I‖) ?_
      · intro h
        have := norm_eq_zero.mp (by simpa using h)
        have := congrArg Complex.re this
        simp at this; exact hs0' this
      · exact (continuous_norm.comp (by fun_prop : Continuous fun z : ℂ ↦
          (s : ℂ) - (z.im : ℂ) * Complex.I)).continuousAt
    · exact (hg.comp (by fun_prop : Continuous fun z : ℂ ↦ s + z.re)).continuousAt


theorem continuous_multU_of_cont_bdd {g : ℝ → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ t, |g t| ≤ M) : Continuous (OCS.multU g 0) := by
  have hgm : Measurable g := hg.measurable
  rw [continuous_iff_continuousAt]
  intro z₀
  set R : ℝ := ‖z₀‖ + 1 with hR
  set Y : ℝ := |z₀.im| + 1 with hY
  have hR0 : 0 ≤ R := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hnear : ∀ᶠ z in 𝓝 z₀, ‖z‖ ≤ R ∧ |z.im| ≤ Y := by
    filter_upwards [ball_mem_nhds z₀ one_pos] with z hz
    have h1 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
    refine ⟨?_, ?_⟩
    · calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ R := by rw [hR]; linarith
    · have h2 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
        simpa using Complex.abs_im_le_norm (z - z₀)
      calc |z.im| = |(z.im - z₀.im) + z₀.im| := by ring_nf
        _ ≤ |z.im - z₀.im| + |z₀.im| := abs_add_le _ _
        _ ≤ Y := by rw [hY]; linarith
  have hsum : (fun z ↦ OCS.multU g 0 z) =ᶠ[𝓝 z₀]
      fun z ↦ (∫ t, aF g z t) + (∫ s, bT g z s) + ∫ t, cF g z t := by
    filter_upwards [hnear] with z ⟨hzR, hzY⟩
    have ha : Integrable (aF g z) :=
      (integrable_aBound M hR0).mono' (measurable_aF hgm z).aestronglyMeasurable
        (ae_of_all _ fun t ↦ abs_aF_le hM hzR t)
    have hc : Integrable (cF g z) :=
      (integrable_cBound M R).mono' (measurable_cF hgm z).aestronglyMeasurable
        (ae_of_all _ fun t ↦ abs_cF_le hM hzR t)
    have hbT : Integrable (bT g z) :=
      (integrable_bBound M Y).mono' (measurable_bT hg z).aestronglyMeasurable (abs_bT_le hM hY0 hzY)
    have hb : Integrable (bF g z) := by
      have := hbT.comp_sub_right z.re
      refine this.congr (Eventually.of_forall fun t ↦ ?_)
      exact bT_sub g z t
    have hab : Integrable (fun t ↦ aF g z t + bF g z t) := ha.add hb
    rw [multU_eq_integral, ← integral_bF_eq]
    rw [← integral_add ha hb, ← integral_add hab hc]
    refine integral_congr_ae ?_
    filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume,
      (Set.countable_singleton z.re).ae_notMem volume] with t h0 h1
    have h0' : t ≠ 0 := by simpa using h0
    have h1' : t ≠ z.re := by simpa using h1
    exact potKernel_mul_eq_abc g z h0' h1'
  refine ContinuousAt.congr ?_ hsum.symm
  exact ((continuousAt_integral_aF hgm hM z₀).add (continuousAt_integral_bT hg hM z₀)).add
    (continuousAt_integral_cF hgm hM z₀)


end FF
