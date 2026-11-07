import FourierFrames.Corollary2.LogInt

/-!
# M07 -- helper lemmas for `Corollary2.lean`: the complex potential `potC`

Copies `argUp'`, `potC'` of the definitions `argUp`, `potC` of `Corollary2.lean` (same bodies, so
the transfer lemmas there are `rfl`).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF


/-- Copy of `argUp` (identical body) used in the helper files. -/
def argUp' (z : ℂ) (t : ℝ) : ℝ :=
  if t < 0 then Complex.arg (1 - z / t) else -Complex.arg (conj (1 - z / t))

/-- The imaginary part of the integrand of `potC` (without `g`). -/
def sigma (z : ℂ) (t : ℝ) : ℝ := argUp' z t + chi t * (z / t).im

/-- Copy of `potC`. -/
def potC' (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (((Real.log ‖1 - z / t‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).re : ℝ) : ℂ) +
    Complex.I * ((argUp' z t + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).im : ℝ) : ℂ)) *
      (g t : ℂ)

theorem abs_argUp'_le (z : ℂ) (t : ℝ) : |argUp' z t| ≤ Real.pi := by
  unfold argUp'
  split_ifs
  · exact Complex.abs_arg_le_pi _
  · rw [abs_neg]; exact Complex.abs_arg_le_pi _

theorem measurable_argUp' (z : ℂ) : Measurable (argUp' z) := by
  unfold argUp'
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) ?_ ?_
  · exact Complex.measurable_arg.comp (by fun_prop)
  · exact (Complex.measurable_arg.comp (Complex.continuous_conj.measurable.comp (by fun_prop))).neg

theorem measurable_sigma (z : ℂ) : Measurable (sigma z) := by
  unfold sigma
  exact (measurable_argUp' z).add (measurable_chi.mul (Complex.measurable_im.comp (by fun_prop)))

theorem abs_sigma_le (z : ℂ) (t : ℝ) : |sigma z t| ≤ Real.pi + ‖z‖ := by
  unfold sigma
  have h1 := abs_argUp'_le z t
  have h2 : |chi t * (z / t).im| ≤ ‖z‖ := by
    rw [abs_mul, abs_of_nonneg (chi_nonneg t)]
    rw [chi_eq]
    by_cases h : |t| ≤ 1
    · simp [h]
    · push Not at h
      simp only [h.not_ge, ↓reduceIte, one_mul]
      calc |(z / (t : ℂ)).im| ≤ ‖z / (t : ℂ)‖ := Complex.abs_im_le_norm _
        _ = ‖z‖ / |t| := by rw [norm_div]; simp
        _ ≤ ‖z‖ := div_le_self (norm_nonneg z) h.le
  calc |argUp' z t + chi t * (z / t).im| ≤ |argUp' z t| + |chi t * (z / t).im| := abs_add_le _ _
    _ ≤ _ := by linarith


theorem argUp'_far (z : ℂ) {t : ℝ} (ht1 : 1 < |t|) (hz : ‖z‖ ≤ |t| / 2) :
    argUp' z t = Complex.arg (1 - z / t) := by
  have ht0 : t ≠ 0 := fun h ↦ by rw [h] at ht1; norm_num at ht1
  have hwn : ‖z / (t : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_div]
    have : ‖(t : ℂ)‖ = |t| := by simp
    rw [this, div_le_iff₀ (by linarith)]; linarith
  have hre : 0 < (1 - z / (t : ℂ)).re := by
    have := Complex.abs_re_le_norm (z / (t : ℂ))
    simp only [Complex.sub_re, Complex.one_re]
    have := (abs_le.mp this).2
    linarith
  unfold argUp'
  by_cases h : t < 0
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]; rw [Complex.arg_conj]
    have hne : Complex.arg (1 - z / (t : ℂ)) ≠ Real.pi := by
      have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
      intro h'; rw [h'] at this
      have : Real.pi < Real.pi / 2 := by simpa [abs_of_pos Real.pi_pos] using this
      linarith [Real.pi_pos]
    simp only [hne, ↓reduceIte]; ring

theorem abs_sigma_far (z : ℂ) {t : ℝ} (ht1 : 1 < |t|) (hz : ‖z‖ ≤ |t| / 2) :
    |sigma z t| ≤ ‖z‖ ^ 2 / t ^ 2 := by
  have ht0 : t ≠ 0 := fun h ↦ by rw [h] at ht1; norm_num at ht1
  have hχ : chi t = 1 := by rw [chi_eq]; simp [not_le.mpr ht1]
  unfold sigma
  rw [hχ, one_mul, argUp'_far z ht1 hz]
  set w : ℂ := z / t with hw
  have hwn : ‖w‖ = ‖z‖ / |t| := by rw [hw, norm_div]; simp
  have hwn2 : ‖w‖ ≤ 1 / 2 := by
    rw [hwn, div_le_iff₀ (by linarith)]; linarith
  have hb := Complex.norm_log_one_add_sub_self_le (z := -w) (by rw [norm_neg]; linarith)
  rw [norm_neg] at hb
  have e : Complex.arg (1 - w) + w.im = (Complex.log (1 + (-w)) - (-w)).im := by
    rw [Complex.sub_im, Complex.log_im, ← sub_eq_add_neg]; simp
  rw [e]
  refine (Complex.abs_im_le_norm _).trans (hb.trans ?_)
  have : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h2 : ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 / t ^ 2 := by
    rw [hwn, div_pow, sq_abs]
  nlinarith [sq_nonneg ‖w‖]


theorem integrable_sigma_mul {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M)
    (z : ℂ) : Integrable fun t ↦ sigma z t * g t := by
  set T : ℝ := 2 * ‖z‖ + 2 with hT
  have hT0 : 0 < T := by linarith [norm_nonneg z]
  have hmeas : Measurable fun t ↦ sigma z t * g t := (measurable_sigma z).mul hg
  rw [← integrableOn_univ, ← union_compl_self (Icc (-T) T)]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := (Real.pi + ‖z‖) * M) (by simp)
      hmeas.aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_sigma_le z t) (hM t) (abs_nonneg _)
      (by positivity)
  · obtain ⟨hI, -⟩ := far_inv_sq hT0
    have hI2 : IntegrableOn (fun t : ℝ ↦ M * (‖z‖ ^ 2 * (t ^ 2)⁻¹)) (Icc (-T) T)ᶜ :=
      (hI.const_mul (‖z‖ ^ 2)).const_mul M
    refine hI2.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
    have htT : T < |t| := by
      simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have h1 := abs_sigma_far z (by linarith [norm_nonneg z]) (by linarith : ‖z‖ ≤ |t| / 2)
    rw [Real.norm_eq_abs, abs_mul]
    calc |sigma z t| * |g t| ≤ (‖z‖ ^ 2 / t ^ 2) * M :=
          mul_le_mul h1 (hM t) (abs_nonneg _) (by positivity)
      _ = M * (‖z‖ ^ 2 * (t ^ 2)⁻¹) := by ring

/-- The complex integrand of `potC`. -/
def potCInt (g : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  ((potKernel z t * g t : ℝ) : ℂ) + Complex.I * ((sigma z t * g t : ℝ) : ℂ)

theorem potC'_eq (g : ℝ → ℝ) (z : ℂ) : potC' g z = ∫ t, potCInt g z t := by
  unfold potC'
  congr 1; funext t
  unfold potCInt potKernel sigma chi
  push_cast; ring

theorem integrable_potCInt {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M)
    (z : ℂ) : Integrable (potCInt g z) := by
  have h1 := (integrable_potKernel_mul hg hM z).ofReal (𝕜 := ℂ)
  have h2 := ((integrable_sigma_mul hg hM z).ofReal (𝕜 := ℂ)).const_mul Complex.I
  exact h1.add h2

theorem potC'_re {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) (z : ℂ) :
    (potC' g z).re = OCS.multU g 0 z := by
  rw [potC'_eq, ← RCLike.re_to_complex, ← integral_re (integrable_potCInt hg hM z), multU_eq_integral]
  congr 1; funext t
  simp [potCInt]

theorem potC'_im {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) (z : ℂ) :
    (potC' g z).im = ∫ t, sigma z t * g t := by
  rw [potC'_eq, ← RCLike.im_to_complex, ← integral_im (integrable_potCInt hg hM z)]
  congr 1; funext t
  simp [potCInt]


theorem sigma_ofReal (x t : ℝ) :
    sigma (x : ℂ) t = Real.pi * (Ioo x 0).indicator (fun _ ↦ (1 : ℝ)) t -
      Real.pi * (Ioo 0 x).indicator (fun _ ↦ (1 : ℝ)) t := by
  have hre : ((x : ℂ) / (t : ℂ)) = ((x / t : ℝ) : ℂ) := by push_cast; rfl
  have him : ((x : ℂ) / (t : ℂ)).im = 0 := by rw [hre]; exact Complex.ofReal_im _
  have h1 : (1 : ℂ) - (x : ℂ) / (t : ℂ) = ((1 - x / t : ℝ) : ℂ) := by rw [hre]; push_cast; ring
  unfold sigma argUp'
  rw [him, mul_zero, add_zero, h1]
  rcases lt_trichotomy t 0 with ht | ht | ht
  · simp only [ht, ↓reduceIte]
    have hx : (1 - x / t < 0) ↔ x < t := by
      rw [sub_neg, lt_div_iff_of_neg ht]; constructor <;> intro h <;> linarith
    by_cases h : x < t
    · have : 1 - x / t < 0 := hx.mpr h
      rw [Complex.arg_ofReal_of_neg this, indicator_of_mem (show t ∈ Ioo x 0 from ⟨h, ht⟩),
        indicator_of_notMem (show t ∉ Ioo 0 x from fun h' ↦ by linarith [h'.1])]
      ring
    · have : 0 ≤ 1 - x / t := le_of_not_gt (fun h' ↦ h (hx.mp h'))
      rw [Complex.arg_ofReal_of_nonneg this, indicator_of_notMem (show t ∉ Ioo x 0 from fun h' ↦ h h'.1),
        indicator_of_notMem (show t ∉ Ioo 0 x from fun h' ↦ by linarith [h'.1])]
      ring
  · subst ht
    simp
  · simp only [not_lt.mpr ht.le, ↓reduceIte]
    rw [Complex.conj_ofReal]
    have hx : (1 - x / t < 0) ↔ t < x := by
      rw [sub_neg, lt_div_iff₀ ht]; constructor <;> intro h <;> linarith
    by_cases h : t < x
    · have : 1 - x / t < 0 := hx.mpr h
      rw [Complex.arg_ofReal_of_neg this, indicator_of_mem (show t ∈ Ioo 0 x from ⟨ht, h⟩),
        indicator_of_notMem (show t ∉ Ioo x 0 from fun h' ↦ by linarith [h'.2])]
      ring
    · have : 0 ≤ 1 - x / t := le_of_not_gt (fun h' ↦ h (hx.mp h'))
      rw [Complex.arg_ofReal_of_nonneg this, indicator_of_notMem (show t ∉ Ioo 0 x from fun h' ↦ h h'.2),
        indicator_of_notMem (show t ∉ Ioo x 0 from fun h' ↦ by linarith [h'.2])]
      ring


theorem potC'_im_ofReal {g φ : ℝ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ t, |g t| ≤ M)
    (hφ : ∀ x, HasDerivAt φ (g x) x) (x : ℝ) :
    (potC' g (x : ℂ)).im = -Real.pi * (φ x - φ 0) := by
  rw [potC'_im hg.measurable hM]
  have hpt : ∀ t, sigma (x : ℂ) t * g t =
      Real.pi * (Ioo x 0).indicator g t - Real.pi * (Ioo 0 x).indicator g t := by
    intro t
    rw [sigma_ofReal]
    by_cases h1 : t ∈ Ioo x 0 <;> by_cases h2 : t ∈ Ioo 0 x <;>
      simp [indicator_of_mem, indicator_of_notMem, h1, h2]
  have hI : ∀ a b : ℝ, Integrable ((Ioo a b).indicator g) := fun a b ↦ by
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact (hg.integrableOn_Icc (a := a) (b := b)).mono_set Ioo_subset_Icc_self
  simp_rw [hpt]
  rw [integral_sub ((hI x 0).const_mul _) ((hI 0 x).const_mul _), integral_const_mul,
    integral_const_mul, integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Ioo]
  have hFTC : ∀ a b : ℝ, ∫ t in a..b, g t = φ b - φ a := fun a b ↦
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hφ t) (hg.intervalIntegrable _ _)
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Ioo_eq_empty (by linarith : ¬ (0 < x)), setIntegral_empty]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h.le, hFTC]
    ring
  · subst h; simp
  · rw [Ioo_eq_empty (by linarith : ¬ (x < 0)), setIntegral_empty]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h.le, hFTC]
    ring


end FF
