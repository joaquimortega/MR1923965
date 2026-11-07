import FourierFrames.Cited.DeBrangesF.Basic

/-!
# Cauchy transforms of finite measures on the circle

The circle is parametrized by a measurable map from the real line. The statements
are independent of de Branges spaces and are used for the normalized measure in
`blueprint/P4F_Elementary.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section
namespace FF

/-- The disk Cauchy kernel, with the boundary parametrized by `u`. -/
def diskCauchyKernel (u : ℝ → ℂ) (w : ℂ) (t : ℝ) : ℂ :=
  (1 - w * conj (u t))⁻¹

/-- A boundedly weighted Cauchy transform. -/
def diskCauchyTransform (ρ : Measure ℝ) (u b : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ t, b t * diskCauchyKernel u w t ∂ρ

lemma diskCauchyKernel_den_ne {u : ℝ → ℂ} (hu : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) (t : ℝ) : 1 - w * conj (u t) ≠ 0 := by
  intro h
  have h' : w * conj (u t) = 1 := (sub_eq_zero.mp h).symm
  have hn := congrArg norm h'
  simp only [norm_mul, Complex.norm_conj, hu t, mul_one, norm_one] at hn
  linarith

lemma diskCauchyKernel_norm_le {u : ℝ → ℂ} (hu : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) (t : ℝ) :
    ‖diskCauchyKernel u w t‖ ≤ (1 - ‖w‖)⁻¹ := by
  have h := norm_sub_norm_le (1 : ℂ) (w * conj (u t))
  simp only [norm_one, norm_mul, Complex.norm_conj, hu t, mul_one] at h
  rw [diskCauchyKernel, norm_inv]
  exact (inv_le_inv₀ (lt_of_lt_of_le (sub_pos.mpr hw) h) (sub_pos.mpr hw)).2 h

lemma diskCauchyKernel_measurable {u : ℝ → ℂ} (hu : Measurable u) (w : ℂ) :
    Measurable (diskCauchyKernel u w) := by
  unfold diskCauchyKernel
  fun_prop

lemma diskCauchyTransform_integrable {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {u b : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    (hb : Measurable b) {M : ℝ} (hM : ∀ t, ‖b t‖ ≤ M)
    {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (fun t ↦ b t * diskCauchyKernel u w t) ρ := by
  refine (integrable_const (M * (1 - ‖w‖)⁻¹)).mono'
    ((hb.mul (diskCauchyKernel_measurable hu w)).aestronglyMeasurable) ?_
  filter_upwards [] with t
  rw [norm_mul]
  exact mul_le_mul (hM t) (diskCauchyKernel_norm_le hun hw t) (norm_nonneg _)
    ((norm_nonneg (b t)).trans (hM t))

lemma diskCauchyKernel_integrable {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {u : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) : Integrable (diskCauchyKernel u w) ρ := by
  simpa using diskCauchyTransform_integrable (ρ := ρ) (b := fun _ ↦ (1 : ℂ)) hu hun measurable_const
    (M := 1) (fun _ ↦ by simp) hw

lemma diskCauchyKernel_sq_integrable {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {u : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (fun t ↦ ‖diskCauchyKernel u w t‖ ^ 2) ρ := by
  refine (integrable_const ((1 - ‖w‖)⁻¹ ^ 2)).mono'
    (((diskCauchyKernel_measurable hu w).norm.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [] with t
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (diskCauchyKernel_norm_le hun hw t) 2

lemma diskCauchyKernel_re_identity {u : ℝ → ℂ} (hu : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) (t : ℝ) :
    2 * (diskCauchyKernel u w t).re - 1 =
      (1 - ‖w‖ ^ 2) * ‖diskCauchyKernel u w t‖ ^ 2 := by
  have hd : Complex.normSq (1 - w * conj (u t)) ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp (diskCauchyKernel_den_ne hu hw t)
  have hsq : Complex.normSq (1 - w * conj (u t)) =
      1 + ‖w‖ ^ 2 - 2 * (w * conj (u t)).re := by
    rw [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_conj,
      Complex.normSq_eq_norm_sq w, Complex.normSq_eq_norm_sq (u t), hu t]
    simp
  simp only [diskCauchyKernel, Complex.inv_re, norm_inv, inv_pow,
    ← Complex.normSq_eq_norm_sq, Complex.sub_re, Complex.one_re]
  rw [← Complex.normSq_eq_norm_sq w] at hsq
  field_simp [hd]
  nlinarith [hsq]

lemma diskCauchyKernel_sq_integral {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {u : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    (∫ t, ‖diskCauchyKernel u w t‖ ^ 2 ∂ρ) =
      (2 * (diskCauchyTransform ρ u (fun _ ↦ 1) w).re - 1) / (1 - ‖w‖ ^ 2) := by
  have hi := diskCauchyKernel_integrable (ρ := ρ) hu hun hw
  have hpos : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have heq := integral_congr_ae (μ := ρ)
    (Eventually.of_forall (diskCauchyKernel_re_identity hun hw))
  change (∫ t, 2 * RCLike.re (diskCauchyKernel u w t) - 1 ∂ρ) = _ at heq
  rw [integral_sub (hi.re.const_mul 2) (integrable_const 1), integral_const_mul,
    integral_re hi, integral_const_mul, integral_const] at heq
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at heq
  unfold diskCauchyTransform
  simp only [one_mul]
  change 2 * (∫ t, diskCauchyKernel u w t ∂ρ).re - 1 =
    (1 - ‖w‖ ^ 2) * (∫ t, ‖diskCauchyKernel u w t‖ ^ 2 ∂ρ) at heq
  exact (eq_div_iff hpos.ne').2 (by simpa only [mul_comm] using heq.symm)

lemma diskCauchyTransform_re_ge_half {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {u : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    1 / 2 ≤ (diskCauchyTransform ρ u (fun _ ↦ 1) w).re := by
  have h := diskCauchyKernel_sq_integral (ρ := ρ) hu hun hw
  have hpos : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hn : 0 ≤ ∫ t, ‖diskCauchyKernel u w t‖ ^ 2 ∂ρ := integral_nonneg fun t ↦ sq_nonneg _
  rw [h] at hn
  have := (le_div_iff₀ hpos).1 hn
  simp only [zero_mul] at this
  linarith

lemma diskCauchyTransform_ne_zero {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {u : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    diskCauchyTransform ρ u (fun _ ↦ 1) w ≠ 0 := by
  intro h
  have := diskCauchyTransform_re_ge_half (ρ := ρ) hu hun hw
  rw [h, Complex.zero_re] at this
  norm_num at this

lemma diskCauchyKernel_hasDerivAt {u : ℝ → ℂ} (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) (t : ℝ) :
    HasDerivAt (fun v ↦ diskCauchyKernel u v t)
      (conj (u t) * diskCauchyKernel u w t ^ 2) w := by
  have hd := (((hasDerivAt_id (𝕜 := ℂ) w).mul_const (conj (u t))).const_sub 1).inv
    (diskCauchyKernel_den_ne hun hw t)
  convert hd using 1 <;> simp only [id_eq, diskCauchyKernel, one_mul, neg_neg, div_eq_mul_inv, inv_pow]
  rfl

lemma diskCauchyTransform_hasDerivAt {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {u b : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    (hb : Measurable b) {M : ℝ} (hM : ∀ t, ‖b t‖ ≤ M)
    {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (diskCauchyTransform ρ u b)
      (∫ t, b t * conj (u t) * diskCauchyKernel u w t ^ 2 ∂ρ) w := by
  let r : ℝ := (‖w‖ + 1) / 2
  have hwr : ‖w‖ < r := by dsimp [r]; linarith
  have hr : r < 1 := by dsimp [r]; linarith
  have hM0 : 0 ≤ M := (norm_nonneg (b 0)).trans (hM 0)
  let f' : ℂ → ℝ → ℂ := fun v t ↦ b t * conj (u t) * diskCauchyKernel u v t ^ 2
  have hs : Metric.ball (0 : ℂ) r ∈ 𝓝 w :=
    Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_zero_right] using hwr)
  have hmeas : ∀ v : ℂ, AEStronglyMeasurable (fun t ↦ b t * diskCauchyKernel u v t) ρ :=
    fun v ↦ (hb.mul (diskCauchyKernel_measurable hu v)).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (f' w) ρ := by
    dsimp [f']
    exact ((hb.mul (Complex.continuous_conj.measurable.comp hu)).mul
      ((diskCauchyKernel_measurable hu w).pow_const 2)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂ρ, ∀ v ∈ Metric.ball (0 : ℂ) r,
      ‖f' v t‖ ≤ M * ((1 - r)⁻¹) ^ 2 := by
    filter_upwards [] with t v hv
    have hvr : ‖v‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hv
    have hv1 : ‖v‖ < 1 := hvr.trans hr
    have hk : ‖diskCauchyKernel u v t‖ ≤ (1 - r)⁻¹ := by
      refine (diskCauchyKernel_norm_le hun hv1 t).trans ?_
      exact (inv_le_inv₀ (sub_pos.mpr hv1) (sub_pos.mpr hr)).2 (by linarith)
    simp only [f', norm_mul, norm_pow, Complex.norm_conj, hun t, mul_one]
    exact mul_le_mul (hM t) (pow_le_pow_left₀ (norm_nonneg _) hk 2) (sq_nonneg _) hM0
  have hderiv : ∀ᵐ t ∂ρ, ∀ v ∈ Metric.ball (0 : ℂ) r,
      HasDerivAt (fun x ↦ b t * diskCauchyKernel u x t) (f' v t) v := by
    filter_upwards [] with t v hv
    have hv1 : ‖v‖ < 1 := (by simpa only [Metric.mem_ball, dist_zero_right] using hv : ‖v‖ < r).trans hr
    simpa only [f', mul_assoc] using (diskCauchyKernel_hasDerivAt hun hv1 t).const_mul (b t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall hmeas) (diskCauchyTransform_integrable hu hun hb hM hw)
    hdmeas hbound (integrable_const _) hderiv).2

lemma diskCauchyTransform_differentiableOn {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {u b : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    (hb : Measurable b) {M : ℝ} (hM : ∀ t, ‖b t‖ ≤ M) :
    DifferentiableOn ℂ (diskCauchyTransform ρ u b) {w : ℂ | ‖w‖ < 1} := by
  intro w hw
  exact (diskCauchyTransform_hasDerivAt hu hun hb hM hw).differentiableAt.differentiableWithinAt

end FF
