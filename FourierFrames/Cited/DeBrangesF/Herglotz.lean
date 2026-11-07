import FourierFrames.Cited.DeBrangesF.Basic

/-!
# The regularized Herglotz integral

A finite moment `∫ (1+t²)⁻¹ dμ` suffices for the holomorphy of the regularized
Cauchy integral and identifies its real part with the Poisson integral.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section
namespace FF
namespace Herglotz

/-- The regularized Cauchy kernel. -/
def kernel (t : ℝ) (z : ℂ) : ℂ :=
  ((t : ℂ) - z)⁻¹ - ((t / (1 + t ^ 2) : ℝ) : ℂ)

lemma real_sub_ne_zero {z : ℂ} (hz : 0 < z.im) (t : ℝ) : (t : ℂ) - z ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at this
  linarith

lemma norm_inv_sub_le {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : r ≤ z.im) (t : ℝ) :
    ‖((t : ℂ) - z)⁻¹‖ ≤ r⁻¹ := by
  rw [norm_inv]
  have h := Complex.abs_im_le_norm ((t : ℂ) - z)
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
  exact (inv_le_inv₀ (hr.trans_le (hz.trans ((le_abs_self _).trans h))) hr).2
    (hz.trans ((le_abs_self _).trans h))

lemma kernel_eq (t : ℝ) {z : ℂ} (hz : 0 < z.im) :
    kernel t z = (((1 + z ^ 2) * ((t : ℂ) - z)⁻¹ + z) : ℂ) /
      ((1 + t ^ 2 : ℝ) : ℂ) := by
  have ht : ((1 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1 + t ^ 2 : ℝ) ≠ 0)
  unfold kernel
  push_cast at ht ⊢
  field_simp [real_sub_ne_zero hz t, ht]
  ring

lemma inv_sq_eq (t : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (((t : ℂ) - z)⁻¹) ^ 2 =
      ((1 + z ^ 2) * (((t : ℂ) - z)⁻¹) ^ 2 + 2 * z * ((t : ℂ) - z)⁻¹ + 1) /
        ((1 + t ^ 2 : ℝ) : ℂ) := by
  have ht : ((1 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1 + t ^ 2 : ℝ) ≠ 0)
  push_cast at ht ⊢
  field_simp [real_sub_ne_zero hz t, ht]
  ring

lemma norm_kernel_le {z : ℂ} {r R : ℝ} (hr : 0 < r) (hz : r ≤ z.im)
    (hR : ‖z‖ ≤ R) (t : ℝ) :
    ‖kernel t z‖ ≤ ((1 + R ^ 2) * r⁻¹ + R) * (1 / (1 + t ^ 2)) := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hnum : ‖1 + z ^ 2‖ ≤ 1 + R ^ 2 := by
    calc
      ‖1 + z ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2‖ := norm_add_le _ _
      _ ≤ 1 + R ^ 2 := by rw [norm_one, norm_pow]; gcongr
  rw [kernel_eq t (hr.trans_le hz), norm_div, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  calc
    ‖(1 + z ^ 2) * ((t : ℂ) - z)⁻¹ + z‖ / (1 + t ^ 2) ≤
        (‖1 + z ^ 2‖ * ‖((t : ℂ) - z)⁻¹‖ + ‖z‖) / (1 + t ^ 2) := by
      gcongr
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
    _ ≤ ((1 + R ^ 2) * r⁻¹ + R) / (1 + t ^ 2) := by
      gcongr
      exact norm_inv_sub_le hr hz t
    _ = _ := by ring

lemma norm_inv_sq_le {z : ℂ} {r R : ℝ} (hr : 0 < r) (hz : r ≤ z.im)
    (hR : ‖z‖ ≤ R) (t : ℝ) :
    ‖(((t : ℂ) - z)⁻¹) ^ 2‖ ≤
      ((1 + R ^ 2) * (r⁻¹) ^ 2 + 2 * R * r⁻¹ + 1) * (1 / (1 + t ^ 2)) := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hi := norm_inv_sub_le hr hz t
  have hn : ‖1 + z ^ 2‖ ≤ 1 + R ^ 2 := by
    calc
      ‖1 + z ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2‖ := norm_add_le _ _
      _ ≤ 1 + R ^ 2 := by rw [norm_one, norm_pow]; gcongr
  rw [inv_sq_eq t (hr.trans_le hz), norm_div, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have hnum : ‖(1 + z ^ 2) * ((t : ℂ) - z)⁻¹ ^ 2 +
      2 * z * ((t : ℂ) - z)⁻¹ + 1‖ ≤
        (1 + R ^ 2) * (r⁻¹) ^ 2 + 2 * R * r⁻¹ + 1 := by
    calc
      _ ≤ ‖(1 + z ^ 2) * ((t : ℂ) - z)⁻¹ ^ 2‖ +
          ‖2 * z * ((t : ℂ) - z)⁻¹‖ + ‖(1 : ℂ)‖ := norm_add₃_le
      _ = ‖1 + z ^ 2‖ * ‖((t : ℂ) - z)⁻¹‖ ^ 2 +
          2 * ‖z‖ * ‖((t : ℂ) - z)⁻¹‖ + 1 := by norm_num [norm_mul, norm_pow]
      _ ≤ _ := by gcongr
  calc
    _ ≤ ((1 + R ^ 2) * (r⁻¹) ^ 2 + 2 * R * r⁻¹ + 1) / (1 + t ^ 2) := by gcongr
    _ = _ := by ring

lemma moment_integrable {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞) :
    Integrable (fun t : ℝ ↦ 1 / (1 + t ^ 2)) μ := by
  exact (lintegral_ofReal_ne_top_iff_integrable (f := fun t : ℝ ↦ 1 / (1 + t ^ 2))
    ((measurable_const.div (measurable_const.add (measurable_id.pow_const 2))).aestronglyMeasurable)
    (Eventually.of_forall fun t ↦ by positivity)).1 hm.ne

lemma kernel_integrable {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞)
    {z : ℂ} (hz : 0 < z.im) : Integrable (fun t : ℝ ↦ kernel t z) μ := by
  refine ((moment_integrable hm).const_mul ((1 + ‖z‖ ^ 2) * z.im⁻¹ + ‖z‖)).mono'
    (by unfold kernel; fun_prop) (Eventually.of_forall fun t ↦ ?_)
  exact norm_kernel_le hz le_rfl le_rfl t

lemma hasDerivAt_kernel (t : ℝ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (kernel t) (((t : ℂ) - z)⁻¹ ^ 2) z := by
  have hd := ((hasDerivAt_const z (t : ℂ)).sub (hasDerivAt_id z)).inv
    (real_sub_ne_zero hz t)
  change HasDerivAt (fun w ↦ ((t : ℂ) - w)⁻¹ - ((t / (1 + t ^ 2) : ℝ) : ℂ)) _ z
  convert hd.sub_const ((t / (1 + t ^ 2) : ℝ) : ℂ) using 1 <;> simp [div_eq_mul_inv, inv_pow]

lemma integral_differentiableAt {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞)
    {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (fun w ↦ ∫ t : ℝ, kernel t w ∂μ) z := by
  let r := z.im / 2
  let R := ‖z‖ + 1
  have hr : 0 < r := half_pos hz
  have hball : ∀ w ∈ Metric.ball z (min 1 r), r ≤ w.im ∧ ‖w‖ ≤ R := by
    intro w hw
    have hd : ‖w - z‖ < min 1 r := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hdi : |w.im - z.im| ≤ ‖w - z‖ := by simpa using Complex.abs_im_le_norm (w - z)
    have hn := norm_sub_norm_le w z
    constructor
    · have := (le_abs_self (z.im - w.im)).trans (by simpa only [abs_sub_comm] using hdi)
      have := hd.trans_le (min_le_right 1 r)
      dsimp [r] at *
      linarith
    · have := hd.trans_le (min_le_left 1 r)
      dsimp [R]
      linarith
  have hb : Integrable (fun t : ℝ ↦
      ((1 + R ^ 2) * r⁻¹ ^ 2 + 2 * R * r⁻¹ + 1) * (1 / (1 + t ^ 2))) μ :=
    (moment_integrable hm).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w (t : ℝ) ↦ kernel t w)
    (F' := fun w (t : ℝ) ↦ ((t : ℂ) - w)⁻¹ ^ 2)
    (s := Metric.ball z (min 1 r))
    (bound := fun t : ℝ ↦ ((1 + R ^ 2) * r⁻¹ ^ 2 + 2 * R * r⁻¹ + 1) * (1 / (1 + t ^ 2)))
    (Metric.ball_mem_nhds z (lt_min zero_lt_one hr))
    (Eventually.of_forall fun w ↦ by unfold kernel; fun_prop)
    (kernel_integrable hm hz)
    (by fun_prop)
    (Eventually.of_forall fun t w hw ↦ norm_inv_sq_le hr (hball w hw).1 (hball w hw).2 t)
    hb
    (Eventually.of_forall fun t w hw ↦ hasDerivAt_kernel t (hr.trans_le (hball w hw).1))
  exact h.2.differentiableAt

lemma re_neg_I_mul_kernel (t : ℝ) (z : ℂ) :
    (-I * kernel t z).re = z.im / ((t - z.re) ^ 2 + z.im ^ 2) := by
  calc
    (-I * kernel t z).re = (((t : ℂ) - z)⁻¹).im := by
      simp only [kernel, Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im,
        Complex.I_im, zero_mul, neg_zero, neg_one_mul, zero_sub, neg_neg,
        Complex.sub_im, Complex.ofReal_im, sub_zero]
    _ = _ := by simp [Complex.inv_im, Complex.normSq_apply, pow_two]

lemma re_scaled_kernel (t : ℝ) (z : ℂ) :
    ((-I / Real.pi) * kernel t z).re =
      z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2)) := by
  calc
    ((-I / Real.pi) * kernel t z).re = (-I * kernel t z).re / Real.pi := by
      rw [div_mul_eq_mul_div]
      simp [Complex.div_re]
      field_simp
    _ = _ := by rw [re_neg_I_mul_kernel, div_div]; congr 1; ring

end Herglotz

/-- The regularized Herglotz integral is holomorphic and its real part is the Poisson integral. -/
theorem herglotzG_spec {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞) (c : ℝ) :
    DifferentiableOn ℂ (herglotzG μ c) UHP ∧
      ∀ z ∈ UHP, poissonInt μ z ≠ ∞ ∧ (poissonInt μ z).toReal = (herglotzG μ c z).re := by
  constructor
  · intro z hz
    change DifferentiableWithinAt ℂ
      (fun y ↦ -(I / Real.pi) * ∫ t : ℝ, Herglotz.kernel t y ∂μ + I * c) UHP z
    exact (((Herglotz.integral_differentiableAt hm hz).const_mul (-(I / Real.pi))).add_const
      (I * c)).differentiableWithinAt
  · intro z hz
    have hi := (Herglotz.kernel_integrable hm hz).const_mul (-I / Real.pi)
    have hip : Integrable (fun t : ℝ ↦ z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2))) μ := by
      have hir : Integrable (fun t : ℝ ↦ ((-I / Real.pi) * Herglotz.kernel t z).re) μ := hi.re
      simpa only [Herglotz.re_scaled_kernel] using hir
    have hpos : ∀ t : ℝ, 0 ≤ z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2)) := by
      intro t
      exact div_nonneg (le_of_lt hz) (mul_nonneg Real.pi_pos.le (by positivity))
    have hfinite : poissonInt μ z ≠ ∞ :=
      (lintegral_ofReal_ne_top_iff_integrable hip.aestronglyMeasurable
        (Eventually.of_forall hpos)).2 hip
    refine ⟨hfinite, ?_⟩
    calc
      (poissonInt μ z).toReal =
          ∫ t : ℝ, z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2)) ∂μ := by
        symm
        exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hpos) hip.aestronglyMeasurable
      _ = (∫ t : ℝ, (-I / Real.pi) * Herglotz.kernel t z ∂μ).re := by
        calc
          _ = ∫ t : ℝ, ((-I / Real.pi) * Herglotz.kernel t z).re ∂μ :=
            integral_congr_ae (Eventually.of_forall fun t ↦ (Herglotz.re_scaled_kernel t z).symm)
          _ = _ := integral_re hi
      _ = (herglotzG μ c z).re := by
        rw [integral_const_mul]
        simp only [herglotzG, Herglotz.kernel, Complex.add_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, neg_div]

end FF
