import FourierFrames.Cited.Pavlov.Basic
import FourierFrames.Cited.DeBrangesF.Herglotz

/-!
# Weighted Schwarz integrals

The regularized kernel and its derivative are dominated by the half-plane
boundary weight. This gives holomorphy and the Poisson/conjugate-Poisson formulas
for real data integrable against that weight.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF.Pavlov

theorem LogIntegrable.aestronglyMeasurable {u : ℝ → ℝ} (hu : LogIntegrable u) :
    AEStronglyMeasurable u volume := by
  have hm := (show Integrable (fun t ↦ u t / (1 + t ^ 2)) volume from hu).aestronglyMeasurable.mul
    (show AEStronglyMeasurable (fun t : ℝ ↦ 1 + t ^ 2) volume from
      (by fun_prop : Measurable (fun t : ℝ ↦ 1 + t ^ 2)).aestronglyMeasurable)
  convert hm using 1
  funext t
  exact (div_mul_cancel₀ (u t) (by positivity : (1 + t ^ 2 : ℝ) ≠ 0)).symm

theorem LogIntegrable.abs_weight {u : ℝ → ℝ} (hu : LogIntegrable u) :
    Integrable (fun t ↦ |u t| / (1 + t ^ 2)) volume := by
  simpa only [norm_div, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 + _ ^ 2)]
    using hu.norm

theorem schwarzKernel_integrable {u : ℝ → ℝ} (hu : LogIntegrable u)
    {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ ↦ Herglotz.kernel t z * (u t : ℂ)) := by
  have hm : AEStronglyMeasurable (fun t : ℝ ↦ (u t : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hu.aestronglyMeasurable
  refine (hu.abs_weight.const_mul ((1 + ‖z‖ ^ 2) * z.im⁻¹ + ‖z‖)).mono' ?_ ?_
  · exact (by unfold Herglotz.kernel; fun_prop : Measurable (fun t : ℝ ↦ Herglotz.kernel t z)).aestronglyMeasurable.mul hm
  · filter_upwards with t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb := mul_le_mul_of_nonneg_right (Herglotz.norm_kernel_le hz le_rfl le_rfl t)
      (abs_nonneg (u t))
    convert hb using 1; ring

theorem schwarzIntegral_differentiableAt {u : ℝ → ℝ} (hu : LogIntegrable u)
    {z : ℂ} (hz : 0 < z.im) : DifferentiableAt ℂ (schwarzIntegral u) z := by
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
  have hm : AEStronglyMeasurable (fun t : ℝ ↦ (u t : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hu.aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w (t : ℝ) ↦ Herglotz.kernel t w * (u t : ℂ))
    (F' := fun w (t : ℝ) ↦ (((t : ℂ) - w)⁻¹ ^ 2) * (u t : ℂ))
    (s := Metric.ball z (min 1 r))
    (bound := fun t : ℝ ↦ ((1 + R ^ 2) * r⁻¹ ^ 2 + 2 * R * r⁻¹ + 1) *
      (|u t| / (1 + t ^ 2)))
    (Metric.ball_mem_nhds z (lt_min zero_lt_one hr))
    (Eventually.of_forall fun w ↦
      (by unfold Herglotz.kernel; fun_prop : Measurable (fun t : ℝ ↦ Herglotz.kernel t w)).aestronglyMeasurable.mul hm)
    (schwarzKernel_integrable hu hz)
    ((by fun_prop : Measurable (fun t : ℝ ↦ (((t : ℂ) - z)⁻¹ ^ 2))).aestronglyMeasurable.mul hm)
    (Eventually.of_forall fun t w hw ↦ ?_)
    (hu.abs_weight.const_mul _)
    (Eventually.of_forall fun t w hw ↦
      (Herglotz.hasDerivAt_kernel t (hr.trans_le (hball w hw).1)).mul_const (u t : ℂ))
  · exact hd.2.differentiableAt.const_mul (-I / Real.pi)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb := mul_le_mul_of_nonneg_right
      (Herglotz.norm_inv_sq_le hr (hball w hw).1 (hball w hw).2 t) (abs_nonneg (u t))
    convert hb using 1; ring

theorem differentiableOn_schwarzIntegral {u : ℝ → ℝ} (hu : LogIntegrable u) :
    DifferentiableOn ℂ (schwarzIntegral u) UHP :=
  fun _ hz ↦ (schwarzIntegral_differentiableAt hu hz).differentiableWithinAt

theorem schwarzIntegral_re {u : ℝ → ℝ} (hu : LogIntegrable u)
    {z : ℂ} (hz : 0 < z.im) :
    (schwarzIntegral u z).re =
      ∫ t : ℝ, z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2)) * u t := by
  have hi := (schwarzKernel_integrable hu hz).const_mul (-I / Real.pi)
  unfold schwarzIntegral
  rw [← integral_const_mul]
  change RCLike.re (∫ t : ℝ, (-I / Real.pi) * (Herglotz.kernel t z * (u t : ℂ))) = _
  rw [← integral_re hi]
  apply integral_congr_ae
  filter_upwards with t
  change ((-I / Real.pi) * (Herglotz.kernel t z * (u t : ℂ))).re = _
  rw [← mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Herglotz.re_scaled_kernel]

theorem schwarzIntegral_im {u : ℝ → ℝ} (hu : LogIntegrable u)
    {x y : ℝ} (hy : 0 < y) :
    (schwarzIntegral u ((x : ℂ) + (y : ℂ) * I)).im = conjugatePoisson u y x := by
  have hz : 0 < ((x : ℂ) + (y : ℂ) * I).im := by simpa using hy
  have hi := (schwarzKernel_integrable hu hz).const_mul (-I / Real.pi)
  unfold schwarzIntegral conjugatePoisson
  rw [← integral_const_mul]
  change RCLike.im (∫ t : ℝ, (-I / Real.pi) *
    (Herglotz.kernel t ((x : ℂ) + (y : ℂ) * I) * (u t : ℂ))) = _
  rw [← integral_im hi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  change ((-I / Real.pi) * (Herglotz.kernel t ((x : ℂ) + (y : ℂ) * I) * (u t : ℂ))).im = _
  rw [div_mul_eq_mul_div, Complex.div_ofReal_im]
  simp [Herglotz.kernel, Complex.mul_im, Complex.mul_re, Complex.inv_re,
    Complex.normSq_apply]
  have ht : ((t : ℂ) / (1 + (t : ℂ) ^ 2)).re = t / (1 + t ^ 2) := by
    norm_cast
  rw [ht]
  ring

theorem poissonKernel_mul_integrable {u : ℝ → ℝ} (hu : LogIntegrable u)
    {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ ↦ z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2)) * u t) := by
  have hi := ((schwarzKernel_integrable hu hz).const_mul (-I / Real.pi)).re
  convert hi using 1
  funext t
  change _ = ((-I / Real.pi) * (Herglotz.kernel t z * (u t : ℂ))).re
  rw [← mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Herglotz.re_scaled_kernel]

theorem conjugatePoisson_integrand_eq_neg_re (u : ℝ → ℝ) (y x t : ℝ) :
    ((x - t) / ((x - t) ^ 2 + y ^ 2) + t / (1 + t ^ 2)) * u t =
      -(Herglotz.kernel t ((x : ℂ) + (y : ℂ) * I) * (u t : ℂ)).re := by
  simp [Herglotz.kernel, Complex.mul_re, Complex.inv_re, Complex.normSq_apply]
  have ht : ((t : ℂ) / (1 + (t : ℂ) ^ 2)).re = t / (1 + t ^ 2) := by norm_cast
  rw [ht]
  ring

theorem conjugatePoisson_integrand_integrable {u : ℝ → ℝ} (hu : LogIntegrable u)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Integrable (fun t : ℝ ↦
      ((x - t) / ((x - t) ^ 2 + y ^ 2) + t / (1 + t ^ 2)) * u t) := by
  simp_rw [conjugatePoisson_integrand_eq_neg_re]
  exact (schwarzKernel_integrable hu (by simpa using hy)).re.neg

theorem logIntegrable_const (c : ℝ) : LogIntegrable (fun _ ↦ c) := by
  simpa only [LogIntegrable, div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul c

theorem LogIntegrable.sub_const {u : ℝ → ℝ} (hu : LogIntegrable u) (c : ℝ) :
    LogIntegrable (fun t ↦ u t - c) := by
  have hc := logIntegrable_const c
  change Integrable (fun t ↦ (u t - c) / (1 + t ^ 2))
  simp only [sub_div]
  exact Integrable.sub hu hc

theorem schwarzIntegral_im_I {u : ℝ → ℝ} (hu : LogIntegrable u) :
    (schwarzIntegral u I).im = 0 := by
  have hi := schwarzIntegral_im hu (x := 0) (y := 1) (by norm_num)
  simp only [Complex.ofReal_zero, Complex.ofReal_one, one_mul, zero_add] at hi
  rw [hi]
  simp [conjugatePoisson, add_comm, neg_div]

theorem schwarzIntegral_re_const (c : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (schwarzIntegral (fun _ ↦ c) z).re = c := by
  rw [schwarzIntegral_re (logIntegrable_const c) hz, integral_mul_const]
  have hm : (∫ t : ℝ, z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2))) = 1 := by
    have he : (fun t : ℝ ↦ z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2))) =
        fun t ↦ (z.im / Real.pi) * ((t - z.re) ^ 2 + z.im ^ 2)⁻¹ := by
      funext t
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he, integral_const_mul, integral_inv_sq_add_sq z.re hz]
    field_simp
  rw [hm, one_mul]

theorem schwarzIntegral_const (c : ℝ) {z : ℂ} (hz : 0 < z.im) :
    schwarzIntegral (fun _ ↦ c) z = (c : ℂ) := by
  have ho : IsOpen UHP := isOpen_lt continuous_const Complex.continuous_im
  have ha := (differentiableOn_schwarzIntegral (logIntegrable_const c)).analyticOnNhd ho
  have hconn : IsConnected UHP := (convex_halfSpace_im_gt 0).isConnected ⟨I, by simp⟩
  obtain ⟨k, hk⟩ := ha.eq_re_add_const_mul_I_of_re_eq_const
    (fun _ hw ↦ schwarzIntegral_re_const c hw) ho hconn
  have hki := congrArg Complex.im (hk I (by simp [UHP]))
  rw [schwarzIntegral_im_I (logIntegrable_const c)] at hki
  have hk0 : k = 0 := by simpa using hki.symm
  simpa only [hk0, Complex.ofReal_zero, zero_mul, add_zero] using hk z hz

theorem conjugatePoisson_const (c : ℝ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    conjugatePoisson (fun _ ↦ c) y x = 0 := by
  rw [← schwarzIntegral_im (logIntegrable_const c) hy,
    schwarzIntegral_const c (by simpa using hy), Complex.ofReal_im]

theorem LogIntegrable.sub {u v : ℝ → ℝ} (hu : LogIntegrable u) (hv : LogIntegrable v) :
    LogIntegrable (fun t ↦ u t - v t) := by
  apply Integrable.congr (Integrable.sub hu hv)
  filter_upwards with t
  simp only [Pi.sub_apply, sub_div]

theorem LogIntegrable.const_mul {u : ℝ → ℝ} (hu : LogIntegrable u) (c : ℝ) :
    LogIntegrable (fun t ↦ c * u t) := by
  simpa only [LogIntegrable, mul_div_assoc] using (Integrable.const_mul hu c)

theorem LogIntegrable.congr {u v : ℝ → ℝ} (hu : LogIntegrable u) (h : u =ᵐ[volume] v) :
    LogIntegrable v := by
  apply Integrable.congr hu
  filter_upwards [h] with t ht
  simp only [ht]

theorem schwarzIntegral_congr_ae {u v : ℝ → ℝ} (h : u =ᵐ[volume] v) (z : ℂ) :
    schwarzIntegral u z = schwarzIntegral v z := by
  unfold schwarzIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [h] with t ht
  rw [ht]

theorem schwarzIntegral_sub {u v : ℝ → ℝ} (hu : LogIntegrable u) (hv : LogIntegrable v)
    {z : ℂ} (hz : 0 < z.im) :
    schwarzIntegral (fun t ↦ u t - v t) z = schwarzIntegral u z - schwarzIntegral v z := by
  change (-I / Real.pi) * (∫ t : ℝ, Herglotz.kernel t z * ((u t - v t : ℝ) : ℂ)) =
    (-I / Real.pi) * (∫ t : ℝ, Herglotz.kernel t z * (u t : ℂ)) -
      (-I / Real.pi) * (∫ t : ℝ, Herglotz.kernel t z * (v t : ℂ))
  simp only [Complex.ofReal_sub, mul_sub]
  rw [integral_sub (schwarzKernel_integrable hu hz) (schwarzKernel_integrable hv hz)]
  ring

theorem schwarzIntegral_const_mul (u : ℝ → ℝ) (c : ℝ) (z : ℂ) :
    schwarzIntegral (fun t ↦ c * u t) z = (c : ℂ) * schwarzIntegral u z := by
  unfold schwarzIntegral
  simp only [Complex.ofReal_mul]
  have he : (fun t : ℝ ↦ (((t : ℂ) - z)⁻¹ - ((t / (1 + t ^ 2) : ℝ) : ℂ)) *
      ((c : ℂ) * (u t : ℂ))) =
      fun t : ℝ ↦ (c : ℂ) * ((((t : ℂ) - z)⁻¹ - ((t / (1 + t ^ 2) : ℝ) : ℂ)) * (u t : ℂ)) := by
    funext t; ring
  rw [he, integral_const_mul]
  ring

theorem conjugatePoisson_sub_const {u : ℝ → ℝ} (hu : LogIntegrable u) (c : ℝ)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    conjugatePoisson (fun t ↦ u t - c) y x = conjugatePoisson u y x := by
  rw [← schwarzIntegral_im (hu.sub_const c) hy,
    schwarzIntegral_sub hu (logIntegrable_const c) (by simpa using hy),
    schwarzIntegral_const c (by simpa using hy), Complex.sub_im, Complex.ofReal_im, sub_zero]
  exact schwarzIntegral_im hu hy

theorem continuous_conjugatePoisson {u : ℝ → ℝ} (hu : LogIntegrable u)
    {y : ℝ} (hy : 0 < y) : Continuous (conjugatePoisson u y) := by
  have he : conjugatePoisson u y = fun x : ℝ ↦
      (schwarzIntegral u ((x : ℂ) + (y : ℂ) * I)).im := by
    funext x
    exact (schwarzIntegral_im hu hy).symm
  rw [he]
  have hc : Continuous (fun x : ℝ ↦ schwarzIntegral u ((x : ℂ) + (y : ℂ) * I)) :=
    (differentiableOn_schwarzIntegral hu).continuousOn.comp_continuous (by fun_prop)
      (fun x ↦ by simpa [UHP] using hy)
  exact Complex.continuous_im.comp hc

end FF.Pavlov
