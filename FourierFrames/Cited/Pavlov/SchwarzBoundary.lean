import FourierFrames.Cited.Pavlov.Schwarz
import FourierFrames.Cited.DeBrangesDE.Cauchy

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF.Pavlov

private def P (z : ℂ) (t : ℝ) : ℝ :=
  z.im / (Real.pi * ((t-z.re)^2+z.im^2))

private lemma P_nonneg {z : ℂ} (hz : 0 < z.im) (t : ℝ) : 0 ≤ P z t := by
  dsimp [P]
  positivity

private lemma P_integrable {z : ℂ} (hz : 0 < z.im) : Integrable (P z) := by
  have heq : P z = fun t : ℝ ↦ (z.im/Real.pi)*((t-z.re)^2+z.im^2)⁻¹ := by
    ext t
    simp [P, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]
  rw [heq]
  exact (integrable_inv_sq_add_sq z.re hz.ne').const_mul _

private lemma integral_P {z : ℂ} (hz : 0 < z.im) : ∫ t : ℝ, P z t = 1 := by
  have hi := FF.lintegral_poissonKernel z.re hz
  change ∫⁻ t : ℝ, ENNReal.ofReal (P z t) = 1 at hi
  rw [← ofReal_integral_eq_lintegral_ofReal (P_integrable hz)
    (Eventually.of_forall (P_nonneg hz))] at hi
  exact ENNReal.ofReal_eq_one.mp hi

private lemma P_mul_integrable {u : ℝ → ℝ} (hu : LogIntegrable u)
    {z : ℂ} (hz : 0 < z.im) : Integrable (fun t ↦ P z t*u t) := by
  have hi := ((schwarzKernel_integrable hu hz).const_mul (-I/Real.pi)).re
  convert hi using 1
  ext t
  change _ = ((-I/Real.pi)*(Herglotz.kernel t z*(u t : ℂ))).re
  rw [← mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Herglotz.re_scaled_kernel]
  rfl

private lemma P_far_le {x δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : 0 < z.im)
    (hnear : |z.re-x| ≤ min 1 (δ/2)) {t : ℝ} (ht : δ ≤ |t-x|) :
    P z t ≤ ((2+(1+2*(|x|+1)^2)/(δ^2/4))/Real.pi)*z.im/(1+t^2) := by
  have hd : δ/2 ≤ |t-z.re| := by
    have := abs_add_le (t-z.re) (z.re-x)
    rw [sub_add_sub_cancel] at this
    linarith [hnear.trans (min_le_right 1 (δ/2))]
  have hr : |z.re| ≤ |x|+1 := by
    have := abs_add_le (z.re-x) x
    rw [sub_add_cancel] at this
    linarith [hnear.trans (min_le_left 1 (δ/2))]
  have hden : 0 < (t-z.re)^2+z.im^2 := by positivity
  have hδsq : 0 < δ^2/4 := by positivity
  have hlow : δ^2/4 ≤ (t-z.re)^2+z.im^2 := by nlinarith [sq_abs (t-z.re), sq_nonneg z.im]
  have hr2 : z.re^2 ≤ (|x|+1)^2 := by
    have := sq_le_sq₀ (abs_nonneg z.re) (by positivity : 0 ≤ |x|+1) |>.mpr hr
    simpa only [sq_abs] using this
  have hquad : 1+t^2 ≤ 2*((t-z.re)^2+z.im^2)+(1+2*(|x|+1)^2) := by
    nlinarith [sq_nonneg (t-2*z.re), sq_nonneg z.im]
  have hratio : (1+t^2)/((t-z.re)^2+z.im^2) ≤ 2+(1+2*(|x|+1)^2)/(δ^2/4) := by
    calc
      _ ≤ (2*((t-z.re)^2+z.im^2)+(1+2*(|x|+1)^2))/((t-z.re)^2+z.im^2) :=
        div_le_div_of_nonneg_right hquad hden.le
      _ = 2+(1+2*(|x|+1)^2)/((t-z.re)^2+z.im^2) := by field_simp
      _ ≤ _ := by gcongr
  dsimp [P]
  apply (le_div_iff₀ (by positivity : 0 < 1+t^2)).mpr
  have hb := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ z.im/Real.pi)
  convert hb using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

private lemma schwarzIntegral_re_sub_const {u : ℝ → ℝ} (hu : LogIntegrable u)
    {z : ℂ} (hz : 0 < z.im) (c : ℝ) :
    (schwarzIntegral u z).re-c = ∫ t : ℝ, P z t*(u t-c) := by
  rw [schwarzIntegral_re hu hz]
  simp_rw [mul_sub]
  rw [integral_sub (P_mul_integrable hu hz) ((P_integrable hz).mul_const c),
    integral_mul_const, integral_P hz, one_mul]
  rfl

/-- Weighted Poisson integrability and continuity at one point give unrestricted
upper-half-plane convergence of the real Schwarz integral. -/
theorem tendsto_schwarzIntegral_re_boundary {u : ℝ → ℝ} (hu : LogIntegrable u)
    {x : ℝ} (hc : ContinuousAt u x) :
    Tendsto (fun z ↦ (schwarzIntegral u z).re) (𝓝[FF.UHP] (x : ℂ)) (𝓝 (u x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hδu⟩ := Metric.continuousAt_iff.mp hc (ε/2) (half_pos hε)
  let C := (2+(1+2*(|x|+1)^2)/(δ^2/4))/Real.pi
  let L := ∫ t : ℝ, |u t-u x|/(1+t^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL : 0 ≤ L := integral_nonneg (fun t ↦ by positivity)
  have hiL : Integrable (fun t : ℝ ↦ |u t-u x|/(1+t^2)) :=
    (hu.sub_const (u x)).abs_weight
  let B : ℂ → ℝ := fun z ↦ C*z.im*L
  have hBlim : Tendsto B (𝓝[FF.UHP] (x : ℂ)) (𝓝 0) := by
    have hb : Continuous B := by dsimp [B]; fun_prop
    simpa [B] using (hb.tendsto (x : ℂ)).mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ z : ℂ in 𝓝[FF.UHP] (x : ℂ), |z.re-x| ≤ min 1 (δ/2) := by
    apply eventually_nhdsWithin_of_eventually_nhds
    filter_upwards [Metric.closedBall_mem_nhds (x : ℂ) (lt_min zero_lt_one (half_pos hδ))] with z hz
    have hr : |z.re-x| ≤ ‖z-(x : ℂ)‖ := by simpa using Complex.abs_re_le_norm (z-(x : ℂ))
    exact hr.trans (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)
  filter_upwards [self_mem_nhdsWithin, hBlim.eventually_lt_const (half_pos hε), hnear] with z hz hB hn
  change 0 < z.im at hz
  rw [Real.dist_eq, schwarzIntegral_re_sub_const hu hz (u x)]
  calc
    |∫ t : ℝ, P z t*(u t-u x)| ≤ ∫ t : ℝ, |P z t*(u t-u x)| := abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ, (ε/2)*P z t + (C*z.im)*(|u t-u x|/(1+t^2)) := by
      apply integral_mono (P_mul_integrable (hu.sub_const (u x)) hz).abs
        (((P_integrable hz).const_mul _).add (hiL.const_mul _))
      intro t
      change |P z t*(u t-u x)| ≤ (ε/2)*P z t + (C*z.im)*(|u t-u x|/(1+t^2))
      rw [abs_mul, abs_of_nonneg (P_nonneg hz t)]
      by_cases ht : |t-x| < δ
      · have huε : |u t-u x| ≤ ε/2 := (hδu (by simpa [Real.dist_eq] using ht)).le
        have hnearbound := mul_le_mul_of_nonneg_left huε (P_nonneg hz t)
        nlinarith [show 0 ≤ (C*z.im)*(|u t-u x|/(1+t^2)) by positivity]
      · have hfar := mul_le_mul_of_nonneg_right (P_far_le hδ hz hn (le_of_not_gt ht)) (abs_nonneg (u t-u x))
        have hident : (C*z.im/(1+t^2))*|u t-u x| = (C*z.im)*(|u t-u x|/(1+t^2)) := by ring
        change P z t*|u t-u x| ≤ (ε/2)*P z t + _
        change P z t*|u t-u x| ≤ C*z.im/(1+t^2)*|u t-u x| at hfar
        rw [hident] at hfar
        linarith [show 0 ≤ (ε/2)*P z t from mul_nonneg (half_pos hε).le (P_nonneg hz t)]
    _ = ε/2+B z := by
      rw [integral_add ((P_integrable hz).const_mul _) (hiL.const_mul _),
        integral_const_mul, integral_const_mul, integral_P hz]
      simp only [mul_one]
      rfl
    _ < ε := by linarith

/-- The Poisson integral, extended by the boundary data on and below the real axis. -/
def poissonExtension (u : ℝ → ℝ) (z : ℂ) : ℝ :=
  if 0 < z.im then (schwarzIntegral u z).re else u z.re

/-- Continuous weighted-integrable data have a continuous Poisson extension. -/
theorem continuous_poissonExtension {u : ℝ → ℝ} (hu : LogIntegrable u)
    (hc : Continuous u) : Continuous (poissonExtension u) := by
  unfold poissonExtension
  apply continuous_if'
  · intro z hz
    have hz0 : z.im = 0 := by simpa using hz
    have heq : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz0]
    have ht := tendsto_schwarzIntegral_re_boundary hu (hc.continuousAt (x := z.re))
    simpa only [← heq, hz0, lt_self_iff_false, ite_false, UHP] using ht
  · intro z hz
    have hz0 : z.im = 0 := by simpa using hz
    simpa [hz0, Function.comp_def] using ((hc.comp continuous_re).tendsto z).mono_left
      (show 𝓝[{z : ℂ | ¬0 < z.im}] z ≤ 𝓝 z from nhdsWithin_le_nhds)
  · exact continuous_re.comp_continuousOn (differentiableOn_schwarzIntegral hu).continuousOn
  · exact (hc.comp continuous_re).continuousOn

theorem continuousOn_poissonExtension {u : ℝ → ℝ} (hu : LogIntegrable u)
    (hc : Continuous u) : ContinuousOn (poissonExtension u) {z : ℂ | 0 ≤ z.im} :=
  (continuous_poissonExtension hu hc).continuousOn

end FF.Pavlov
