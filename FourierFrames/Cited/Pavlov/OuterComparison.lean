import FourierFrames.Cited.Pavlov.Schwarz
import FourierFrames.HB.H2

/-! # Hardy outer comparison and the phase of a logarithmic defect -/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section
namespace FF.Pavlov

private def P (z : ℂ) (t : ℝ) : ℝ :=
  z.im / (Real.pi * ((t-z.re)^2+z.im^2))

private theorem P_nonneg {z : ℂ} (hz : 0 < z.im) (t : ℝ) : 0 ≤ P z t := by
  dsimp [P]
  positivity

private theorem P_mass {z : ℂ} (hz : 0 < z.im) : (∫ t : ℝ, P z t) = 1 := by
  have h := schwarzIntegral_re_const 1 hz
  rw [schwarzIntegral_re (logIntegrable_const 1) hz] at h
  simpa only [P, mul_one] using h

private theorem P_integrable {z : ℂ} (hz : 0 < z.im) : Integrable (P z) := by
  change Integrable (fun t : ℝ ↦ z.im/(Real.pi*((t-z.re)^2+z.im^2)))
  simpa only [mul_one] using poissonKernel_mul_integrable (logIntegrable_const 1) hz

private theorem P_bound {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    ‖P z t‖ ≤ 1/(Real.pi*z.im) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (P_nonneg hz t)]
  dsimp [P]
  have hd : 0 < Real.pi*((t-z.re)^2+z.im^2) := by positivity
  rw [div_le_div_iff₀ hd (mul_pos Real.pi_pos hz)]
  nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg (t-z.re))]

private theorem P_mul_exp_integrable {u : ℝ → ℝ}
    (he : Integrable (fun t : ℝ ↦ Real.exp (2*u t))) {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ ↦ P z t * Real.exp (2*u t)) :=
  he.bdd_mul (f := P z) (by
    have hc : Continuous (P z) := by
      unfold P
      apply Continuous.div continuous_const (by fun_prop)
      intro t
      exact (mul_pos Real.pi_pos (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hz))).ne'
    exact hc.aestronglyMeasurable) (Eventually.of_forall (P_bound hz))

/-- The exponential tangent inequality gives the Poisson majorant of the squared outer norm. -/
theorem norm_exp_schwarzIntegral_sq_le {u : ℝ → ℝ} (hu : LogIntegrable u)
    (he : Integrable (fun t : ℝ ↦ Real.exp (2*u t))) {z : ℂ} (hz : 0 < z.im) :
    ‖Complex.exp (schwarzIntegral u z)‖^2 ≤
      ∫ t : ℝ, z.im/(Real.pi*((t-z.re)^2+z.im^2))*Real.exp (2*u t) := by
  let m := 2*(schwarzIntegral u z).re
  have hip := P_integrable hz
  have hiu : Integrable (fun t ↦ P z t*u t) := poissonKernel_mul_integrable hu hz
  have hil : Integrable (fun t ↦ P z t*Real.exp m*(1+2*u t-m)) := by
    convert (hip.const_mul (Real.exp m*(1-m))).add (hiu.const_mul (2*Real.exp m)) using 1
    funext t
    change _ = (Real.exp m*(1-m))*P z t + (2*Real.exp m)*(P z t*u t)
    ring
  have hib := P_mul_exp_integrable he hz
  have hpoint (t : ℝ) : P z t*Real.exp m*(1+2*u t-m) ≤ P z t*Real.exp (2*u t) := by
    have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2*u t-m)) (Real.exp_pos m).le
    rw [← Real.exp_add] at ht
    have heq : m+(2*u t-m) = 2*u t := by ring
    rw [heq] at ht
    have hm : Real.exp m*(1+2*u t-m) ≤ Real.exp (2*u t) := by nlinarith [ht]
    nlinarith [mul_le_mul_of_nonneg_left hm (P_nonneg hz t)]
  have hint := integral_mono hil hib hpoint
  have heq : (∫ t : ℝ, P z t*Real.exp m*(1+2*u t-m)) = Real.exp m := by
    have hf : (fun t ↦ P z t*Real.exp m*(1+2*u t-m)) =
        fun t ↦ (Real.exp m*(1-m))*P z t + (2*Real.exp m)*(P z t*u t) := by
      funext t
      ring
    rw [hf, integral_add (hip.const_mul _) (hiu.const_mul _), integral_const_mul,
      integral_const_mul, P_mass hz, mul_one]
    have hm : m = 2*∫ t : ℝ, P z t*u t := by
      dsimp [m]
      rw [schwarzIntegral_re hu hz]
      rfl
    rw [hm]
    ring
  rw [heq] at hint
  have hn : ‖Complex.exp (schwarzIntegral u z)‖^2 = Real.exp m := by
    rw [Complex.norm_exp, ← Real.exp_nat_mul]
    simp only [Nat.cast_ofNat, m]
  rwa [hn]

private theorem P_reflect (x y t : ℝ) :
    P ((x : ℂ)+(y : ℂ)*I) t = P ((t : ℂ)+(y : ℂ)*I) x := by
  simp only [P, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
    add_zero, zero_add, Complex.add_re, Complex.mul_re, sub_zero]
  congr 2
  ring

/-- The outer exponential's horizontal L2 mass is bounded by its boundary exponential mass. -/
theorem lintegral_exp_schwarzIntegral_sq_le {u : ℝ → ℝ} (hu : LogIntegrable u)
    (he : Integrable (fun t : ℝ ↦ Real.exp (2*u t))) {y : ℝ} (hy : 0 < y) :
    (∫⁻ x : ℝ, ‖Complex.exp (schwarzIntegral u ((x : ℂ)+(y : ℂ)*I))‖ₑ^2) ≤
      ENNReal.ofReal (∫ t : ℝ, Real.exp (2*u t)) := by
  have hz (x : ℝ) : 0 < ((x : ℂ)+(y : ℂ)*I).im := by simpa using hy
  have hm : AEMeasurable (Function.uncurry (fun x t : ℝ ↦
      ENNReal.ofReal (P ((x : ℂ)+(y : ℂ)*I) t * Real.exp (2*u t))))
      (volume.prod volume) := by
    have hc : Continuous (fun p : ℝ×ℝ ↦ y/(Real.pi*((p.2-p.1)^2+y^2))) := by
      apply Continuous.div continuous_const (by fun_prop)
      intro p
      positivity
    have hp : AEStronglyMeasurable (fun p : ℝ×ℝ ↦ P ((p.1 : ℂ)+(y : ℂ)*I) p.2)
        (volume.prod volume) := by
      convert hc.aestronglyMeasurable using 1
      funext p
      simp [P]
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (hp.mul he.aestronglyMeasurable.comp_snd).aemeasurable
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal
        (∫ t : ℝ, P ((x : ℂ)+(y : ℂ)*I) t * Real.exp (2*u t)) := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [enorm_sq_eq_ofReal]
      exact ENNReal.ofReal_le_ofReal (norm_exp_schwarzIntegral_sq_le hu he (hz x))
    _ = ∫⁻ x : ℝ, ∫⁻ t : ℝ, ENNReal.ofReal
        (P ((x : ℂ)+(y : ℂ)*I) t * Real.exp (2*u t)) := by
      apply lintegral_congr
      intro x
      exact ofReal_integral_eq_lintegral_ofReal (P_mul_exp_integrable he (hz x))
        (Eventually.of_forall (fun t ↦ mul_nonneg (P_nonneg (hz x) t) (Real.exp_pos _).le))
    _ = ∫⁻ t : ℝ, ∫⁻ x : ℝ, ENNReal.ofReal
        (P ((x : ℂ)+(y : ℂ)*I) t * Real.exp (2*u t)) := lintegral_lintegral_swap hm
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (2*u t)) := by
      apply lintegral_congr
      intro t
      simp_rw [ENNReal.ofReal_mul (P_nonneg (hz _) _)]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      have hmass : (∫⁻ x : ℝ, ENNReal.ofReal (P ((x : ℂ)+(y : ℂ)*I) t)) = 1 := by
        simp_rw [P_reflect]
        rw [← ofReal_integral_eq_lintegral_ofReal (P_integrable (hz t))
          (Eventually.of_forall (P_nonneg (hz t))), P_mass (hz t)]
        simp
      rw [hmass, one_mul]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal he
      (Eventually.of_forall (fun t ↦ (Real.exp_pos (2*u t)).le))).symm

/-- An integrable boundary exponential produces an H2 outer comparison. -/
theorem isH2Upper_exp_schwarzIntegral {u : ℝ → ℝ} (hu : LogIntegrable u)
    (he : Integrable (fun t : ℝ ↦ Real.exp (2*u t))) :
    IsH2Upper (fun z ↦ Complex.exp (schwarzIntegral u z)) := by
  refine ⟨(differentiableOn_schwarzIntegral hu).cexp,
    (ENNReal.ofReal (∫ t : ℝ, Real.exp (2*u t))).toNNReal, ?_⟩
  intro y hy
  rw [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]
  exact lintegral_exp_schwarzIntegral_sq_le hu he hy

/-- A linear logarithmic defect determines the exponential phase factor. -/
theorem factor_of_log_defect {u : ℝ → ℝ} (hu : LogIntegrable u)
    {A : ℂ → ℂ} (hA : DifferentiableOn ℂ A UHP)
    (hnz : ∀ z ∈ UHP, A z ≠ 0) (a : ℝ)
    (hdefect : ∀ z ∈ UHP,
      (schwarzIntegral u z).re - Real.log ‖A z‖ = a*z.im) :
    ∃ b : ℝ, ∀ z ∈ UHP,
      A z = Complex.exp (I*((a : ℂ)*z+(b : ℂ))) *
        Complex.exp (schwarzIntegral u z) := by
  let B : ℂ → ℂ := fun z ↦ A z * Complex.exp (-schwarzIntegral u z-I*(a : ℂ)*z)
  have hd : DifferentiableOn ℂ B UHP :=
    hA.mul (((differentiableOn_schwarzIntegral hu).neg.sub
      (differentiable_id.const_mul (I*(a : ℂ))).differentiableOn).cexp)
  have hnorm (z : ℂ) (hz : z ∈ UHP) : ‖B z‖ = 1 := by
    have hp : 0 < ‖A z‖ := norm_pos_iff.mpr (hnz z hz)
    dsimp [B]
    rw [norm_mul, Complex.norm_exp]
    have hre : (-schwarzIntegral u z-I*(a : ℂ)*z).re = -Real.log ‖A z‖ := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      linarith [hdefect z hz]
    rw [hre, Real.exp_neg, Real.exp_log hp]
    exact mul_inv_cancel₀ hp.ne'
  have hI : (I : ℂ) ∈ UHP := by simp [UHP]
  have hconn : IsPreconnected UHP := (convex_halfSpace_im_gt 0).isPreconnected
  have hopen : IsOpen UHP := isOpen_lt continuous_const continuous_im
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hconn hopen hd hI
    (show IsMaxOn (norm ∘ B) UHP I from fun z hz ↦ by
      change ‖B z‖ ≤ ‖B I‖
      simp only [hnorm z hz, hnorm I hI, le_refl])
  refine ⟨Complex.arg (B I), ?_⟩
  intro z hz
  have hc : Complex.exp (I*(Complex.arg (B I) : ℂ)) = B I := by
    simpa only [hnorm I hI, Complex.ofReal_one, one_mul, mul_comm] using
      Complex.norm_mul_exp_arg_mul_I (B I)
  have hh := heq hz
  change A z * Complex.exp (-schwarzIntegral u z-I*(a : ℂ)*z) = B I at hh
  rw [← hc] at hh
  have hexp := Complex.exp_ne_zero (-schwarzIntegral u z-I*(a : ℂ)*z)
  apply (mul_right_cancel₀ hexp)
  rw [hh]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

end FF.Pavlov
