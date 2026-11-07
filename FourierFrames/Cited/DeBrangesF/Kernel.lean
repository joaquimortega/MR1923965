import FourierFrames.Cited.DeBrangesF.Basic

/-!
# Kernel normalization for isometric measures

The kernel at `i` identifies the de Branges kernel with a disk model kernel.
The calculation is algebraic; it uses neither Theorem F nor an inner factorization.
See `blueprint/P4F_Elementary.md`, §§1–2.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF.FMeasure

/-- Cayley map from the upper half-plane to the disk. -/
def cayley (z : ℂ) : ℂ := (z - I) / (z + I)

/-- Value of the original inner function at the normalization point. -/
def anchor (E : ℂ → ℂ) : ℂ := thetaFn E I

/-- Positive defect of the normalization parameter. -/
def defect (E : ℂ → ℂ) : ℝ := 1 - ‖anchor E‖ ^ 2

/-- Denominator of the disk automorphism. -/
def denom (E : ℂ → ℂ) (z : ℂ) : ℂ := 1 - conj (anchor E) * thetaFn E z

/-- The normalized inner function, vanishing at `i`. -/
def theta (E : ℂ → ℂ) (z : ℂ) : ℂ := (thetaFn E z - anchor E) / denom E z

/-- The kernel used to normalize the measure. -/
def baseKernel (E : ℂ → ℂ) : ℂ → ℂ := deBrangesKernel E I

/-- Its positive squared norm. -/
def baseNorm (E : ℂ → ℂ) : ℝ := (deBrangesKernel E I I).re

theorem add_I_ne_zero {z : ℂ} (hz : 0 ≤ z.im) : z + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem sub_conj_ne_zero {z w : ℂ} (hz : 0 < z.im) (hw : 0 ≤ w.im) : w - conj z ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem cayley_norm_sq_diff (z : ℂ) : ‖z + I‖ ^ 2 - ‖z - I‖ ^ 2 = 4 * z.im := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  ring

theorem norm_cayley_lt_one {z : ℂ} (hz : 0 < z.im) : ‖cayley z‖ < 1 := by
  rw [cayley, norm_div, div_lt_one (norm_pos_iff.mpr (add_I_ne_zero hz.le))]
  have h := cayley_norm_sq_diff z
  nlinarith [norm_nonneg (z + I), norm_nonneg (z - I)]

theorem norm_cayley_real (t : ℝ) : ‖cayley (t : ℂ)‖ = 1 := by
  rw [cayley, norm_div]
  have h := cayley_norm_sq_diff (t : ℂ)
  simp only [Complex.ofReal_im, mul_zero] at h
  have he : ‖(t : ℂ) - I‖ = ‖(t : ℂ) + I‖ := by
    nlinarith [norm_nonneg ((t : ℂ) + I), norm_nonneg ((t : ℂ) - I)]
  rw [he, div_self (norm_ne_zero_iff.mpr (add_I_ne_zero (by simp)))]

@[simp] theorem cayley_I : cayley I = 0 := by simp [cayley]

theorem differentiableOn_cayley : DifferentiableOn ℂ cayley UHP := by
  intro z hz
  exact ((differentiableAt_id.sub_const I).div (differentiableAt_id.add_const I)
    (add_I_ne_zero (le_of_lt hz))).differentiableWithinAt

theorem norm_thetaFn_lt_one {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ} (hz : z ∈ UHP) :
    ‖thetaFn E z‖ < 1 := by
  rw [thetaFn, norm_div, div_lt_one (norm_pos_iff.mpr (hE.1.2.1 z hz)), norm_fstar]
  exact hE.2 z hz

theorem norm_thetaFn_real {E : ℂ → ℂ} (h0 : ∀ t : ℝ, E t ≠ 0) (t : ℝ) :
    ‖thetaFn E t‖ = 1 := by
  rw [thetaFn, norm_div, fstar_ofReal, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr (h0 t))]

theorem norm_anchor_lt_one {E : ℂ → ℂ} (hE : IsStrictHB E) : ‖anchor E‖ < 1 :=
  norm_thetaFn_lt_one hE (by simp [UHP])

theorem defect_pos {E : ℂ → ℂ} (hE : IsStrictHB E) : 0 < defect E := by
  have h := norm_anchor_lt_one hE
  dsimp [defect]
  nlinarith [norm_nonneg (anchor E)]

theorem one_sub_conj_mul_ne_zero {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) :
    1 - conj a * b ≠ 0 := by
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  rw [norm_one, norm_mul, Complex.norm_conj] at he
  have hm : ‖a‖ * ‖b‖ ≤ ‖a‖ := by nlinarith [norm_nonneg a, norm_nonneg b]
  linarith

theorem denom_ne_zero {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ} (hz : z ∈ UHP) :
    denom E z ≠ 0 :=
  one_sub_conj_mul_ne_zero (norm_anchor_lt_one hE) (norm_thetaFn_lt_one hE hz).le

theorem denom_real_ne_zero {E : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (t : ℝ) : denom E t ≠ 0 :=
  one_sub_conj_mul_ne_zero (norm_anchor_lt_one hE) (norm_thetaFn_real h0 t).le

theorem mobius_norm_sq_diff (a b : ℂ) :
    ‖1 - conj a * b‖ ^ 2 - ‖b - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem norm_theta_lt_one {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ} (hz : z ∈ UHP) :
    ‖theta E z‖ < 1 := by
  have ha := norm_anchor_lt_one hE
  have hb := norm_thetaFn_lt_one hE hz
  have hd := mobius_norm_sq_diff (anchor E) (thetaFn E z)
  have hpos : 0 < (1 - ‖anchor E‖ ^ 2) * (1 - ‖thetaFn E z‖ ^ 2) := by
    apply mul_pos <;> nlinarith [norm_nonneg (anchor E), norm_nonneg (thetaFn E z)]
  rw [theta, norm_div, div_lt_one (norm_pos_iff.mpr (denom_ne_zero hE hz))]
  dsimp only [denom]
  nlinarith [norm_nonneg (1 - conj (anchor E) * thetaFn E z),
    norm_nonneg (thetaFn E z - anchor E)]

theorem norm_theta_real {E : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (t : ℝ) : ‖theta E t‖ = 1 := by
  have hd := mobius_norm_sq_diff (anchor E) (thetaFn E t)
  rw [norm_thetaFn_real h0 t] at hd
  have he : ‖thetaFn E t - anchor E‖ = ‖denom E t‖ := by
    dsimp only [denom]
    nlinarith [norm_nonneg (1 - conj (anchor E) * thetaFn E t),
      norm_nonneg (thetaFn E t - anchor E)]
  rw [theta, norm_div, he, div_self (norm_ne_zero_iff.mpr (denom_real_ne_zero hE h0 t))]

@[simp] theorem theta_I (E : ℂ → ℂ) : theta E I = 0 := by simp [theta, anchor]

theorem differentiableOn_thetaFn {E : ℂ → ℂ} (hE : IsHB E) :
    DifferentiableOn ℂ (thetaFn E) UHP :=
  (FF.Differentiable.fstar hE.1).differentiableOn.div hE.1.differentiableOn hE.2.1

theorem differentiableOn_theta {E : ℂ → ℂ} (hE : IsStrictHB E) :
    DifferentiableOn ℂ (theta E) UHP := by
  have h := differentiableOn_thetaFn hE.1
  exact (h.sub_const _).div ((differentiableOn_const _).sub (h.const_mul _))
    (fun _ hz ↦ denom_ne_zero hE hz)

theorem continuousAt_thetaFn_real {E : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (t : ℝ) : ContinuousAt (thetaFn E) (t : ℂ) :=
  (FF.Differentiable.fstar hE.1).continuous.continuousAt.div hE.1.continuous.continuousAt (h0 t)

theorem continuousAt_theta_real {E : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (t : ℝ) : ContinuousAt (theta E) (t : ℂ) := by
  have h := continuousAt_thetaFn_real hE.1 h0 t
  exact (h.sub_const _).div (continuousAt_const.sub (h.const_mul _))
    (denom_real_ne_zero hE h0 t)

theorem thetaFn_norm_le_one_closed {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ}
    (hz : 0 ≤ z.im) (he : E z ≠ 0) : ‖thetaFn E z‖ ≤ 1 := by
  rw [thetaFn, norm_div, div_le_one (norm_pos_iff.mpr he), norm_fstar]
  rcases eq_or_lt_of_le hz with h | h
  · have hzreal : (z.re : ℂ) = z := by apply Complex.ext <;> simp [← h]
    rw [← hzreal]
    simp
  · exact hE.2.2 z h

theorem denom_closed_ne_zero {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ}
    (hz : 0 ≤ z.im) (he : E z ≠ 0) : denom E z ≠ 0 :=
  one_sub_conj_mul_ne_zero (norm_anchor_lt_one hE) (thetaFn_norm_le_one_closed hE.1 hz he)

theorem baseKernel_eq {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ}
    (hz : 0 ≤ z.im) (he : E z ≠ 0) :
    baseKernel E z = (I / (2 * Real.pi)) * conj (E I) * E z * denom E z / (z + I) := by
  have hne : z ≠ conj I := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hEi : E I ≠ 0 := hE.1.2.1 I (by simp)
  rw [baseKernel, deBrangesKernel_of_ne E hne]
  simp only [kernelNum, denom, anchor, thetaFn, map_div₀, Complex.conj_I, sub_neg_eq_add]
  have hci : conj (E I) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hEi
  field_simp [hEi, hci, he]

theorem baseKernel_ne_zero {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ}
    (hz : 0 ≤ z.im) (he : E z ≠ 0) : baseKernel E z ≠ 0 := by
  rw [baseKernel_eq hE hz he]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (div_ne_zero I_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (by simpa using hE.1.2.1 I (by simp))) he) (denom_closed_ne_zero hE hz he)) (add_I_ne_zero hz)

theorem baseNorm_eq {E : ℂ → ℂ} (hE : IsStrictHB E) :
    baseNorm E = ‖E I‖ ^ 2 * defect E / (4 * Real.pi) := by
  rw [baseNorm, deBrangesKernel_diag E (by simp)]
  simp only [Complex.I_im, mul_one, Complex.ofReal_re]
  have he : ‖E I‖ ≠ 0 := norm_ne_zero_iff.mpr (hE.1.2.1 I (by simp))
  simp only [defect, anchor, thetaFn, norm_div, norm_fstar]
  field_simp

theorem baseNorm_pos {E : ℂ → ℂ} (hE : IsStrictHB E) : 0 < baseNorm E := by
  rw [baseNorm_eq hE]
  exact div_pos (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (hE.1.2.1 I (by simp))))
    (defect_pos hE)) (by positivity)

theorem baseKernel_I {E : ℂ → ℂ} : baseKernel E I = (baseNorm E : ℂ) := by
  rw [baseKernel, baseNorm, deBrangesKernel_diag E (by simp)]
  rfl

theorem theta_ne_zero_of_numerator {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ}
    (hz : z ∈ UHP) (hn : fstar E z - anchor E * E z ≠ 0) : theta E z ≠ 0 := by
  apply div_ne_zero _ (denom_ne_zero hE hz)
  intro h
  apply hn
  have he := hE.1.2.1 z hz
  dsimp only [thetaFn] at h
  have heq := (div_eq_iff he).mp (sub_eq_zero.mp h)
  exact sub_eq_zero.mpr heq

theorem defect_complex (E : ℂ → ℂ) :
    (defect E : ℂ) = 1 - anchor E * conj (anchor E) := by
  simp only [defect, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem mobius_kernel (a u v : ℂ) (hu : 1 - conj a * u ≠ 0) (hv : 1 - conj a * v ≠ 0) :
    1 - ((u - a) / (1 - conj a * u)) * conj ((v - a) / (1 - conj a * v)) =
      (1 - a * conj a) * (1 - u * conj v) /
        ((1 - conj a * u) * conj (1 - conj a * v)) := by
  have hvc : conj (1 - conj a * v) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hv
  simp only [map_div₀]
  apply (eq_div_iff (mul_ne_zero hu hvc)).2
  have hu' : 1 - u * conj a ≠ 0 := by simpa [mul_comm] using hu
  field_simp [hu, hvc, hu']
  simp only [map_sub, map_one, map_mul, Complex.conj_conj]
  ring

theorem theta_kernel {E : ℂ → ℂ} {z t : ℂ}
    (ht : denom E t ≠ 0) (hz : denom E z ≠ 0) :
    1 - theta E t * conj (theta E z) =
      (defect E : ℂ) * (1 - thetaFn E t * conj (thetaFn E z)) /
        (denom E t * conj (denom E z)) := by
  rw [defect_complex]
  exact mobius_kernel (anchor E) (thetaFn E t) (thetaFn E z) ht hz

theorem cayley_kernel {z t : ℂ} (ht : t + I ≠ 0) (hz : z + I ≠ 0) :
    1 - cayley t * conj (cayley z) =
      -(2 * I) * (t - conj z) / ((t + I) * (conj z - I)) := by
  have hzc : conj z - I ≠ 0 := by simpa [sub_eq_add_neg] using ((map_ne_zero (starRingEnd ℂ)).mpr hz : conj (z + I) ≠ 0)
  simp only [cayley, map_div₀, map_add, map_sub, Complex.conj_I, sub_neg_eq_add]
  have hzc' : -I + conj z ≠ 0 := by simpa [sub_eq_add_neg, add_comm] using hzc
  field_simp [ht, hz, hzc, hzc', sub_eq_add_neg]
  ring_nf
  field_simp [hzc']
  ring

theorem kernel_eq_theta {E : ℂ → ℂ} {z t : ℂ} (hz : E z ≠ 0) (ht : E t ≠ 0)
    (hne : t ≠ conj z) :
    deBrangesKernel E z t = (I / (2 * Real.pi)) * E t * conj (E z) *
      (1 - thetaFn E t * conj (thetaFn E z)) / (t - conj z) := by
  rw [deBrangesKernel_of_ne E hne]
  have hzc : conj (E z) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz
  simp only [kernelNum, thetaFn, map_div₀]
  field_simp [hz, ht, hzc]

theorem normalized_kernel {E : ℂ → ℂ} (hE : IsStrictHB E) {z t : ℂ}
    (hz : z ∈ UHP) (ht : 0 ≤ t.im) (hEt : E t ≠ 0) :
    (baseNorm E : ℂ) * deBrangesKernel E z t / (baseKernel E t * conj (baseKernel E z)) =
      (1 - theta E t * conj (theta E z)) / (1 - cayley t * conj (cayley z)) := by
  have hEz : E z ≠ 0 := hE.1.2.1 z hz
  have hEi : E I ≠ 0 := hE.1.2.1 I (by simp)
  have hEzc : conj (E z) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hEz
  have hEic : conj (E I) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hEi
  have hDt := denom_closed_ne_zero hE ht hEt
  have hDz := denom_ne_zero hE hz
  have hDzc : conj (denom E z) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hDz
  have hti := add_I_ne_zero ht
  have hzi := add_I_ne_zero (le_of_lt hz)
  have hzci : conj z - I ≠ 0 := by simpa [sub_eq_add_neg] using ((map_ne_zero (starRingEnd ℂ)).mpr hzi : conj (z + I) ≠ 0)
  have htz := sub_conj_ne_zero hz ht
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [kernel_eq_theta hEz hEt (sub_ne_zero.mp htz), baseKernel_eq hE ht hEt,
    baseKernel_eq hE (le_of_lt hz) hEz, baseNorm_eq hE,
    theta_kernel hDt hDz, cayley_kernel hti hzi]
  push_cast
  have he : ((‖E I‖ ^ 2 : ℝ) : ℂ) = E I * conj (E I) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_pow, he]
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_I,
    Complex.conj_ofReal, Complex.conj_conj, map_add]
  field_simp [hEz, hEt, hEi, hEzc, hEic, hDt, hDz, hDzc, hti, hzi, hzci, htz, hp]
  ring

/-- Scalar identifying the conjugate model kernel with a de Branges kernel. -/
def conjKernelCoeff (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  I * (defect E : ℂ) / 2 * (z + I) * conj (E I) / (denom E z * E z)

theorem normalized_conj_kernel {E : ℂ → ℂ} (hE : IsStrictHB E) {z t : ℂ}
    (hz : z ∈ UHP) (ht : 0 ≤ t.im) (hEt : E t ≠ 0) (htz : t ≠ z) :
    baseKernel E t * ((theta E t - theta E z) / (cayley t - cayley z)) =
      conjKernelCoeff E z * deBrangesKernel E (conj z) t := by
  have hEz := hE.1.2.1 z hz
  have hDt := denom_closed_ne_zero hE ht hEt
  have hDz := denom_ne_zero hE hz
  have hti := add_I_ne_zero ht
  have hzi := add_I_ne_zero hz.le
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdiff : cayley t - cayley z = 2 * I * (t-z) / ((t+I)*(z+I)) := by
    unfold cayley
    field_simp [hti, hzi]
    ring
  rw [baseKernel_eq hE ht hEt, hdiff, deBrangesKernel_of_ne E (by simpa using htz)]
  simp only [kernelNum, fstar, Complex.conj_conj]
  unfold conjKernelCoeff theta
  rw [defect_complex]
  dsimp only [denom, thetaFn] at *
  have hsub : t-z ≠ 0 := sub_ne_zero.mpr htz
  have hNt : E t - conj (anchor E) * fstar E t ≠ 0 := by
    have hh : (1 - conj (anchor E) * (fstar E t / E t)) * E t = E t - conj (anchor E) * fstar E t := by field_simp
    rw [← hh]
    exact mul_ne_zero hDt hEt
  have hNz : -(conj (anchor E) * fstar E z) + E z ≠ 0 := by
    have hh : (1 - conj (anchor E) * (fstar E z / E z)) * E z = -(conj (anchor E) * fstar E z) + E z := by field_simp; ring
    rw [← hh]
    exact mul_ne_zero hDz hEz
  field_simp [hDt, hDz, hti, hzi, hEt, hEz, hsub, hp, hNt, hNz]
  ring_nf
  field_simp [hNt, hNz]
  simp only [Complex.I_sq, fstar]
  ring

theorem one_add_conj_anchor_mul_theta {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ}
    (hz : 0 ≤ z.im) (he : E z ≠ 0) :
    1 + conj (anchor E) * theta E z = (defect E : ℂ) / denom E z := by
  have hd := denom_closed_ne_zero hE hz he
  rw [theta, defect_complex]
  apply (eq_div_iff hd).mpr
  dsimp only [denom] at *
  field_simp [hd]
  ring

theorem baseKernel_div_norm_sq {E : ℂ → ℂ} (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) (t : ℝ) :
    ‖baseKernel E t / E t‖ ^ 2 =
      ‖E I‖ ^ 2 * ‖denom E t‖ ^ 2 / (4 * Real.pi ^ 2 * (1+t^2)) := by
  rw [baseKernel_eq hE (by simp) (h0 t)]
  have hp : ‖(t : ℂ) + I‖ ^ 2 = 1+t^2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [norm_div, norm_mul, Complex.norm_conj, Complex.norm_I, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simp only [div_pow, mul_pow]
  rw [hp]
  have hn : ‖E t‖ ≠ 0 := norm_ne_zero_iff.mpr (h0 t)
  field_simp [hn]
  ring

end FF.FMeasure
