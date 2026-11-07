import FourierFrames.Cited.DeBrangesF.Transforms

/-!
# Two kernel identities for the normalized Cauchy transforms

The reproducing kernels at `z` and at its reflection yield the two identities
used in the contractivity argument. Their normalized squared norm supplies the
remaining input to Cauchy--Schwarz. See `blueprint/P4F_Elementary.md`, §§2--3.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF.FMeasure

/-- The disk form of the normalized reproducing kernel. -/
def modelKernel (E : ℂ → ℂ) (z t : ℂ) : ℂ :=
  (1 - theta E t * conj (theta E z)) / (1 - cayley t * conj (cayley z))

/-- The reflected kernel in disk coordinates. -/
def reflectedModelKernel (E : ℂ → ℂ) (z t : ℂ) : ℂ :=
  (theta E t - theta E z) / (cayley t - cayley z)

lemma disk_reflected_identity {u w : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ < 1)
    (v p : ℂ) :
    w * ((v-p)/(u-w)) = v * (1-w*conj u)⁻¹ - p * (1-w*conj u)⁻¹ - v + p := by
  have huc : u * conj u = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; norm_num
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have huw : u-w ≠ 0 := by
    intro h
    have := congrArg norm (sub_eq_zero.mp h)
    rw [hu] at this
    linarith
  have hd : 1-w*conj u ≠ 0 := by
    intro h
    have he := congrArg norm (sub_eq_zero.mp h)
    simp only [norm_one, norm_mul, Complex.norm_conj, hu, mul_one] at he
    linarith
  apply (mul_right_cancel₀ (mul_ne_zero huw hd))
  field_simp [huw, hd]
  linear_combination (p-v)*w*huc

variable {μ : Measure ℝ} {E : ℂ → ℂ}

theorem modelKernel_eq_normalized (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    {z : ℂ} (hz : z ∈ UHP) (t : ℝ) :
    modelKernel E z t = ((baseNorm E : ℂ) / conj (baseKernel E z)) *
      (deBrangesKernel E z t / deBrangesKernel E I t) := by
  rw [modelKernel, ← normalized_kernel hE hz (by simp) (h0 t)]
  dsimp only [baseKernel]
  ring

theorem integral_modelKernel (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    ∫ t : ℝ, modelKernel E z t ∂normalizedKernelMeasure μ E = 1 := by
  simp_rw [modelKernel_eq_normalized hE h0 hz]
  rw [integral_const_mul, integral_normalizedKernel hE h0 hμ
    (memHE_deBrangesKernel hE.1 h0 z)]
  have hκ : (baseNorm E : ℂ) ≠ 0 := ofReal_ne_zero.mpr (baseNorm_pos hE).ne'
  have hh : conj (baseKernel E z) ≠ 0 :=
    (map_ne_zero _).mpr (baseKernel_ne_zero hE (le_of_lt hz) (hE.1.2.1 z hz))
  rw [← conj_deBrangesKernel E I z]
  change (baseNorm E : ℂ) / conj (baseKernel E z) *
    (conj (baseKernel E z) / (baseNorm E : ℂ)) = 1
  field_simp

theorem conj_modelKernel (E : ℂ → ℂ) (z : ℂ) (t : ℝ) :
    conj (modelKernel E z t) =
      diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t -
        theta E z * (conj (theta E t) *
          diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t) := by
  simp only [modelKernel, map_div₀, map_sub, map_one, map_mul, Complex.conj_conj,
    diskCauchyKernel]
  ring

/-- Reproduction of the upper-half-plane kernel gives the first transform identity. -/
theorem cauchyF_sub_theta_mul_H (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    cauchyF μ E z - theta E z * cauchyH μ E z = 1 := by
  have h := congrArg conj (integral_modelKernel hE h0 hμ hz)
  rw [← integral_conj] at h
  simp only [conj_modelKernel, map_one] at h
  rw [integral_sub (integrable_cauchyF hE h0 hμ hz)
    ((integrable_cauchyH hE h0 hμ hz).const_mul _), integral_const_mul] at h
  simpa only [cauchyF, cauchyH, diskCauchyTransform, one_mul] using h

theorem reflectedModelKernel_eq_normalized (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) {z : ℂ} (hz : z ∈ UHP) (t : ℝ) :
    reflectedModelKernel E z t = conjKernelCoeff E z *
      (deBrangesKernel E (conj z) t / deBrangesKernel E I t) := by
  have htz : (t : ℂ) ≠ z := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.ofReal_im] at this
    exact (ne_of_gt hz) this.symm
  have h := normalized_conj_kernel hE hz (by simp) (h0 t) htz
  change deBrangesKernel E I t * reflectedModelKernel E z t = _ at h
  rw [← mul_div_assoc]
  apply (eq_div_iff (kernel_i_real_ne_zero hE h0 t)).2
  simpa only [mul_comm] using h

theorem integrable_reflectedModelKernel (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    Integrable (fun t : ℝ ↦ reflectedModelKernel E z t)
      (normalizedKernelMeasure μ E) := by
  simp_rw [reflectedModelKernel_eq_normalized hE h0 hz]
  exact (integrable_normalizedKernel hE h0 hμ
    (memHE_deBrangesKernel hE.1 h0 (conj z))).const_mul _

theorem cayley_mul_integral_reflectedModelKernel (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) (hμ : IsIsometricMeasure μ E)
    {z : ℂ} (hz : z ∈ UHP) :
    cayley z * (∫ t : ℝ, reflectedModelKernel E z t ∂normalizedKernelMeasure μ E) =
      theta E z := by
  by_cases hzi : z = I
  · simp [hzi]
  have hw : cayley z ≠ 0 := div_ne_zero (sub_ne_zero.mpr hzi) (add_I_ne_zero hz.le)
  simp_rw [reflectedModelKernel_eq_normalized hE h0 hz]
  rw [integral_const_mul, integral_normalizedKernel hE h0 hμ
    (memHE_deBrangesKernel hE.1 h0 (conj z))]
  have hv := normalized_conj_kernel hE hz (show 0 ≤ I.im by simp)
    (hE.1.2.1 I (by simp)) (Ne.symm hzi)
  simp only [baseKernel_I, theta_I, cayley_I, zero_sub, neg_div_neg_eq] at hv
  change (baseNorm E : ℂ) * (theta E z / cayley z) = _ at hv
  change cayley z * (conjKernelCoeff E z *
    (deBrangesKernel E (conj z) I / (baseNorm E : ℂ))) = _
  rw [← mul_div_assoc, ← hv]
  have hκ : (baseNorm E : ℂ) ≠ 0 := ofReal_ne_zero.mpr (baseNorm_pos hE).ne'
  field_simp

/-- Reproduction of the reflected kernel gives the second transform identity. -/
theorem cauchyJ_sub_mean_eq_theta_mul_F (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    cauchyJ μ E z - boundaryMean μ E = theta E z * cauchyF μ E z := by
  let := normalizedKernelMeasure_probability hE h0 hμ
  have hiF := integrable_cauchyF hE h0 hμ hz
  have hiJ := integrable_cauchyJ hE h0 hμ hz
  have hic := integrable_boundaryMean hE h0 hμ
  have he := integral_congr_ae (μ := normalizedKernelMeasure μ E)
    (Eventually.of_forall (fun t : ℝ ↦
      disk_reflected_identity (norm_cayley_real t) (norm_cayley_lt_one hz)
        (theta E t) (theta E z)))
  change (∫ t : ℝ, cayley z * reflectedModelKernel E z t ∂_) =
    ∫ t : ℝ, theta E t * diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t -
      theta E z * diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t -
      theta E t + theta E z ∂_ at he
  rw [integral_const_mul, cayley_mul_integral_reflectedModelKernel hE h0 hμ hz] at he
  have hAdd := integral_add ((hiJ.sub (hiF.const_mul (theta E z))).sub hic)
    (integrable_const (theta E z))
  have hSub := integral_sub (hiJ.sub (hiF.const_mul (theta E z))) hic
  have hSub' := integral_sub hiJ (hiF.const_mul (theta E z))
  simp only [Pi.sub_apply] at hAdd hSub hSub'
  rw [hAdd, hSub, hSub', integral_const_mul, integral_const] at he
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at he
  have hF : (∫ t : ℝ, diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t
      ∂normalizedKernelMeasure μ E) = cauchyF μ E z := by
    simp [cauchyF, diskCauchyTransform]
  rw [hF] at he
  change theta E z = cauchyJ μ E z - theta E z * cauchyF μ E z -
    boundaryMean μ E + theta E z at he
  linear_combination -he

/-- Normalized model kernels are square integrable. -/
theorem integrable_modelKernel_norm_sq (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    Integrable (fun t : ℝ ↦ ‖modelKernel E z t‖ ^ 2)
      (normalizedKernelMeasure μ E) := by
  simp_rw [modelKernel_eq_normalized hE h0 hz, norm_mul, mul_pow]
  exact (integrable_normalizedKernel_norm_sq hE h0 hμ
    (memHE_deBrangesKernel hE.1 h0 z)).const_mul _

/-- The exact squared norm of the normalized reproducing kernel. -/
theorem integral_modelKernel_norm_sq (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    ∫ t : ℝ, ‖modelKernel E z t‖ ^ 2 ∂normalizedKernelMeasure μ E =
      (1 - ‖theta E z‖ ^ 2) / (1 - ‖cayley z‖ ^ 2) := by
  simp_rw [modelKernel_eq_normalized hE h0 hz, norm_mul, mul_pow]
  rw [integral_const_mul, integral_normalizedKernel_norm_sq hE h0 hμ
    (memHE_deBrangesKernel hE.1 h0 z), heNormSq_kernel hE.1 h0 z]
  have hd := normalized_kernel hE hz hz.le (hE.1.2.1 z hz)
  have hn : ∀ v : ℂ, v * conj v = (‖v‖ ^ 2 : ℝ) := fun v ↦ by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn, hn, hn] at hd
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_sub] at hd
  have hd' := congrArg Complex.re hd
  simp only [Complex.div_ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hd'
  rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (baseNorm_pos hE), div_pow]
  have hk : ‖baseKernel E z‖ ≠ 0 := norm_ne_zero_iff.mpr
    (baseKernel_ne_zero hE hz.le (hE.1.2.1 z hz))
  have hκ := (baseNorm_pos hE).ne'
  calc
    baseNorm E ^ 2 / ‖baseKernel E z‖ ^ 2 *
        ((deBrangesKernel E z z).re / (deBrangesKernel E I I).re) =
      baseNorm E * (deBrangesKernel E z z).re / ‖baseKernel E z‖ ^ 2 := by
        change _ / _ * (_ / baseNorm E) = _
        field_simp
    _ = _ := hd'

end FF.FMeasure
