import FourierFrames.Cited.DeBrangesF.Basic

/-!
# The finite moment of an isometric measure

The kernel at `i`, divided by `E`, is bounded below by a positive constant times
`(1+t²)⁻¹/²` on the real line. Its squared norm in an isometric measure is finite,
so the same is true of the moment `∫ (1+t²)⁻¹ dμ`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- The kernel at `i`, divided by `E`, controls the standard Herglotz weight. -/
theorem momentWeight_le_kernel {E : ℂ → ℂ} (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) (t : ℝ) :
    1 / (1 + t ^ 2) ≤
      (2 * Real.pi / (‖E I‖ - ‖fstar E I‖)) ^ 2 *
        ‖deBrangesKernel E I t / E t‖ ^ 2 := by
  have hc : 0 < ‖E I‖ - ‖fstar E I‖ := by
    rw [norm_fstar]
    exact sub_pos.mpr (hE.2 I (by simp))
  have he : ‖E (t : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (h0 t)
  have hr : ‖fstar E (t : ℂ) / E t‖ = 1 := by
    rw [norm_div, fstar_ofReal, Complex.norm_conj, div_self he]
  have hlower := norm_sub_norm_le (conj (E I))
    ((fstar E (t : ℂ) / E t) * conj (fstar E I))
  rw [Complex.norm_conj, norm_mul, hr, one_mul, Complex.norm_conj] at hlower
  have hid :
      (deBrangesKernel E I t / E t) * ((2 * Real.pi : ℂ) * ((t : ℂ) + I)) =
        I * (conj (E I) - (fstar E (t : ℂ) / E t) * conj (fstar E I)) := by
    have hne : (t : ℂ) ≠ conj I := by
      intro h
      have := congrArg Complex.im h
      simp at this
    rw [deBrangesKernel_of_ne E hne]
    simp only [kernelNum, Complex.conj_I, sub_neg_eq_add]
    have hti : (t : ℂ) + I ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [h0 t]
  have hn := congrArg norm hid
  simp only [norm_mul, Complex.norm_I, one_mul, norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at hn
  have hlow : ‖E I‖ - ‖fstar E I‖ ≤
      ‖deBrangesKernel E I t / E t‖ * (2 * Real.pi * ‖(t : ℂ) + I‖) := by
    rw [hn]
    exact hlower
  have hsq := (sq_le_sq₀ hc.le (by positivity)).2 hlow
  have htn : ‖(t : ℂ) + I‖ ^ 2 = 1 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [mul_pow, mul_pow, mul_pow, htn] at hsq
  have hd : 0 < 1 + t ^ 2 := by positivity
  apply (div_le_iff₀ hd).2
  have hcs : (‖E I‖ - ‖fstar E I‖) ^ 2 > 0 := sq_pos_of_pos hc
  apply (mul_le_mul_iff_right₀ hcs).mp
  field_simp
  nlinarith [hsq]

/-- An isometric measure has finite Herglotz moment. -/
theorem isometric_moment {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) :
    ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞ := by
  let C := (2 * Real.pi / (‖E I‖ - ‖fstar E I‖)) ^ 2
  have hk := memHE_deBrangesKernel hE.1 h0 I
  have hb : (∫⁻ t : ℝ, ‖deBrangesKernel E I t / E t‖ₑ ^ 2 ∂μ) < ∞ := by
    rw [hμ _ hk]
    exact hk.heNormSq_lt_top hE.1.1 h0
  calc
    ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ ≤
        ∫⁻ t : ℝ, ENNReal.ofReal C * ‖deBrangesKernel E I t / E t‖ₑ ^ 2 ∂μ := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [enorm_sq_eq_ofReal, ← ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (momentWeight_le_kernel hE h0 t)
    _ = ENNReal.ofReal C * ∫⁻ t : ℝ, ‖deBrangesKernel E I t / E t‖ₑ ^ 2 ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb

end FF
