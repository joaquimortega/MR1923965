import FourierFrames.Cited.DeBrangesF.Analytic
import FourierFrames.Cited.DeBrangesF.KernelIdentities
import FourierFrames.Cited.DeBrangesF.Schur

/-!
# The contractive holomorphic parameter of an isometric measure

The two kernel identities imply the Schur inequality. The identity theorem
extends the inequality across the zeros of the normalized inner function, and
an inverse disk automorphism returns the parameter for the original function E.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF.FMeasure

variable {μ : Measure ℝ} {E : ℂ → ℂ}

/-- The numerator of the normalized inner function is not identically zero. -/
theorem theta_numerator_ne_zero_at_zero (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) : fstar E 0 - anchor E * E 0 ≠ 0 := by
  intro h
  have hn := congrArg norm (sub_eq_zero.mp h)
  change ‖fstar E (0 : ℝ)‖ = ‖anchor E * E (0 : ℝ)‖ at hn
  rw [fstar_ofReal, Complex.norm_conj, norm_mul] at hn
  have hp : 0 < ‖E (0 : ℝ)‖ := norm_pos_iff.mpr (h0 0)
  have ha := norm_anchor_lt_one hE
  nlinarith

/-- The normalized weighted transform is dominated by the unweighted transform. -/
theorem cauchyH_norm_le (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) : ∀ z ∈ UHP, ‖cauchyH μ E z‖ ≤ ‖cauchyF μ E z‖ := by
  let := normalizedKernelMeasure_probability hE h0 hμ
  apply norm_le_on_upper_of_mul_norm_le
    ((FF.Differentiable.fstar hE.1.1).sub (hE.1.1.const_mul (anchor E)))
    ⟨0, theta_numerator_ne_zero_at_zero hE h0⟩
    (differentiableOn_cauchyH hE h0 hμ).continuousOn
    (differentiableOn_cauchyF hE h0 hμ).continuousOn
    (φ := theta E)
    (fun _ hz hn ↦ theta_ne_zero_of_numerator hE hz hn)
  intro z hz
  have h₁ := cauchyF_sub_theta_mul_H hE h0 hμ hz
  have h₂ := cauchyJ_sub_mean_eq_theta_mul_F hE h0 hμ hz
  have h₁' : cauchyF μ E z - 1 = theta E z * cauchyH μ E z := by
    linear_combination h₁
  have hs := schur_bound_of_kernel_identities
    (ρ := normalizedKernelMeasure μ E) measurable_cayley_real norm_cayley_real
    (measurable_theta_real hE.1) (norm_theta_real hE h0)
    (norm_cayley_lt_one hz) (norm_theta_lt_one hE hz)
    h₁' h₂ (integral_modelKernel_norm_sq hE h0 hμ hz)
  change ‖cauchyF μ E z - 1‖ ≤ ‖theta E z * cauchyF μ E z‖ at hs
  rwa [h₁'] at hs

/-- The Schur parameter in the original de Branges normalization. -/
def isometricSchur (μ : Measure ℝ) (E : ℂ → ℂ) : ℂ → ℂ :=
  schurParameter (anchor E) (cauchyF μ E) (cauchyH μ E)

/-- The constructed parameter is holomorphic and has norm at most one. -/
theorem isometricSchur_spec (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) :
    DifferentiableOn ℂ (isometricSchur μ E) UHP ∧
      ∀ z ∈ UHP, ‖isometricSchur μ E z‖ ≤ 1 :=
  schurParameter_spec (norm_anchor_lt_one hE)
    (differentiableOn_cauchyF hE h0 hμ) (differentiableOn_cauchyH hE h0 hμ)
    (fun _ hz ↦ cauchyF_ne_zero hE h0 hμ hz) (cauchyH_norm_le hE h0 hμ)

/-- Undo the disk automorphism of the original inner function. -/
theorem thetaFn_eq_diskBack (hE : IsStrictHB E) {z : ℂ} (hz : z ∈ UHP) :
    thetaFn E z = (anchor E + theta E z) / (1 + conj (anchor E) * theta E z) := by
  have hn := diskBack_den_ne_zero (norm_anchor_lt_one hE) (norm_theta_lt_one hE hz).le
  apply (eq_div_iff hn).2
  have hd := denom_ne_zero hE hz
  unfold theta
  dsimp only [denom] at hd ⊢
  have hd' : 1 - thetaFn E z * conj (anchor E) ≠ 0 := by simpa only [mul_comm] using hd
  field_simp [hd, hd']
  ring

/-- The inner-function Cayley quotient is the quotient in Theorem F. -/
theorem cayley_thetaFn_eq {E : ℂ → ℂ} {z A : ℂ} (hE : E z ≠ 0) :
    (1 + thetaFn E z * A) / (1 - thetaFn E z * A) =
      (E z + fstar E z * A) / (E z - fstar E z * A) := by
  unfold thetaFn
  field_simp

end FF.FMeasure
