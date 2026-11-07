import FourierFrames.Cited.DeBrangesF.Contractive
import FourierFrames.Cited.DeBrangesF.Poisson

/-!
# de Branges' Theorem F: isometric measures

Two reproducing-kernel identities for a normalized probability measure give a
contractive holomorphic parameter by Cauchy--Schwarz. An explicit change of
measure recovers the original Poisson integral. This proves the unchanged
statement `TheoremF` with the additional linear term equal to zero.

See `blueprint/P4F_Elementary.md` and `reviews/R11_TheoremF.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF
namespace FMeasure

/-- The Schur parameter represents the Poisson integral of the original measure. -/
theorem poissonInt_eq_isometricSchur {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0) (hμ : IsIsometricMeasure μ E)
    {z : ℂ} (hz : z ∈ UHP) :
    poissonInt μ z ≠ ∞ ∧ (poissonInt μ z).toReal =
      ((E z + fstar E z * isometricSchur μ E z) /
        (E z - fstar E z * isometricSchur μ E z)).re := by
  have hp := poissonInt_cayley_spec (isometric_moment hE h0 hμ) hz
  refine ⟨hp.1, hp.2.trans ?_⟩
  have hc := weighted_cauchy_cayley_re (norm_anchor_lt_one hE)
    (norm_theta_lt_one hE hz) (cauchyF_ne_zero hE h0 hμ hz)
    (cauchyH_norm_le hE h0 hμ z hz) (cauchyF_sub_theta_mul_H hE h0 hμ hz)
    (cauchyJ_sub_mean_eq_theta_mul_F hE h0 hμ hz)
  have hd : (defect E : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (defect_pos hE).ne'
  have hF : ((1 + (‖anchor E‖ ^ 2 : ℝ) : ℂ) * cauchyF μ E z +
      conj (anchor E) * cauchyJ μ E z + anchor E * cauchyH μ E z) / (defect E : ℂ) =
        originalCauchyF μ z := by
    apply (div_eq_iff hd).2
    simpa only [mul_comm] using (originalCauchyF_expand hE h0 hμ hz).symm
  have hm : ((1 + (‖anchor E‖ ^ 2 : ℝ) : ℂ) +
      conj (anchor E) * boundaryMean μ E + anchor E * conj (boundaryMean μ E)) /
        (defect E : ℂ) = (originalMass μ : ℂ) := by
    apply (div_eq_iff hd).2
    simpa only [mul_comm] using (originalMass_expand hE h0 hμ).symm
  change (2 * (_ / (defect E : ℂ)) - _ / (defect E : ℂ)).re = _ at hc
  simp only [← Complex.ofReal_pow] at hc
  rw [hF, hm, ← thetaFn_eq_diskBack hE hz] at hc
  change (2 * originalCauchyF μ z - (originalMass μ : ℂ)).re =
    ((1 + thetaFn E z * isometricSchur μ E z) /
      (1 - thetaFn E z * isometricSchur μ E z)).re at hc
  rw [cayley_thetaFn_eq (hE.1.2.1 z hz)] at hc
  simpa [Complex.mul_re] using hc

end FMeasure

/-- **Theorem F**: every isometric measure has a contractive holomorphic parameter. -/
theorem theoremF_holds : TheoremF := by
  intro μ E hE h0 hμ
  have hμ' : IsIsometricMeasure μ E := hμ
  have hA := FMeasure.isometricSchur_spec hE h0 hμ'
  refine ⟨FMeasure.isometricSchur μ E, hA.1, hA.2, 0, le_rfl, ?_⟩
  intro z hz
  simpa only [zero_mul, add_zero] using FMeasure.poissonInt_eq_isometricSchur hE h0 hμ' hz

end FF
