import FourierFrames.Defs
import OrtegaCerdaSeip.Lemma3.Potential

/-!
# M07 -- helper lemmas for `Corollary2.lean`: the kernel of the potential `U`
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- The kernel of the potential `U`: `log|1 - z/t| + 1_{|t|>1} Re(z/t)`. -/
def potKernel (z : ℂ) (t : ℝ) : ℝ :=
  Real.log ‖1 - z / t‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).re

theorem OCS_isMultWeight_one : OCS.IsMultWeight (fun _ : ℝ ↦ (1 : ℝ)) 1 1 :=
  ⟨measurable_const, one_pos, fun _ ↦ le_rfl, fun _ ↦ le_rfl⟩

theorem potKernel_eq (z : ℂ) : potKernel z = OCS.multUIntegrand (fun _ : ℝ ↦ (1 : ℝ)) z := by
  funext t; simp [OCS.multUIntegrand, potKernel]

theorem integrable_potKernel (z : ℂ) : Integrable (potKernel z) := by
  rw [potKernel_eq]; exact OCS.integrable_multUIntegrand OCS_isMultWeight_one z

theorem measurable_potKernel (z : ℂ) : Measurable (potKernel z) := by
  rw [potKernel_eq]; exact OCS.measurable_multUIntegrand OCS_isMultWeight_one z

theorem multU_eq_integral (g : ℝ → ℝ) (z : ℂ) :
    OCS.multU g 0 z = ∫ t, potKernel z t * g t := by
  simp [OCS.multU, potKernel]

theorem integrable_potKernel_mul {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ t, |g t| ≤ M) (z : ℂ) : Integrable fun t ↦ potKernel z t * g t :=
  (integrable_potKernel z).mul_bdd (c := M) hg.aestronglyMeasurable (ae_of_all _ fun t ↦ by simpa using hM t)


end FF
