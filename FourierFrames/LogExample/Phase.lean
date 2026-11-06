import Mathlib

/-!
# Auxiliary lemma for `LogExample.lean`: `∫ cos² φ` over long intervals for an increasing phase.
-/

open MeasureTheory Set

namespace FF.LogEx

theorem integral_cos_sq_phase_ge {φ φ' : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hcont : Continuous φ') {m₁ M₁ : ℝ} (hM : 0 < M₁) (h1 : ∀ x, m₁ ≤ φ' x)
    (h2 : ∀ x, φ' x ≤ M₁) {T : ℝ} (hT : 0 ≤ T) :
    (m₁ * T / 2 - 1 / 2) / M₁ ≤ ∫ x in (0 : ℝ)..T, Real.cos (φ x) ^ 2 := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun x ↦ (hφ x).continuousAt
  set G : ℝ → ℝ := fun x ↦ φ x / 2 + Real.sin (2 * φ x) / 4 with hG
  have hGd : ∀ x, HasDerivAt G (Real.cos (φ x) ^ 2 * φ' x) x := by
    intro x
    have h := ((hφ x).div_const 2).add ((((hφ x).const_mul 2).sin).div_const 4)
    convert h using 1
    rw [Real.cos_sq]; ring
  have hint : IntervalIntegrable (fun x ↦ Real.cos (φ x) ^ 2 * φ' x) volume 0 T :=
    ((Real.continuous_cos.comp hφc).pow 2 |>.mul hcont).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hGd x) hint
  have hmono : Monotone (fun x ↦ φ x - m₁ * x) := by
    apply monotone_of_deriv_nonneg
    · exact fun x ↦ ((hφ x).fun_sub (by simpa using (hasDerivAt_id' x).const_mul m₁)).differentiableAt
    · intro x
      have hd : HasDerivAt (fun x ↦ φ x - m₁ * x) (φ' x - m₁) x := by
        have h3 : HasDerivAt (fun x : ℝ ↦ m₁ * x) m₁ x := by
          simpa using (hasDerivAt_id' x).const_mul m₁
        exact (hφ x).fun_sub h3
      rw [hd.deriv]
      have := h1 x; linarith
  have hφT : m₁ * T ≤ φ T - φ 0 := by
    have := hmono hT
    simp at this; linarith
  have hsin1 := Real.neg_one_le_sin (2 * φ T)
  have hsin2 := Real.sin_le_one (2 * φ T)
  have hsin3 := Real.neg_one_le_sin (2 * φ 0)
  have hsin4 := Real.sin_le_one (2 * φ 0)
  have hGT : (m₁ * T / 2 - 1 / 2) ≤ G T - G 0 := by
    simp only [hG]; linarith
  have hle : ∫ x in (0 : ℝ)..T, Real.cos (φ x) ^ 2 * φ' x / M₁ ≤
      ∫ x in (0 : ℝ)..T, Real.cos (φ x) ^ 2 := by
    apply intervalIntegral.integral_mono_on hT
    · exact (hint.div_const M₁)
    · exact ((Real.continuous_cos.comp hφc).pow 2).intervalIntegrable _ _
    · intro x _
      rw [div_le_iff₀ hM]
      have := sq_nonneg (Real.cos (φ x))
      nlinarith [h2 x]
  rw [intervalIntegral.integral_div, hftc] at hle
  calc (m₁ * T / 2 - 1 / 2) / M₁ ≤ (G T - G 0) / M₁ := by gcongr
    _ ≤ _ := hle

end FF.LogEx
