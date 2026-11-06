import FourierFrames.Defs

/-!
# M07 -- helper lemmas for `Corollary2.lean`: growth bounds for entire functions
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- Sup bound on balls from the real-part growth (Borel--Caratheodory). -/
theorem norm_le_of_re_growth {H : ℂ → ℂ} (hH : Differentiable ℂ H) {K : ℝ}
    (hK : ∀ z : ℂ, |(H z).re| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ z : ℂ, ‖z‖ ≤ r → ‖H z‖ ≤ C * r ^ (3 / 2 : ℝ) := by
  have hK0 : 0 ≤ K := by
    have := (abs_nonneg _).trans (hK 0)
    simpa using this
  refine ⟨2 * (K * 3 ^ (3 / 2 : ℝ) + 1) + 3 * ‖H 0‖, by positivity, fun r hr z hz ↦ ?_⟩
  set M : ℝ := K * (3 * r) ^ (3 / 2 : ℝ) + 1 with hM
  have hMpos : 0 < M := by positivity
  have hmaps : Set.MapsTo H (ball 0 (2 * r)) {w | w.re ≤ M} := by
    intro w hw
    have hw' : ‖w‖ < 2 * r := by simpa using hw
    have h1 : (H w).re ≤ K * (1 + ‖w‖) ^ (3 / 2 : ℝ) := (le_abs_self _).trans (hK w)
    have h2 : (1 + ‖w‖) ^ (3 / 2 : ℝ) ≤ (3 * r) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    simp only [mem_ofPred_eq]
    nlinarith
  have hz' : z ∈ ball (0 : ℂ) (2 * r) := by simp; linarith
  have hBC := Complex.borelCaratheodory hMpos hH.differentiableOn hmaps (by linarith) hz'
  have hden : r ≤ 2 * r - ‖z‖ := by linarith
  have hden0 : 0 < 2 * r - ‖z‖ := by linarith
  have e1 : 2 * M * ‖z‖ / (2 * r - ‖z‖) ≤ 2 * M := by
    rw [div_le_iff₀ hden0]; nlinarith [norm_nonneg z]
  have e2 : ‖H 0‖ * (2 * r + ‖z‖) / (2 * r - ‖z‖) ≤ 3 * ‖H 0‖ := by
    rw [div_le_iff₀ hden0]; nlinarith [norm_nonneg z, norm_nonneg (H 0)]
  have hr32 : 1 ≤ r ^ (3 / 2 : ℝ) := Real.one_le_rpow hr (by norm_num)
  have e3 : M ≤ (K * 3 ^ (3 / 2 : ℝ) + 1) * r ^ (3 / 2 : ℝ) := by
    rw [hM, Real.mul_rpow (by norm_num) (by linarith)]
    nlinarith
  calc ‖H z‖ ≤ 2 * M * ‖z‖ / (2 * r - ‖z‖) + ‖H 0‖ * (2 * r + ‖z‖) / (2 * r - ‖z‖) := hBC
    _ ≤ 2 * M + 3 * ‖H 0‖ := add_le_add e1 e2
    _ ≤ 2 * ((K * 3 ^ (3 / 2 : ℝ) + 1) * r ^ (3 / 2 : ℝ)) + 3 * ‖H 0‖ * r ^ (3 / 2 : ℝ) := by
        nlinarith [norm_nonneg (H 0)]
    _ = _ := by ring


end FF
