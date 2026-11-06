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


theorem entire_affine_aux {H : ℂ → ℂ} (hH : Differentiable ℂ H) {K : ℝ}
    (hK : ∀ z : ℂ, |(H z).re| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ)) :
    ∃ α β : ℂ, ∀ z : ℂ, H z = α + β * z := by
  obtain ⟨C, hC0, hC⟩ := norm_le_of_re_growth hH hK
  have hH' : Differentiable ℂ (deriv H) := hH.deriv
  -- bound on the derivative
  have hder : ∀ R : ℝ, 1 ≤ R → ∀ w : ℂ, ‖w‖ ≤ 2 * R →
      ‖deriv H w‖ ≤ C * (3 * R) ^ (3 / 2 : ℝ) / R := by
    intro R hR w hw
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith) hH.diffContOnCl
      (fun u hu ↦ ?_)
    have hu' : ‖u - w‖ = R := by simpa [dist_eq_norm] using hu
    have : ‖u‖ ≤ 3 * R := by
      calc ‖u‖ = ‖(u - w) + w‖ := by ring_nf
        _ ≤ ‖u - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ 3 * R := by linarith
    exact hC (3 * R) (by linarith) u this
  have hsecond : ∀ c : ℂ, deriv (deriv H) c = 0 := by
    intro c
    have hbound : ∀ R : ℝ, 1 + ‖c‖ ≤ R → ‖deriv (deriv H) c‖ ≤ C * 3 ^ (3 / 2 : ℝ) / Real.sqrt R := by
      intro R hR
      have hR1 : 1 ≤ R := by linarith [norm_nonneg c]
      have hRpos : 0 < R := by linarith
      refine (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hH'.diffContOnCl
        (C := C * (3 * R) ^ (3 / 2 : ℝ) / R) (fun u hu ↦ ?_)).trans ?_
      · have hu' : ‖u - c‖ = R := by simpa [dist_eq_norm] using hu
        refine hder R hR1 u ?_
        calc ‖u‖ = ‖(u - c) + c‖ := by ring_nf
          _ ≤ ‖u - c‖ + ‖c‖ := norm_add_le _ _
          _ ≤ 2 * R := by linarith
      · have hsq : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hRpos.le
        have hsqpos : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRpos
        have h32 : R ^ (3 / 2 : ℝ) = R * Real.sqrt R := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hRpos.le (by norm_num)]
          norm_num
        rw [Real.mul_rpow (by norm_num) hRpos.le, h32]
        have : C * (3 ^ (3 / 2 : ℝ) * (R * Real.sqrt R)) / R / R = C * 3 ^ (3 / 2 : ℝ) / Real.sqrt R := by
          field_simp
          nlinarith [hsq]
        rw [this]
    have hlim : Tendsto (fun R : ℝ ↦ C * 3 ^ (3 / 2 : ℝ) / Real.sqrt R) atTop (𝓝 0) := by
      have : Tendsto (fun R : ℝ ↦ Real.sqrt R) atTop atTop := by
        simpa [Real.sqrt_eq_rpow] using tendsto_rpow_atTop (show (0:ℝ) < 1 / 2 by norm_num)
      exact this.const_div_atTop _ |>.congr' (by filter_upwards with R; rfl)
    have := ge_of_tendsto hlim (eventually_atTop.mpr ⟨1 + ‖c‖, fun R hR ↦ hbound R hR⟩)
    exact norm_le_zero_iff.mp this
  have hconst : ∀ z, deriv H z = deriv H 0 := fun z ↦
    is_const_of_deriv_eq_zero hH' hsecond z 0
  refine ⟨H 0, deriv H 0, fun z ↦ ?_⟩
  have h2 : Differentiable ℂ (fun z ↦ H z - deriv H 0 * z) := hH.sub (differentiable_const _ |>.mul differentiable_id)
  have h3 : ∀ z, deriv (fun z ↦ H z - deriv H 0 * z) z = 0 := fun z ↦ by
    have hd : HasDerivAt (fun z ↦ H z - deriv H 0 * z) (deriv H z - deriv H 0 * 1) z :=
      (hH z).hasDerivAt.sub ((hasDerivAt_id z).const_mul _)
    rw [hd.deriv, hconst z]; ring
  have := is_const_of_deriv_eq_zero h2 h3 z 0
  simp at this
  linear_combination this

end FF
