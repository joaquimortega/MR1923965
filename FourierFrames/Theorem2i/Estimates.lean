import FourierFrames.Theorem2i.Cells
import FourierFrames.Theorem2i.Near

/-!
# M08 helper: estimates of the cell terms

See `blueprint/M08_Theorem2i.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

/-! ## §5. Estimates of `j_n(z)`, `Im z ≥ 0`, `z ≠ 0`

Constants: `ρ₁ = 2 (1 + C)`, `K₀ = 8 + 2 ρ₁`, `c = cAngle`. -/

/-- Constant `ρ₁`. -/
def rho1 (C : ℝ) : ℝ := 2 * (1 + C)
/-- Constant `K₀`. -/
def K0 (C : ℝ) : ℝ := 8 + 2 * rho1 C

/-- Cells below `|z|/2`. -/
theorem RegData.abs_cellTerm_below (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : 0 ≤ z.im) (hzn : t n ≤ ‖z‖ / 2) (hz0 : z ≠ 0) :
    |cellTerm ψ t C n z| ≤ (4 + 2 * (1 + C) * Real.log (1 + C)) * (cellLen t n / ‖z‖) := by
  sorry

/-- Cells above `2|z|`. -/
theorem RegData.abs_cellTerm_above (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) {z : ℂ}
    (hz : 0 ≤ z.im) (hzn : 2 * ‖z‖ ≤ t (n - 1)) (hz0 : z ≠ 0) :
    |cellTerm ψ t C n z| ≤
      (2 * Real.log (1 + C) + 2) * (cellLen t n * ‖z‖ / t (n - 1) ^ 2) := by
  sorry

/-- Cells comparable to `|z|` and at distance `≥ K₀ d_n`. -/
theorem RegData.abs_cellTerm_far (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) {z : ℂ}
    (hz : 0 ≤ z.im) (hz1 : ‖z‖ ≤ rho1 C * rCentre ψ t n) (hz2 : rCentre ψ t n ≤ rho1 C * ‖z‖)
    (hfar : K0 C * cellLen t n ≤ ‖z - rCentre ψ t n‖) :
    |cellTerm ψ t C n z| ≤
      (2 * rho1 C * (1 + C) ^ 3 + (3 + rho1 C)) * (cellLen t n ^ 2 / ‖z - rCentre ψ t n‖ ^ 2)
        + 2 * (cellLen t n * z.im / ‖z - rCentre ψ t n‖ ^ 2) := by
  sorry

/-- Cells at distance `< K₀ d_n` (needs `DensBound`). Also valid for `n = 1`. -/
theorem RegData.abs_cellTerm_near (h : RegData ψ t C M) (hK : DensBound ψ t K) {n : ℕ}
    (hn : 1 ≤ n) {z : ℂ} (hz : 0 ≤ z.im)
    (hnear : ‖z - rCentre ψ t n‖ < K0 C * cellLen t n) :
    |cellTerm ψ t C n z| ≤ 2 * K + Real.log (K0 C + 1) +
      Real.log (Real.pi / (2 * cAngle ψ t C)) := by
  have hK0 : 0 < K0 C := by
    have := h.one_le; unfold K0 rho1; linarith
  exact h.abs_cellTerm_near_gen hK hn hz hK0 hnear

/-- Counting: the number of `n ∈ W(z)` with `‖z - r_n‖ < K₀ d_n` is at most `3 (1 + K₀²) M`,
and `∑_{n ∈ W(z), far} d_n² / ‖z - r_n‖² ≤ 3 (1 + K₀⁻²) M`. -/
theorem RegData.card_near_le (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0) :
    ((({n : ℕ | 1 ≤ n ∧ ‖z‖ / 2 < t n ∧ t n < 2 * ‖z‖ ∧
        ‖z - rCentre ψ t n‖ < K0 C * cellLen t n}) : Set ℕ).ncard : ℝ) ≤
      3 * (1 + K0 C ^ 2) * M := by
  have hK0 : 0 < K0 C := by
    have := h.one_le; unfold K0 rho1; linarith
  have hfin := h.finite_near hz0 hK0
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact h.finset_card_near_le hz0 hK0 _ (fun n hn => by simpa using hn)

theorem RegData.sum_far_le (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0) :
    ∑' n : {n : ℕ | 1 ≤ n ∧ ‖z‖ / 2 < t n ∧ t n < 2 * ‖z‖ ∧
        K0 C * cellLen t n ≤ ‖z - rCentre ψ t n‖},
      cellLen t n ^ 2 / ‖z - rCentre ψ t n‖ ^ 2 ≤ 3 * (1 + (K0 C)⁻¹ ^ 2) * M := by
  have hK0 : 0 < K0 C := by
    have := h.one_le; unfold K0 rho1; linarith
  have hM := D2.one_le_M h
  refine Real.tsum_le_of_sum_le (fun n => by positivity) fun u => ?_
  have := h.finset_sum_far_le hz0 hK0 (u.map (Function.Embedding.subtype _))
    (fun n hn => by
      obtain ⟨m, _, rfl⟩ := Finset.mem_map.mp hn
      exact m.2)
  rw [Finset.sum_map] at this; exact this

/-- The Riemann-sum bound `∑_n d_n y / |z - r_n|² ≤ (9/4) π` over far `n`. -/
theorem RegData.sum_far_im_le (h : RegData ψ t C M) {z : ℂ} :
    ∑' n : {n : ℕ | 1 ≤ n ∧ K0 C * cellLen t n ≤ ‖z - rCentre ψ t n‖},
      cellLen t n * z.im / ‖z - rCentre ψ t n‖ ^ 2 ≤ 9 / 4 * Real.pi := by
  have hK8 : 8 ≤ K0 C := by
    have := h.one_le; unfold K0 rho1; linarith
  have hpi := Real.pi_pos
  have key : ∀ u : Finset {n : ℕ | 1 ≤ n ∧ K0 C * cellLen t n ≤ ‖z - rCentre ψ t n‖},
      ∑ x ∈ u, cellLen t x * z.im / ‖z - (rCentre ψ t x : ℂ)‖ ^ 2 ≤ 9 / 4 * Real.pi := by
    intro u
    have := h.finset_sum_far_im_le hK8 (u.map (Function.Embedding.subtype _))
      (fun n hn => by
        obtain ⟨m, _, rfl⟩ := Finset.mem_map.mp hn
        exact m.2)
    rw [Finset.sum_map] at this; exact this
  rcases le_or_gt 0 z.im with hy | hy
  · exact Real.tsum_le_of_sum_le (fun n => by
      have := D2.cellLen_pos h n.2.1
      positivity) key
  · refine le_trans (tsum_nonpos fun n => ?_) (by positivity)
    have := D2.cellLen_pos h n.2.1
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos this.le hy.le)
      (by positivity)

-- `exists_bound_cellTerm` and `exists_approx` are proved in `Theorem2i/Assembly.lean`.

end FF
