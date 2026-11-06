import FourierFrames.Defs

/-!
# Weierstrass elementary factors of variable genus

`elemFactor p w = (1 - w) exp (w + w²/2 + … + w^p/p)`, and the estimate
`‖E_p(w)^m - 1‖ ≤ 4 m ‖w‖^{p+1}` for `‖w‖ ≤ 1/2`, `2 m ‖w‖^{p+1} ≤ 1`.
-/

open Complex Filter Topology
open scoped ComplexConjugate

namespace FF
namespace Suff

/-- The Weierstrass elementary factor of genus `p`. -/
noncomputable def elemFactor (p : ℕ) (w : ℂ) : ℂ :=
  (1 - w) * Complex.exp (∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1))

theorem differentiable_elemFactor (p : ℕ) : Differentiable ℂ (elemFactor p) := by
  unfold elemFactor
  fun_prop

theorem elemFactor_eq_zero_iff (p : ℕ) (w : ℂ) : elemFactor p w = 0 ↔ w = 1 := by
  unfold elemFactor
  rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), sub_eq_zero, eq_comm]

theorem conj_elemFactor (p : ℕ) (w : ℂ) : conj (elemFactor p w) = elemFactor p (conj w) := by
  unfold elemFactor
  rw [map_mul, map_sub, map_one, ← Complex.exp_conj]
  congr 2
  simp [map_sum, map_div₀]

/-- The tail of the logarithm series: `E_p(w) = exp (- ∑_{k > p} w^k / k)`, with `‖T‖ ≤ 2‖w‖^{p+1}`
for `‖w‖ ≤ 1/2`. -/
theorem elemFactor_eq_exp_neg_tail (p : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ∃ T : ℂ, ‖T‖ ≤ 2 * ‖w‖ ^ (p + 1) ∧ elemFactor p w = Complex.exp (-T) := by
  have hw1 : ‖w‖ < 1 := by linarith
  have hs := Complex.hasSum_taylorSeries_neg_log' hw1
  have hs2 := (hasSum_nat_add_iff' p).mpr hs
  set T : ℂ := -Complex.log (1 - w) - ∑ i ∈ Finset.range p, w ^ (i + 1) / ((i : ℂ) + 1) with hT
  refine ⟨T, ?_, ?_⟩
  · have hg := (hasSum_geometric_of_lt_one (norm_nonneg w) hw1).mul_left (‖w‖ ^ (p + 1))
    have := hs2.norm_le_of_bounded hg (fun n ↦ by
      rw [norm_div, norm_pow]
      have h1 : (1 : ℝ) ≤ ‖((n + p : ℕ) : ℂ) + 1‖ := by
        rw [show (((n + p : ℕ) : ℂ) + 1) = (((n + p + 1 : ℕ)) : ℂ) by push_cast; ring,
          Complex.norm_natCast]
        exact_mod_cast Nat.succ_pos _
      calc ‖w‖ ^ (n + p + 1) / ‖((n + p : ℕ) : ℂ) + 1‖ ≤ ‖w‖ ^ (n + p + 1) :=
            div_le_self (by positivity) h1
        _ = ‖w‖ ^ (p + 1) * ‖w‖ ^ n := by rw [← pow_add]; congr 1; ring)
    refine this.trans ?_
    have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) two_pos]; linarith
    calc ‖w‖ ^ (p + 1) * (1 - ‖w‖)⁻¹ ≤ ‖w‖ ^ (p + 1) * 2 := by gcongr
      _ = 2 * ‖w‖ ^ (p + 1) := by ring
  · have h1 : (1 : ℂ) - w ≠ 0 := by
      intro h
      have : w = 1 := by linear_combination -h
      rw [this] at hw1; simp at hw1
    unfold elemFactor
    rw [hT, neg_sub, sub_neg_eq_add, Complex.exp_add, Complex.exp_log h1, mul_comm]

theorem norm_elemFactor_pow_sub_one_le (p m : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2)
    (h : 2 * m * ‖w‖ ^ (p + 1) ≤ 1) :
    ‖elemFactor p w ^ m - 1‖ ≤ 4 * m * ‖w‖ ^ (p + 1) := by
  obtain ⟨T, hT, hE⟩ := elemFactor_eq_exp_neg_tail p hw
  rw [hE, ← Complex.exp_nat_mul]
  have hb : ‖(m : ℂ) * -T‖ ≤ 2 * m * ‖w‖ ^ (p + 1) := by
    rw [norm_mul, norm_neg, Complex.norm_natCast]
    calc (m : ℝ) * ‖T‖ ≤ m * (2 * ‖w‖ ^ (p + 1)) := by gcongr
      _ = 2 * m * ‖w‖ ^ (p + 1) := by ring
  have := Complex.norm_exp_sub_one_le (hb.trans h)
  calc _ ≤ 2 * ‖(m : ℂ) * -T‖ := this
    _ ≤ 2 * (2 * m * ‖w‖ ^ (p + 1)) := by gcongr
    _ = 4 * m * ‖w‖ ^ (p + 1) := by ring

end Suff
end FF
