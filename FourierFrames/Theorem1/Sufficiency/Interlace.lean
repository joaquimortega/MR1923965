import FourierFrames.PW.PlancherelPolya

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF
namespace Suff

/-- Core of the interlacing argument: two points of the shifted level set whose indices differ
by at least `2` are at distance `≥ δ`. -/
theorem sepBy_aux {φ : ℝ → ℝ} (hc : Continuous φ) {δ : ℝ}
    (hsep : IsSepBy δ (phaseLevel φ (Real.pi / 2))) {ε : ℝ} (hε0 : 0 < ε) (hεπ : ε < Real.pi)
    {x y : ℝ} {k k' : ℤ} (hx : φ x = Real.pi / 2 + ε + k * Real.pi)
    (hy : φ y = Real.pi / 2 + ε + k' * Real.pi) (hxy : x < y) (hk : k + 2 ≤ k') :
    δ ≤ y - x := by
  have hπ := Real.pi_pos
  have hkR : (k : ℝ) + 2 ≤ k' := by exact_mod_cast hk
  have hmid : ∀ u : ℝ, φ x < u → u < φ y → ∃ z, x < z ∧ z < y ∧ φ z = u := by
    intro u h1 h2
    have := intermediate_value_Ioo hxy.le hc.continuousOn ⟨h1, h2⟩
    obtain ⟨z, ⟨hz1, hz2⟩, hz⟩ := this
    exact ⟨z, hz1, hz2, hz⟩
  obtain ⟨z1, hz1a, hz1b, hz1⟩ := hmid (Real.pi / 2 + ((k + 1 : ℤ) : ℝ) * Real.pi)
    (by rw [hx]; push_cast; nlinarith) (by rw [hy]; push_cast; nlinarith)
  obtain ⟨z2, hz2a, hz2b, hz2⟩ := hmid (Real.pi / 2 + ((k + 2 : ℤ) : ℝ) * Real.pi)
    (by rw [hx]; push_cast; nlinarith) (by rw [hy]; push_cast; nlinarith)
  have hne : z2 ≠ z1 := by
    intro h
    rw [h] at hz2
    rw [hz1] at hz2
    push_cast at hz2
    nlinarith
  have := hsep z2 ⟨k + 2, hz2⟩ z1 ⟨k + 1, hz1⟩ hne
  have h3 : |z2 - z1| < y - x := by
    rw [abs_lt]; constructor <;> linarith
  linarith

theorem phaseLevel_sepBy_two_aux {φ : ℝ → ℝ} (hc : Continuous φ) (hφ : StrictMono φ) {δ : ℝ}
    (hsep : IsSepBy δ (phaseLevel φ (Real.pi / 2))) {ε : ℝ} (hε0 : 0 < ε) (hεπ : ε < Real.pi) :
    ∃ A B : Set ℝ, phaseLevel φ (Real.pi / 2 + ε) = A ∪ B ∧ IsSepBy δ A ∧ IsSepBy δ B := by
  have hπ := Real.pi_pos
  have main : ∀ (j : ℤ) {x y : ℝ} {k k' : ℤ}, φ x = Real.pi / 2 + ε + k * Real.pi →
      φ y = Real.pi / 2 + ε + k' * Real.pi → k % 2 = j → k' % 2 = j → x < y → δ ≤ y - x := by
    intro j x y k k' hx hy h1 h2 hxy
    have hlt : φ x < φ y := hφ hxy
    rw [hx, hy] at hlt
    have : (k : ℝ) < k' := by nlinarith
    have hkk : k < k' := by exact_mod_cast this
    exact sepBy_aux hc hsep hε0 hεπ hx hy hxy (by omega)
  have key : ∀ j : ℤ,
      IsSepBy δ {x : ℝ | ∃ k : ℤ, φ x = Real.pi / 2 + ε + k * Real.pi ∧ k % 2 = j} := by
    intro j a ha b hb hab
    obtain ⟨k, hk, hkj⟩ := ha
    obtain ⟨k', hk', hkj'⟩ := hb
    rcases lt_or_gt_of_ne hab with h | h
    · rw [abs_sub_comm, abs_of_pos (by linarith)]
      exact main j hk hk' hkj hkj' h
    · rw [abs_of_pos (by linarith)]
      exact main j hk' hk hkj' hkj h
  refine ⟨{x : ℝ | ∃ k : ℤ, φ x = Real.pi / 2 + ε + k * Real.pi ∧ k % 2 = 0},
    {x : ℝ | ∃ k : ℤ, φ x = Real.pi / 2 + ε + k * Real.pi ∧ k % 2 = 1}, ?_, key 0, key 1⟩
  ext x
  constructor
  · rintro ⟨k, hk⟩
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · exact Or.inl ⟨k, hk, h⟩
    · exact Or.inr ⟨k, hk, h⟩
  · rintro (⟨k, hk, -⟩ | ⟨k, hk, -⟩) <;> exact ⟨k, hk⟩

end Suff
end FF
