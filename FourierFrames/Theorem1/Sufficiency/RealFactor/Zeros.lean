import Mathlib

/-!
# Zeros of a non-trivial entire function: orders, discreteness and countability of the real zeros
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

namespace FF
namespace Suff

theorem analyticOrderAt_ne_top_of_exists {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h : ∃ z, F z ≠ 0) (x : ℂ) : analyticOrderAt F x ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  obtain ⟨z, hz⟩ := h
  have hall : Set.EqOn F 0 Set.univ :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun y _ ↦ hF.analyticAt y) isPreconnected_univ (Set.mem_univ x) htop
  exact hz (hall (Set.mem_univ z))

theorem eventually_ne_zero_nhdsNE {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h : ∃ z, F z ≠ 0) (x : ℂ) : ∀ᶠ w in 𝓝[≠] x, F w ≠ 0 := by
  rcases (hF.analyticAt x).eventually_eq_zero_or_eventually_ne_zero with h1 | h1
  · exact absurd (analyticOrderAt_eq_top.mpr h1) (analyticOrderAt_ne_top_of_exists hF h x)
  · exact h1

theorem finite_realZeros {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) (R : ℝ) :
    {x : ℝ | F x = 0 ∧ |x| ≤ R}.Finite := by
  by_contra hinf
  have hsub : {x : ℝ | F x = 0 ∧ |x| ≤ R} ⊆ Icc (-R) R := fun x hx ↦ abs_le.mp hx.2
  obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc hsub
  rw [accPt_iff_frequently_nhdsNE] at hx
  have he := eventually_ne_zero_nhdsNE hF h (x : ℂ)
  have htend : Tendsto (fun y : ℝ ↦ (y : ℂ)) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(Complex.continuous_ofReal.tendsto x).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa using hy
  have := htend.eventually he
  obtain ⟨y, hy1, hy2⟩ := (hx.and_eventually this).exists
  exact hy2 hy1.1

theorem countable_realZeros {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) :
    {x : ℝ | F x = 0}.Countable := by
  have : {x : ℝ | F x = 0} = ⋃ n : ℕ, {x : ℝ | F x = 0 ∧ |x| ≤ n} := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      exact ⟨n, hx, hn⟩
    · rintro ⟨n, hx, -⟩; exact hx
  rw [this]
  exact countable_iUnion fun n ↦ (finite_realZeros hF h n).countable

end Suff
end FF
