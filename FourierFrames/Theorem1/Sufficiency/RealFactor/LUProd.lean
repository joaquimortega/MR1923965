import FourierFrames.Defs

/-!
# Locally uniformly convergent infinite products of entire functions
-/

open Complex Filter Topology Set Metric
open scoped ComplexConjugate

namespace FF
namespace Suff

/-- The data of a locally uniformly convergent product `∏' k, f k z` of entire factors: on every
disc, `‖f k z - 1‖` is bounded by a summable sequence, for all but finitely many `k`. -/
def LUProd {κ : Type*} (f : κ → ℂ → ℂ) : Prop :=
  (∀ k, Differentiable ℂ (f k)) ∧ ∀ R : ℝ, ∃ u : κ → ℝ, Summable u ∧
    ∀ᶠ k in cofinite, ∀ z ∈ closedBall (0 : ℂ) R, ‖f k z - 1‖ ≤ u k

variable {κ : Type*} {f : κ → ℂ → ℂ}

theorem LUProd.mono {g : κ → ℂ → ℂ} (h : LUProd f) (hg : ∀ k, Differentiable ℂ (g k))
    (hle : ∀ k z, ‖g k z - 1‖ ≤ ‖f k z - 1‖) : LUProd g := by
  refine ⟨hg, fun R ↦ ?_⟩
  obtain ⟨u, hu, hev⟩ := h.2 R
  refine ⟨u, hu, ?_⟩
  filter_upwards [hev] with k hk z hz
  exact (hle k z).trans (hk z hz)

theorem LUProd.summable_norm_sub_one (h : LUProd f) (z : ℂ) :
    Summable fun k ↦ ‖f k z - 1‖ := by
  obtain ⟨u, hu, hev⟩ := h.2 ‖z‖
  refine hu.of_norm_bounded_eventually ?_
  filter_upwards [hev] with k hk
  rw [norm_norm]
  exact hk z (by simp)

theorem LUProd.multipliable (h : LUProd f) (z : ℂ) : Multipliable fun k ↦ f k z := by
  simpa using multipliable_one_add_of_summable (h.summable_norm_sub_one z)

theorem LUProd.hasProd (h : LUProd f) :
    HasProdLocallyUniformlyOn f (fun z ↦ ∏' k, f k z) univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨u, hu, hev⟩ := h.2 R
  have := Summable.hasProdUniformlyOn_one_add hK hu
    (f := fun k z ↦ f k z - 1)
    (by filter_upwards [hev] with k hk z hz using hk z (hR hz))
    (fun k ↦ ((h.1 k).continuous.sub continuous_const).continuousOn)
  simp only [add_sub_cancel] at this
  exact this

theorem LUProd.differentiable (h : LUProd f) : Differentiable ℂ (fun z ↦ ∏' k, f k z) := by
  rw [← differentiableOn_univ]
  refine (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp h.hasProd).differentiableOn
    ?_ isOpen_univ
  exact Eventually.of_forall fun t ↦ DifferentiableOn.fun_finsetProd
    fun a _ ↦ (h.1 a).differentiableOn

theorem LUProd.tprod_ne_zero (h : LUProd f) (z : ℂ) (hne : ∀ k, f k z ≠ 0) :
    ∏' k, f k z ≠ 0 := by
  have hne' : ∀ k, 1 + (f k z - 1) ≠ 0 := fun k ↦ by rw [add_sub_cancel]; exact hne k
  have := tprod_one_add_ne_zero_of_summable hne' (h.summable_norm_sub_one z)
  simpa only [add_sub_cancel] using this

theorem LUProd.tprod_eq_zero_iff (h : LUProd f) (z : ℂ) :
    ∏' k, f k z = 0 ↔ ∃ k, f k z = 0 := by
  constructor
  · intro h0
    by_contra hex
    push Not at hex
    exact h.tprod_ne_zero z hex h0
  · rintro ⟨k, hk⟩
    exact tprod_of_exists_eq_zero ⟨k, hk⟩

/-- `conj` commutes with the product when the factors do. -/
theorem LUProd.conj_tprod (h : LUProd f) (z : ℂ) :
    conj (∏' k, f k z) = ∏' k, conj (f k z) := by
  have := (h.multipliable z).hasProd.map (starRingEnd ℂ : ℂ →* ℂ) Complex.continuous_conj
  exact this.tprod_eq.symm

end Suff
end FF
