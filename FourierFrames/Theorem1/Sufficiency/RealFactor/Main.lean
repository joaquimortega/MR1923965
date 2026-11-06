import FourierFrames.Theorem1.Sufficiency.RealFactor.Product
import FourierFrames.HB.Basic

/-!
# `exists_realFactor`: the quotient `G = F / S`
-/

open Complex Filter Topology Set Metric
open scoped ComplexConjugate

namespace FF
namespace Suff

noncomputable section

variable {F : ℂ → ℂ}

/-- The quotient `F / S`, extended at the zeros of `S` by its limit. -/
def quotG (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  if Sfac F z = 0 then limUnder (𝓝[≠] z) (fun w ↦ F w / Sfac F w) else F z / Sfac F z

theorem quotG_local (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) (z₀ : ℂ) :
    ∃ Gl : ℂ → ℂ, DifferentiableAt ℂ Gl z₀ ∧ (quotG F =ᶠ[𝓝 z₀] Gl) ∧
      ((∃ x : ℝ, z₀ = (x : ℂ)) → Gl z₀ ≠ 0) := by
  by_cases hS : Sfac F z₀ = 0
  · obtain ⟨a, rfl, ha⟩ := Sfac_eq_zero hF h hS
    obtain ⟨S₁, hS₁a, hS₁0, hSeq⟩ := Sfac_local hF h ha
    have hord := (hF.analyticAt (a : ℂ)).analyticOrderAt_ne_top.mp
      (analyticOrderAt_ne_top_of_exists hF h _)
    obtain ⟨F₁, hF₁a, hF₁0, hFeq⟩ := hord
    -- `mult F a = analyticOrderNatAt F a`
    have hm : mult F a = analyticOrderNatAt F (a : ℂ) := rfl
    set m := mult F a with hmdef
    have hS₁ev : ∀ᶠ w in 𝓝 (a : ℂ), S₁ w ≠ 0 := hS₁a.continuousAt.eventually_ne hS₁0
    have hpunct0 : ∀ᶠ w in 𝓝[≠] (a : ℂ),
        Sfac F w ≠ 0 ∧ F w / Sfac F w = F₁ w / S₁ w := by
      have hFev : ∀ᶠ w in 𝓝[≠] (a : ℂ), F w = (w - a) ^ m • F₁ w := by
        rw [hm]; exact hFeq.filter_mono nhdsWithin_le_nhds
      filter_upwards [hFev, hS₁ev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with
        w hw1 hw2 hw3
      have hwa : w - a ≠ 0 := sub_ne_zero.mpr hw3
      have hSw : Sfac F w = (w - a) ^ m * S₁ w := hSeq w
      have hSw0 : Sfac F w ≠ 0 := by rw [hSw]; exact mul_ne_zero (pow_ne_zero _ hwa) hw2
      refine ⟨hSw0, ?_⟩
      rw [hw1, hSw, smul_eq_mul]
      field_simp
    have hcont : ContinuousAt (fun w ↦ F₁ w / S₁ w) (a : ℂ) :=
      hF₁a.continuousAt.div hS₁a.continuousAt hS₁0
    have hat : quotG F (a : ℂ) = F₁ a / S₁ a := by
      unfold quotG
      simp only [hS, ↓reduceIte]
      refine Filter.Tendsto.limUnder_eq ?_
      have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {(a : ℂ)}ᶜ))
      refine hlim.congr' ?_
      filter_upwards [hpunct0] with w hw using hw.2.symm
    have hpunct : ∀ᶠ w in 𝓝[≠] (a : ℂ), quotG F w = F₁ w / S₁ w := by
      filter_upwards [hpunct0] with w hw
      unfold quotG
      simp only [hw.1, ↓reduceIte]
      exact hw.2
    refine ⟨fun w ↦ F₁ w / S₁ w, hF₁a.differentiableAt.div hS₁a.differentiableAt hS₁0, ?_, ?_⟩
    · have := eventually_nhdsWithin_iff.mp hpunct
      filter_upwards [this] with w hw
      by_cases hwa : w = (a : ℂ)
      · rw [hwa]; exact hat
      · exact hw hwa
    · intro _
      exact div_ne_zero hF₁0 hS₁0
  · refine ⟨fun w ↦ F w / Sfac F w, (hF z₀).div ((differentiable_Sfac hF h) z₀) hS, ?_, ?_⟩
    · have hev : ∀ᶠ w in 𝓝 z₀, Sfac F w ≠ 0 :=
        (differentiable_Sfac hF h).continuous.continuousAt.eventually_ne hS
      filter_upwards [hev] with w hw
      unfold quotG
      simp only [hw, ↓reduceIte]
    · rintro ⟨x, rfl⟩
      refine div_ne_zero ?_ hS
      intro hFx
      exact hS (Sfac_eq_zero_of_zero hF h hFx)

theorem differentiable_quotG (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) :
    Differentiable ℂ (quotG F) := by
  intro z
  obtain ⟨Gl, hGl, hev, -⟩ := quotG_local hF h z
  exact hGl.congr_of_eventuallyEq hev
  
theorem quotG_ne_zero (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) (x : ℝ) : quotG F x ≠ 0 := by
  obtain ⟨Gl, hGl, hev, hne⟩ := quotG_local hF h (x : ℂ)
  rw [hev.self_of_nhds]
  exact hne ⟨x, rfl⟩

theorem eq_Sfac_mul_quotG (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) (z : ℂ) :
    F z = Sfac F z * quotG F z := by
  by_cases hS : Sfac F z = 0
  · obtain ⟨x, rfl, hx⟩ := Sfac_eq_zero hF h hS
    rw [hS, zero_mul, hx]
  · unfold quotG
    simp only [hS, ↓reduceIte]
    field_simp

end

theorem exists_realFactor_aux {F : ℂ → ℂ} (hF : IsHB F) (hF0 : ∃ z, F z ≠ 0) :
    ∃ S G : ℂ → ℂ, Differentiable ℂ S ∧ IsHB G ∧ (∀ z, F z = S z * G z) ∧
      (∀ z, fstar S z = S z) ∧ (∀ z, S z = 0 → z.im = 0) ∧ (∀ x : ℝ, G x ≠ 0) := by
  obtain ⟨hFd, hF1, hF2⟩ := hF
  have hSne : ∀ z : ℂ, 0 < z.im → Sfac F z ≠ 0 := by
    intro z hz h
    obtain ⟨x, rfl, -⟩ := Sfac_eq_zero hFd hF0 h
    simp at hz
  refine ⟨Sfac F, quotG F, differentiable_Sfac hFd hF0, ⟨differentiable_quotG hFd hF0, ?_, ?_⟩,
    eq_Sfac_mul_quotG hFd hF0, fstar_Sfac hFd hF0, ?_, quotG_ne_zero hFd hF0⟩
  · intro z hz h0
    have := eq_Sfac_mul_quotG hFd hF0 z
    rw [h0, mul_zero] at this
    exact hF1 z hz this
  · intro z hz
    have hSc : ‖Sfac F (conj z)‖ = ‖Sfac F z‖ := by
      have := fstar_Sfac hFd hF0 z
      unfold fstar at this
      rw [← this, RCLike.norm_conj]
    have h1 := hF2 z hz
    rw [eq_Sfac_mul_quotG hFd hF0 (conj z), eq_Sfac_mul_quotG hFd hF0 z, norm_mul, norm_mul,
      hSc] at h1
    exact le_of_mul_le_mul_left h1 (norm_pos_iff.mpr (hSne z hz))
  · intro z hz
    obtain ⟨x, rfl, -⟩ := Sfac_eq_zero hFd hF0 hz
    simp

end Suff
end FF
