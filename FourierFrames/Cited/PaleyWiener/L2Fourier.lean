import FourierFrames.Defs

/-!
# P1 — the `L²` Fourier transform agrees with the integral on `L¹ ∩ L²`

Mathlib has the `L²` Fourier transform `Lp.fourierTransformₗᵢ` (Plancherel) and the `L¹` integral
`𝓕 φ`, but (as of Mathlib v4.35) no lemma identifying them on `L¹ ∩ L²`.  We prove it by testing
against Schwartz functions, using only `inner_fourier_eq`, `SchwartzMap.toLp_fourier_eq` and the
Fubini identity `VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip`.

See `blueprint/P1_PaleyWiener.md`, §2.
-/

open MeasureTheory Set Complex Filter Topology SchwartzMap
open scoped ENNReal NNReal ComplexConjugate FourierTransform

noncomputable section

namespace FF.PW1

/-- The `L²` Fourier transform on `ℝ`, as a linear isometry equivalence of `Lp ℂ 2`. -/
abbrev F2 : Lp (α := ℝ) ℂ 2 ≃ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 := Lp.fourierTransformₗᵢ ℝ ℂ

/-- Self-adjointness of the `L¹` Fourier transform on `ℝ`. -/
theorem integral_fourier_smul {φ ψ : ℝ → ℂ} (hφ : Integrable φ) (hψ : Integrable ψ) :
    ∫ ξ, (𝓕 φ ξ) • ψ ξ = ∫ x, φ x • 𝓕 ψ x := by
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞) (μ := volume) (ν := volume)
    (L := innerₗ ℝ) (f := φ) (g := ψ) Real.continuous_fourierChar
    continuous_inner hφ hψ
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext; simp
  rw [hflip] at this
  exact this

/-- Pairing of the `L²` transform with a Schwartz function. -/
theorem integral_smul_F2 (Φ : Lp (α := ℝ) ℂ 2) (ψ : 𝓢(ℝ, ℂ)) :
    ∫ x, ψ x • (F2 Φ : ℝ → ℂ) x = ∫ x, (𝓕 ψ) x • (Φ : ℝ → ℂ) x := by
  have h1 := Lp.fourier_toTemperedDistribution_eq (E := ℝ) (F := ℂ) Φ
  have h2 := congrArg (fun T : 𝓢'(ℝ, ℂ) => T ψ) h1
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h2
  exact h2.symm

/-- Two locally integrable functions with the same pairings against all Schwartz functions
agree a.e. -/
theorem ae_eq_of_schwartz_pairing {u v : ℝ → ℂ} (hu : LocallyIntegrable u) (hv : LocallyIntegrable v)
    (h : ∀ ψ : 𝓢(ℝ, ℂ), ∫ x, ψ x • u x = ∫ x, ψ x • v x) : u =ᵐ[volume] v := by
  refine ae_eq_of_integral_contDiff_smul_eq hu hv fun g hg hcs ↦ ?_
  have hc : HasCompactSupport (fun x ↦ ((g x : ℝ) : ℂ)) :=
    hcs.comp_left (g := Complex.ofReal) (by simp)
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x ↦ ((g x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hg
  obtain ⟨ψ, hψ⟩ : ∃ ψ : 𝓢(ℝ, ℂ), ∀ x, ψ x = (g x : ℂ) :=
    ⟨HasCompactSupport.toSchwartzMap hc hs, fun x ↦ rfl⟩
  have e : ∀ w : ℝ → ℂ, ∫ x, g x • w x = ∫ x, ψ x • w x := fun w ↦
    integral_congr_ae (Eventually.of_forall fun x ↦ by simp [hψ, Complex.real_smul])
  rw [e u, e v, h ψ]

/-- **The `L²` transform agrees with the integral on `L¹ ∩ L²`.** -/
theorem F2_toLp_ae_eq {φ : ℝ → ℂ} (h1 : Integrable φ) (h2 : MemLp φ 2) :
    (F2 (h2.toLp φ) : ℝ → ℂ) =ᵐ[volume] 𝓕 φ := by
  have hu : LocallyIntegrable (F2 (h2.toLp φ) : ℝ → ℂ) :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hv : Continuous (𝓕 φ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner h1
  refine ae_eq_of_schwartz_pairing hu hv.locallyIntegrable fun ψ ↦ ?_
  have key := integral_smul_F2 (h2.toLp φ) ψ
  have e2 : ∫ x, (𝓕 ψ) x • ((h2.toLp φ : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) x = ∫ x, φ x • (𝓕 ψ) x := by
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx, smul_eq_mul, smul_eq_mul, mul_comm]
  have e3 := integral_fourier_smul h1 ψ.integrable
  have e4 : ∫ x, ψ x • 𝓕 φ x = ∫ x, 𝓕 φ x • ψ x :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by simp [mul_comm])
  rw [key, e2, e4, e3]
  rfl

/-- Self-adjointness of the inverse `L¹` Fourier transform on `ℝ`. -/
theorem integral_fourierInv_smul {φ ψ : ℝ → ℂ} (hφ : Integrable φ) (hψ : Integrable ψ) :
    ∫ ξ, (𝓕⁻ φ ξ) • ψ ξ = ∫ x, φ x • 𝓕⁻ ψ x := by
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞) (μ := volume) (ν := volume)
    (L := -innerₗ ℝ) (f := φ) (g := ψ) Real.continuous_fourierChar
    continuous_inner.neg hφ hψ
  have hflip : (-(innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ)).flip = -innerₗ ℝ := by
    ext; simp
  rw [hflip] at this
  exact this

/-- Pairing of the inverse `L²` transform with a Schwartz function. -/
theorem integral_smul_F2_symm (Φ : Lp (α := ℝ) ℂ 2) (ψ : 𝓢(ℝ, ℂ)) :
    ∫ x, ψ x • (F2.symm Φ : ℝ → ℂ) x = ∫ x, (𝓕⁻ ψ) x • (Φ : ℝ → ℂ) x := by
  have h1 := Lp.fourierInv_toTemperedDistribution_eq (E := ℝ) (F := ℂ) Φ
  have h2 := congrArg (fun T : 𝓢'(ℝ, ℂ) => T ψ) h1
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at h2
  exact h2.symm

/-- Inverse transform on `L¹ ∩ L²`. -/
theorem F2_symm_toLp_ae_eq {φ : ℝ → ℂ} (h1 : Integrable φ) (h2 : MemLp φ 2) :
    ((F2.symm (h2.toLp φ) : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ φ := by
  have hu : LocallyIntegrable (F2.symm (h2.toLp φ) : ℝ → ℂ) :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hv : Continuous (𝓕⁻ φ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner.neg h1
  refine ae_eq_of_schwartz_pairing hu hv.locallyIntegrable fun ψ ↦ ?_
  have key := integral_smul_F2_symm (h2.toLp φ) ψ
  have e2 : ∫ x, (𝓕⁻ ψ) x • ((h2.toLp φ : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) x = ∫ x, φ x • (𝓕⁻ ψ) x := by
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx, smul_eq_mul, smul_eq_mul, mul_comm]
  have e3 := integral_fourierInv_smul h1 ψ.integrable
  have e4 : ∫ x, ψ x • 𝓕⁻ φ x = ∫ x, 𝓕⁻ φ x • ψ x :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by simp [mul_comm])
  rw [key, e2, e4, e3]
  simp only [SchwartzMap.fourierInv_coe]

end FF.PW1
