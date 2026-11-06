import FourierFrames.Theorem1.Sufficiency
import FourierFrames.Corollary1.Rotate

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF

theorem enorm_div_sq_eq (g E : ℂ → ℂ) (t : ℝ) :
    ‖g t / E t‖ₑ ^ 2 = ENNReal.ofReal ((‖g t‖ / ‖E t‖) ^ 2) := by
  rw [← ofReal_norm, norm_div, ENNReal.ofReal_pow (by positivity)]

/-- `heNormSq` as a real integral. -/
theorem heNormSq_integral {E g : ℂ → ℂ} (hE : Continuous E) (hg : Continuous g)
    (hE0 : ∀ x : ℝ, E x ≠ 0) (hfin : heNormSq E g ≠ ⊤) :
    Integrable (fun t : ℝ ↦ (‖g t‖ / ‖E t‖) ^ 2) ∧
      ∫ t : ℝ, (‖g t‖ / ‖E t‖) ^ 2 = (heNormSq E g).toReal := by
  have hmeas : Continuous fun t : ℝ ↦ (‖g t‖ / ‖E t‖) ^ 2 := by
    refine Continuous.pow (Continuous.div ?_ ?_ ?_) 2
    · exact (hg.comp Complex.continuous_ofReal).norm
    · exact (hE.comp Complex.continuous_ofReal).norm
    · intro t; exact norm_ne_zero_iff.mpr (hE0 t)
  have hnn : 0 ≤ᵐ[volume] fun t : ℝ ↦ (‖g t‖ / ‖E t‖) ^ 2 :=
    Filter.Eventually.of_forall fun t ↦ by positivity
  have hl : ∫⁻ t : ℝ, ENNReal.ofReal ((‖g t‖ / ‖E t‖) ^ 2) = heNormSq E g := by
    unfold heNormSq
    congr 1; ext t; exact (enorm_div_sq_eq g E t).symm
  have hi : Integrable (fun t : ℝ ↦ (‖g t‖ / ‖E t‖) ^ 2) :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable hnn).mp (by rw [hl]; exact hfin)
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable, hl]


theorem kernel_orthogonal_aux (hPW : PaleyWienerThm) (hD : TheoremD) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {Λ : Set ℝ} (hΛ : IsSeparated Λ)
    (hcis : IsCompleteInterpolating Λ)
    (hnorm : ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Λ f)
    {a b : ℝ} (ha : a ∈ Λ) (hb : b ∈ Λ) (hab : a ≠ b) : deBrangesKernel E a b = 0 := by
  classical
  have hstrict := HEEqPW.isStrictHB hEHB hEPW
  have hE0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  have hEc : Continuous E := hEHB.1.continuous
  obtain ⟨hKHE, hrep⟩ := hD E hstrict hE0 (a : ℂ)
  set K : ℂ → ℂ := deBrangesKernel E (a : ℂ) with hKdef
  have hKPW : MemPW K := (hEPW.1 K).mp hKHE
  have hKc : Continuous K := hKHE.1.continuous
  -- the interpolant of `δ_a`
  let d : ℝ → ℂ := fun x ↦ if x = a then 1 else 0
  have hdne : ∀ x : Λ, x ≠ (⟨a, ha⟩ : Λ) → (x : ℝ) ≠ a := fun x hx h ↦ hx (Subtype.ext h)
  have hdsum : ∑' x : Λ, ‖d x‖ₑ ^ 2 = 1 := by
    rw [tsum_eq_single (⟨a, ha⟩ : Λ)]
    · simp [d]
    · intro x hx; simp [d, hdne x hx]
  obtain ⟨e, ⟨hePW, hed⟩, -⟩ := hcis d (by rw [hdsum]; exact ENNReal.one_lt_top)
  have hea : e a = 1 := by rw [hed a ha]; simp [d]
  have hesum : sampleSum Λ e = 1 := by
    unfold sampleSum
    rw [tsum_eq_single (⟨a, ha⟩ : Λ)]
    · simp [hea]
    · intro x hx; rw [hed x x.2]; simp [d, hdne x hx]
  have hen : heNormSq E e = 1 := by rw [hnorm e hePW, hesum]
  have heHE : MemHE E e := (hEPW.1 e).mpr hePW
  obtain ⟨δ, hδ, hδsep⟩ := hΛ
  obtain ⟨B, hB⟩ := plancherelPolya hPW hδ
  have hKfin : heNormSq E K ≠ ⊤ := by
    rw [hnorm K hKPW]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (pwNormSq_ne_top hKPW))
      (hB Λ hδsep K hKPW)
  obtain ⟨hKi, hKint⟩ := heNormSq_integral hEc hKc hE0 hKfin
  obtain ⟨hei, heint⟩ := heNormSq_integral hEc hePW.1.continuous hE0 (by rw [hen]; exact ENNReal.one_ne_top)
  set k : ℝ := (heNormSq E K).toReal with hk
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hpt : ∀ t : ℝ, K t * conj (K t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) = (((‖K t‖ / ‖E t‖) ^ 2 : ℝ) : ℂ) := by
    intro t
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, div_pow]
    push_cast; ring
  -- `K(a) = k`
  have hKa : K a = (k : ℂ) := by
    have h1 := hrep K hKHE
    simp_rw [hpt] at h1
    rw [integral_complex_ofReal, hKint] at h1
    exact h1.symm
  -- `k ≥ 1`
  have hk1 : 1 ≤ k := by
    have h1 := hrep e heHE
    simp only [hea] at h1
    have hbd : ∀ t : ℝ, ‖e t * conj (K t) / ((‖E t‖ ^ 2 : ℝ) : ℂ)‖ ≤
        ((‖e t‖ / ‖E t‖) ^ 2 + (‖K t‖ / ‖E t‖) ^ 2) / 2 := by
      intro t
      have hE : 0 < ‖E t‖ := norm_pos_iff.mpr (hE0 t)
      have : ‖e t * conj (K t) / ((‖E t‖ ^ 2 : ℝ) : ℂ)‖ =
          (‖e t‖ / ‖E t‖) * (‖K t‖ / ‖E t‖) := by
        rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        field_simp
      rw [this]
      nlinarith [sq_nonneg (‖e t‖ / ‖E t‖ - ‖K t‖ / ‖E t‖)]
    have hmeas : Continuous fun t : ℝ ↦ e t * conj (K t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) := by
      refine Continuous.div ?_ ?_ ?_
      · exact (hePW.1.continuous.comp Complex.continuous_ofReal).mul
          (Complex.continuous_conj.comp (hKc.comp Complex.continuous_ofReal))
      · exact Complex.continuous_ofReal.comp ((hEc.comp Complex.continuous_ofReal).norm.pow 2)
      · intro t
        have := norm_pos_iff.mpr (hE0 t)
        exact_mod_cast (pow_pos this 2).ne'
    have h2 : ‖∫ t : ℝ, e t * conj (K t) / ((‖E t‖ ^ 2 : ℝ) : ℂ)‖ ≤
        ∫ t : ℝ, ((‖e t‖ / ‖E t‖) ^ 2 + (‖K t‖ / ‖E t‖) ^ 2) / 2 := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t ↦ norm_nonneg _) ?_
        (Filter.Eventually.of_forall hbd)
      exact (hei.add hKi).div_const 2
    rw [h1, integral_div, integral_add hei hKi, heint, hKint] at h2
    simp only [norm_one] at h2
    have hen' : (heNormSq E e).toReal = 1 := by rw [hen]; simp
    rw [hen'] at h2
    linarith
  -- the norm identity for `K`
  have hKN : heNormSq E K = ENNReal.ofReal k := (ENNReal.ofReal_toReal hKfin).symm
  have hsum := hnorm K hKPW
  unfold sampleSum at hsum
  rw [ENNReal.tsum_eq_add_tsum_ite (⟨a, ha⟩ : Λ)] at hsum
  set R : ℝ≥0∞ := ∑' x : Λ, if x = (⟨a, ha⟩ : Λ) then 0 else ‖K ((x : ℝ) : ℂ)‖ₑ ^ 2 with hR
  have hfa : ‖K (((⟨a, ha⟩ : Λ) : ℝ) : ℂ)‖ₑ ^ 2 = ENNReal.ofReal k ^ 2 := by
    show ‖K (a : ℂ)‖ₑ ^ 2 = _
    rw [hKa, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk0]
  rw [hfa, hKN] at hsum
  have hX : ENNReal.ofReal k ≤ ENNReal.ofReal k ^ 2 := by
    rw [← ENNReal.ofReal_pow hk0]
    apply ENNReal.ofReal_le_ofReal; nlinarith
  have hR0 : R = 0 := by
    have h1 : ENNReal.ofReal k + R ≤ ENNReal.ofReal k + 0 := by
      calc ENNReal.ofReal k + R ≤ ENNReal.ofReal k ^ 2 + R := by gcongr
        _ = ENNReal.ofReal k := by rw [hR]; convert hsum.symm
        _ = _ := (add_zero _).symm
    exact le_antisymm (ENNReal.le_of_add_le_add_left ENNReal.ofReal_ne_top h1) bot_le
  have hz := ENNReal.tsum_eq_zero.mp hR0 (⟨b, hb⟩ : Λ)
  have hne : (⟨b, hb⟩ : Λ) ≠ (⟨a, ha⟩ : Λ) := fun h ↦ hab (by simpa using (congrArg Subtype.val h).symm)
  simp only [hne, ↓reduceIte] at hz
  have : K (b : ℂ) = 0 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.mp hz
    exact enorm_eq_zero.mp this
  exact this

end FF
