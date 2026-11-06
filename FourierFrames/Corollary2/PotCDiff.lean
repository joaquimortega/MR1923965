import FourierFrames.Corollary2.PotC

/-!
# M07 -- helper lemmas for `Corollary2.lean`: holomorphy of `potC` on the upper half plane
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF


theorem potCInt_eq_log (g : ℝ → ℝ) {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    potCInt g z t = (Complex.log (1 - z / (t : ℂ)) + (chi t : ℂ) * (z / (t : ℂ))) * (g t : ℂ) := by
  by_cases ht : t = 0
  · subst ht
    simp [potCInt, potKernel, sigma, argUp', chi]
  · have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have him : (1 - z / (t : ℂ)).im = -(z.im / t) := by
      rw [Complex.sub_im, Complex.one_im, Complex.div_ofReal_im]; ring
    have hne : (1 - z / (t : ℂ)).im ≠ 0 := by
      rw [him]; exact neg_ne_zero.mpr (div_ne_zero hz.ne' ht)
    have harg : argUp' z t = Complex.arg (1 - z / (t : ℂ)) := by
      unfold argUp'
      by_cases h : t < 0
      · simp only [h, ↓reduceIte]
      · simp only [h, ↓reduceIte]
        rw [Complex.arg_conj]
        have : Complex.arg (1 - z / (t : ℂ)) ≠ Real.pi := fun h' ↦
          hne (Complex.arg_eq_pi_iff.mp h').2
        simp only [this, ↓reduceIte]; ring
    unfold potCInt sigma potKernel
    rw [harg]
    apply Complex.ext
    · simp [Complex.log_re, chi]
    · simp [Complex.log_im, chi]


/-- Holomorphic integrand on the upper half plane. -/
def potF (g : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (Complex.log (1 - z / (t : ℂ)) + (chi t : ℂ) * (z / (t : ℂ))) * (g t : ℂ)

/-- Its `z`-derivative. -/
def potF' (g : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (1 / (z - (t : ℂ)) + (chi t : ℂ) / (t : ℂ)) * (g t : ℂ)

theorem measurable_potF (g : ℝ → ℝ) (hg : Measurable g) (z : ℂ) : Measurable (potF g z) := by
  unfold potF
  refine Measurable.mul (Measurable.add ?_ ?_) (Complex.measurable_ofReal.comp hg)
  · exact Complex.measurable_log.comp (measurable_const.sub
      (measurable_const.div Complex.measurable_ofReal))
  · exact (Complex.measurable_ofReal.comp measurable_chi).mul
      (measurable_const.div Complex.measurable_ofReal)

theorem measurable_potF' (g : ℝ → ℝ) (hg : Measurable g) (z : ℂ) : Measurable (potF' g z) := by
  unfold potF'
  refine Measurable.mul (Measurable.add ?_ ?_) (Complex.measurable_ofReal.comp hg)
  · exact measurable_const.div (measurable_const.sub Complex.measurable_ofReal)
  · exact (Complex.measurable_ofReal.comp measurable_chi).div Complex.measurable_ofReal

theorem hasDerivAt_potF (g : ℝ → ℝ) {z : ℂ} (hz : 0 < z.im) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun w ↦ potF g w t) (potF' g z t) z := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hslit : 1 - z / (t : ℂ) ∈ Complex.slitPlane := by
    right
    rw [Complex.sub_im, Complex.one_im, Complex.div_ofReal_im]
    simp only [zero_sub, ne_eq, neg_eq_zero]
    exact div_ne_zero hz.ne' ht
  have h1 : HasDerivAt (fun w : ℂ ↦ 1 - w / (t : ℂ)) (-(1 / (t : ℂ))) z := by
    have := ((hasDerivAt_id z).div_const (t : ℂ)).const_sub 1
    simpa using this
  have h2 := h1.clog hslit
  have h3 : HasDerivAt (fun w : ℂ ↦ (chi t : ℂ) * (w / (t : ℂ))) ((chi t : ℂ) / (t : ℂ)) z := by
    have := ((hasDerivAt_id z).div_const (t : ℂ)).const_mul (chi t : ℂ)
    simpa [div_eq_mul_inv] using this
  have h4 := (h2.add h3).mul_const (g t : ℂ)
  unfold potF potF'
  convert h4 using 1
  have hzt : z - (t : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this; linarith
  have htz : (t : ℂ) - z ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.mpr hzt
  field_simp
  ring


/-- The dominating function for `potF'`. -/
def potFBound (M δ R : ℝ) (t : ℝ) : ℝ :=
  (Icc (-(2 * R + 2)) (2 * R + 2)).indicator (fun _ ↦ M * (1 / δ + 1)) t +
    ((Icc (-(2 * R + 2)) (2 * R + 2))ᶜ).indicator (fun t ↦ M * (2 * R) * (t ^ 2)⁻¹) t

theorem integrable_potFBound (M δ : ℝ) {R : ℝ} (hR : 0 ≤ R) : Integrable (potFBound M δ R) := by
  have hT : 0 < 2 * R + 2 := by linarith
  unfold potFBound
  refine Integrable.add ?_ ?_
  · rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by simp)
  · rw [integrable_indicator_iff measurableSet_Icc.compl]
    exact (far_inv_sq hT).1.const_mul _

theorem norm_potF'_le {g : ℝ → ℝ} {M : ℝ} (hM : ∀ t, |g t| ≤ M) {δ R : ℝ} (hδ : 0 < δ)
    {z : ℂ} (hz : δ ≤ z.im) (hzR : ‖z‖ ≤ R) (t : ℝ) :
    ‖potF' g z t‖ ≤ potFBound M δ R t := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hzR
  unfold potF' potFBound
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hzt : δ ≤ ‖z - (t : ℂ)‖ := by
    refine hz.trans ((le_abs_self _).trans ?_)
    have := Complex.abs_im_le_norm (z - (t : ℂ))
    simpa using this
  by_cases ht : t ∈ Icc (-(2 * R + 2)) (2 * R + 2)
  · rw [indicator_of_mem ht, indicator_of_notMem (by simpa using ht), add_zero]
    have h1 : ‖1 / (z - (t : ℂ))‖ ≤ 1 / δ := by
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hδ hzt
    have h2 : ‖(chi t : ℂ) / (t : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs]; exact abs_chi_div_le t
    calc ‖1 / (z - (t : ℂ)) + (chi t : ℂ) / (t : ℂ)‖ * |g t| ≤ (1 / δ + 1) * M :=
          mul_le_mul ((norm_add_le _ _).trans (add_le_add h1 h2)) (hM t) (abs_nonneg _) (by positivity)
      _ = M * (1 / δ + 1) := by ring
  · rw [indicator_of_notMem ht, indicator_of_mem (by simpa using ht), zero_add]
    have htT : 2 * R + 2 < |t| := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have ht0 : t ≠ 0 := fun h ↦ by rw [h] at htT; simp at htT; linarith
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    have hχ : chi t = 1 := by rw [chi_eq]; simp [not_le.mpr (by linarith : 1 < |t|)]
    have hzt' : z - (t : ℂ) ≠ 0 := by
      intro h; rw [h, norm_zero] at hzt; linarith
    have hnt : |t| ≤ ‖z - (t : ℂ)‖ + ‖z‖ := by
      have : ‖(t : ℂ)‖ ≤ ‖z - (t : ℂ)‖ + ‖z‖ := by
        calc ‖(t : ℂ)‖ = ‖z - (z - (t : ℂ))‖ := by ring_nf
          _ ≤ ‖z‖ + ‖z - (t : ℂ)‖ := norm_sub_le _ _
          _ = _ := add_comm _ _
      simpa using this
    have hzt2 : |t| / 2 ≤ ‖z - (t : ℂ)‖ := by linarith
    have e : 1 / (z - (t : ℂ)) + (chi t : ℂ) / (t : ℂ) = z / ((t : ℂ) * (z - (t : ℂ))) := by
      rw [hχ]; push_cast; field_simp; ring
    rw [e, norm_div, norm_mul]
    have htn : ‖(t : ℂ)‖ = |t| := by simp
    rw [htn]
    have hpos : 0 < |t| := abs_pos.mpr ht0
    calc ‖z‖ / (|t| * ‖z - (t : ℂ)‖) * |g t| ≤ (2 * R / t ^ 2) * M := by
          refine mul_le_mul ?_ (hM t) (abs_nonneg _) (by positivity)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : ‖z‖ * (t ^ 2) ≤ 2 * R * (|t| * ‖z - (t : ℂ)‖) := by
            rw [← sq_abs t]
            have h1 : ‖z‖ ≤ R := hzR
            nlinarith [norm_nonneg z, mul_le_mul_of_nonneg_left hzt2 hpos.le]
          exact this
      _ = M * (2 * R) * (t ^ 2)⁻¹ := by ring


theorem differentiableAt_potC' {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M)
    {z₀ : ℂ} (hz₀ : 0 < z₀.im) : DifferentiableAt ℂ (potC' g) z₀ := by
  set δ : ℝ := z₀.im / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set R : ℝ := ‖z₀‖ + δ with hR
  have hR0 : 0 ≤ R := by positivity
  have hball : ∀ z ∈ ball z₀ δ, δ ≤ z.im ∧ ‖z‖ ≤ R := by
    intro z hz
    have h1 : ‖z - z₀‖ < δ := by simpa [dist_eq_norm] using hz
    refine ⟨?_, ?_⟩
    · have := Complex.abs_im_le_norm (z - z₀)
      simp only [Complex.sub_im] at this
      have := (abs_le.mp this).1
      linarith
    · calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ R := by rw [hR]; linarith
  have hupper : ∀ z ∈ ball z₀ δ, 0 < z.im := fun z hz ↦ lt_of_lt_of_le hδ0 (hball z hz).1
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := potF g) (F' := potF' g) (μ := volume) (x₀ := z₀) (bound := potFBound M δ R)
    (ball_mem_nhds z₀ hδ0)
    (Eventually.of_forall fun z ↦ (measurable_potF g hg z).aestronglyMeasurable)
    (by
      have : potF g z₀ = potCInt g z₀ := by
        funext t; exact (potCInt_eq_log g hz₀ t).symm
      rw [this]; exact integrable_potCInt hg hM z₀)
    (measurable_potF' g hg z₀).aestronglyMeasurable
    (ae_of_all _ fun t z hz ↦ norm_potF'_le hM hδ0 (hball z hz).1 (hball z hz).2 t)
    (integrable_potFBound M δ hR0)
    (by
      filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with t ht z hz
      exact hasDerivAt_potF g (hupper z hz) (by simpa using ht))
  have hev : (fun z ↦ ∫ t, potF g z t) =ᶠ[𝓝 z₀] potC' g := by
    filter_upwards [ball_mem_nhds z₀ hδ0] with z hz
    rw [potC'_eq]
    congr 1; funext t
    exact (potCInt_eq_log g (hupper z hz) t).symm
  exact (hdiff.2.congr_of_eventuallyEq hev.symm).differentiableAt


end FF
