import FourierFrames.Corollary2.PotC
import FourierFrames.Corollary2.UCont

/-!
# M07 -- helper lemmas for `Corollary2.lean`: continuity of the imaginary part of `potC`
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF


theorem continuousWithinAt_arg_comp {S : Set ℂ} {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : ContinuousWithinAt f S z₀) (hmaps : MapsTo f S {w : ℂ | 0 ≤ w.im}) (hne : f z₀ ≠ 0) :
    ContinuousWithinAt (fun z ↦ Complex.arg (f z)) S z₀ := by
  have h : ContinuousWithinAt Complex.arg {w : ℂ | 0 ≤ w.im} (f z₀) := by
    by_cases hs : f z₀ ∈ Complex.slitPlane
    · exact (Complex.continuousAt_arg hs).continuousWithinAt
    · have h1 : (f z₀).re ≤ 0 ∧ (f z₀).im = 0 := by
        rw [Complex.mem_slitPlane_iff] at hs
        push Not at hs
        exact hs
      have h2 : (f z₀).re < 0 := by
        rcases lt_or_eq_of_le h1.1 with h | h
        · exact h
        · exact absurd (Complex.ext h h1.2) hne
      exact Complex.continuousWithinAt_arg_of_re_neg_of_im_zero h2 h1.2
  exact h.comp hf hmaps

theorem continuousWithinAt_argUp' {z₀ : ℂ} {t : ℝ} (ht : t ≠ 0)
    (hne : z₀ ≠ (t : ℂ)) :
    ContinuousWithinAt (fun z ↦ argUp' z t) {z : ℂ | 0 ≤ z.im} z₀ := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hne' : (1 : ℂ) - z₀ / (t : ℂ) ≠ 0 := by
    intro h
    apply hne
    have : z₀ / (t : ℂ) = 1 := by linear_combination -h
    field_simp at this; exact this
  unfold argUp'
  by_cases h : t < 0
  · simp only [h, ↓reduceIte]
    refine continuousWithinAt_arg_comp (f := fun z ↦ 1 - z / (t : ℂ)) ?_ ?_ hne'
    · fun_prop
    · intro z hz
      show 0 ≤ (1 - z / (t : ℂ)).im
      rw [Complex.sub_im, Complex.one_im, Complex.div_ofReal_im]
      have : z.im / t ≤ 0 := div_nonpos_of_nonneg_of_nonpos hz h.le
      linarith
  · simp only [h, ↓reduceIte]
    have ht' : 0 < t := lt_of_le_of_ne (not_lt.mp h) (Ne.symm ht)
    refine ContinuousWithinAt.neg (continuousWithinAt_arg_comp
      (f := fun z ↦ conj (1 - z / (t : ℂ))) ?_ ?_ ?_)
    · exact (Complex.continuous_conj.comp (by fun_prop : Continuous fun z : ℂ ↦ 1 - z / (t : ℂ))).continuousWithinAt
    · intro z hz
      show 0 ≤ (conj (1 - z / (t : ℂ))).im
      rw [Complex.conj_im, Complex.sub_im, Complex.one_im, Complex.div_ofReal_im]
      have : 0 ≤ z.im / t := div_nonneg hz ht'.le
      linarith
    · exact (map_ne_zero (starRingEnd ℂ)).mpr hne'


/-- Dominating function for `σ g`. -/
def sigmaBound (M R : ℝ) (t : ℝ) : ℝ :=
  (Icc (-(2 * R + 2)) (2 * R + 2)).indicator (fun _ ↦ (Real.pi + R) * M) t +
    ((Icc (-(2 * R + 2)) (2 * R + 2))ᶜ).indicator (fun t ↦ M * R ^ 2 * (t ^ 2)⁻¹) t

theorem integrable_sigmaBound (M : ℝ) {R : ℝ} (hR : 0 ≤ R) : Integrable (sigmaBound M R) := by
  have hT : 0 < 2 * R + 2 := by linarith
  unfold sigmaBound
  refine Integrable.add ?_ ?_
  · rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by simp)
  · rw [integrable_indicator_iff measurableSet_Icc.compl]
    exact (far_inv_sq hT).1.const_mul _

theorem abs_sigma_mul_le {g : ℝ → ℝ} {M : ℝ} (hM : ∀ t, |g t| ≤ M) {R : ℝ} {z : ℂ}
    (hzR : ‖z‖ ≤ R) (t : ℝ) : ‖sigma z t * g t‖ ≤ sigmaBound M R t := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hzR
  unfold sigmaBound
  rw [Real.norm_eq_abs, abs_mul]
  by_cases ht : t ∈ Icc (-(2 * R + 2)) (2 * R + 2)
  · rw [indicator_of_mem ht, indicator_of_notMem (by simpa using ht), add_zero]
    exact mul_le_mul ((abs_sigma_le z t).trans (by linarith)) (hM t) (abs_nonneg _) (by positivity)
  · rw [indicator_of_notMem ht, indicator_of_mem (by simpa using ht), zero_add]
    have htT : 2 * R + 2 < |t| := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have h1 := abs_sigma_far z (by linarith) (by linarith : ‖z‖ ≤ |t| / 2)
    calc |sigma z t| * |g t| ≤ (‖z‖ ^ 2 / t ^ 2) * M :=
          mul_le_mul h1 (hM t) (abs_nonneg _) (by positivity)
      _ ≤ (R ^ 2 / t ^ 2) * M := by gcongr
      _ = M * R ^ 2 * (t ^ 2)⁻¹ := by ring

theorem continuousWithinAt_sigma_integral {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ t, |g t| ≤ M) {z₀ : ℂ} :
    ContinuousWithinAt (fun z ↦ ∫ t, sigma z t * g t) {z : ℂ | 0 ≤ z.im} z₀ := by
  set R : ℝ := ‖z₀‖ + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  refine continuousWithinAt_of_dominated (bound := sigmaBound M R) ?_ ?_
    (integrable_sigmaBound M hR0) ?_
  · exact Eventually.of_forall fun z ↦ ((measurable_sigma z).mul hg).aestronglyMeasurable
  · have : ∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] z₀, ‖z‖ ≤ R := by
      refine mem_nhdsWithin_of_mem_nhds ?_
      have : ball z₀ 1 ∈ 𝓝 z₀ := ball_mem_nhds z₀ one_pos
      filter_upwards [this] with z hz
      have h1 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ R := by rw [hR]; linarith
    filter_upwards [this] with z hz
    exact ae_of_all _ fun t ↦ abs_sigma_mul_le hM hz t
  · have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({0, z₀.re} : Set ℝ) :=
      (Set.toFinite _).countable.ae_notMem volume
    filter_upwards [hnull] with t ht
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
    have hne : z₀ ≠ (t : ℂ) := by
      intro h; apply ht.2; rw [h]; simp
    unfold sigma
    refine ContinuousWithinAt.mul (ContinuousWithinAt.add (continuousWithinAt_argUp' ht.1 hne) ?_)
      continuousWithinAt_const
    have : Continuous fun z : ℂ ↦ chi t * (z / (t : ℂ)).im :=
      continuous_const.mul (Complex.continuous_im.comp (continuous_id.div_const _))
    exact this.continuousWithinAt


theorem continuousOn_potC' {g : ℝ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    ContinuousOn (potC' g) {z : ℂ | 0 ≤ z.im} := by
  intro z₀ hz₀
  have hre : Continuous fun z : ℂ ↦ (potC' g z).re := by
    have : (fun z : ℂ ↦ (potC' g z).re) = OCS.multU g 0 :=
      funext fun z ↦ potC'_re hg.measurable hM z
    rw [this]; exact continuous_multU_of_cont_bdd hg hM
  have him : ContinuousWithinAt (fun z : ℂ ↦ (potC' g z).im) {z : ℂ | 0 ≤ z.im} z₀ := by
    have : (fun z : ℂ ↦ (potC' g z).im) = fun z ↦ ∫ t, sigma z t * g t :=
      funext fun z ↦ potC'_im hg.measurable hM z
    rw [this]; exact continuousWithinAt_sigma_integral hg.measurable hM
  have h2 : ContinuousWithinAt (fun z : ℂ ↦ (((potC' g z).re : ℝ) : ℂ) +
      Complex.I * (((potC' g z).im : ℝ) : ℂ)) {z : ℂ | 0 ≤ z.im} z₀ :=
    (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt hre.continuousWithinAt).add
      (continuousWithinAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt him))
  refine h2.congr (fun z _ ↦ ?_) ?_
  · exact Complex.ext (by simp) (by simp)
  · exact Complex.ext (by simp) (by simp)

end FF
