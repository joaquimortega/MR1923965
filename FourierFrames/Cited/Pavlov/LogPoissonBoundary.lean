import FourierFrames.Cited.Pavlov.SchwarzBoundary
import FourierFrames.Cited.Pavlov.LogPoissonKernel

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF.Pavlov

private lemma exists_local_factor {A : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hnz : ∀ z ∈ FF.UHP, A z ≠ 0) (a : ℝ) :
    ∃ m : ℕ, ∃ B : ℂ → ℂ, AnalyticAt ℂ B (a : ℂ) ∧ B a ≠ 0 ∧
      ∀ᶠ z in 𝓝 (a : ℂ), A z = (z-(a : ℂ))^m*B z := by
  apply (hA.analyticAt (a : ℂ)).exists_eventuallyEq_pow_smul_nonzero_iff.mpr
  intro hzero
  have han : AnalyticOnNhd ℂ A univ := fun z _ ↦ hA.analyticAt z
  have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ (a : ℂ)) hzero
  exact hnz I (by simp [FF.UHP]) (heq (mem_univ I))

private lemma log_norm_factor {A B : ℂ → ℂ} {a z : ℂ} {m : ℕ}
    (hf : A z = (z-a)^m*B z) (hz : z ≠ a) (hB : B z ≠ 0) :
    Real.log ‖A z‖ = (m : ℝ)*Real.log ‖z-a‖+Real.log ‖B z‖ := by
  rw [hf, norm_mul, norm_pow, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)))
    (norm_ne_zero_iff.mpr hB), Real.log_pow]

private lemma continuousAt_log_residual {A B : ℂ → ℂ} {a : ℝ} {m : ℕ}
    (hB : AnalyticAt ℂ B (a : ℂ)) (hBne : B a ≠ 0)
    (hf : ∀ᶠ z in 𝓝 (a : ℂ), A z = (z-(a : ℂ))^m*B z) :
    ContinuousAt (Function.update (fun t : ℝ ↦ Real.log ‖A t‖-(m : ℝ)*Real.log |t-a|)
      a (Real.log ‖B a‖)) a := by
  have hc : ContinuousAt (fun t : ℝ ↦ Real.log ‖B t‖) a :=
    (hB.continuousAt.norm.log (norm_ne_zero_iff.mpr hBne)).comp
      continuous_ofReal.continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [(continuous_ofReal.tendsto a).eventually hf,
    (continuous_ofReal.tendsto a).eventually (hB.continuousAt.eventually_ne hBne)] with t ht hBt
  by_cases hta : t = a
  · subst t
    simp
  · rw [Function.update_of_ne hta]
    have hneq : (t : ℂ) ≠ (a : ℂ) := by exact_mod_cast hta
    have hl := log_norm_factor ht hneq hBt
    have hn : ‖(t : ℂ)-(a : ℂ)‖ = |t-a| := by rw [← ofReal_sub, norm_real, Real.norm_eq_abs]
    rw [hn] at hl
    linarith

/-- The logarithmic Poisson defect tends to zero, including at real zeros of A. -/
theorem tendsto_poisson_log_defect_boundary {A : ℂ → ℂ}
    (hA : Differentiable ℂ A) (hnz : ∀ z ∈ FF.UHP, A z ≠ 0)
    (hv : LogIntegrable (fun t : ℝ ↦ Real.log ‖A t‖)) (a : ℝ) :
    Tendsto (fun z ↦ (schwarzIntegral (fun t : ℝ ↦ Real.log ‖A t‖) z).re -
      Real.log ‖A z‖) (𝓝[FF.UHP] (a : ℂ)) (𝓝 0) := by
  obtain ⟨m,B,hB,hBne,hf⟩ := exists_local_factor hA hnz a
  let v : ℝ → ℝ := fun t ↦ Real.log ‖A t‖
  let w₀ : ℝ → ℝ := fun t ↦ v t-(m : ℝ)*Real.log |t-a|
  let w : ℝ → ℝ := Function.update w₀ a (Real.log ‖B a‖)
  have hwc : ContinuousAt w a := continuousAt_log_residual hB hBne hf
  have hwae : w =ᵐ[volume] w₀ := by
    filter_upwards [volume.ae_ne a] with t ht
    exact Function.update_of_ne ht _ _
  have hw₀ : LogIntegrable w₀ := hv.sub ((logIntegrable_log_abs_sub a).const_mul (m : ℝ))
  have hw : LogIntegrable w := hw₀.congr hwae.symm
  have hSw : ∀ z ∈ FF.UHP, (schwarzIntegral w z).re =
      (schwarzIntegral v z).re-(m : ℝ)*Real.log ‖z-(a : ℂ)‖ := by
    intro z hz
    rw [schwarzIntegral_congr_ae hwae z]
    change (schwarzIntegral (fun t ↦ v t-(m : ℝ)*Real.log |t-a|) z).re = _
    rw [schwarzIntegral_sub hv ((logIntegrable_log_abs_sub a).const_mul (m : ℝ)) hz,
      schwarzIntegral_const_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, schwarzIntegral_re_log_abs_sub a hz]
  have ht₁ : Tendsto (fun z ↦ (schwarzIntegral w z).re) (𝓝[FF.UHP] (a : ℂ))
      (𝓝 (Real.log ‖B a‖)) := by
    simpa only [w, Function.update_self] using tendsto_schwarzIntegral_re_boundary hw hwc
  have ht₂ : Tendsto (fun z ↦ Real.log ‖B z‖) (𝓝[FF.UHP] (a : ℂ))
      (𝓝 (Real.log ‖B a‖)) :=
    (hB.continuousAt.norm.log (norm_ne_zero_iff.mpr hBne)).tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun z ↦ (schwarzIntegral v z).re-Real.log ‖A z‖) =ᶠ[𝓝[FF.UHP] (a : ℂ)]
      (fun z ↦ (schwarzIntegral w z).re-Real.log ‖B z‖) := by
    filter_upwards [self_mem_nhdsWithin, hf.filter_mono nhdsWithin_le_nhds,
      (hB.continuousAt.eventually_ne hBne).filter_mono nhdsWithin_le_nhds] with z hz hzf hBz
    have hza : z ≠ (a : ℂ) := by
      intro he
      subst z
      simp [FF.UHP] at hz
    rw [hSw z hz, log_norm_factor hzf hza hBz]
    ring
  have ht : Tendsto (fun z ↦ (schwarzIntegral w z).re-Real.log ‖B z‖)
      (𝓝[FF.UHP] (a : ℂ)) (𝓝 0) := by simpa only [sub_self] using ht₁.sub ht₂
  exact ht.congr' heq.symm

/-- The Poisson/logarithm defect with its zero boundary values. -/
def poissonLogDefect (A : ℂ → ℂ) (z : ℂ) : ℝ :=
  if 0 < z.im then (schwarzIntegral (fun t : ℝ ↦ Real.log ‖A t‖) z).re -
    Real.log ‖A z‖ else 0

/-- Finite-order boundary zero cancellation makes the defect continuous. -/
theorem continuous_poissonLogDefect {A : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hnz : ∀ z ∈ FF.UHP, A z ≠ 0)
    (hv : LogIntegrable (fun t : ℝ ↦ Real.log ‖A t‖)) : Continuous (poissonLogDefect A) := by
  unfold poissonLogDefect
  apply continuous_if'
  · intro z hz
    have hz0 : z.im = 0 := by simpa using hz
    have heq : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz0]
    simpa only [← heq, hz0, lt_self_iff_false, ite_false, FF.UHP] using
      tendsto_poisson_log_defect_boundary hA hnz hv z.re
  · intro z hz
    have hz0 : z.im = 0 := by simpa using hz
    simpa [hz0] using (tendsto_const_nhds : Tendsto (fun _ : ℂ ↦ (0 : ℝ))
      (𝓝[{z : ℂ | ¬0 < z.im}] z) (𝓝 0))
  · exact (continuous_re.comp_continuousOn (differentiableOn_schwarzIntegral hv).continuousOn).sub
      (hA.continuous.norm.continuousOn.log (fun z hz ↦ norm_ne_zero_iff.mpr (hnz z hz)))
  · exact continuous_const.continuousOn

/-- The defect extends continuously by zero to the closed upper half-plane. -/
theorem poisson_log_defect_continuous_zero_boundary {A : ℂ → ℂ}
    (hA : Differentiable ℂ A) (hnz : ∀ z ∈ FF.UHP, A z ≠ 0)
    (hv : LogIntegrable (fun t : ℝ ↦ Real.log ‖A t‖)) :
    ContinuousOn (poissonLogDefect A) {z : ℂ | 0 ≤ z.im} :=
  (continuous_poissonLogDefect hA hnz hv).continuousOn

end FF.Pavlov
