import FourierFrames.Cited.PaleyWiener.Part1
import FourierFrames.Cited.PaleyWiener.Spectrum
import OrtegaCerdaSeip.Bernstein.PhragmenLindelof

/-!
# P1 — Paley–Wiener, part (2): every `f ∈ PW` is a transform of an `L²(-π, π)` function

See `blueprint/P1_PaleyWiener.md`, §4.  Chain:
crude spectrum bound (`spectrum_vanish`, `a = b = π + 1`) ⇒ `f` bounded on `ℝ` (inversion on a
compact spectrum) ⇒ Phragmén–Lindelöf `|f(z)| ≤ M e^{π|Im z|}` (`OCS.norm_le_mul_exp_abs_im`)
⇒ sharp spectrum bound (`spectrum_vanish`, `a = 0`, `b = π`) ⇒ inversion ⇒ identity theorem.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform

noncomputable section

namespace FF.PW1

/-- The `L²` Fourier transform of `f|ℝ` (a chosen representative). -/
def specOf {f : ℂ → ℂ} (hL2 : MemLp (fun x : ℝ ↦ f x) 2) : ℝ → ℂ :=
  (F2 (hL2.toLp (fun x : ℝ ↦ f x)) : ℝ → ℂ)

theorem memLp_specOf {f : ℂ → ℂ} (hL2 : MemLp (fun x : ℝ ↦ f x) 2) :
    MemLp (specOf hL2) 2 :=
  Lp.memLp _

theorem stronglyMeasurable_specOf {f : ℂ → ℂ} (hL2 : MemLp (fun x : ℝ ↦ f x) 2) :
    StronglyMeasurable (specOf hL2) :=
  Lp.stronglyMeasurable _

/-- Inversion for a spectrum contained in `[-ρ, ρ]`: for *every* real `x`
(a.e. equality of two continuous functions). -/
theorem eq_integral_of_spectrum {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hL2 : MemLp (fun x : ℝ ↦ f x) 2) {ρ : ℝ} (hρ : 0 < ρ)
    (hsp : ∀ᵐ w : ℝ, ρ < |w| → specOf hL2 w = 0) (x : ℝ) :
    f x = ∫ w in (-ρ)..ρ, specOf hL2 w * Complex.exp (2 * Real.pi * I * w * x) := by
  set Φ := specOf hL2 with hΦdef
  set Φ₀ := (Icc (-ρ) ρ).indicator Φ with hΦ₀def
  have hΦ : MemLp Φ 2 := memLp_specOf hL2
  have hΦ₀2 : MemLp Φ₀ 2 := hΦ.indicator measurableSet_Icc.nullMeasurableSet
  have hΦ₀1 : Integrable Φ₀ := by
    rw [hΦ₀def, integrable_indicator_iff measurableSet_Icc]
    exact (hΦ.restrict (Icc (-ρ) ρ)).integrable (by norm_num)
  have hae : Φ₀ =ᵐ[volume] Φ := by
    filter_upwards [hsp] with w hw
    by_cases h : w ∈ Icc (-ρ) ρ
    · simp [hΦ₀def, h]
    · rw [hΦ₀def, indicator_of_notMem h]
      symm; apply hw
      rw [mem_Icc, ← abs_le] at h
      exact lt_of_not_ge h
  have hLp : F2 (hL2.toLp (fun x : ℝ ↦ f x)) = hΦ₀2.toLp Φ₀ :=
    Lp.ext (hae.symm.trans hΦ₀2.coeFn_toLp.symm)
  have hu : hL2.toLp (fun x : ℝ ↦ f x) = F2.symm (hΦ₀2.toLp Φ₀) := by
    rw [← hLp, LinearIsometryEquiv.symm_apply_apply]
  have h1 : (fun x : ℝ ↦ f x) =ᵐ[volume] 𝓕⁻ Φ₀ := by
    have := F2_symm_toLp_ae_eq hΦ₀1 hΦ₀2
    rw [← hu] at this
    exact hL2.coeFn_toLp.symm.trans this
  have hcont1 : Continuous (fun x : ℝ ↦ f x) := hd.continuous.comp continuous_ofReal
  have hcont2 : Continuous (𝓕⁻ Φ₀) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner.neg hΦ₀1
  have h2 := (hcont1.ae_eq_iff_eq volume hcont2).1 h1
  rw [show f x = 𝓕⁻ Φ₀ x from congrFun h2 x, Real.fourierInv_eq_fourier_neg,
    Real.fourier_real_eq_integral_exp_smul]
  have e : (fun v : ℝ ↦ Complex.exp (↑(-2 * Real.pi * v * -x) * Complex.I) • Φ₀ v) =
      (Icc (-ρ) ρ).indicator (fun v ↦ Φ v * Complex.exp (2 * Real.pi * I * v * x)) := by
    funext v
    rw [hΦ₀def, indicator_apply, indicator_apply]
    split_ifs
    · rw [smul_eq_mul, mul_comm]
      congr 2
      push_cast
      ring
    · simp
  rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]

theorem bounded_of_spectrum {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hL2 : MemLp (fun x : ℝ ↦ f x) 2) {ρ : ℝ} (hρ : 0 < ρ)
    (hsp : ∀ᵐ w : ℝ, ρ < |w| → specOf hL2 w = 0) :
    ∃ M : ℝ, ∀ x : ℝ, ‖f x‖ ≤ M := by
  refine ⟨∫ w in (-ρ)..ρ, ‖specOf hL2 w‖, fun x ↦ ?_⟩
  rw [eq_integral_of_spectrum hd hL2 hρ hsp x]
  refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr fun w _ ↦ ?_
  simp only [norm_mul, Complex.norm_exp]
  simp

/-- Exponential type bound in the form used by `spectrum_vanish`. -/
theorem norm_le_exp_re_im {f : ℂ → ℂ} {C τ : ℝ} (hC : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (τ * ‖z‖))
    (hτ : 0 ≤ τ) (z : ℂ) : ‖f z‖ ≤ |C| * Real.exp (τ * |z.re| + τ * |z.im|) := by
  refine (hC z).trans ?_
  calc C * Real.exp (τ * ‖z‖) ≤ |C| * Real.exp (τ * ‖z‖) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * Real.exp (τ * |z.re| + τ * |z.im|) := by
        gcongr
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im z) hτ

/-- Step A: `f ∈ PW` is bounded on `ℝ`. -/
theorem pw_bounded {f : ℂ → ℂ} (hd : Differentiable ℂ f) (he : IsExpTypeLE Real.pi f)
    (hL2 : MemLp (fun x : ℝ ↦ f x) 2) : ∃ M : ℝ, ∀ x : ℝ, ‖f x‖ ≤ M := by
  obtain ⟨C, hC⟩ := he 1 one_pos
  have hτ : (0 : ℝ) ≤ Real.pi + 1 := by linarith [Real.pi_pos]
  have hsp := spectrum_vanish hd hL2 hτ hτ (norm_le_exp_re_im hC hτ)
  have hρ : (0 : ℝ) < 1 + 1 / Real.pi := by have := Real.pi_pos; positivity
  refine bounded_of_spectrum hd hL2 hρ ?_
  filter_upwards [hsp] with w hw hρw
  apply hw
  have : 2 * Real.pi * (1 + 1 / Real.pi) = Real.pi + 1 + (Real.pi + 1) := by
    field_simp; ring
  rw [← this]
  exact mul_lt_mul_of_pos_left hρw (by positivity)

/-- Step B: sharp spectrum, using Phragmén–Lindelöf. -/
theorem pw_spectrum {f : ℂ → ℂ} (hd : Differentiable ℂ f) (he : IsExpTypeLE Real.pi f)
    (hL2 : MemLp (fun x : ℝ ↦ f x) 2) :
    ∀ᵐ w : ℝ, (1 / 2 : ℝ) < |w| → specOf hL2 w = 0 := by
  obtain ⟨M, hM⟩ := pw_bounded hd he hL2
  have hPL : ∀ z : ℂ, ‖f z‖ ≤ M * Real.exp (0 * |z.re| + Real.pi * |z.im|) := fun z ↦ by
    rw [zero_mul, zero_add]
    exact OCS.norm_le_mul_exp_abs_im hd he Real.pi_pos.le hM z
  have hsp := spectrum_vanish hd hL2 le_rfl Real.pi_pos.le hPL
  filter_upwards [hsp] with w hw hw2
  apply hw
  have : 2 * Real.pi * (1 / 2) = 0 + Real.pi := by ring
  rw [← this]
  exact mul_lt_mul_of_pos_left hw2 (by positivity)

/-- Step C: the representation on `ℝ`, with `g(t) = Φ(t/2π)/2π`. -/
theorem pw_representation_real {f : ℂ → ℂ} (hd : Differentiable ℂ f) (he : IsExpTypeLE Real.pi f)
    (hL2 : MemLp (fun x : ℝ ↦ f x) 2) :
    ∃ g : ℝ → ℂ, L2pi g ∧ ∀ x : ℝ, f x = ft g x := by
  set Φ := specOf hL2 with hΦdef
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h2πc : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast h2π
  refine ⟨fun t ↦ Φ (t / (2 * Real.pi)) / (2 * Real.pi), ?_, fun x ↦ ?_⟩
  · have hsm : StronglyMeasurable (fun t : ℝ ↦ Φ (t / (2 * Real.pi))) :=
      (stronglyMeasurable_specOf hL2).comp_measurable (measurable_id.div_const _)
    have hm : MemLp (fun t : ℝ ↦ Φ (t / (2 * Real.pi))) 2 := by
      rw [memLp_two_iff_integrable_sq_norm hsm.aestronglyMeasurable]
      have := (memLp_two_iff_integrable_sq_norm (memLp_specOf hL2).aestronglyMeasurable).1
        (memLp_specOf hL2)
      exact this.comp_div h2π
    simp_rw [div_eq_mul_inv]
    exact (hm.mul_const _).restrict _
  · rw [eq_integral_of_spectrum hd hL2 (by norm_num : (0 : ℝ) < 1 / 2) (pw_spectrum hd he hL2) x]
    unfold ft
    set F : ℝ → ℂ := fun w ↦ Φ w * Complex.exp (2 * Real.pi * I * w * x) with hF
    have e1 : ∀ t : ℝ, Φ (t / (2 * Real.pi)) / (2 * Real.pi) * Complex.exp (I * x * t) =
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ * F (t / (2 * Real.pi)) := by
      intro t
      rw [hF]
      simp only
      push_cast
      have : (2 * (Real.pi : ℂ) * I * ((t : ℂ) / (2 * Real.pi)) * x) = I * x * t := by
        field_simp
      rw [this]
      field_simp
    simp_rw [e1]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div F h2π]
    have ea : -Real.pi / (2 * Real.pi) = -(1 / 2) := by field_simp
    have eb : Real.pi / (2 * Real.pi) = 1 / 2 := by field_simp
    rw [ea, eb, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast h2π), one_mul]

/-- Identity theorem: entire functions agreeing on `ℝ` agree on `ℂ`. -/
theorem eq_of_eq_on_real {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h : ∀ x : ℝ, F x = G x) : ∀ z : ℂ, F z = G z := by
  have hFa : AnalyticOnNhd ℂ F univ := fun z _ ↦ hF.analyticAt z
  have hGa : AnalyticOnNhd ℂ G univ := fun z _ ↦ hG.analyticAt z
  have ht : Tendsto (fun n : ℕ ↦ (((1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
    · have := (continuous_ofReal.tendsto (0 : ℝ)).comp tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [Function.comp_def, Complex.ofReal_zero] using this
    · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
  have hfr : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F z = G z :=
    ht.frequently (Frequently.of_forall fun n ↦ h _)
  intro z
  exact congrFun (hFa.eq_of_frequently_eq hGa hfr) z

/-- **Paley–Wiener, part (2)**, in the shape of `FF.PaleyWienerThm`. -/
theorem paleyWiener_part2 : ∀ f : ℂ → ℂ, MemPW f →
    ∃ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) ∧
      ∀ z : ℂ, f z = ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t) := by
  intro f hf
  obtain ⟨hd, he, hL2⟩ := hf
  obtain ⟨g, hg, h⟩ := pw_representation_real hd he hL2
  exact ⟨g, hg, eq_of_eq_on_real hd (differentiable_ft hg) h⟩

end FF.PW1
