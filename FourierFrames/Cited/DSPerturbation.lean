import FourierFrames.PW.PlancherelPolya

/-!
# P2a — Duffin–Schaeffer perturbation lemma (`DSPerturbation`)

See `blueprint/P2_DS_JN.md`, Part A.  Route: Bernstein in `L²` (`‖f'‖ ≤ π ‖f‖`, from
`f' = pwFT (i t g)`) + Cauchy–Schwarz on `f(γ+δ) - f(γ) = ∫ f'` + finite overlap of the intervals
`[γ-L, γ+L]` for a separated `Γ`.  No Taylor series, no higher derivatives.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Bernstein's inequality in `L²` -/

theorem enorm_ofReal_eq (t : ℝ) : ‖(t : ℂ)‖ₑ = ENNReal.ofReal |t| := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]

theorem l2pi_mul_t_aux {g : ℝ → ℂ} :
    ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖I * (t : ℂ) * g t‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.pi ^ 2) * l2piSq g := by
  rw [l2piSq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
  have h1 : ‖I * (t : ℂ) * g t‖ₑ ^ 2 = ENNReal.ofReal (t ^ 2) * ‖g t‖ₑ ^ 2 := by
    rw [enorm_mul, enorm_mul, mul_pow]
    have : ‖I‖ₑ = 1 := by simp [enorm]
    rw [this, one_mul, enorm_ofReal_eq,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [h1]
  have : |t| ≤ Real.pi := abs_le.2 ⟨ht.1.le, ht.2⟩
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by nlinarith [abs_nonneg t, sq_abs t])) _

/-- `t ↦ i t g(t)` stays in `L²(-π, π)` and `‖i t g‖² ≤ π² ‖g‖²`. -/
theorem memL2pi_mul_t {g : ℝ → ℂ} (hg : MemL2pi g) :
    MemL2pi (fun t ↦ I * (t : ℂ) * g t) ∧
      l2piSq (fun t ↦ I * (t : ℂ) * g t) ≤ ENNReal.ofReal (Real.pi ^ 2) * l2piSq g := by
  have hle := l2pi_mul_t_aux (g := g)
  refine ⟨?_, hle⟩
  have hm : AEStronglyMeasurable (fun t : ℝ ↦ I * (t : ℂ) * g t)
      (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    (by fun_prop : AEStronglyMeasurable (fun t : ℝ ↦ I * (t : ℂ)) _).mul hg.aestronglyMeasurable
  refine memLp_two_of_lintegral hm (lt_of_le_of_lt hle ?_)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (l2piSq_ne_top hg).lt_top


/-- Differentiation under the integral sign: `(pwFT g)' = pwFT (i t g)` on all of `ℂ`. -/
theorem hasDerivAt_pwFT {g : ℝ → ℂ} (hg : MemL2pi g) (z : ℂ) :
    HasDerivAt (pwFT g) (pwFT (fun t ↦ I * (t : ℂ) * g t) z) z := by
  have hg1 := memL2pi_mul_t hg
  have hπ := Real.pi_pos
  have hIoc : Set.uIoc (-Real.pi) Real.pi = Ioc (-Real.pi) Real.pi := by
    rw [uIoc_of_le (by linarith)]
  let F : ℂ → ℝ → ℂ := fun x t ↦ g t * Complex.exp (I * x * t)
  let F' : ℂ → ℝ → ℂ := fun x t ↦ I * (t : ℂ) * g t * Complex.exp (I * x * t)
  have hmeas : ∀ x : ℂ, AEStronglyMeasurable (F x) (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    fun x ↦ hg.aestronglyMeasurable.mul (by fun_prop)
  have hmeas' : AEStronglyMeasurable (F' z) (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    hg1.1.aestronglyMeasurable.mul (by fun_prop)
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (-Real.pi) Real.pi →
      ∀ x ∈ Metric.ball z 1, ‖F' x t‖ ≤ Real.pi * ‖g t‖ * Real.exp (Real.pi * (‖z‖ + 1)) := by
    refine Eventually.of_forall fun t ht x hx ↦ ?_
    rw [hIoc] at ht
    have h1 := norm_exp_I_mul_le x ht
    have h2 : |x.im| ≤ ‖z‖ + 1 := by
      calc |x.im| ≤ ‖x‖ := Complex.abs_im_le_norm x
        _ ≤ ‖z‖ + ‖x - z‖ := by simpa using norm_le_insert' x z
        _ ≤ ‖z‖ + 1 := by have := mem_ball_iff_norm.1 hx; linarith
    have h3 : |t| ≤ Real.pi := abs_le.2 ⟨ht.1.le, ht.2⟩
    simp only [F']
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have h4 : ‖Complex.exp (I * x * t)‖ ≤ Real.exp (Real.pi * (‖z‖ + 1)) :=
      h1.trans (Real.exp_le_exp.2 (by gcongr))
    exact mul_le_mul (mul_le_mul_of_nonneg_right h3 (norm_nonneg _)) h4 (norm_nonneg _)
      (by positivity)
  have hint : IntervalIntegrable (fun t : ℝ ↦ Real.pi * ‖g t‖ * Real.exp (Real.pi * (‖z‖ + 1)))
      volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact (hg.integrableOn.norm.const_mul Real.pi).mul_const _
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (-Real.pi) Real.pi →
      ∀ x ∈ Metric.ball z 1, HasDerivAt (fun x => F x t) (F' x t) x := by
    refine Eventually.of_forall fun t ht x hx ↦ ?_
    simp only [F, F']
    have h1 : HasDerivAt (fun x : ℂ ↦ I * x * (t : ℂ)) (I * (t : ℂ)) x := by
      simpa [mul_comm, mul_assoc] using ((hasDerivAt_id x).const_mul I).mul_const (t : ℂ)
    have := (h1.cexp).const_mul (g t)
    convert this using 1
    ring
  have hm0 : AEStronglyMeasurable (F' z) (volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
    rw [hIoc]; exact hmeas'
  have hm1 : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc (-Real.pi) Real.pi)) :=
    Eventually.of_forall fun x ↦ by rw [hIoc]; exact hmeas x
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := -Real.pi) (b := Real.pi) (F := F) (F' := F') (x₀ := z) (s := Metric.ball z 1) (bound := fun t ↦ Real.pi * ‖g t‖ * Real.exp (Real.pi * (‖z‖ + 1))) (Metric.ball_mem_nhds z one_pos) hm1 (intervalIntegrable_mul_exp hg z) hm0 hbound hint hdiff
  exact key.2


/-- **Bernstein's inequality in `L²`**: `f ∈ PW ⇒ f' ∈ PW` and `‖f'‖² ≤ π² ‖f‖²`. -/
theorem pw_bernstein (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) :
    MemPW (deriv f) ∧ pwNormSq (deriv f) ≤ ENNReal.ofReal (Real.pi ^ 2) * pwNormSq f := by
  obtain ⟨g, hg, hfg, hn⟩ := exists_pwFT hPW hf
  obtain ⟨hg1, hg2⟩ := memL2pi_mul_t hg
  have hd : deriv f = pwFT (fun t ↦ I * (t : ℂ) * g t) := by
    funext z
    rw [hfg]
    exact (hasDerivAt_pwFT hg z).deriv
  obtain ⟨hm, hn1⟩ := memPW_pwFT hPW hg1
  rw [hd]
  refine ⟨hm, ?_⟩
  rw [hn1, hn, mul_left_comm]
  exact mul_le_mul_right hg2 _

/-! ## Increments of `f ∈ PW` -/

/-- `|f(γ+δ) - f(γ)|² ≤ |δ| ∫_{γ-|δ|}^{γ+|δ|} |f'|²` (FTC + Cauchy–Schwarz). -/
theorem enorm_sq_sub_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (γ δ : ℝ) :
    ‖f ((γ + δ : ℝ) : ℂ) - f (γ : ℂ)‖ₑ ^ 2 ≤
      ENNReal.ofReal |δ| * ∫⁻ x in Icc (γ - |δ|) (γ + |δ|), ‖deriv f (x : ℂ)‖ₑ ^ 2 := by
  sorry

/-- A `d`-separated set has at most `2L/d + 1` points in any interval of length `2L`. -/
theorem IsSepBy.ncard_Icc_le {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ) (x L : ℝ)
    (hL : 0 ≤ L) : ((Γ ∩ Icc (x - L) (x + L)).ncard : ℝ) ≤ 2 * L / d + 1 := by
  sorry

/-- Finite overlap: `∑_{γ ∈ Γ} ∫_{γ-L}^{γ+L} φ ≤ (2L/d + 1) ∫ φ` for `φ ≥ 0` measurable. -/
theorem tsum_lintegral_Icc_le {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ) {L : ℝ}
    (hL : 0 ≤ L) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∑' γ : Γ, ∫⁻ x in Icc ((γ : ℝ) - L) ((γ : ℝ) + L), φ x ≤
      ENNReal.ofReal (2 * L / d + 1) * ∫⁻ x, φ x := by
  sorry

/-- The key estimate: `∑_γ |f(γ+δ_γ) - f(γ)|² ≤ π² L (2L/d + 1) ‖f‖²` when `|δ_γ| ≤ L`. -/
theorem tsum_sub_le (hPW : PaleyWienerThm) {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ)
    {L : ℝ} (hL : 0 ≤ L) {δ : ℝ → ℝ} (hδ : ∀ x ∈ Γ, |δ x| ≤ L) {f : ℂ → ℂ} (hf : MemPW f) :
    ∑' γ : Γ, ‖f (((γ : ℝ) + δ γ : ℝ) : ℂ) - f ((γ : ℝ) : ℂ)‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.pi ^ 2 * L * (2 * L / d + 1)) * pwNormSq f := by
  sorry

/-! ## Sampling sums over an injective image -/

theorem sampleSum_image {φ : ℝ → ℝ} {Γ : Set ℝ} (hφ : InjOn φ Γ) (f : ℂ → ℂ) :
    sampleSum (φ '' Γ) f = ∑' γ : Γ, ‖f ((φ γ : ℝ) : ℂ)‖ₑ ^ 2 := by
  sorry

/-- `(a+b)² ≤ 2a² + 2b²` in `ℝ≥0∞`, summed. -/
theorem tsum_enorm_sq_add_le {ι : Type*} (a b : ι → ℂ) :
    ∑' i, ‖a i + b i‖ₑ ^ 2 ≤ 2 * ∑' i, ‖a i‖ₑ ^ 2 + 2 * ∑' i, ‖b i‖ₑ ^ 2 := by
  sorry

/-! ## Main result -/

theorem dsPerturbation_of_paleyWiener (hPW : PaleyWienerThm) : DSPerturbation := by
  sorry

end FF
