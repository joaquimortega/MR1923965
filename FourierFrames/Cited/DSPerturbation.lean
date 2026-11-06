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

/-- Cauchy–Schwarz on a set: `(∫_s u)² ≤ |s| ∫_s u²`. -/
theorem ennreal_rpow_half_sq (A : ℝ≥0∞) : (A ^ (1 / 2 : ℝ)) ^ 2 = A := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem lintegral_sq_le (s : Set ℝ) {u : ℝ → ℝ≥0∞} (hu : AEMeasurable u (volume.restrict s)) :
    (∫⁻ x in s, u x) ^ 2 ≤ volume s * ∫⁻ x in s, u x ^ 2 := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict s)
    (Real.HolderConjugate.two_two) hu (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, lintegral_const, Measure.restrict_apply_univ,
    one_pow, one_mul, ENNReal.rpow_two] at hH
  have h2 := pow_le_pow_left' hH 2
  rw [mul_pow, ennreal_rpow_half_sq, ennreal_rpow_half_sq, mul_comm] at h2
  exact h2


/-- `|f(γ+δ) - f(γ)|² ≤ |δ| ∫_{γ-|δ|}^{γ+|δ|} |f'|²` (FTC + Cauchy–Schwarz).  (`hPW` dropped.) -/
theorem enorm_sq_sub_le {f : ℂ → ℂ} (hf : MemPW f) (γ δ : ℝ) :
    ‖f ((γ + δ : ℝ) : ℂ) - f (γ : ℂ)‖ₑ ^ 2 ≤
      ENNReal.ofReal |δ| * ∫⁻ x in Icc (γ - |δ|) (γ + |δ|), ‖deriv f (x : ℂ)‖ₑ ^ 2 := by
  set φ : ℝ → ℂ := fun x ↦ deriv f (x : ℂ) with hφ
  have hcont : Continuous φ :=
    ((hf.1.contDiff (n := 1)).continuous_deriv le_rfl).comp Complex.continuous_ofReal
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ ↦ f y) (φ x) x :=
    fun x ↦ ((hf.1 x).hasDerivAt).comp_ofReal
  have hftc : f ((γ + δ : ℝ) : ℂ) - f (γ : ℂ) = ∫ x in γ..γ + δ, φ x :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x)
      (hcont.intervalIntegrable _ _)).symm
  -- an interval `J` of length `|δ|` inside `[γ-|δ|, γ+|δ|]` bounding the increment
  obtain ⟨J, hJsub, hJvol, hJ⟩ : ∃ J : Set ℝ, J ⊆ Icc (γ - |δ|) (γ + |δ|) ∧
      volume J = ENNReal.ofReal |δ| ∧
      ‖f ((γ + δ : ℝ) : ℂ) - f (γ : ℂ)‖ₑ ≤ ∫⁻ x in J, ‖φ x‖ₑ := by
    rcases le_total 0 δ with h0 | h0
    · refine ⟨Ioc γ (γ + δ), fun x hx ↦ ⟨?_, ?_⟩, ?_, ?_⟩
      · rw [abs_of_nonneg h0]; linarith [hx.1]
      · rw [abs_of_nonneg h0]; exact hx.2
      · rw [Real.volume_Ioc, abs_of_nonneg h0]; congr 1; ring
      · rw [hftc, intervalIntegral.integral_of_le (by linarith)]
        exact enorm_integral_le_lintegral_enorm _
    · refine ⟨Ioc (γ + δ) γ, fun x hx ↦ ⟨?_, ?_⟩, ?_, ?_⟩
      · rw [abs_of_nonpos h0]; linarith [hx.1]
      · rw [abs_of_nonpos h0]; linarith [hx.2]
      · rw [Real.volume_Ioc, abs_of_nonpos h0]; congr 1; ring
      · rw [hftc, intervalIntegral.integral_symm, intervalIntegral.integral_of_le (by linarith),
          enorm_neg]
        exact enorm_integral_le_lintegral_enorm _
  have hmeas : AEMeasurable (fun x ↦ ‖φ x‖ₑ) (volume.restrict J) :=
    hcont.measurable.enorm.aemeasurable
  calc ‖f ((γ + δ : ℝ) : ℂ) - f (γ : ℂ)‖ₑ ^ 2 ≤ (∫⁻ x in J, ‖φ x‖ₑ) ^ 2 := by gcongr
    _ ≤ volume J * ∫⁻ x in J, ‖φ x‖ₑ ^ 2 := lintegral_sq_le J hmeas
    _ ≤ _ := by
      rw [hJvol]
      gcongr

theorem IsSepBy.finite_inter_Icc {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ) (x L : ℝ) :
    (Γ ∩ Icc (x - L) (x + L)).Finite := by
  refine ((IsSeparated.finite_inter_Icc ⟨d, hd, hΓ⟩ (|x| + |L|))).subset ?_
  intro y hy
  refine ⟨hy.1, ?_, ?_⟩
  · linarith [hy.2.1, neg_abs_le x, neg_abs_le L, le_abs_self L]
  · linarith [hy.2.2, le_abs_self x, le_abs_self L]

theorem IsSepBy.ncard_Icc_le {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ) (x L : ℝ)
    (hL : 0 ≤ L) : ((Γ ∩ Icc (x - L) (x + L)).ncard : ℝ) ≤ 2 * L / d + 1 := by
  have hfin := hΓ.finite_inter_Icc hd x L
  set T := hfin.toFinset with hT
  have hcard : (Γ ∩ Icc (x - L) (x + L)).ncard = T.card := Set.ncard_eq_toFinset_card _ hfin
  rw [hcard]
  have hdisj : (T : Set ℝ).PairwiseDisjoint (fun t ↦ Ico (t - d / 2) (t + d / 2)) := by
    intro s hs t ht hst
    simp only [hT, Finset.mem_coe, Set.Finite.mem_toFinset] at hs ht
    have := hΓ s hs.1 t ht.1 hst
    rw [Function.onFun, Set.disjoint_left]
    intro y hy1 hy2
    rcases le_abs'.1 this with h1 | h1 <;>
      linarith [hy1.1, hy1.2, hy2.1, hy2.2]
  have hmeas := measure_biUnion_finset (μ := volume) hdisj (fun t _ ↦ measurableSet_Ico)
  have hsub : (⋃ t ∈ T, Ico (t - d / 2) (t + d / 2)) ⊆ Icc (x - L - d / 2) (x + L + d / 2) := by
    intro y hy
    simp only [mem_iUnion] at hy
    obtain ⟨t, ht, hy⟩ := hy
    simp only [hT, Set.Finite.mem_toFinset] at ht
    exact ⟨by linarith [ht.2.1, hy.1], by linarith [ht.2.2, hy.2]⟩
  have h2 := measure_mono (μ := volume) hsub
  rw [hmeas] at h2
  simp only [Real.volume_Ico, Real.volume_Icc] at h2
  have e1 : ∀ t : ℝ, t + d / 2 - (t - d / 2) = d := fun t ↦ by ring
  simp only [e1, Finset.sum_const, nsmul_eq_mul] at h2
  have e2 : x + L + d / 2 - (x - L - d / 2) = 2 * L + d := by ring
  rw [e2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have h3 : (T.card : ℝ) ≤ (2 * L + d) / d := (le_div_iff₀ hd).2 h2
  have h4 : (2 * L + d) / d = 2 * L / d + 1 := by field_simp
  linarith


theorem IsSepBy.countable {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ) : Γ.Countable := by
  have : Γ = ⋃ n : ℕ, Γ ∩ Icc (0 - (n : ℝ)) (0 + n) := by
    ext y
    simp only [mem_iUnion, mem_inter_iff, mem_Icc, zero_sub, zero_add]
    refine ⟨fun hy ↦ ?_, fun ⟨_, h, _⟩ ↦ h⟩
    obtain ⟨n, hn⟩ := exists_nat_ge |y|
    exact ⟨n, hy, by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  rw [this]
  exact countable_iUnion fun n ↦ (hΓ.finite_inter_Icc hd 0 n).countable

theorem tsum_indicator_Icc_le {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ) {L : ℝ}
    (hL : 0 ≤ L) (c : ℝ≥0∞) (x : ℝ) :
    ∑' γ : Γ, (Icc ((γ : ℝ) - L) ((γ : ℝ) + L)).indicator (fun _ ↦ c) x ≤
      ENNReal.ofReal (2 * L / d + 1) * c := by
  have hfin := hΓ.finite_inter_Icc hd x L
  have h1 : ∀ γ : Γ, (Icc ((γ : ℝ) - L) ((γ : ℝ) + L)).indicator (fun _ ↦ c) x =
      (Γ ∩ Icc (x - L) (x + L)).indicator (fun _ ↦ c) (γ : ℝ) := by
    intro γ
    have hγ : (γ : ℝ) ∈ Γ := γ.2
    by_cases h : x ∈ Icc ((γ : ℝ) - L) ((γ : ℝ) + L)
    · have : (γ : ℝ) ∈ Γ ∩ Icc (x - L) (x + L) :=
        ⟨hγ, by linarith [h.2], by linarith [h.1]⟩
      rw [indicator_of_mem h, indicator_of_mem this]
    · have : (γ : ℝ) ∉ Γ ∩ Icc (x - L) (x + L) := fun h' ↦
        h ⟨by linarith [h'.2.2], by linarith [h'.2.1]⟩
      rw [indicator_of_notMem h, indicator_of_notMem this]
  simp_rw [h1]
  rw [tsum_subtype Γ (fun y ↦ (Γ ∩ Icc (x - L) (x + L)).indicator (fun _ ↦ c) y),
    indicator_indicator, inter_eq_right.2 inter_subset_left]
  rw [tsum_eq_sum (s := hfin.toFinset) (fun y hy ↦ by
    rw [indicator_of_notMem]; simpa using hy)]
  have : ∀ y ∈ hfin.toFinset, (Γ ∩ Icc (x - L) (x + L)).indicator (fun _ ↦ c) y = c := fun y hy ↦
    indicator_of_mem (by simpa using hy) _
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin]
  have h2 := hΓ.ncard_Icc_le hd x L hL
  calc ((Γ ∩ Icc (x - L) (x + L)).ncard : ℝ≥0∞) * c
      = ENNReal.ofReal ((Γ ∩ Icc (x - L) (x + L)).ncard : ℝ) * c := by
        rw [ENNReal.ofReal_natCast]
    _ ≤ _ := by gcongr


theorem tsum_lintegral_Icc_le {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ) {L : ℝ}
    (hL : 0 ≤ L) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∑' γ : Γ, ∫⁻ x in Icc ((γ : ℝ) - L) ((γ : ℝ) + L), φ x ≤
      ENNReal.ofReal (2 * L / d + 1) * ∫⁻ x, φ x := by
  have : Countable Γ := (hΓ.countable hd).to_subtype
  have h1 : ∀ γ : Γ, ∫⁻ x in Icc ((γ : ℝ) - L) ((γ : ℝ) + L), φ x =
      ∫⁻ x, (Icc ((γ : ℝ) - L) ((γ : ℝ) + L)).indicator φ x := fun γ ↦
    (lintegral_indicator measurableSet_Icc _).symm
  simp_rw [h1]
  rw [← lintegral_tsum (fun γ ↦ (hφ.indicator measurableSet_Icc).aemeasurable),
    ← lintegral_const_mul _ hφ]
  refine lintegral_mono fun x ↦ ?_
  have : ∀ γ : Γ, (Icc ((γ : ℝ) - L) ((γ : ℝ) + L)).indicator φ x =
      (Icc ((γ : ℝ) - L) ((γ : ℝ) + L)).indicator (fun _ ↦ φ x) x := fun γ ↦ by
    by_cases h : x ∈ Icc ((γ : ℝ) - L) ((γ : ℝ) + L) <;> simp [h]
  simp_rw [this]
  exact tsum_indicator_Icc_le hd hΓ hL _ x


/-- The key estimate: `∑_γ |f(γ+δ_γ) - f(γ)|² ≤ π² L (2L/d + 1) ‖f‖²` when `|δ_γ| ≤ L`. -/
theorem tsum_sub_le (hPW : PaleyWienerThm) {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ)
    {L : ℝ} (hL : 0 ≤ L) {δ : ℝ → ℝ} (hδ : ∀ x ∈ Γ, |δ x| ≤ L) {f : ℂ → ℂ} (hf : MemPW f) :
    ∑' γ : Γ, ‖f (((γ : ℝ) + δ γ : ℝ) : ℂ) - f ((γ : ℝ) : ℂ)‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.pi ^ 2 * L * (2 * L / d + 1)) * pwNormSq f := by
  have hcont : Continuous fun x : ℝ ↦ deriv f (x : ℂ) :=
    ((hf.1.contDiff (n := 1)).continuous_deriv le_rfl).comp Complex.continuous_ofReal
  have hφ : Measurable fun x : ℝ ↦ ‖deriv f (x : ℂ)‖ₑ ^ 2 := hcont.measurable.enorm.pow_const 2
  have h1 : ∀ γ : Γ, ‖f (((γ : ℝ) + δ γ : ℝ) : ℂ) - f ((γ : ℝ) : ℂ)‖ₑ ^ 2 ≤
      ENNReal.ofReal L * ∫⁻ x in Icc ((γ : ℝ) - L) ((γ : ℝ) + L), ‖deriv f (x : ℂ)‖ₑ ^ 2 := by
    intro γ
    refine (enorm_sq_sub_le hf γ (δ γ)).trans ?_
    have hle := hδ γ γ.2
    gcongr
  calc ∑' γ : Γ, ‖f (((γ : ℝ) + δ γ : ℝ) : ℂ) - f ((γ : ℝ) : ℂ)‖ₑ ^ 2
      ≤ ∑' γ : Γ, ENNReal.ofReal L *
          ∫⁻ x in Icc ((γ : ℝ) - L) ((γ : ℝ) + L), ‖deriv f (x : ℂ)‖ₑ ^ 2 :=
        ENNReal.tsum_le_tsum h1
    _ = ENNReal.ofReal L * ∑' γ : Γ,
          ∫⁻ x in Icc ((γ : ℝ) - L) ((γ : ℝ) + L), ‖deriv f (x : ℂ)‖ₑ ^ 2 := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal L * (ENNReal.ofReal (2 * L / d + 1) * pwNormSq (deriv f)) := by
        gcongr
        exact tsum_lintegral_Icc_le hd hΓ hL hφ
    _ ≤ ENNReal.ofReal L * (ENNReal.ofReal (2 * L / d + 1) *
          (ENNReal.ofReal (Real.pi ^ 2) * pwNormSq f)) := by
        gcongr
        exact (pw_bernstein hPW hf).2
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc,
          mul_assoc]
        ring_nf

/-! ## Sampling sums over an injective image -/

theorem sampleSum_image {φ : ℝ → ℝ} {Γ : Set ℝ} (hφ : InjOn φ Γ) (f : ℂ → ℂ) :
    sampleSum (φ '' Γ) f = ∑' γ : Γ, ‖f ((φ γ : ℝ) : ℂ)‖ₑ ^ 2 := by
  unfold sampleSum
  exact (Equiv.tsum_eq (Equiv.Set.imageOfInjOn φ Γ hφ) (fun y : φ '' Γ ↦ ‖f ((y : ℝ) : ℂ)‖ₑ ^ 2)).symm

/-- `(a+b)² ≤ 2a² + 2b²` in `ℝ≥0∞`, summed. -/
theorem tsum_enorm_sq_add_le {ι : Type*} (a b : ι → ℂ) :
    ∑' i, ‖a i + b i‖ₑ ^ 2 ≤ 2 * ∑' i, ‖a i‖ₑ ^ 2 + 2 * ∑' i, ‖b i‖ₑ ^ 2 := by
  have h : ∀ i, ‖a i + b i‖ₑ ^ 2 ≤ 2 * ‖a i‖ₑ ^ 2 + 2 * ‖b i‖ₑ ^ 2 := by
    intro i
    have hr : ‖a i + b i‖ ^ 2 ≤ 2 * ‖a i‖ ^ 2 + 2 * ‖b i‖ ^ 2 := by
      nlinarith [norm_add_le (a i) (b i), sq_nonneg (‖a i‖ - ‖b i‖), norm_nonneg (a i),
        norm_nonneg (b i), norm_nonneg (a i + b i)]
    have := ENNReal.ofReal_le_ofReal hr
    rwa [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      ofReal_norm, ofReal_norm, ENNReal.ofReal_ofNat] at this
  calc ∑' i, ‖a i + b i‖ₑ ^ 2 ≤ ∑' i, (2 * ‖a i‖ₑ ^ 2 + 2 * ‖b i‖ₑ ^ 2) := ENNReal.tsum_le_tsum h
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]

/-! ## Main result -/

theorem dsPerturbation_of_paleyWiener (hPW : PaleyWienerThm) : DSPerturbation := by
  intro Γ ⟨d, hd, hsep⟩ ⟨A, B, hA, hS⟩
  have hπ := Real.pi_pos
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  set L : ℝ := min d ((A : ℝ) / (12 * Real.pi ^ 2)) with hLdef
  have hL0 : 0 < L := lt_min hd (by positivity)
  have hLd : L ≤ d := min_le_left _ _
  have hLA : L ≤ (A : ℝ) / (12 * Real.pi ^ 2) := min_le_right _ _
  have hε : Real.pi ^ 2 * L * (2 * L / d + 1) ≤ (A : ℝ) / 4 := by
    have h1 : 2 * L / d ≤ 2 := by
      rw [div_le_iff₀ hd]; linarith
    have h2 : L * (12 * Real.pi ^ 2) ≤ A := by
      rwa [le_div_iff₀ (by positivity)] at hLA
    have h3 : 0 ≤ Real.pi ^ 2 * L := by positivity
    calc Real.pi ^ 2 * L * (2 * L / d + 1) ≤ Real.pi ^ 2 * L * 3 := by gcongr; linarith
      _ ≤ (A : ℝ) / 4 := by nlinarith
  refine ⟨L, hL0, fun δ hδ hinj ↦ ?_⟩
  set a4 : ℝ≥0 := A / 4 with ha4
  have ha4pos : 0 < a4 := by positivity
  have hAa4 : (A : ℝ≥0∞) = 4 * a4 := by
    rw [ha4, ← ENNReal.coe_ofNat, ← ENNReal.coe_mul]
    congr 1
    rw [mul_div_cancel₀ _ (by norm_num : (4 : ℝ≥0) ≠ 0)]
  refine ⟨a4, 2 * B + 2 * a4, ha4pos, fun f hf ↦ ?_⟩
  set N := pwNormSq f with hN
  have hNtop : N ≠ ⊤ := pwNormSq_ne_top hf
  have hdel : ∀ x ∈ Γ, |δ x| ≤ L := hδ
  set D := ∑' γ : Γ, ‖f (((γ : ℝ) + δ γ : ℝ) : ℂ) - f ((γ : ℝ) : ℂ)‖ₑ ^ 2 with hD
  have hDle : D ≤ (a4 : ℝ≥0∞) * N := by
    refine (tsum_sub_le hPW hd hsep hL0.le hdel hf).trans ?_
    gcongr
    rw [ha4, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by rw [NNReal.coe_div]; simpa using hε)
  have hS' : sampleSum ((fun x ↦ x + δ x) '' Γ) f = ∑' γ : Γ, ‖f (((γ : ℝ) + δ γ : ℝ) : ℂ)‖ₑ ^ 2 :=
    sampleSum_image hinj f
  obtain ⟨hlow, hup⟩ := hS f hf
  have hK : (a4 : ℝ≥0∞) * N ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hNtop
  rw [hS']
  have hSdef : sampleSum Γ f = ∑' γ : Γ, ‖f ((γ : ℝ) : ℂ)‖ₑ ^ 2 := rfl
  constructor
  · -- lower bound
    have h1 := tsum_enorm_sq_add_le (fun γ : Γ ↦ f (((γ : ℝ) + δ γ : ℝ) : ℂ))
      (fun γ : Γ ↦ f ((γ : ℝ) : ℂ) - f (((γ : ℝ) + δ γ : ℝ) : ℂ))
    simp only [add_sub_cancel] at h1
    have h2 : ∑' γ : Γ, ‖f ((γ : ℝ) : ℂ) - f (((γ : ℝ) + δ γ : ℝ) : ℂ)‖ₑ ^ 2 = D := by
      rw [hD]
      refine tsum_congr fun γ ↦ ?_
      rw [enorm_sub_rev]
    rw [h2, ← hSdef] at h1
    have h3 : 4 * ((a4 : ℝ≥0∞) * N) ≤ 2 * ∑' γ : Γ, ‖f (((γ : ℝ) + δ γ : ℝ) : ℂ)‖ₑ ^ 2 +
        2 * ((a4 : ℝ≥0∞) * N) := by
      calc 4 * ((a4 : ℝ≥0∞) * N) = (A : ℝ≥0∞) * N := by rw [hAa4, mul_assoc]
        _ ≤ sampleSum Γ f := hlow
        _ ≤ _ := h1
        _ ≤ _ := by gcongr
    have h4 : 2 * ((a4 : ℝ≥0∞) * N) + 2 * ((a4 : ℝ≥0∞) * N) ≤
        2 * ∑' γ : Γ, ‖f (((γ : ℝ) + δ γ : ℝ) : ℂ)‖ₑ ^ 2 + 2 * ((a4 : ℝ≥0∞) * N) := by
      refine le_trans (le_of_eq ?_) h3
      ring
    have h5 := (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (by simp) hK)).1 h4
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by simp)).1 h5
  · -- upper bound
    have h1 := tsum_enorm_sq_add_le (fun γ : Γ ↦ f ((γ : ℝ) : ℂ))
      (fun γ : Γ ↦ f (((γ : ℝ) + δ γ : ℝ) : ℂ) - f ((γ : ℝ) : ℂ))
    simp only [add_sub_cancel] at h1
    rw [← hD, ← hSdef] at h1
    refine h1.trans ?_
    have : ((2 * B + 2 * a4 : ℝ≥0) : ℝ≥0∞) * N = 2 * ((B : ℝ≥0∞) * N) + 2 * ((a4 : ℝ≥0∞) * N) := by
      push_cast; ring
    rw [this]
    gcongr

end FF
