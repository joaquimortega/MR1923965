import FourierFrames.PW.Bounds

/-!
# M01 — The Plancherel–Pólya inequality and its uniform tail version

See `blueprint/M01_PW.md`, §3.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

theorem memL2pi_of_continuous {g : ℝ → ℂ} (hg : Continuous g) : MemL2pi g := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -Real.pi) (b := Real.pi)).exists_bound_of_continuousOn
    hg.continuousOn
  refine MemLp.of_bound hg.aestronglyMeasurable C ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2
    (Filter.Eventually.of_forall fun t ht ↦ hC t (Ioc_subset_Icc_self ht))

/-- Circle sub-mean-value inequality. -/
theorem circle_sq_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) (ρ : ℝ) :
    ENNReal.ofReal (2 * Real.pi) * ‖f c‖ₑ ^ 2 ≤
      ∫⁻ θ in Ioc (-Real.pi) Real.pi, ‖f (circleMap c ρ θ)‖ₑ ^ 2 := by
  set g : ℝ → ℂ := fun θ ↦ f (circleMap c ρ θ) with hgdef
  have hgc : Continuous g := hf.continuous.comp (continuous_circleMap c ρ)
  have hg : MemL2pi g := memL2pi_of_continuous hgc
  have hmean : f c = ((2 * Real.pi)⁻¹ : ℝ) • ∫ θ in (-Real.pi)..Real.pi, g θ := by
    have h1 := (hf.diffContOnCl (s := Metric.ball c |ρ|)).circleAverage (R := ρ)
    have h2 : Real.circleAverage f c ρ = ((2 * Real.pi)⁻¹ : ℝ) • ∫ θ in 0..2 * Real.pi, g θ :=
      Real.circleAverage_def
    have hper : Function.Periodic g (2 * Real.pi) := (periodic_circleMap c ρ).comp f
    have hI := hper.intervalIntegral_add_eq (-Real.pi) 0
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at hI
    rw [← h1, h2, hI]
  have hpi : 0 < 2 * Real.pi := by positivity
  have hS : l2piSq g ≠ ⊤ := l2piSq_ne_top hg
  have h1 : ‖∫ θ in (-Real.pi)..Real.pi, g θ‖ ≤ Real.sqrt (2 * Real.pi * (l2piSq g).toReal) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    refine (norm_integral_le_lintegral_norm _).trans ?_
    simp_rw [ofReal_norm]
    exact lintegral_enorm_le_sqrt hg
  have h2 : ‖f c‖ ≤ (2 * Real.pi)⁻¹ * Real.sqrt (2 * Real.pi * (l2piSq g).toReal) := by
    rw [hmean, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : 2 * Real.pi * ‖f c‖ ^ 2 ≤ (l2piSq g).toReal := by
    have h4 : ‖f c‖ ^ 2 ≤ ((2 * Real.pi)⁻¹ * Real.sqrt (2 * Real.pi * (l2piSq g).toReal)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at h4
    have : 2 * Real.pi * ‖f c‖ ^ 2 ≤ 2 * Real.pi * ((2 * Real.pi)⁻¹ ^ 2 * (2 * Real.pi * (l2piSq g).toReal)) :=
      mul_le_mul_of_nonneg_left h4 hpi.le
    refine this.trans (le_of_eq ?_)
    field_simp
  have h5 : ENNReal.ofReal (2 * Real.pi) * ‖f c‖ₑ ^ 2 ≤ l2piSq g := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul hpi.le]
    calc ENNReal.ofReal (2 * Real.pi * ‖f c‖ ^ 2) ≤ ENNReal.ofReal (l2piSq g).toReal :=
          ENNReal.ofReal_le_ofReal h3
      _ = l2piSq g := ENNReal.ofReal_toReal hS
  exact h5

theorem lintegral_Ioo_id (r : ℝ) (hr : 0 < r) :
    ∫⁻ ρ in Ioo 0 r, ENNReal.ofReal ρ = ENNReal.ofReal (r ^ 2 / 2) := by
  have hI : IntegrableOn (fun ρ : ℝ ↦ ρ) (Ioo 0 r) :=
    (continuous_id.integrableOn_Icc (a := 0) (b := r)).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ↦ hx.1.le)]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le, integral_id]
  ring

/-- **Sub-mean-value property** of `|f|²` for entire `f`:
`|f(c)|² ≤ (π r²)⁻¹ ∫_{D(c,r)} |f|² dA`. -/
theorem enorm_sq_le_lintegral_ball {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) {r : ℝ}
    (hr : 0 < r) :
    ‖f c‖ₑ ^ 2 ≤ ENNReal.ofReal (1 / (Real.pi * r ^ 2)) * ∫⁻ z in ball c r, ‖f z‖ₑ ^ 2 := by
  set h : ℂ → ℝ≥0∞ := fun z ↦ ‖f z‖ₑ ^ 2 with hh
  have hhm : Measurable h := (hf.continuous.measurable.enorm).pow_const 2
  set F : ℂ → ℝ≥0∞ := (ball (0 : ℂ) r).indicator (fun z ↦ h (c + z)) with hF
  have hFm : Measurable F := (hhm.comp (measurable_const.add measurable_id)).indicator measurableSet_ball
  -- Step A
  have hA : ∫⁻ z in ball c r, h z = ∫⁻ z, F z := by
    rw [← lintegral_indicator measurableSet_ball,
      ← lintegral_add_left_eq_self (μ := (volume : Measure ℂ)) ((ball c r).indicator h) c]
    refine lintegral_congr fun z ↦ ?_
    simp only [hF, Set.indicator, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  -- Step B
  have hB := Complex.lintegral_comp_polarCoord_symm F
  have hsm : Measurable (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p) := by
    have : (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p) =
        fun p ↦ (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I) :=
      funext Complex.polarCoord_symm_apply
    rw [this]; fun_prop
  have hGm : Measurable (fun p : ℝ × ℝ ↦
      ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p)) := by
    simp only [smul_eq_mul]
    exact (ENNReal.measurable_ofReal.comp measurable_fst).mul (hFm.comp hsm)
  have hsub : (Ioo 0 r) ×ˢ (Ioo (-Real.pi) Real.pi) ⊆ Complex.polarCoord.target :=
    fun p hp ↦ ⟨hp.1.1, hp.2⟩
  have hC : ∫⁻ p in (Ioo 0 r) ×ˢ (Ioo (-Real.pi) Real.pi),
      ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p) ≤ ∫⁻ z, F z := by
    rw [← hB]; exact lintegral_mono_set hsub
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hGm.aemeasurable] at hC
  have hD : ∀ ρ ∈ Ioo 0 r, ENNReal.ofReal ρ * (ENNReal.ofReal (2 * Real.pi) * ‖f c‖ₑ ^ 2) ≤
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (ρ, θ).1 • F (Complex.polarCoord.symm (ρ, θ)) := by
    intro ρ hρ
    have h1 : ∀ θ ∈ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (ρ, θ).1 • F (Complex.polarCoord.symm (ρ, θ)) =
          ENNReal.ofReal ρ * h (circleMap c ρ θ) := by
      intro θ _
      have hz : Complex.polarCoord.symm (ρ, θ) = circleMap 0 ρ θ := by
        rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I]
        simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
      have hz2 : circleMap 0 ρ θ ∈ ball (0 : ℂ) r := by
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hρ.1]; exact hρ.2
      simp only [smul_eq_mul, hz, hF, Set.indicator_of_mem hz2]
      congr 2
      simp [circleMap]
    rw [setLIntegral_congr_fun measurableSet_Ioo h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul' le_rfl ?_
    rw [setLIntegral_congr Ioo_ae_eq_Ioc]
    exact circle_sq_le hf c ρ
  have hE : ENNReal.ofReal (r ^ 2 / 2) * (ENNReal.ofReal (2 * Real.pi) * ‖f c‖ₑ ^ 2) ≤ ∫⁻ z, F z := by
    refine le_trans ?_ hC
    calc ENNReal.ofReal (r ^ 2 / 2) * (ENNReal.ofReal (2 * Real.pi) * ‖f c‖ₑ ^ 2)
        = ∫⁻ ρ in Ioo 0 r, ENNReal.ofReal ρ * (ENNReal.ofReal (2 * Real.pi) * ‖f c‖ₑ ^ 2) := by
          rw [lintegral_mul_const _ ENNReal.measurable_ofReal, lintegral_Ioo_id r hr]
      _ ≤ _ := setLIntegral_mono' measurableSet_Ioo hD
  rw [← hA] at hE
  have hpr : 0 < Real.pi * r ^ 2 := by positivity
  have h2 : ENNReal.ofReal (r ^ 2 / 2) * ENNReal.ofReal (2 * Real.pi) = ENNReal.ofReal (Real.pi * r ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have h3 : ENNReal.ofReal (1 / (Real.pi * r ^ 2)) * ENNReal.ofReal (Real.pi * r ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hpr.ne', ENNReal.ofReal_one]
  calc ‖f c‖ₑ ^ 2 = ENNReal.ofReal (1 / (Real.pi * r ^ 2)) * (ENNReal.ofReal (Real.pi * r ^ 2) * ‖f c‖ₑ ^ 2) := by
        rw [← mul_assoc, h3, one_mul]
    _ ≤ _ := by
        refine mul_le_mul' le_rfl ?_
        rw [← h2, mul_assoc]; exact hE

theorem integral_exp_two_pi (r : ℝ) :
    ∫ y in (0 : ℝ)..r, Real.exp (2 * Real.pi * y) = (Real.exp (2 * Real.pi * r) - 1) / (2 * Real.pi) := by
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y ↦ Real.exp (2 * Real.pi * y) / (2 * Real.pi))
    (f' := fun y ↦ Real.exp (2 * Real.pi * y))]
  · simp [sub_div]
  · intro x _
    have := ((hasDerivAt_id x).const_mul (2 * Real.pi)).exp.div_const (2 * Real.pi)
    refine this.congr_deriv ?_
    simp only [id, mul_one]
    field_simp
  · exact (by fun_prop : Continuous fun y : ℝ ↦ Real.exp (2 * Real.pi * y)).intervalIntegrable _ _

theorem integral_exp_abs (r : ℝ) (hr : 0 ≤ r) :
    ∫ y in (-r)..r, Real.exp (2 * Real.pi * |y|) = (Real.exp (2 * Real.pi * r) - 1) / Real.pi := by
  have hc : Continuous fun y : ℝ ↦ Real.exp (2 * Real.pi * |y|) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h0 : ∫ y in (0 : ℝ)..r, Real.exp (2 * Real.pi * |y|) =
      ∫ y in (0 : ℝ)..r, Real.exp (2 * Real.pi * y) := by
    refine intervalIntegral.integral_congr fun y hy ↦ ?_
    rw [uIcc_of_le hr] at hy
    simp only [abs_of_nonneg hy.1]
  have h1 : ∫ y in (-r)..0, Real.exp (2 * Real.pi * |y|) =
      ∫ y in (0 : ℝ)..r, Real.exp (2 * Real.pi * |y|) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := r)
      (fun y : ℝ ↦ Real.exp (2 * Real.pi * |y|))
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  rw [h1, h0, integral_exp_two_pi]
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem measurableEquivRealProd_symm_mk (x y : ℝ) :
    (Complex.measurableEquivRealProd.symm (x, y)) = (x : ℂ) + (y : ℂ) * I := by
  apply Complex.ext <;> simp [Complex.measurableEquivRealProd]

/-- `∫∫_{|y| < r} |f(x+iy)|² dx dy ≤ (e^{2πr} - 1)/π · ‖f‖²`. -/
theorem lintegral_strip_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) {r : ℝ} (hr : 0 < r) :
    ∫⁻ z in {z : ℂ | |z.im| < r}, ‖f z‖ₑ ^ 2 ≤
      ENNReal.ofReal ((Real.exp (2 * Real.pi * r) - 1) / Real.pi) * pwNormSq f := by
  set S : Set ℂ := {z : ℂ | |z.im| < r} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_lt (continuous_abs.comp Complex.continuous_im).measurable measurable_const
  set G : ℂ → ℝ≥0∞ := fun z ↦ ‖f z‖ₑ ^ 2 with hG
  have hGm : Measurable G := (hf.1.continuous.measurable.enorm).pow_const 2
  have hm : Measurable (fun p : ℝ × ℝ ↦ S.indicator G (Complex.measurableEquivRealProd.symm p)) :=
    (hGm.indicator hS).comp Complex.measurableEquivRealProd.symm.measurable
  rw [← lintegral_indicator hS,
    ← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod_symm _ hm.aemeasurable]
  have h1 : ∀ y : ℝ, ∫⁻ x : ℝ, S.indicator G (Complex.measurableEquivRealProd.symm (x, y)) ≤
      (Ioo (-r) r).indicator (fun y ↦ ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * pwNormSq f) y := by
    intro y
    by_cases hy : y ∈ Ioo (-r) r
    · rw [Set.indicator_of_mem hy]
      have hyS : |y| < r := abs_lt.2 ⟨hy.1, hy.2⟩
      calc ∫⁻ x : ℝ, S.indicator G (Complex.measurableEquivRealProd.symm (x, y))
          = ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 := by
            refine lintegral_congr fun x ↦ ?_
            rw [measurableEquivRealProd_symm_mk, Set.indicator_of_mem (by simpa [hSdef] using hyS)]
        _ ≤ _ := by
            exact pw_line_integral_le hPW hf y
    · rw [Set.indicator_of_notMem hy]
      have : ∀ x : ℝ, S.indicator G (Complex.measurableEquivRealProd.symm (x, y)) = 0 := by
        intro x
        rw [measurableEquivRealProd_symm_mk, Set.indicator_of_notMem]
        have : ¬ (|y| < r) := fun h ↦ hy (abs_lt.1 h)
        simpa [hSdef] using this
      simp only [this, lintegral_zero]
      exact bot_le
  have hcont : Continuous fun y : ℝ ↦ Real.exp (2 * Real.pi * |y|) := by fun_prop
  have hint : ∫⁻ y in Ioo (-r) r, ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) =
      ENNReal.ofReal ((Real.exp (2 * Real.pi * r) - 1) / Real.pi) := by
    have hI : IntegrableOn (fun y : ℝ ↦ Real.exp (2 * Real.pi * |y|)) (Ioo (-r) r) :=
      (hcont.integrableOn_Icc (a := -r) (b := r)).mono_set Ioo_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hI
      (ae_restrict_of_forall_mem measurableSet_Ioo fun x _ ↦ (Real.exp_pos _).le),
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
      integral_exp_abs r hr.le]
  calc _ ≤ ∫⁻ y : ℝ, (Ioo (-r) r).indicator
        (fun y ↦ ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * pwNormSq f) y := lintegral_mono h1
    _ = ∫⁻ y in Ioo (-r) r, ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * pwNormSq f :=
        lintegral_indicator measurableSet_Ioo _
    _ = _ := by
        rw [lintegral_mul_const' _ _ (pwNormSq_ne_top hf), hint]

/-- The Plancherel–Pólya constant `C(δ) = 4 (e^{πδ} - 1) / (π² δ²)`; it depends only on `δ`. -/
def ppConst (δ : ℝ) : ℝ := 4 * (Real.exp (Real.pi * δ) - 1) / (Real.pi ^ 2 * δ ^ 2)

theorem sampleSum_eq_tsum_indicator (Λ : Set ℝ) (f : ℂ → ℂ) :
    sampleSum Λ f = ∑' x : ℝ, Λ.indicator (fun x : ℝ ↦ ‖f (x : ℂ)‖ₑ ^ 2) x := by
  unfold sampleSum
  exact tsum_subtype Λ (fun x : ℝ ↦ ‖f (x : ℂ)‖ₑ ^ 2)

/-- `sampleSum` is monotone in the set (moved here from `Perturbation.lean` / `Suff` at
assembly). -/
theorem sampleSum_mono {Λ₁ Λ₂ : Set ℝ} (h : Λ₁ ⊆ Λ₂) (f : ℂ → ℂ) :
    sampleSum Λ₁ f ≤ sampleSum Λ₂ f := by
  rw [sampleSum_eq_tsum_indicator, sampleSum_eq_tsum_indicator]
  exact ENNReal.tsum_le_tsum fun x ↦ Set.indicator_le_indicator_of_subset h (by intro; positivity) x

/-- Subadditivity of the sampling sum (used for `Λ_α = Λ' ∪ Λ''`, p. 796). -/
theorem sampleSum_union_le (Λ₁ Λ₂ : Set ℝ) (f : ℂ → ℂ) :
    sampleSum (Λ₁ ∪ Λ₂) f ≤ sampleSum Λ₁ f + sampleSum Λ₂ f := by
  rw [sampleSum_eq_tsum_indicator, sampleSum_eq_tsum_indicator, sampleSum_eq_tsum_indicator,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  by_cases h1 : x ∈ Λ₁ <;> by_cases h2 : x ∈ Λ₂ <;> simp [Set.indicator, h1, h2]

/-- The core packing argument: a `δ`-separated set whose `δ/2`-discs all lie in a region `T`. -/
theorem sampleSum_le_lintegral {δ : ℝ} (hδ : 0 < δ) {Λ : Set ℝ} (hΛ : IsSepBy δ Λ)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (T : Set ℂ)
    (hT : ∀ x ∈ Λ, ball ((x : ℝ) : ℂ) (δ / 2) ⊆ T) :
    sampleSum Λ f ≤ ENNReal.ofReal (1 / (Real.pi * (δ / 2) ^ 2)) * ∫⁻ z in T, ‖f z‖ₑ ^ 2 := by
  have hr : 0 < δ / 2 := by positivity
  unfold sampleSum
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  have hdisj : (↑s : Set Λ).PairwiseDisjoint (fun x : Λ ↦ ball (((x : ℝ)) : ℂ) (δ / 2)) := by
    intro x _ y _ hxy
    apply Metric.ball_disjoint_ball
    rw [Complex.dist_eq]
    have : (x : ℝ) ≠ (y : ℝ) := fun h ↦ hxy (Subtype.ext h)
    have h1 := hΛ x x.2 y y.2 this
    have h2 : ‖((x : ℝ) : ℂ) - ((y : ℝ) : ℂ)‖ = |(x : ℝ) - (y : ℝ)| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [h2]; linarith
  calc ∑ x ∈ s, ‖f (((x : ℝ)) : ℂ)‖ₑ ^ 2
      ≤ ∑ x ∈ s, ENNReal.ofReal (1 / (Real.pi * (δ / 2) ^ 2)) *
          ∫⁻ z in ball (((x : ℝ)) : ℂ) (δ / 2), ‖f z‖ₑ ^ 2 :=
        Finset.sum_le_sum fun x _ ↦ enorm_sq_le_lintegral_ball hf _ hr
    _ = ENNReal.ofReal (1 / (Real.pi * (δ / 2) ^ 2)) *
          ∫⁻ z in ⋃ x ∈ s, ball (((x : ℝ)) : ℂ) (δ / 2), ‖f z‖ₑ ^ 2 := by
        rw [← Finset.mul_sum, lintegral_biUnion_finset hdisj (fun _ _ ↦ measurableSet_ball)]
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (lintegral_mono_set ?_)
        exact Set.iUnion₂_subset fun x _ ↦ hT x x.2

/-- **Plancherel–Pólya**, explicit constant. -/
theorem plancherelPolya_explicit (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) {Λ : Set ℝ}
    (hΛ : IsSepBy δ Λ) {f : ℂ → ℂ} (hf : MemPW f) :
    sampleSum Λ f ≤ ENNReal.ofReal (ppConst δ) * pwNormSq f := by
  have hr : 0 < δ / 2 := by positivity
  have hstrip : ∀ x ∈ Λ, ball ((x : ℝ) : ℂ) (δ / 2) ⊆ {z : ℂ | |z.im| < δ / 2} := by
    intro x _ z hz
    rw [mem_ball, Complex.dist_eq] at hz
    have h1 : |(z - ((x : ℝ) : ℂ)).im| ≤ ‖z - ((x : ℝ) : ℂ)‖ := Complex.abs_im_le_norm _
    show |z.im| < δ / 2
    simpa using h1.trans_lt hz
  refine (sampleSum_le_lintegral hδ hΛ hf.1 _ hstrip).trans ?_
  refine (mul_le_mul' le_rfl (lintegral_strip_le hPW hf hr)).trans (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  unfold ppConst
  have : 2 * Real.pi * (δ / 2) = Real.pi * δ := by ring
  rw [this]
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Plancherel–Pólya** (interface form): the constant depends only on `δ`. -/
theorem plancherelPolya (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ Λ : Set ℝ, IsSepBy δ Λ → ∀ f : ℂ → ℂ, MemPW f → sampleSum Λ f ≤ C * pwNormSq f := by
  refine ⟨(ENNReal.ofReal (ppConst δ)).toNNReal, fun Λ hΛ f hf ↦ ?_⟩
  rw [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]
  exact plancherelPolya_explicit hPW hδ hΛ hf

/-- The strip-tail integral `∫∫_{|y|<r, |x| ≥ R} |f|²` tends to `0` as `R → ∞`. -/
theorem tendsto_strip_tail (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R : ℝ ↦ ∫⁻ z in {z : ℂ | |z.im| < r ∧ R ≤ |z.re|}, ‖f z‖ₑ ^ 2)
      atTop (nhds 0) := by
  set S : Set ℂ := {z : ℂ | |z.im| < r} with hSdef
  have hSm : MeasurableSet S :=
    measurableSet_lt (continuous_abs.comp Complex.continuous_im).measurable measurable_const
  set G : ℂ → ℝ≥0∞ := fun z ↦ ‖f z‖ₑ ^ 2 with hG
  have hGm : Measurable G := (hf.1.continuous.measurable.enorm).pow_const 2
  have hAm : ∀ R : ℝ, MeasurableSet {z : ℂ | R ≤ |z.re|} := fun R ↦
    measurableSet_le measurable_const (continuous_abs.comp Complex.continuous_re).measurable
  have heq : ∀ R : ℝ, ∫⁻ z in {z : ℂ | |z.im| < r ∧ R ≤ |z.re|}, G z =
      ∫⁻ z in S, ({z : ℂ | R ≤ |z.re|}).indicator G z := by
    intro R
    rw [setLIntegral_indicator (hAm R)]
    have : {z : ℂ | R ≤ |z.re|} ∩ S = {z : ℂ | |z.im| < r ∧ R ≤ |z.re|} := by
      ext z; simp [hSdef, and_comm]
    rw [this]
  simp_rw [heq]
  have h0 : ∫⁻ z in S, (0 : ℝ≥0∞) = 0 := by simp
  rw [← h0]
  refine tendsto_lintegral_filter_of_dominated_convergence (bound := G) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun R ↦ hGm.indicator (hAm R)
  · exact Filter.Eventually.of_forall fun R ↦ Filter.Eventually.of_forall fun z ↦
      Set.indicator_le_self _ _ z
  · have := lintegral_strip_le hPW hf hr
    exact ((this.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.2 (pwNormSq_ne_top hf)))).ne)
  · refine Filter.Eventually.of_forall fun z ↦ ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop |z.re|] with R hR
    have hz : z ∉ {z : ℂ | R ≤ |z.re|} := by simpa using hR
    exact (Set.indicator_of_notMem hz _).symm

/-- **Uniform tail version**: for fixed `δ` and `f ∈ PW`, `∑_{λ ∈ Λ, |λ| ≥ R} |f(λ)|² → 0` as
`R → ∞`, uniformly over all `δ`-separated `Λ`. Explicitly,
`sampleSum (Λ ∩ {|x| ≥ R}) f ≤ (π (δ/2)²)⁻¹ ∫∫_{|y|<δ/2, |x| ≥ R - δ/2} |f|²`. -/
theorem plancherelPolya_tail (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) {f : ℂ → ℂ}
    (hf : MemPW f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ R : ℝ, ∀ Λ : Set ℝ, IsSepBy δ Λ → sampleSum (Λ ∩ {x : ℝ | R ≤ |x|}) f ≤ ε := by
  have hr : 0 < δ / 2 := by positivity
  set C0 : ℝ≥0∞ := ENNReal.ofReal (1 / (Real.pi * (δ / 2) ^ 2)) with hC0
  have hlim := ENNReal.Tendsto.const_mul (tendsto_strip_tail hPW hf hr) (Or.inr (ENNReal.ofReal_ne_top (r := 1 / (Real.pi * (δ / 2) ^ 2))))
  rw [mul_zero] at hlim
  obtain ⟨R', hR'⟩ := (hlim.eventually (gt_mem_nhds (pos_iff_ne_zero.2 hε))).exists_forall_of_atTop
  refine ⟨R' + δ / 2 , fun Λ hΛ ↦ ?_⟩
  have hsep : IsSepBy δ (Λ ∩ {x : ℝ | R' + δ / 2 ≤ |x|}) := hΛ.mono le_rfl Set.inter_subset_left
  have hT : ∀ x ∈ Λ ∩ {x : ℝ | R' + δ / 2 ≤ |x|}, ball ((x : ℝ) : ℂ) (δ / 2) ⊆
      {z : ℂ | |z.im| < δ / 2 ∧ R' ≤ |z.re|} := by
    intro x hx z hz
    rw [mem_ball, Complex.dist_eq] at hz
    have h1 : |(z - ((x : ℝ) : ℂ)).im| ≤ ‖z - ((x : ℝ) : ℂ)‖ := Complex.abs_im_le_norm _
    have h2 : |(z - ((x : ℝ) : ℂ)).re| ≤ ‖z - ((x : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.sub_re, Complex.ofReal_re] at h1 h2
    have hx2 : R' + δ / 2 ≤ |x| := hx.2
    refine ⟨show |z.im| < δ / 2 from h1.trans_lt hz, ?_⟩
    have h3 : |x| ≤ |z.re| + |z.re - x| := by
      calc |x| = |z.re - (z.re - x)| := by ring_nf
        _ ≤ |z.re| + |z.re - x| := abs_sub _ _
    linarith
  refine ((sampleSum_le_lintegral hδ hsep hf.1 _ hT).trans (le_of_lt ?_))
  exact hR' R' le_rfl

/-- The tail bound for a union of two `δ`-separated sets (used for the level sets `Λ_α`, which are
unions of two `δ`-separated sets, in the limit `α → π/2` of Theorem 1). -/
theorem plancherelPolya_tail_union (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) {f : ℂ → ℂ}
    (hf : MemPW f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ R : ℝ, ∀ A B : Set ℝ, IsSepBy δ A → IsSepBy δ B →
      sampleSum ((A ∪ B) ∩ {x : ℝ | R ≤ |x|}) f ≤ ε := by
  obtain ⟨R, hR⟩ := plancherelPolya_tail hPW hδ hf (ENNReal.half_pos hε).ne'
  refine ⟨R, fun A B hA hB ↦ ?_⟩
  rw [Set.union_inter_distrib_right]
  exact (sampleSum_union_le _ _ f).trans ((add_le_add (hR A hA) (hR B hB)).trans_eq (ENNReal.add_halves ε))

end FF
