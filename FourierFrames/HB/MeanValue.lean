import FourierFrames.Defs

/-!
# M02 helper — circle and area mean-value inequalities for `|G|²`
-/

open MeasureTheory Metric Set Complex Filter Topology intervalIntegral
open scoped ENNReal NNReal

noncomputable section

namespace FF

/-- Cauchy–Schwarz for continuous complex-valued functions on an interval. -/
theorem sq_norm_intervalIntegral_le {a : ℝ → ℂ} (ha : Continuous a) {s t : ℝ} (hst : s ≤ t) :
    ‖∫ θ in s..t, a θ‖ ^ 2 ≤ (t - s) * ∫ θ in s..t, ‖a θ‖ ^ 2 := by
  rcases hst.eq_or_lt with h | h
  · subst h; simp
  set L := t - s with hL
  have hLpos : 0 < L := by rw [hL]; linarith
  have hn : Continuous fun θ ↦ ‖a θ‖ := ha.norm
  set S := ∫ θ in s..t, ‖a θ‖ with hS
  set Q := ∫ θ in s..t, ‖a θ‖ ^ 2 with hQ
  have h1 : ‖∫ θ in s..t, a θ‖ ≤ S := norm_integral_le_integral_norm hst
  set k := S / L with hk
  have h2 : 0 ≤ ∫ θ in s..t, (‖a θ‖ - k) ^ 2 :=
    intervalIntegral.integral_nonneg hst fun θ _ ↦ sq_nonneg _
  have h3 : ∫ θ in s..t, (‖a θ‖ - k) ^ 2 = Q - 2 * k * S + k ^ 2 * L := by
    have e : ∀ θ, (‖a θ‖ - k) ^ 2 = (‖a θ‖ ^ 2 - 2 * k * ‖a θ‖) + k ^ 2 := fun θ ↦ by ring
    simp only [e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul]
    · simp [hQ, hS, hL]; ring
    · exact (hn.pow 2).intervalIntegrable _ _
    · exact (hn.const_mul _).intervalIntegrable _ _
    · exact ((hn.pow 2).sub (hn.const_mul _)).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
  rw [h3] at h2
  have h4 : k * L = S := by rw [hk]; field_simp
  have h5 : S ^ 2 ≤ L * Q := by
    have : Q - 2 * k * S + k ^ 2 * L = Q - S ^ 2 / L := by
      rw [hk]; field_simp; ring
    rw [this] at h2
    have : S ^ 2 / L ≤ Q := by linarith
    rw [div_le_iff₀ hLpos] at this
    linarith
  have h6 : 0 ≤ ‖∫ θ in s..t, a θ‖ := norm_nonneg _
  calc ‖∫ θ in s..t, a θ‖ ^ 2 ≤ S ^ 2 := by gcongr
    _ ≤ L * Q := h5

theorem enorm_sq_eq_ofReal (z : ℂ) : ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Circle inequality for `|G|²` in `ℝ≥0∞` form, over `(-π, π]`. -/
theorem circle_lintegral_ge {G : ℂ → ℂ} {c : ℂ} {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hG : DifferentiableOn ℂ G (closedBall c r)) :
    ENNReal.ofReal (2 * Real.pi) * ‖G c‖ₑ ^ 2 ≤
      ∫⁻ θ in Ioc (-Real.pi) Real.pi, ‖G (circleMap c ρ θ)‖ₑ ^ 2 := by
  set a : ℝ → ℂ := fun θ ↦ G (circleMap c ρ θ) with ha
  have hsph : ∀ θ, circleMap c ρ θ ∈ closedBall c r := fun θ ↦
    (closedBall_subset_closedBall hρr) (sphere_subset_closedBall (circleMap_mem_sphere c hρ.le θ))
  have hac : Continuous a :=
    hG.continuousOn.comp_continuous (continuous_circleMap c ρ) hsph
  have hdc : DiffContOnCl ℂ G (ball c |ρ|) := by
    apply DifferentiableOn.diffContOnCl
    rw [abs_of_pos hρ, closure_ball c hρ.ne']
    exact hG.mono (closedBall_subset_closedBall hρr)
  have havg := hdc.circleAverage
  rw [Real.circleAverage_def] at havg
  have hint : ∫ θ in (0:ℝ)..2 * Real.pi, a θ = (2 * Real.pi) • G c :=
    (inv_smul_eq_iff₀ (by positivity)).mp havg
  have hper : Function.Periodic a (2 * Real.pi) := fun θ ↦ by
    simp only [ha]; rw [periodic_circleMap c ρ θ]
  have hshift : ∫ θ in (-Real.pi)..Real.pi, a θ = ∫ θ in (0:ℝ)..2 * Real.pi, a θ := by
    have := hper.intervalIntegral_add_eq (-Real.pi) 0
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at this
    exact this
  have hcs := sq_norm_intervalIntegral_le hac (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])
  rw [hshift, hint] at hcs
  have hnorm : ‖(2 * Real.pi) • G c‖ = 2 * Real.pi * ‖G c‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm] at hcs
  have hQ : 2 * Real.pi * ‖G c‖ ^ 2 ≤ ∫ θ in (-Real.pi)..Real.pi, ‖a θ‖ ^ 2 := by
    have : (2 * Real.pi) * (2 * Real.pi * ‖G c‖ ^ 2) ≤
        (2 * Real.pi) * ∫ θ in (-Real.pi)..Real.pi, ‖a θ‖ ^ 2 := by
      nlinarith [hcs]
    exact le_of_mul_le_mul_left this (by positivity)
  have hlint : ∫⁻ θ in Ioc (-Real.pi) Real.pi, ‖a θ‖ₑ ^ 2 =
      ENNReal.ofReal (∫ θ in (-Real.pi)..Real.pi, ‖a θ‖ ^ 2) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      ofReal_integral_eq_lintegral_ofReal]
    · simp only [enorm_sq_eq_ofReal]
    · exact ((hac.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · exact Filter.Eventually.of_forall fun θ ↦ by positivity
  show _ ≤ ∫⁻ θ in Ioc (-Real.pi) Real.pi, ‖a θ‖ₑ ^ 2
  rw [hlint, enorm_sq_eq_ofReal, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hQ

theorem lintegral_Ioo_ofReal_id {r : ℝ} (hr : 0 < r) :
    ∫⁻ ρ in Ioo (0:ℝ) r, ENNReal.ofReal ρ = ENNReal.ofReal (r ^ 2 / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
    simp
  · exact (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · exact (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun ρ h ↦ h.1.le)

theorem circleMap_eq_polar (c : ℂ) (p : ℝ × ℝ) :
    circleMap c p.1 p.2 = c + Complex.polarCoord.symm p := by
  rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

theorem area_ge_of_measurable {G : ℂ → ℂ} (hm : Measurable G) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (closedBall c r)) :
    ENNReal.ofReal (Real.pi * r ^ 2) * ‖G c‖ₑ ^ 2 ≤ ∫⁻ z in ball c r, ‖G z‖ₑ ^ 2 := by
  set F : ℂ → ℝ≥0∞ := fun z ↦ ‖G z‖ₑ ^ 2 with hF
  have hFm : Measurable F := (hm.enorm).pow_const 2
  set f : ℂ → ℝ≥0∞ := fun w ↦ (ball c r).indicator F (c + w) with hf
  have h1 : ∫⁻ z in ball c r, F z = ∫⁻ w, f w := by
    rw [← lintegral_indicator measurableSet_ball]
    exact (lintegral_add_left_eq_self ((ball c r).indicator F) c).symm
  rw [h1, ← Complex.lintegral_comp_polarCoord_symm f]
  -- restrict to the rectangle `(0, r) × (-π, π)`
  have hsub : Ioo (0:ℝ) r ×ˢ Ioo (-Real.pi) Real.pi ⊆ Complex.polarCoord.target := by
    rw [Complex.polarCoord_target]
    exact prod_mono (fun x hx ↦ hx.1) subset_rfl
  have h2 : ∫⁻ p in Ioo (0:ℝ) r ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * F (circleMap c p.1 p.2) ≤
      ∫⁻ p in Complex.polarCoord.target, ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p) := by
    calc ∫⁻ p in Ioo (0:ℝ) r ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * F (circleMap c p.1 p.2)
        = ∫⁻ p in Ioo (0:ℝ) r ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p) := by
          refine setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun p hp ↦ ?_
          have hp1 : 0 < p.1 := hp.1.1
          have : c + Complex.polarCoord.symm p ∈ ball c r := by
            rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_polarCoord_symm,
              abs_of_pos hp1]
            exact hp.1.2
          simp only [hf, smul_eq_mul, Set.indicator_of_mem this, hF, circleMap_eq_polar]
      _ ≤ _ := lintegral_mono_set hsub
  refine le_trans ?_ h2
  have hmeas : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1 * F (circleMap c p.1 p.2) := by
    have : Measurable fun p : ℝ × ℝ ↦ circleMap c p.1 p.2 := by
      unfold circleMap; fun_prop
    exact (ENNReal.measurable_ofReal.comp measurable_fst).mul (hFm.comp this)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hmeas.aemeasurable]
  have hin : ∀ ρ ∈ Ioo (0:ℝ) r, ENNReal.ofReal ρ * (ENNReal.ofReal (2 * Real.pi) * F c) ≤
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal ρ * F (circleMap c ρ θ) := by
    intro ρ hρ
    have hmc : Measurable fun θ : ℝ ↦ F (circleMap c ρ θ) :=
      hFm.comp (by unfold circleMap; fun_prop : Measurable fun θ : ℝ ↦ circleMap c ρ θ)
    rw [lintegral_const_mul _ hmc]
    gcongr
    rw [setLIntegral_congr Ioo_ae_eq_Ioc]
    exact circle_lintegral_ge hρ.1 hρ.2.le hG
  calc ENNReal.ofReal (Real.pi * r ^ 2) * ‖G c‖ₑ ^ 2
      = ∫⁻ ρ in Ioo (0:ℝ) r, ENNReal.ofReal ρ * (ENNReal.ofReal (2 * Real.pi) * F c) := by
        have hFc : F c ≠ ⊤ := ENNReal.pow_ne_top enorm_ne_top
        rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFc),
          lintegral_Ioo_ofReal_id hr, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
    _ ≤ _ := setLIntegral_mono' measurableSet_Ioo hin

open Classical in
theorem area_ge {G : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (closedBall c r)) :
    ENNReal.ofReal (Real.pi * r ^ 2) * ‖G c‖ₑ ^ 2 ≤ ∫⁻ z in ball c r, ‖G z‖ₑ ^ 2 := by
  set G' : ℂ → ℂ := (closedBall c r).piecewise G 0 with hG'
  have hm : Measurable G' :=
    hG.continuousOn.measurable_piecewise continuousOn_const isClosed_closedBall.measurableSet
  have hG'd : DifferentiableOn ℂ G' (closedBall c r) :=
    hG.congr fun z hz ↦ Set.piecewise_eq_of_mem _ _ _ hz
  have h := area_ge_of_measurable hm hr hG'd
  have hc : G' c = G c := Set.piecewise_eq_of_mem _ _ _ (mem_closedBall_self hr.le)
  rw [hc] at h
  refine h.trans (le_of_eq (setLIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_))
  simp only [hG', Set.piecewise_eq_of_mem _ _ _ (ball_subset_closedBall hz)]

/-- Tonelli on `ℂ ≃ ℝ × ℝ`: integral over a horizontal strip. -/
theorem lintegral_strip {g : ℂ → ℝ≥0∞} (hg : Measurable g) {T : Set ℝ} (hT : MeasurableSet T) :
    ∫⁻ z in {z : ℂ | z.im ∈ T}, g z = ∫⁻ s in T, ∫⁻ x : ℝ, g ((x : ℂ) + (s : ℂ) * I) := by
  have hS : MeasurableSet {z : ℂ | z.im ∈ T} := Complex.measurable_im hT
  rw [← lintegral_indicator hS]
  have h1 : ∫⁻ z, ({z : ℂ | z.im ∈ T}).indicator g z =
      ∫⁻ p : ℝ × ℝ, ({z : ℂ | z.im ∈ T}).indicator g ((p.1 : ℂ) + (p.2 : ℂ) * I) := by
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
    refine lintegral_congr fun a ↦ ?_
    have : Complex.measurableEquivRealProd.symm a = (a.1 : ℂ) + (a.2 : ℂ) * I := by
      apply Complex.ext <;> simp [Complex.measurableEquivRealProd]
    rw [this]
  rw [h1, Measure.volume_eq_prod, lintegral_prod_symm]
  · rw [← lintegral_indicator hT]
    refine lintegral_congr fun s ↦ ?_
    by_cases hs : s ∈ T
    · rw [Set.indicator_of_mem hs]
      refine lintegral_congr fun x ↦ ?_
      simp [Set.indicator, hs]
    · rw [Set.indicator_of_notMem hs]
      simp [Set.indicator, hs]
  · exact ((hg.indicator hS).comp (by fun_prop : Measurable fun p : ℝ × ℝ ↦ (p.1 : ℂ) + (p.2 : ℂ) * I)).aemeasurable

end FF
