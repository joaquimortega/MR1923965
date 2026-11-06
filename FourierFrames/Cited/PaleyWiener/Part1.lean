import FourierFrames.Defs

/-!
# P1 — Paley–Wiener, part (1): the transform of an `L²(-π, π)` function

See `blueprint/P1_PaleyWiener.md`, §1.  For `g ∈ L²(-π, π)` the function
`f(z) = ∫_{-π}^{π} g(t) e^{izt} dt` is entire, of exponential type `≤ π`, square integrable on `ℝ`,
and `∫_ℝ |f|² = 2π ∫ |g|²`.  The norm identity is proved by Parseval for Fourier series on
`[-π, π]` applied to `g(t) e^{ixt}` for *every* `x`, followed by integration of
`∑_k |f(x + k)|²` over `x ∈ [0, 1)` (no Fourier transform on `ℝ` is needed).
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate Interval

noncomputable section

namespace FF.PW1

/-- `g ∈ L²(-π, π)`. -/
abbrev L2pi (g : ℝ → ℂ) : Prop :=
  MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))

/-- The transform `z ↦ ∫_{-π}^{π} g(t) e^{izt} dt`. -/
def ft (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)

/-! ### 1.1 Entire, exponential type -/

theorem L2pi.integrable {g : ℝ → ℂ} (hg : L2pi g) :
    IntegrableOn g (Ioc (-Real.pi) Real.pi) :=
  MemLp.integrable (by norm_num) hg

theorem norm_cexp_le (z : ℂ) {t : ℝ} (ht : |t| ≤ Real.pi) :
    ‖Complex.exp (I * z * t)‖ ≤ Real.exp (Real.pi * ‖z‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have h1 : (I * z * t).re = -z.im * t := by simp
  rw [h1]
  have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  calc -z.im * t ≤ |(-z.im * t)| := le_abs_self _
    _ = |z.im| * |t| := by rw [abs_mul, abs_neg]
    _ ≤ ‖z‖ * Real.pi := mul_le_mul h2 ht (abs_nonneg _) (norm_nonneg _)
    _ = _ := by ring

theorem abs_le_pi_of_mem_uIoc {t : ℝ} (ht : t ∈ Ι (-Real.pi) Real.pi) : |t| ≤ Real.pi := by
  rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at ht
  exact abs_le.2 ⟨ht.1.le, ht.2⟩

theorem abs_le_pi_of_mem_Ioc {t : ℝ} (ht : t ∈ Ioc (-Real.pi) Real.pi) : |t| ≤ Real.pi :=
  abs_le.2 ⟨ht.1.le, ht.2⟩

theorem aesm_mul_cexp {g : ℝ → ℂ} (hg : L2pi g) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ ↦ g t * Complex.exp (I * z * t))
      (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
  (MemLp.aestronglyMeasurable hg).mul (by fun_prop)

theorem differentiable_ft {g : ℝ → ℂ} (hg : L2pi g) : Differentiable ℂ (ft g) := by
  intro z₀
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ ↦ g t * Complex.exp (I * z * t))
      (volume.restrict (Ι (-Real.pi) Real.pi)) := fun z => by
    rw [Set.uIoc_of_le hπ]; exact aesm_mul_cexp hg z
  have hbint : IntervalIntegrable (fun t : ℝ ↦ ‖g t‖ * Real.pi * Real.exp (Real.pi * (‖z₀‖ + 1)))
      volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hπ]
    exact ((L2pi.integrable hg).norm.mul_const _).mul_const _
  have hF : IntervalIntegrable (fun t : ℝ ↦ g t * Complex.exp (I * z₀ * t)) volume
      (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hπ]
    refine Integrable.mono' ((L2pi.integrable hg).norm.mul_const (Real.exp (Real.pi * ‖z₀‖)))
      (aesm_mul_cexp hg z₀) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht ↦ ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cexp_le z₀ (abs_le_pi_of_mem_Ioc ht)) (norm_nonneg _)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := -Real.pi) (b := Real.pi)
    (F := fun (z : ℂ) (t : ℝ) ↦ g t * Complex.exp (I * z * t))
    (F' := fun (z : ℂ) (t : ℝ) ↦ g t * (I * t) * Complex.exp (I * z * t))
    (x₀ := z₀) (s := Metric.ball z₀ 1) (bound := fun t ↦ ‖g t‖ * Real.pi * Real.exp (Real.pi * (‖z₀‖ + 1)))
    (Metric.ball_mem_nhds _ one_pos) (Eventually.of_forall hmeas) hF
    (by
      have := (hmeas z₀)
      refine AEStronglyMeasurable.congr (this.mul (by fun_prop : AEStronglyMeasurable (fun t : ℝ ↦ (I * (t : ℂ))) _)) ?_
      exact Eventually.of_forall fun t ↦ by simp only [Pi.mul_apply]; ring)
    (by
      refine Eventually.of_forall fun t ht z hz ↦ ?_
      have htπ := abs_le_pi_of_mem_uIoc ht
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have := Metric.mem_ball.1 hz
        rw [dist_eq_norm] at this
        calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ ≤ _ := by linarith
      have h1 := norm_cexp_le z htπ
      have h2 : Real.exp (Real.pi * ‖z‖) ≤ Real.exp (Real.pi * (‖z₀‖ + 1)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz' Real.pi_pos.le)
      calc ‖g t‖ * |t| * ‖Complex.exp (I * z * t)‖
          ≤ ‖g t‖ * Real.pi * Real.exp (Real.pi * (‖z₀‖ + 1)) := by
            gcongr
            exact h1.trans h2)
    hbint
    (by
      refine Eventually.of_forall fun t _ z _ ↦ ?_
      have h1 : HasDerivAt (fun z : ℂ ↦ I * z * (t : ℂ)) (I * 1 * (t : ℂ)) z := by
        have := ((hasDerivAt_id z).const_mul I).mul_const (t : ℂ)
        simpa using this
      have := (h1.cexp).const_mul (g t)
      convert this using 1
      simp only [mul_one]; ring)
  exact key.2.differentiableAt

theorem norm_ft_le {g : ℝ → ℂ} (hg : L2pi g) (z : ℂ) :
    ‖ft g z‖ ≤ (∫ t in Ioc (-Real.pi) Real.pi, ‖g t‖) * Real.exp (Real.pi * ‖z‖) := by
  unfold ft
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  calc _ ≤ ∫ t in Ioc (-Real.pi) Real.pi, ‖g t‖ * Real.exp (Real.pi * ‖z‖) := by
        refine norm_integral_le_of_norm_le ((L2pi.integrable hg).norm.mul_const _) ?_
        rw [ae_restrict_iff' measurableSet_Ioc]
        refine Eventually.of_forall fun t ht ↦ ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_cexp_le z (abs_le_pi_of_mem_Ioc ht)) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

theorem isExpTypeLE_ft {g : ℝ → ℂ} (hg : L2pi g) : IsExpTypeLE Real.pi (ft g) := by
  intro ε hε
  refine ⟨∫ t in Ioc (-Real.pi) Real.pi, ‖g t‖, fun z ↦ (norm_ft_le hg z).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (integral_nonneg fun _ ↦ norm_nonneg _)
  nlinarith [norm_nonneg z]

/-! ### 1.2 The norm identity via Parseval on `[-π, π]` -/

theorem norm_cexp_real (x t : ℝ) : ‖Complex.exp (I * x * t)‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- Multiplying by `e^{ixt}` (`x` real) preserves `L²(-π, π)`. -/
theorem L2pi.mul_cexp {g : ℝ → ℂ} (hg : L2pi g) (x : ℝ) :
    L2pi (fun t ↦ g t * Complex.exp (I * x * t)) :=
  MemLp.congr_norm (f := g) hg (aesm_mul_cexp hg x)
    (Eventually.of_forall fun t ↦ by rw [norm_mul, norm_cexp_real, mul_one])

/-- `f(x + k) = ∫ (g e^{ix·}) e^{ik·}`. -/
theorem ft_add_intCast {g : ℝ → ℂ} (x : ℝ) (k : ℤ) :
    ft g ((x : ℂ) + k) = ft (fun t ↦ g t * Complex.exp (I * x * t)) k := by
  unfold ft
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only
  rw [mul_assoc (g t) (Complex.exp _), ← Complex.exp_add]
  congr 3
  ring

/-- The Fourier coefficient of `g` on `[-π, π]` (period `2π`) is `(2π)⁻¹ ft g (-n)`. -/
theorem ft_intCast_eq_fourierCoeffOn {g : ℝ → ℂ} (n : ℤ) :
    ft g (n : ℂ) =
      (2 * Real.pi : ℂ) * fourierCoeffOn (by linarith [Real.pi_pos] : -Real.pi < Real.pi) g (-n) := by
  rw [fourierCoeffOn_eq_integral]
  unfold ft
  have h2 : (Real.pi - -Real.pi) = 2 * Real.pi := by ring
  have hne : (2 * Real.pi : ℂ) ≠ 0 := by
    have := Real.pi_pos.ne'
    simp [this]
  have hf : ∀ x : ℝ, fourier (- -n) (x : AddCircle (Real.pi - -Real.pi)) =
      Complex.exp (I * n * x) := by
    intro y
    rw [fourier_coe_apply]
    congr 1
    push_cast
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    field_simp
    ring
  have hI : ∫ (x : ℝ) in -Real.pi..Real.pi, (fourier (- -n)) (x : AddCircle (Real.pi - -Real.pi)) * g x
      = ∫ (t : ℝ) in -Real.pi..Real.pi, g t * Complex.exp (I * n * t) :=
    intervalIntegral.integral_congr fun t _ ↦ by simp only [hf]; ring
  simp only [smul_eq_mul]
  rw [hI]
  rw [Complex.real_smul]
  push_cast
  field_simp
  ring

/-- Parseval for the samples `f(x + k)`, `k ∈ ℤ`, for every real `x`. -/
theorem hasSum_sq_ft_add_intCast {g : ℝ → ℂ} (hg : L2pi g) (x : ℝ) :
    HasSum (fun k : ℤ ↦ ‖ft g ((x : ℂ) + k)‖ ^ 2)
      (2 * Real.pi * ∫ t in (-Real.pi)..Real.pi, ‖g t‖ ^ 2) := by
  have hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have h1 := hasSum_sq_fourierCoeffOn hab (hg.mul_cexp x)
  have h2 := ((Equiv.neg ℤ).hasSum_iff.2 h1).mul_left ((2 * Real.pi) ^ 2)
  have hnorm : ∀ t : ℝ, ‖g t * Complex.exp (I * x * t)‖ = ‖g t‖ := fun t ↦ by
    rw [norm_mul, norm_cexp_real, mul_one]
  simp only [hnorm] at h2
  convert h2 using 1
  · funext k
    rw [ft_add_intCast, ft_intCast_eq_fourierCoeffOn, norm_mul, mul_pow]
    simp [Equiv.neg_apply]
  · rw [smul_eq_mul]
    have : Real.pi ≠ 0 := Real.pi_pos.ne'
    have h3 : Real.pi - -Real.pi = 2 * Real.pi := by ring
    rw [h3]
    field_simp

/-- The same in `ℝ≥0∞`. -/
theorem tsum_enorm_sq_ft_add_intCast {g : ℝ → ℂ} (hg : L2pi g) (x : ℝ) :
    ∑' k : ℤ, ‖ft g ((x : ℂ) + k)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2 := by
  have h := hasSum_sq_ft_add_intCast hg x
  have hnn : ∀ k : ℤ, 0 ≤ ‖ft g ((x : ℂ) + k)‖ ^ 2 := fun k ↦ by positivity
  have h1 := ENNReal.ofReal_tsum_of_nonneg hnn h.summable
  rw [h.tsum_eq] at h1
  have h2 : ∀ k : ℤ, ENNReal.ofReal (‖ft g ((x : ℂ) + k)‖ ^ 2) = ‖ft g ((x : ℂ) + k)‖ₑ ^ 2 :=
    fun k ↦ by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp_rw [h2] at h1
  rw [← h1]
  have hint : Integrable (fun t ↦ ‖g t‖ ^ 2) (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    (memLp_two_iff_integrable_sq_norm (MemLp.aestronglyMeasurable hg)).1 hg
  rw [ENNReal.ofReal_mul (by positivity), intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t ↦ by positivity)]
  congr 1
  refine lintegral_congr fun t ↦ ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Unit-interval decomposition of `∫_ℝ |F|²` for measurable `F`. -/
theorem lintegral_enorm_sq_eq_lintegral_tsum {F : ℝ → ℂ} (hF : Measurable F) :
    ∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 = ∫⁻ x in Ico (0 : ℝ) 1, ∑' k : ℤ, ‖F (x + k)‖ₑ ^ 2 := by
  set G : ℝ → ℝ≥0∞ := fun x ↦ ‖F x‖ₑ ^ 2 with hG
  have hGm : Measurable G := (hF.enorm).pow_const 2
  have h1 : ∫⁻ x : ℝ, G x = ∑' k : ℤ, ∫⁻ x in Ico (k : ℝ) (k + 1), G x := by
    rw [← lintegral_iUnion (fun k ↦ measurableSet_Ico) (pairwise_disjoint_Ico_intCast ℝ)]
    rw [iUnion_Ico_intCast, Measure.restrict_univ]
  have h2 : ∀ k : ℤ, ∫⁻ x in Ico (k : ℝ) (k + 1), G x = ∫⁻ x in Ico (0 : ℝ) 1, G (x + k) := by
    intro k
    have := (measurePreserving_add_right volume (k : ℝ)).setLIntegral_comp_emb
      (measurableEmbedding_addRight (k : ℝ)) G (Ico (0 : ℝ) 1)
    rw [this, Set.image_add_const_Ico, zero_add, add_comm 1 (k : ℝ)]
  simp_rw [h2] at h1
  rw [h1]
  exact (lintegral_tsum (μ := volume.restrict (Ico (0 : ℝ) 1))
    (fun k : ℤ ↦ (hGm.comp (measurable_id.add_const (k : ℝ))).aemeasurable)).symm

theorem pwNormSq_ft {g : ℝ → ℂ} (hg : L2pi g) :
    ∫⁻ x : ℝ, ‖ft g x‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2 := by
  have hc : Continuous (fun x : ℝ ↦ ft g x) :=
    (differentiable_ft hg).continuous.comp Complex.continuous_ofReal
  rw [lintegral_enorm_sq_eq_lintegral_tsum hc.measurable]
  have : ∀ x : ℝ, ∑' k : ℤ, ‖ft g ((x + k : ℝ) : ℂ)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2 := fun x ↦ by
    push_cast
    exact tsum_enorm_sq_ft_add_intCast hg x
  simp_rw [this]
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ]
  simp

theorem memLp_ft_real {g : ℝ → ℂ} (hg : L2pi g) : MemLp (fun x : ℝ ↦ ft g x) 2 := by
  have hc : Continuous (fun x : ℝ ↦ ft g x) :=
    (differentiable_ft hg).continuous.comp Complex.continuous_ofReal
  rw [MemLp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
    hc.aestronglyMeasurable]
  have h := pwNormSq_ft hg
  have hfin : ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2 < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hg
    simpa using this
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  rw [h]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- **Paley–Wiener, part (1)**, in the shape of `FF.PaleyWienerThm`. -/
theorem paleyWiener_part1 : ∀ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) →
      MemPW (fun z ↦ ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)) ∧
      pwNormSq (fun z ↦ ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)) =
        ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2 := by
  intro g hg
  exact ⟨⟨differentiable_ft hg, isExpTypeLE_ft hg, memLp_ft_real hg⟩, pwNormSq_ft hg⟩

end FF.PW1
