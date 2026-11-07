import FourierFrames.Cited.PaleyWiener.L2Fourier
import TauCeti.Analysis.Fourier.L2Multiplier

/-!
# The regularized conjugate Poisson operator

The multiplier is `-i sign(ξ) exp(-2π y |ξ|)`. With Mathlib's Fourier normalization
its inverse transform is `t / (π (t² + y²))`. See `blueprint/P5_HilbertL2.md`.
-/

open MeasureTheory Set Complex Filter Topology FourierTransform ContinuousLinearMap
open scoped ENNReal NNReal FourierTransform ComplexConjugate SchwartzMap

noncomputable section
namespace FF.Pavlov

abbrev C2 := Lp ℂ 2 (volume : Measure ℝ)

def conjugatePoissonKernel (y t : ℝ) : ℝ :=
  t / (Real.pi * (t ^ 2 + y ^ 2))

def conjugatePoissonSymbol (y ξ : ℝ) : ℂ :=
  if ξ < 0 then Complex.I * (Real.exp (-(2 * Real.pi * y * |ξ|)) : ℂ)
  else if 0 < ξ then -Complex.I * (Real.exp (-(2 * Real.pi * y * |ξ|)) : ℂ)
  else 0

lemma conjugatePoissonSymbol_eq (y ξ : ℝ) :
    conjugatePoissonSymbol y ξ = -I * (Real.sign ξ : ℂ) *
      (Real.exp (-(2 * Real.pi * y * |ξ|)) : ℂ) := by
  rcases lt_trichotomy ξ 0 with h | rfl | h
  · simp [conjugatePoissonSymbol, h, Real.sign_of_neg h]
  · simp [conjugatePoissonSymbol]
  · simp [conjugatePoissonSymbol, h, h.not_gt, Real.sign_of_pos h]

lemma conjugatePoissonSymbol_measurable (y : ℝ) :
    Measurable (conjugatePoissonSymbol y) := by
  unfold conjugatePoissonSymbol
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const)
  · fun_prop
  · apply Measurable.ite (measurableSet_lt measurable_const measurable_id) <;> fun_prop

lemma conjugatePoissonSymbol_norm_le_exp (y ξ : ℝ) :
    ‖conjugatePoissonSymbol y ξ‖ ≤ Real.exp (-(2 * Real.pi * y * |ξ|)) := by
  unfold conjugatePoissonSymbol
  split_ifs <;> simp [Complex.norm_exp, (Real.exp_pos _).le]

lemma conjugatePoissonSymbol_norm_le {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    ‖conjugatePoissonSymbol y ξ‖ ≤ 1 := by
  refine (conjugatePoissonSymbol_norm_le_exp y ξ).trans ?_
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))

private lemma integrable_exp_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ Real.exp (-(a * |x|))) := by
  have hn : IntegrableOn (fun x : ℝ ↦ Real.exp (-(a * |x|))) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic ha 0).congr_fun _ measurableSet_Iic
    intro x hx
    dsimp
    rw [abs_of_nonpos (mem_Iic.mp hx)]
    congr 1
    ring
  have hp : IntegrableOn (fun x : ℝ ↦ Real.exp (-(a * |x|))) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).congr_fun _ measurableSet_Ioi
    intro x hx
    dsimp
    rw [abs_of_pos (mem_Ioi.mp hx)]
    congr 1
    ring
  simpa only [Iic_union_Ioi, integrableOn_univ] using hn.union hp


lemma conjugatePoissonSymbol_integrable {y : ℝ} (hy : 0 < y) :
    Integrable (conjugatePoissonSymbol y) := by
  exact (integrable_exp_abs (by positivity : 0 < 2 * Real.pi * y)).mono'
    (conjugatePoissonSymbol_measurable y).aestronglyMeasurable
    (.of_forall (conjugatePoissonSymbol_norm_le_exp y))

lemma conjugatePoissonSymbol_memLp_two {y : ℝ} (hy : 0 < y) :
    MemLp (conjugatePoissonSymbol y) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (conjugatePoissonSymbol_measurable y).aestronglyMeasurable).2
  refine (integrable_exp_abs (by positivity : 0 < 2 * (2 * Real.pi * y))).mono'
    (((conjugatePoissonSymbol_measurable y).norm.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [] with ξ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc ‖conjugatePoissonSymbol y ξ‖ ^ 2 ≤
      Real.exp (-(2 * Real.pi * y * |ξ|)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (conjugatePoissonSymbol_norm_le_exp y ξ) 2
    _ = Real.exp (-(2 * (2 * Real.pi * y) * |ξ|)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

lemma conjugatePoissonSymbol_memLp_top {y : ℝ} (hy : 0 < y) :
    MemLp (conjugatePoissonSymbol y) ∞ volume :=
  memLp_top_of_bound (conjugatePoissonSymbol_measurable y).aestronglyMeasurable 1
    (.of_forall (conjugatePoissonSymbol_norm_le hy))

def conjugatePoissonOperator (y : ℝ) (hy : 0 < y) : C2 →L[ℂ] C2 :=
  MeasureTheory.Lp.fourierMultiplierCLM ℂ
    ((conjugatePoissonSymbol_memLp_top hy).toLp (conjugatePoissonSymbol y))

lemma norm_conjugatePoissonOperator_le {y : ℝ} (hy : 0 < y) :
    ‖conjugatePoissonOperator y hy‖ ≤ 1 := by
  refine (MeasureTheory.Lp.norm_fourierMultiplierCLM_le _).trans ?_
  rw [Lp.norm_toLp]
  have h : eLpNorm (conjugatePoissonSymbol y) ∞ volume ≤ ENNReal.ofReal 1 := by
    rw [eLpNorm_exponent_top (conjugatePoissonSymbol_measurable y).aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (.of_forall (conjugatePoissonSymbol_norm_le hy))
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

lemma norm_conjugatePoissonOperator_apply_le {y : ℝ} (hy : 0 < y) (f : C2) :
    ‖conjugatePoissonOperator y hy f‖ ≤ ‖f‖ := by
  exact ((conjugatePoissonOperator y hy).le_opNorm f).trans
    (by simpa using (mul_le_mul_of_nonneg_right (norm_conjugatePoissonOperator_le hy)
      (norm_nonneg f)))

lemma fourierInv_conjugatePoissonSymbol {y : ℝ} (hy : 0 < y) (x : ℝ) :
    𝓕⁻ (conjugatePoissonSymbol y) x = (conjugatePoissonKernel y x : ℂ) := by
  let a : ℝ := 2 * Real.pi * y
  let b : ℝ := 2 * Real.pi * x
  have ha : 0 < a := by dsimp [a]; positivity
  have hn : ((a : ℂ) + b * I).re = a := by simp
  have hp : (-(a : ℂ) + b * I).re = -a := by simp
  have hkey (c ξ : ℝ) :
      cexp ((b : ℂ) * ξ * I) * (Real.exp (c * ξ) : ℂ) =
        cexp (((c : ℂ) + b * I) * ξ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hneg : (fun ξ : ℝ ↦ cexp ((b : ℂ) * ξ * I) * conjugatePoissonSymbol y ξ)
      =ᵐ[volume.restrict (Iic 0)]
        (fun ξ : ℝ ↦ I * cexp (((a : ℂ) + b * I) * ξ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Iic,
      (volume.ae_ne (0 : ℝ)).filter_mono MeasureTheory.ae_restrict_le] with ξ hξ hne
    have hlt : ξ < 0 := lt_of_le_of_ne (mem_Iic.mp hξ) hne
    simp only [conjugatePoissonSymbol, ite_eq_left hlt, abs_of_neg hlt]
    have he : -(2 * Real.pi * y * -ξ) = a * ξ := by dsimp [a]; ring
    rw [he, mul_left_comm, hkey]
  have hpos : (fun ξ : ℝ ↦ cexp ((b : ℂ) * ξ * I) * conjugatePoissonSymbol y ξ)
      =ᵐ[volume.restrict (Ioi 0)]
        (fun ξ : ℝ ↦ -I * cexp (((-(a : ℂ)) + b * I) * ξ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    have hlt := mem_Ioi.mp hξ
    simp only [conjugatePoissonSymbol, ite_eq_right hlt.not_gt, ite_eq_left hlt, abs_of_pos hlt]
    have he : -(2 * Real.pi * y * ξ) = (-a) * ξ := by dsimp [a]; ring
    rw [he, mul_left_comm, hkey, Complex.ofReal_neg]
  have hint : Integrable (fun ξ : ℝ ↦ cexp ((b : ℂ) * ξ * I) *
      conjugatePoissonSymbol y ξ) :=
    (conjugatePoissonSymbol_integrable hy).bdd_mul (c := 1) (by fun_prop)
      (.of_forall fun ξ ↦ by simp [Complex.norm_exp])
  rw [Real.fourierInv_eq']
  simp only [RCLike.inner_apply, conj_trivial] at *
  change (∫ ξ : ℝ, cexp ((↑(2 * Real.pi * (x * ξ)) * I)) •
    conjugatePoissonSymbol y ξ) = _
  have heq : (fun ξ : ℝ ↦ cexp ((↑(2 * Real.pi * (x * ξ)) * I)) •
      conjugatePoissonSymbol y ξ) =
      (fun ξ : ℝ ↦ cexp ((b : ℂ) * ξ * I) * conjugatePoissonSymbol y ξ) := by
    funext ξ
    rw [smul_eq_mul]
    congr 2
    dsimp [b]
    push_cast
    ring
  rw [heq, ← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn,
    integral_congr_ae hneg, integral_congr_ae hpos,
    integral_const_mul, integral_const_mul,
    integral_exp_mul_complex_Iic (by rw [hn]; exact ha),
    integral_exp_mul_complex_Ioi (by rw [hp]; linarith)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_div]
  have hcalc : I / ((a : ℂ) + b * I) + I / (-(a : ℂ) + b * I) =
      ((2 * b / (a ^ 2 + b ^ 2) : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
      simp [Complex.div_re, Complex.normSq_apply]
      ring
    · rw [Complex.ofReal_im]
      simp [Complex.div_im, Complex.normSq_apply]
      ring
  simp only [neg_div, neg_mul_neg, mul_one_div]
  change I / ((a : ℂ) + b * I) + I / (-(a : ℂ) + b * I) = _
  rw [hcalc]
  congr 1
  unfold conjugatePoissonKernel
  dsimp [a, b]
  field_simp
  ring

lemma conjugatePoissonKernel_memLp_two {y : ℝ} (hy : 0 < y) :
    MemLp (fun t ↦ (conjugatePoissonKernel y t : ℂ)) 2 volume := by
  have h := PW1.F2_symm_toLp_ae_eq (conjugatePoissonSymbol_integrable hy)
    (conjugatePoissonSymbol_memLp_two hy)
  have hm : MemLp (PW1.F2.symm
      ((conjugatePoissonSymbol_memLp_two hy).toLp (conjugatePoissonSymbol y)) : ℝ → ℂ) 2 volume :=
    Lp.memLp _
  exact (memLp_congr_ae (h.trans (.of_forall
    (fourierInv_conjugatePoissonSymbol hy)))).mp hm

lemma conjugatePoissonKernel_mul_integrable {y : ℝ} (hy : 0 < y)
    (f : C2) (x : ℝ) :
    Integrable (fun t ↦ (conjugatePoissonKernel y (x-t) : ℂ) * f t) := by
  exact ((conjugatePoissonKernel_memLp_two hy).comp_measurePreserving
    (volume.measurePreserving_sub_left x)).integrable_mul (Lp.memLp f)

private lemma fourier_modulated_conjugatePoissonSymbol {y : ℝ} (hy : 0 < y) (x t : ℝ) :
    𝓕 (fun ξ : ℝ ↦ cexp ((↑(2 * Real.pi * (x * ξ))) * I) *
      conjugatePoissonSymbol y ξ) t = (conjugatePoissonKernel y (x-t) : ℂ) := by
  rw [← fourierInv_conjugatePoissonSymbol hy]
  simp only [Real.fourier_eq', Real.fourierInv_eq', RCLike.inner_apply, conj_trivial,
    smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma fourierInv_symbol_mul_fourier {y : ℝ} (hy : 0 < y)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    𝓕⁻ (fun ξ ↦ conjugatePoissonSymbol y ξ * 𝓕 f ξ) x =
      ∫ t, (conjugatePoissonKernel y (x-t) : ℂ) * f t := by
  let ψ : ℝ → ℂ := fun ξ ↦ cexp ((↑(2 * Real.pi * (x * ξ))) * I) *
    conjugatePoissonSymbol y ξ
  have hψ : Integrable ψ :=
    (conjugatePoissonSymbol_integrable hy).bdd_mul (c := 1) (by fun_prop)
      (.of_forall fun ξ ↦ by simp [Complex.norm_exp])
  calc
    _ = ∫ ξ, (𝓕 f ξ) • ψ ξ := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [ψ, RCLike.inner_apply, conj_trivial, smul_eq_mul]
      ring
    _ = ∫ t, f t • 𝓕 ψ t := PW1.integral_fourier_smul hf hψ
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [show 𝓕 ψ t = (conjugatePoissonKernel y (x-t) : ℂ) from
        fourier_modulated_conjugatePoissonSymbol hy x t, smul_eq_mul, mul_comm]

lemma conjugatePoissonOperator_eq_integral_of_integrable {y : ℝ} (hy : 0 < y)
    (f : C2) (hf : Integrable (f : ℝ → ℂ)) :
    (conjugatePoissonOperator y hy f : ℝ → ℂ) =ᵐ[volume]
      fun x ↦ ∫ t, (conjugatePoissonKernel y (x-t) : ℂ) * f t := by
  have hff : (PW1.F2 f : ℝ → ℂ) =ᵐ[volume] 𝓕 (f : ℝ → ℂ) := by
    simpa only [Lp.toLp_coeFn] using PW1.F2_toLp_ae_eq hf (Lp.memLp f)
  have hF : MemLp (𝓕 (f : ℝ → ℂ)) 2 volume :=
    (memLp_congr_ae hff).mp (Lp.memLp (PW1.F2 f))
  have hprod : MemLp (fun ξ ↦ conjugatePoissonSymbol y ξ * 𝓕 (f : ℝ → ℂ) ξ) 2 volume :=
    (conjugatePoissonSymbol_memLp_top hy).mul hF
  have hi : Integrable (fun ξ ↦ conjugatePoissonSymbol y ξ * 𝓕 (f : ℝ → ℂ) ξ) :=
    (conjugatePoissonSymbol_memLp_two hy).integrable_mul hF
  have hmul : ((conjugatePoissonSymbol_memLp_top hy).toLp (conjugatePoissonSymbol y) •
      𝓕 f : C2) = hprod.toLp _ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_lpSMul (r := 2)
      ((conjugatePoissonSymbol_memLp_top hy).toLp (conjugatePoissonSymbol y)) (𝓕 f),
      (conjugatePoissonSymbol_memLp_top hy).coeFn_toLp, hprod.coeFn_toLp, hff]
      with ξ h₁ h₂ h₃ h₄
    rw [h₁, h₃]
    change (((conjugatePoissonSymbol_memLp_top hy).toLp
      (conjugatePoissonSymbol y) : ℝ → ℂ) ξ) * (PW1.F2 f : ℝ → ℂ) ξ = _
    rw [h₂, h₄]
  have hop : conjugatePoissonOperator y hy f = PW1.F2.symm (hprod.toLp _) := by
    unfold conjugatePoissonOperator
    rw [Lp.fourierMultiplierCLM_apply, hmul]
    rfl
  rw [hop]
  exact (PW1.F2_symm_toLp_ae_eq hi hprod).trans
    (.of_forall (fourierInv_symbol_mul_fourier hy hf))

lemma conjugatePoissonOperator_eq_integral {y : ℝ} (hy : 0 < y) (f : C2) :
    (conjugatePoissonOperator y hy f : ℝ → ℂ) =ᵐ[volume]
      fun x ↦ ∫ t, (conjugatePoissonKernel y (x-t) : ℂ) * f t := by
  have hK : ∀ x : ℝ, MemLp (fun t ↦ (conjugatePoissonKernel y (x-t) : ℂ)) 2 volume :=
    fun x ↦ (conjugatePoissonKernel_memLp_two hy).comp_measurePreserving
      (volume.measurePreserving_sub_left x)
  obtain ⟨u, hu⟩ : ∃ u : ℕ → 𝓢(ℝ, ℂ),
      Tendsto (fun n ↦ (u n).toLp 2) atTop (𝓝 f) := by
    have := (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) (μ := volume)
      ENNReal.ofNat_ne_top).closure_range ▸ Set.mem_univ f
    obtain ⟨v, hv, hvf⟩ := mem_closure_iff_seq_limit.1 this
    choose u hu using hv
    refine ⟨u, ?_⟩
    convert hvf using 2 with n
    exact hu n
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp
    (((conjugatePoissonOperator y hy).continuous.tendsto f).comp hu)).exists_seq_tendsto_ae
  have hsch : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n : ℕ,
      conjugatePoissonOperator y hy ((u n).toLp 2) x =
        ∫ t, (conjugatePoissonKernel y (x-t) : ℂ) * ((u n).toLp 2 : ℝ → ℂ) t := by
    refine ae_all_iff.2 fun n ↦ conjugatePoissonOperator_eq_integral_of_integrable hy _ ?_
    exact (u n).integrable.congr ((u n).coeFn_toLp 2).symm
  filter_upwards [hae, hsch] with x hx hxs
  refine tendsto_nhds_unique hx ?_
  have hpair : ∀ g : C2, (lsmul ℂ ℂ).lpPairing volume 2 2
      ((hK x).toLp _) g = ∫ t, (conjugatePoissonKernel y (x-t) : ℂ) * g t := fun g ↦ by
    rw [lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [(hK x).coeFn_toLp] with t ht
    simp only [lsmul_apply, ht, smul_eq_mul]
  simp only [Function.comp_apply, hxs, ← hpair]
  exact ((((lsmul ℂ ℂ).lpPairing volume 2 2 ((hK x).toLp _)).continuous.tendsto f).comp hu).comp
    hns.tendsto_atTop

end FF.Pavlov
