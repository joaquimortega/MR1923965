import FourierFrames.Cited.Pavlov.BMOSecondMoment
import FourierFrames.Cited.Pavlov.ConjugatePoisson

/-!
# The near part of the conjugate Poisson BMO estimate

The local John--Nirenberg square bound constructs the cutoff in `L²`.
The conjugate Poisson multiplier is a contraction, and interval Hölder gives
the required uniform average estimate. See `blueprint/P5_PoissonBMO.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace
noncomputable section
namespace FF.Pavlov

/-- The complex-valued cutoff of the oscillation around an interval mean. -/
def centeredCutoff (u : ℝ → ℝ) (a b : ℝ) : ℝ → ℂ :=
  (Icc a b).indicator (fun t ↦ ((u t-intervalMean u a b : ℝ) : ℂ))

theorem centeredCutoff_memLp_two {u : ℝ → ℝ} (hu : LocallyIntegrable u)
    {a b : ℝ} (hs : IntegrableOn (fun t ↦ (u t-intervalMean u a b)^2) (Icc a b)) :
    MemLp (centeredCutoff u a b) 2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).mpr
  apply MemLp.ofReal
  have hm : AEStronglyMeasurable (fun t ↦ u t-intervalMean u a b)
      (volume.restrict (Icc a b)) := ((hu.integrableOn_isCompact isCompact_Icc).sub
    (integrableOn_const isCompact_Icc.measure_lt_top.ne (C := intervalMean u a b))).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [IntegrableOn, Real.norm_eq_abs, sq_abs] using hs

/-- The ordinary square integral agrees with the Hilbert space norm. -/
theorem c2_norm_sq_eq_integral (f : C2) : ‖f‖^2 = ∫ t : ℝ, ‖f t‖^2 := by
  have h := L2.inner_def (𝕜 := ℂ) f f
  simp only [inner_self_eq_norm_sq_to_K] at h
  simp_rw [← RCLike.ofReal_pow, RCLike.ofReal_eq_complex_ofReal] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- The cutoff defines an `L²` class with exactly the local square integral as norm. -/
theorem exists_centeredCutoff_L2 {u : ℝ → ℝ} (hu : LocallyIntegrable u)
    {a b : ℝ} (hab : a < b)
    (hs : IntegrableOn (fun t ↦ (u t-intervalMean u a b)^2) (Icc a b)) :
    ∃ f : C2, (f : ℝ → ℂ) =ᵐ[volume] centeredCutoff u a b ∧
      ‖f‖^2 = ∫ t in a..b, (u t-intervalMean u a b)^2 := by
  let hm := centeredCutoff_memLp_two hu hs
  refine ⟨hm.toLp _, hm.coeFn_toLp, ?_⟩
  rw [c2_norm_sq_eq_integral]
  have he : (∫ t : ℝ, ‖(hm.toLp (centeredCutoff u a b)) t‖^2) =
      ∫ t : ℝ, ‖centeredCutoff u a b t‖^2 := by
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with t ht
    rw [ht]
  rw [he]
  have hp : (fun t ↦ ‖centeredCutoff u a b t‖^2) =
      (Icc a b).indicator (fun t ↦ (u t-intervalMean u a b)^2) := by
    ext t
    by_cases ht : t ∈ Icc a b
    · simp only [centeredCutoff, indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · simp [centeredCutoff, ht]
  rw [hp, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab.le]

/-- Interval Hölder bounds the average size of an `L²` function by its global norm. -/
theorem integral_norm_C2_le (f : C2) {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, ‖f t‖) ≤ Real.sqrt (b-a) * ‖f‖ := by
  have hm : MemLp (fun t : ℝ ↦ ‖f t‖) 2 (volume.restrict (Ioc a b)) :=
    ((Lp.memLp f).restrict _).norm
  have h1 : MemLp (fun _ : ℝ ↦ (1:ℝ)) 2 (volume.restrict (Ioc a b)) := memLp_const 1
  have hh := integral_mul_norm_le_Lp_mul_Lq (f := fun t : ℝ ↦ ‖f t‖)
    (g := fun _ : ℝ ↦ (1:ℝ)) Real.HolderConjugate.two_two
    (by simpa only [ENNReal.ofReal_ofNat] using hm)
    (by simpa only [ENNReal.ofReal_ofNat] using h1)
  have hsq : (∫ t in Ioc a b, ‖f t‖^2) ≤ ‖f‖^2 := by
    rw [c2_norm_sq_eq_integral]
    exact integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun _ ↦ sq_nonneg _) ((Lp.memLp f).integrable_norm_pow (by norm_num))
  simp only [Real.norm_of_nonneg (norm_nonneg _), Real.norm_eq_abs,
    abs_of_pos (show (0:ℝ)<1 by norm_num), mul_one, Real.rpow_two,
    one_pow, integral_const, smul_eq_mul, mul_one,
    measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_pos.mpr hab).le] at hh
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  rw [intervalIntegral.integral_of_le hab.le]
  exact hh.trans (by
    rw [mul_comm]
    gcongr
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg f)] using Real.sqrt_le_sqrt hsq)

/-- The real near-field convolution over the doubled interval. -/
def nearConjugatePoisson (u : ℝ → ℝ) (y c r x : ℝ) : ℝ :=
  ∫ t in Icc (c-2*r) (c+2*r),
    conjugatePoissonKernel y (x-t) * (u t-intervalMean u (c-2*r) (c+2*r))

/-- The unscaled near-field kernel is integrable on the cutoff interval. -/
theorem nearConjugatePoisson_fraction_integrable {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {y : ℝ} (hy : 0 < y) (c r x : ℝ) :
    IntegrableOn (fun t ↦ ((x-t)/((x-t)^2+y^2)) *
      (u t-intervalMean u (c-2*r) (c+2*r))) (Icc (c-2*r) (c+2*r)) := by
  have hi : IntegrableOn (fun t ↦ u t-intervalMean u (c-2*r) (c+2*r))
      (Icc (c-2*r) (c+2*r)) :=
    (hu.integrableOn_isCompact isCompact_Icc).sub
      (integrableOn_const isCompact_Icc.measure_lt_top.ne)
  have hc : Continuous (fun t : ℝ ↦ (x-t)/((x-t)^2+y^2)) := by
    apply (continuous_const.sub continuous_id).div
      (((continuous_const.sub continuous_id).pow 2).add continuous_const)
    intro t
    have hp : 0 < (x-t)^2+y^2 := by positivity
    exact hp.ne'
  exact IntegrableOn.continuousOn_mul hc.continuousOn hi isCompact_Icc

/-- Convert the normalized kernel to the fraction used in the far-field identity. -/
theorem nearConjugatePoisson_eq_fraction (u : ℝ → ℝ) (y c r x : ℝ) :
    nearConjugatePoisson u y c r x = Real.pi⁻¹ *
      ∫ t in Icc (c-2*r) (c+2*r), ((x-t)/((x-t)^2+y^2)) *
        (u t-intervalMean u (c-2*r) (c+2*r)) := by
  rw [nearConjugatePoisson, ← integral_const_mul]
  congr 1
  ext t
  simp only [conjugatePoissonKernel, div_eq_mul_inv, mul_inv_rev]
  ring

theorem conjugatePoisson_centeredCutoff_eq {u : ℝ → ℝ} {c r y : ℝ}
    (hy : 0 < y) (f : C2)
    (hf : (f : ℝ → ℂ) =ᵐ[volume] centeredCutoff u (c-2*r) (c+2*r)) :
    (conjugatePoissonOperator y hy f : ℝ → ℂ) =ᵐ[volume]
      (fun x ↦ (nearConjugatePoisson u y c r x : ℂ)) := by
  refine (conjugatePoissonOperator_eq_integral hy f).trans ?_
  apply Eventually.of_forall
  intro x
  calc
    (∫ t : ℝ, (conjugatePoissonKernel y (x-t) : ℂ) * f t) =
        ∫ t : ℝ, (conjugatePoissonKernel y (x-t) : ℂ) *
          centeredCutoff u (c-2*r) (c+2*r) t := by
      apply integral_congr_ae
      filter_upwards [hf] with t ht
      rw [ht]
    _ = ∫ t : ℝ, (Icc (c-2*r) (c+2*r)).indicator
        (fun t ↦ ((conjugatePoissonKernel y (x-t) *
          (u t-intervalMean u (c-2*r) (c+2*r)) : ℝ) : ℂ)) t := by
      congr 1
      ext t
      by_cases ht : t ∈ Icc (c-2*r) (c+2*r)
      · simp only [centeredCutoff, indicator_of_mem ht, Complex.ofReal_mul]
      · simp only [centeredCutoff, indicator_of_notMem ht, mul_zero]
    _ = _ := by
      rw [integral_indicator measurableSet_Icc, integral_complex_ofReal]
      rfl

/-- Near-field control from an explicit local square estimate. -/
theorem nearConjugatePoisson_bound {u : ℝ → ℝ} (hu : LocallyIntegrable u)
    {C M c r y : ℝ} (hC : 0 < C) (hM : 0 < M) (hr : 0 < r) (hy : 0 < y)
    (hs : IntegrableOn
      (fun t ↦ (u t-intervalMean u (c-2*r) (c+2*r))^2)
      (Icc (c-2*r) (c+2*r)))
    (hb : (∫ t in (c-2*r)..(c+2*r),
      (u t-intervalMean u (c-2*r) (c+2*r))^2) ≤ C*M^2*(4*r)) :
    IntegrableOn (nearConjugatePoisson u y c r) (Icc (c-r) (c+r)) ∧
      (2*r)⁻¹ * ∫ x in (c-r)..(c+r), |nearConjugatePoisson u y c r x| ≤
        Real.sqrt (2*C)*M := by
  obtain ⟨f, hf, hnorm⟩ := exists_centeredCutoff_L2 hu (by linarith : c-2*r<c+2*r) hs
  let F := conjugatePoissonOperator y hy f
  have he : (F : ℝ → ℂ) =ᵐ[volume]
      (fun x ↦ (nearConjugatePoisson u y c r x : ℂ)) :=
    conjugatePoisson_centeredCutoff_eq hy f hf
  have hi : IntegrableOn (nearConjugatePoisson u y c r) (Icc (c-r) (c+r)) := by
    have hi' := (((Lp.memLp F).re).restrict (Icc (c-r) (c+r))).integrable (by norm_num)
    apply hi'.congr
    filter_upwards [ae_restrict_of_ae he] with x hx
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using congrArg Complex.re hx
  refine ⟨hi, ?_⟩
  have heInt : (∫ x in (c-r)..(c+r), |nearConjugatePoisson u y c r x|) =
      ∫ x in (c-r)..(c+r), ‖F x‖ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [he] with x hx _
    rw [hx, Complex.norm_real, Real.norm_eq_abs]
  rw [heInt]
  have h₁ := integral_norm_C2_le F (by linarith : c-r<c+r)
  have h₂ := norm_conjugatePoissonOperator_apply_le hy f
  change ‖F‖ ≤ ‖f‖ at h₂
  have hlen : (c+r)-(c-r) = 2*r := by ring
  rw [hlen] at h₁
  have h₃ : (∫ x in (c-r)..(c+r), ‖F x‖) ≤ Real.sqrt (2*r)*‖f‖ :=
    h₁.trans (mul_le_mul_of_nonneg_left h₂ (Real.sqrt_nonneg _))
  have h₄ : ‖f‖^2 ≤ C*M^2*(4*r) := hnorm ▸ hb
  have h₅ := mul_le_mul_of_nonneg_left h₄ (show 0 ≤ 2*r by positivity)
  have hsq : (∫ x in (c-r)..(c+r), ‖F x‖)^2 ≤
      (2*r)*(C*M^2*(4*r)) := by
    have hp : 0 ≤ (∫ x in (c-r)..(c+r), ‖F x‖) :=
      intervalIntegral.integral_nonneg (by linarith : c-r≤c+r)
        (fun x _ ↦ norm_nonneg (F x))
    have hs' := sq_le_sq₀ hp (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f)) |>.mpr h₃
    rw [mul_pow, Real.sq_sqrt (show 0 ≤ 2*r by positivity)] at hs'
    exact hs'.trans h₅
  have hgoal : (∫ x in (c-r)..(c+r), ‖F x‖) ≤ (2*r)*(Real.sqrt (2*C)*M) := by
    have heq : ((2*r)*(Real.sqrt (2*C)*M))^2 = (2*r)*(C*M^2*(4*r)) := by
      simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2*C)]
      ring
    rw [← heq] at hsq
    exact le_of_sq_le_sq hsq (by positivity)
  exact (inv_mul_le_iff₀ (by positivity : 0<2*r)).mpr hgoal

/-- A universal near-field BMO bound follows from John--Nirenberg. -/
theorem bmo_near_conjugatePoisson_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ), LocallyIntegrable u →
      ∀ M : ℝ, 0 < M →
      (∀ a b : ℝ, a < b → meanOsc u a b ≤ M) →
      ∀ y : ℝ, 0 < y → ∀ c r : ℝ, 0 < r →
        IntegrableOn (nearConjugatePoisson u y c r) (Icc (c-r) (c+r)) ∧
        (2*r)⁻¹ * ∫ x in (c-r)..(c+r), |nearConjugatePoisson u y c r x| ≤ C*M := by
  obtain ⟨C, hC, hb⟩ := bmo_local_square_bound
  refine ⟨Real.sqrt (2*C), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro u hu M hM hosc y hy c r hr
  obtain ⟨hs, hsbound⟩ := hb u hu M hM hosc (c-2*r) (c+2*r) (by linarith)
  apply nearConjugatePoisson_bound hu hC hM hr hy hs
  convert hsbound using 1
  ring

end FF.Pavlov
