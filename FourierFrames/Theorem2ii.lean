import FourierFrames.Defs
import FourierFrames.Lemma3Uniform
import FourierFrames.Theorem2ii.Window
import FourierFrames.Theorem2ii.UOne
import FourierFrames.Theorem2ii.Ramp

/-!
# M09 — Theorem 2 (ii)

See `blueprint/M09_Theorem2ii.md`.  The printed proof (pp. 804–805) is broken (see the section
"Issues in the source" of the blueprint); the proof below is a reconstruction.

Idea.  `Λ(ψ) ∩ (-∞, 0] = ℤ_{≤ 0}`.  If `x ψ'(x) → 0`, then for every `η > 0` and `s > 0` there is
a window `[x₀, x₀ e^s]` far out on which `ψ` stays within `η` of a half integer `n + 1/2`, i.e.
`Λ(ψ)` is within `η` of `ℤ + 1/2` there.  Take the [OS99] Lemma 3 function `F` of the density
`m = 1 + μ`, `μ` = two negative ramps of mass `-1/2` each, on `[a₁, 2a₁]` and `[a₂, 2a₂]`, where
`x₀ ≈ 2 a₁`, `x₀ e^s ≈ a₂`.  Its zeros are `ℤ` on the left, `ℤ + 1/2` between the ramps, and
`ℤ` again after the second ramp, and `|f|² ≃ min(1, a₁/|x|) min(1, a₂/|x|) dist(x, zeros)²`.
Hence `‖f‖² ≳ a₁ log(a₂/a₁)` while `∑_{Λ(ψ)} |f|² ≲ a₁ (1 + η² log(a₂/a₁))`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## The test density and the test function -/

/-- The perturbation `μ = m - 1`: two uniform negative ramps, each of total mass `-1/2`,
on `[a₁, 2a₁]` and `[a₂, 2a₂]`. -/
def rampMu (a₁ a₂ : ℝ) (t : ℝ) : ℝ :=
  -((1 / 2) / a₁) * (Icc a₁ (2 * a₁)).indicator 1 t -
    ((1 / 2) / a₂) * (Icc a₂ (2 * a₂)).indicator 1 t

/-- The density `m = 1 + μ` fed to [OS99] Lemma 3. -/
def dens (a₁ a₂ : ℝ) (t : ℝ) : ℝ :=
  1 + rampMu a₁ a₂ t

/-- The envelope `min(1, a₁/|x|) · min(1, a₂/|x|)`, written without division by `0`. -/
def env (a₁ a₂ x : ℝ) : ℝ :=
  a₁ / max a₁ |x| * (a₂ / max a₂ |x|)

/-- The real potential `W(z) = ∫ μ(t) log|1 - z/t| dt`. -/
def potW (a₁ a₂ : ℝ) (z : ℂ) : ℝ :=
  ∫ t : ℝ, rampMu a₁ a₂ t * Real.log ‖1 - z / t‖

/-- The linear coefficient `κ = ∫ μ(t)/t dt` (`μ` is supported in `[a₁, ∞) ⊂ [1, ∞)`). -/
def kappaMu (a₁ a₂ : ℝ) : ℝ :=
  ∫ t : ℝ, rampMu a₁ a₂ t / t

/-- `G(z) = F(z) e^{-κ z}`, `F = multF (dens a₁ a₂) 0`: the function whose modulus on `ℝ` is
`≃ e^{W} dist(·, Γ)`. -/
def gFun (a₁ a₂ : ℝ) (z : ℂ) : ℂ :=
  OCS.multF (dens a₁ a₂) 0 z * Complex.exp (-(kappaMu a₁ a₂ : ℂ) * z)

/-- The test function `f(z) = G(z + 1/2)`: zeros `ℤ` on the left, `ℤ + 1/2` between the ramps. -/
def testFn (a₁ a₂ : ℝ) (z : ℂ) : ℂ :=
  gFun a₁ a₂ (z + 1 / 2)

/-! ## Part A: the density, and the potential `U` -/

/-- `m = 1 + μ` is a multiplier weight with `a = 1/2`, `b = 1`
(needs `1 ≤ a₁` and disjoint ramps `2 a₁ < a₂`). -/
theorem rampMu_bounds {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (t : ℝ) :
    -(1 / 2) ≤ rampMu a₁ a₂ t ∧ rampMu a₁ a₂ t ≤ 0 := by
  have ha₁ : 0 < a₁ := by linarith
  have ha₂ : 0 < a₂ := by linarith
  have hc₁ : (1 / 2) / a₁ ≤ 1 / 2 := by
    rw [div_le_iff₀ ha₁]; linarith
  have hc₁' : 0 < (1 / 2) / a₁ := by positivity
  have hc₂ : (1 / 2) / a₂ ≤ 1 / 2 := by
    rw [div_le_iff₀ ha₂]; linarith
  have hc₂' : 0 < (1 / 2) / a₂ := by positivity
  unfold rampMu
  by_cases hA : t ∈ Icc a₁ (2 * a₁)
  · have hB : t ∉ Icc a₂ (2 * a₂) := by
      intro hB; linarith [hA.2, hB.1]
    rw [indicator_of_mem hA, indicator_of_notMem hB]
    simp only [Pi.one_apply]
    constructor <;> nlinarith
  · by_cases hB : t ∈ Icc a₂ (2 * a₂)
    · rw [indicator_of_notMem hA, indicator_of_mem hB]
      simp only [Pi.one_apply]
      constructor <;> nlinarith
    · rw [indicator_of_notMem hA, indicator_of_notMem hB]
      simp

theorem measurable_rampMu (a₁ a₂ : ℝ) : Measurable (rampMu a₁ a₂) := by
  have h1 : Measurable ((Icc a₁ (2 * a₁)).indicator (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Icc
  have h2 : Measurable ((Icc a₂ (2 * a₂)).indicator (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Icc
  unfold rampMu
  exact (measurable_const.mul h1).sub (measurable_const.mul h2)

theorem dens_isMultWeight {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    OCS.IsMultWeight (dens a₁ a₂) (1 / 2) 1 where
  measurable := measurable_const.add (measurable_rampMu a₁ a₂)
  pos := by norm_num
  le t := by have := (rampMu_bounds h₁ h₂ t).1; unfold dens; linarith
  ge t := by have := (rampMu_bounds h₁ h₂ t).2; unfold dens; linarith

/-- `U_1(x) = 0` for real `x`: `∫ [log|1 - x/t| + (1 - χ_{[-1,1]}(t)) x/t] dt = 0`. -/
theorem multUIntegrand_one_real (x : ℝ) :
    ∫ t : ℝ, OCS.multUIntegrand (fun _ ↦ (1 : ℝ)) (x : ℂ) t = 0 := by
  rw [T2ii.multUIntegrand_one]; simp

/-- `U_1(z) = π |Im z|`. -/
theorem multUIntegrand_one (z : ℂ) :
    ∫ t : ℝ, OCS.multUIntegrand (fun _ ↦ (1 : ℝ)) z t = Real.pi * |z.im| :=
  T2ii.multUIntegrand_one z

/-- `U_m(z) = π|Im z| + W(z) + κ Re z` for `m = dens a₁ a₂`. -/
theorem rampMu_eq_zero {a₁ a₂ : ℝ} (h₂ : 2 * a₁ < a₂) (h₁ : 0 < a₁) {t : ℝ}
    (ht : t ∉ Icc a₁ (2 * a₂)) : rampMu a₁ a₂ t = 0 := by
  have hA : t ∉ Icc a₁ (2 * a₁) := fun h ↦ ht ⟨h.1, by linarith [h.2]⟩
  have hB : t ∉ Icc a₂ (2 * a₂) := fun h ↦ ht ⟨by linarith [h.1], h.2⟩
  unfold rampMu
  rw [indicator_of_notMem hA, indicator_of_notMem hB]; simp

theorem integrable_rampMu_div {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    Integrable (fun t : ℝ ↦ rampMu a₁ a₂ t / t) := by
  have hg : Integrable ((Icc a₁ (2 * a₂)).indicator (fun _ : ℝ ↦ (1 / 2 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp) (by simp))
  refine hg.mono' ((measurable_rampMu a₁ a₂).div measurable_id).aestronglyMeasurable
    (ae_of_all _ fun t ↦ ?_)
  by_cases ht : t ∈ Icc a₁ (2 * a₂)
  · rw [indicator_of_mem ht, Real.norm_eq_abs, abs_div]
    have := rampMu_bounds h₁ h₂ t
    have h3 : |rampMu a₁ a₂ t| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [this.1, this.2]
    have h4 : 1 ≤ |t| := by rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1]
    calc |rampMu a₁ a₂ t| / |t| ≤ |rampMu a₁ a₂ t| / 1 := by gcongr
      _ ≤ 1 / 2 := by rw [div_one]; exact h3
  · rw [indicator_of_notMem ht, rampMu_eq_zero h₂ (by linarith) ht]; simp

/-- The bracket `log |1 - z/t| + (1 - χ_{[-1,1]}(t)) Re (z/t)` of the integrand of `U`. -/
def bracketU (z : ℂ) (t : ℝ) : ℝ :=
  Real.log ‖1 - z / t‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).re

theorem integrable_rampMu_mul_bracketU {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (z : ℂ) :
    Integrable (fun t ↦ rampMu a₁ a₂ t * bracketU z t) := by
  have hw := dens_isMultWeight h₁ h₂
  have hw1 : OCS.IsMultWeight (fun _ : ℝ ↦ (1 : ℝ)) 1 1 :=
    ⟨measurable_const, one_pos, fun _ ↦ le_rfl, fun _ ↦ le_rfl⟩
  refine ((OCS.integrable_multUIntegrand hw z).sub (OCS.integrable_multUIntegrand hw1 z)).congr
    (ae_of_all _ fun t ↦ ?_)
  simp only [Pi.sub_apply, OCS.multUIntegrand, dens, bracketU]; ring

theorem rampMu_mul_bracketU_ae {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (z : ℂ) :
    ∀ᵐ t : ℝ, rampMu a₁ a₂ t * bracketU z t =
      rampMu a₁ a₂ t * Real.log ‖1 - z / t‖ + z.re * (rampMu a₁ a₂ t / t) := by
  filter_upwards [OCS.ae_ne_real 1] with t ht1
  by_cases ht : t ∈ Icc a₁ (2 * a₂)
  · have h1t : 1 < t := lt_of_le_of_ne (h₁.trans ht.1) (Ne.symm ht1)
    have : t ∉ Icc (-1 : ℝ) 1 := fun h ↦ by linarith [h.2]
    simp only [bracketU, indicator_of_notMem this, Complex.div_ofReal_re]
    ring
  · rw [rampMu_eq_zero h₂ (by linarith) ht]; simp

theorem integrable_rampMu_log {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (z : ℂ) :
    Integrable (fun t ↦ rampMu a₁ a₂ t * Real.log ‖1 - z / t‖) := by
  refine ((integrable_rampMu_mul_bracketU h₁ h₂ z).sub
    ((integrable_rampMu_div h₁ h₂).const_mul z.re)).congr ?_
  filter_upwards [rampMu_mul_bracketU_ae h₁ h₂ z] with t ht
  simp only [Pi.sub_apply]; rw [ht]; ring

theorem multU_dens {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (z : ℂ) :
    OCS.multU (dens a₁ a₂) 0 z = Real.pi * |z.im| + potW a₁ a₂ z + kappaMu a₁ a₂ * z.re := by
  have hw1 : OCS.IsMultWeight (fun _ : ℝ ↦ (1 : ℝ)) 1 1 :=
    ⟨measurable_const, one_pos, fun _ ↦ le_rfl, fun _ ↦ le_rfl⟩
  have hI1 := OCS.integrable_multUIntegrand hw1 z
  have hdecomp : ∀ t, OCS.multUIntegrand (dens a₁ a₂) z t =
      OCS.multUIntegrand (fun _ ↦ (1 : ℝ)) z t + rampMu a₁ a₂ t * bracketU z t := by
    intro t; simp only [OCS.multUIntegrand, dens, bracketU]; ring
  rw [OCS.multU_eq, add_zero]
  simp_rw [hdecomp]
  rw [integral_add hI1 (integrable_rampMu_mul_bracketU h₁ h₂ z), multUIntegrand_one z,
    integral_congr_ae (rampMu_mul_bracketU_ae h₁ h₂ z),
    integral_add (integrable_rampMu_log h₁ h₂ z) ((integrable_rampMu_div h₁ h₂).const_mul z.re),
    integral_const_mul]
  simp only [potW, kappaMu]
  ring

/-- **Ramp potential.**  For `a ≥ 1` and real `x`,
`|(1/a) ∫_a^{2a} log|1 - x/t| dt - log max(1, |x|/a)| ≤ 4`. -/
theorem rampPot_estimate {a : ℝ} (ha : 1 ≤ a) (x : ℝ) :
    |(1 / a) * ∫ t in a..2 * a, Real.log ‖1 - (x : ℂ) / t‖ - Real.log (max 1 (|x| / a))| ≤ 4 :=
  T2ii.rampPot_estimate (by linarith) x

/-- **Envelope.**  `|W(x) - (1/2) log env(x)| ≤ 4` for real `x` (needs `1 ≤ a₁`, `2 a₁ < a₂`). -/
theorem integral_indicator_ramp {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ∫ t : ℝ, (Icc a (2 * a)).indicator (fun t : ℝ ↦ Real.log ‖1 - z / t‖) t =
      ∫ t in a..2 * a, Real.log ‖1 - z / t‖ := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]

theorem integrableOn_ramp_log {a : ℝ} (ha : 0 < a) (x : ℝ) :
    IntegrableOn (fun t : ℝ ↦ Real.log ‖1 - (x : ℂ) / t‖) (Icc a (2 * a)) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1
    (T2ii.intervalIntegrable_g ha (by linarith) x)

theorem potW_real_eq {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (x : ℝ) :
    potW a₁ a₂ (x : ℂ) = -((1 / 2) / a₁) * (∫ t in a₁..2 * a₁, Real.log ‖1 - (x : ℂ) / t‖) -
      ((1 / 2) / a₂) * ∫ t in a₂..2 * a₂, Real.log ‖1 - (x : ℂ) / t‖ := by
  have ha₁ : 0 < a₁ := by linarith
  have ha₂ : 0 < a₂ := by linarith
  have hfun : (fun t : ℝ ↦ rampMu a₁ a₂ t * Real.log ‖1 - (x : ℂ) / t‖) = fun t ↦
      -((1 / 2) / a₁) * (Icc a₁ (2 * a₁)).indicator (fun t : ℝ ↦ Real.log ‖1 - (x : ℂ) / t‖) t -
      ((1 / 2) / a₂) * (Icc a₂ (2 * a₂)).indicator (fun t : ℝ ↦ Real.log ‖1 - (x : ℂ) / t‖) t := by
    funext t
    unfold rampMu
    simp only [Set.indicator_apply, Pi.one_apply]
    split_ifs <;> ring
  have i₁ := (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_ramp_log ha₁ x)
  have i₂ := (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_ramp_log ha₂ x)
  unfold potW
  rw [hfun, integral_sub (i₁.const_mul _) (i₂.const_mul _), integral_const_mul, integral_const_mul,
    integral_indicator_ramp ha₁, integral_indicator_ramp ha₂]

theorem log_div_max {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Real.log (a / max a |x|) = -Real.log (max 1 (|x| / a)) := by
  have hM : 0 < max 1 (|x| / a) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have : max a |x| = a * max 1 (|x| / a) := by
    rw [mul_max_of_nonneg _ _ ha.le, mul_one, mul_div_cancel₀ _ ha.ne']
  rw [this, ← div_div, div_self ha.ne', one_div, Real.log_inv]

theorem potW_estimate {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (x : ℝ) :
    |potW a₁ a₂ (x : ℂ) - Real.log (env a₁ a₂ x) / 2| ≤ 4 := by
  have ha₁ : 0 < a₁ := by linarith
  have ha₂ : 0 < a₂ := by linarith
  have e1 := T2ii.rampPot_estimate' ha₁ x
  have e2 := T2ii.rampPot_estimate' ha₂ x
  have hlog : Real.log (env a₁ a₂ x) =
      -Real.log (max 1 (|x| / a₁)) - Real.log (max 1 (|x| / a₂)) := by
    unfold env
    have p1 : 0 < a₁ / max a₁ |x| := div_pos ha₁ (lt_of_lt_of_le ha₁ (le_max_left _ _))
    have p2 : 0 < a₂ / max a₂ |x| := div_pos ha₂ (lt_of_lt_of_le ha₂ (le_max_left _ _))
    rw [Real.log_mul p1.ne' p2.ne', log_div_max ha₁, log_div_max ha₂]; ring
  rw [potW_real_eq h₁ h₂, hlog]
  set I₁ := ∫ t in a₁..2 * a₁, Real.log ‖1 - (x : ℂ) / t‖
  set I₂ := ∫ t in a₂..2 * a₂, Real.log ‖1 - (x : ℂ) / t‖
  set ℓ₁ := Real.log (max 1 (|x| / a₁))
  set ℓ₂ := Real.log (max 1 (|x| / a₂))
  have : -((1 / 2) / a₁) * I₁ - (1 / 2) / a₂ * I₂ - (-ℓ₁ - ℓ₂) / 2 =
      -(1 / 2) * ((1 / a₁ * I₁ - ℓ₁) + (1 / a₂ * I₂ - ℓ₂)) := by
    field_simp; ring
  rw [this, abs_mul, abs_neg]
  have := abs_add_le (1 / a₁ * I₁ - ℓ₁) (1 / a₂ * I₂ - ℓ₂)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

/-- A one-sided bound on `W` for complex `z`, enough for exponential type: since `μ ≤ 0`,
`W(z) = ∫ |μ| (log t - log|t - z|) ≤ log(2 a₂) + 1` for every `z`. -/
theorem integrable_rampMu {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    Integrable (rampMu a₁ a₂) := by
  have hg : Integrable ((Icc a₁ (2 * a₂)).indicator (fun _ : ℝ ↦ (1 / 2 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  refine hg.mono' (measurable_rampMu a₁ a₂).aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
  by_cases ht : t ∈ Icc a₁ (2 * a₂)
  · rw [indicator_of_mem ht, Real.norm_eq_abs]
    have := rampMu_bounds h₁ h₂ t
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  · rw [indicator_of_notMem ht, rampMu_eq_zero h₂ (by linarith) ht]; simp

theorem integral_rampMu {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    ∫ t, rampMu a₁ a₂ t = -1 := by
  have ha₁ : 0 < a₁ := by linarith
  have ha₂ : 0 < a₂ := by linarith
  have i₁ : Integrable ((Icc a₁ (2 * a₁)).indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have i₂ : Integrable ((Icc a₂ (2 * a₂)).indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hfun : rampMu a₁ a₂ = fun t ↦ -((1 / 2) / a₁) * (Icc a₁ (2 * a₁)).indicator 1 t -
    ((1 / 2) / a₂) * (Icc a₂ (2 * a₂)).indicator 1 t := rfl
  rw [hfun, integral_sub (i₁.const_mul _) (i₂.const_mul _), integral_const_mul, integral_const_mul,
    integral_indicator_one measurableSet_Icc, integral_indicator_one measurableSet_Icc]
  simp only [Real.volume_real_Icc, ]
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  field_simp
  ring

theorem potW_le_complex {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (z : ℂ) :
    potW a₁ a₂ z ≤ Real.log (2 * a₂) + 1 := by
  have ha₁ : 0 < a₁ := by linarith
  have ha₂ : 0 < a₂ := by linarith
  have hVi : Integrable (fun t : ℝ ↦ T2ii.Vneg (t - z.re)) := T2ii.integrable_Vneg.comp_sub_right z.re
  have hVint : ∫ t : ℝ, T2ii.Vneg (t - z.re) = -2 := by
    rw [integral_sub_right_eq_self (fun t ↦ T2ii.Vneg t) z.re]; exact T2ii.integral_Vneg
  set rhs : ℝ → ℝ := fun t ↦ (-rampMu a₁ a₂ t) * Real.log (2 * a₂) + (1 / 2) * (-T2ii.Vneg (t - z.re))
    with hrhs
  have hrhsi : Integrable rhs :=
    ((integrable_rampMu h₁ h₂).neg.mul_const _).add (hVi.neg.const_mul _)
  have hle : ∀ᵐ t : ℝ, rampMu a₁ a₂ t * Real.log ‖1 - z / t‖ ≤ rhs t := by
    filter_upwards [OCS.ae_ne_real z.re] with t hre
    have hV : 0 ≤ -T2ii.Vneg (t - z.re) := by
      have : T2ii.Vneg (t - z.re) ≤ 0 := min_le_left _ _
      linarith
    by_cases ht : t ∈ Icc a₁ (2 * a₂)
    · have ht0 : 0 < t := by linarith [ht.1]
      have hb := rampMu_bounds h₁ h₂ t
      have hz : (t : ℂ) ≠ z := fun h ↦ hre (by rw [← h]; simp)
      have hL : Real.log ‖1 - z / t‖ = Real.log ‖(t : ℂ) - z‖ - Real.log t := by
        rw [OCS.log_norm_one_sub_div z ht0.ne' hz, sub_zero, Complex.norm_real,
          Real.norm_eq_abs, Real.log_abs]
      have h1 : Real.log t ≤ Real.log (2 * a₂) := Real.log_le_log ht0 ht.2
      have hd : 0 < |t - z.re| := abs_pos.2 (sub_ne_zero.2 hre)
      have h2 : |t - z.re| ≤ ‖(t : ℂ) - z‖ := by
        have := Complex.abs_re_le_norm ((t : ℂ) - z)
        simpa using this
      have h3 : Real.log |t - z.re| ≤ Real.log ‖(t : ℂ) - z‖ := Real.log_le_log hd h2
      have h4 : -Real.log ‖(t : ℂ) - z‖ ≤ -T2ii.Vneg (t - z.re) := by
        have : T2ii.Vneg (t - z.re) ≤ Real.log |t - z.re| := min_le_right _ _
        linarith
      have h5 : -Real.log ‖1 - z / t‖ ≤ Real.log (2 * a₂) + (-T2ii.Vneg (t - z.re)) := by
        rw [hL]; linarith
      simp only [hrhs]
      nlinarith [mul_nonneg (by linarith [hb.2] : 0 ≤ -rampMu a₁ a₂ t)
        (by linarith : 0 ≤ Real.log (2 * a₂) + (-T2ii.Vneg (t - z.re)) - (-Real.log ‖1 - z / t‖)),
        mul_nonneg (by linarith [hb.1] : 0 ≤ 1 / 2 + rampMu a₁ a₂ t) hV]
    · simp only [hrhs]
      rw [rampMu_eq_zero h₂ (by linarith) ht]
      simp only [zero_mul, neg_zero]
      linarith
  have := integral_mono_ae (integrable_rampMu_log h₁ h₂ z) hrhsi hle
  have hI : ∫ t, rhs t = Real.log (2 * a₂) + 1 := by
    simp only [hrhs]
    have h1 : Integrable (fun t ↦ -rampMu a₁ a₂ t * Real.log (2 * a₂)) :=
      (integrable_rampMu h₁ h₂).neg.mul_const _
    have h2 : Integrable (fun t : ℝ ↦ 1 / 2 * -T2ii.Vneg (t - z.re)) := hVi.neg.const_mul _
    rw [integral_add h1 h2, integral_mul_const, integral_neg, integral_const_mul, integral_neg, integral_rampMu h₁ h₂, hVint]
    ring
  unfold potW
  linarith

/-! ## Part B: the zeros of `F` -/

/-- `∫_0^x m = x - 1/2` for `2 a₁ ≤ x ≤ a₂`. -/
theorem dens_eq_one_of_lt {a₁ a₂ : ℝ} (h₂ : 2 * a₁ < a₂) (h₁ : 0 < a₁) {t : ℝ} (ht : t < a₁) :
    dens a₁ a₂ t = 1 := by
  unfold dens; rw [rampMu_eq_zero h₂ h₁ (fun h ↦ by linarith [h.1])]; simp

theorem dens_eq_one_of_mem_Ioo {a₁ a₂ t : ℝ} (ht : t ∈ Ioo (2 * a₁) a₂) : dens a₁ a₂ t = 1 := by
  have hA : t ∉ Icc a₁ (2 * a₁) := fun h ↦ by linarith [h.2, ht.1]
  have hB : t ∉ Icc a₂ (2 * a₂) := fun h ↦ by linarith [h.1, ht.2]
  unfold dens rampMu
  rw [indicator_of_notMem hA, indicator_of_notMem hB]; simp

theorem multPrim_dens_small {a₁ a₂ : ℝ} (h₂ : 2 * a₁ < a₂) (h₁ : 0 < a₁) {x : ℝ} (hx : x ≤ a₁) :
    OCS.multPrim (dens a₁ a₂) x = x := by
  unfold OCS.multPrim
  have : ∫ t in (0 : ℝ)..x, dens a₁ a₂ t = ∫ t in (0 : ℝ)..x, (1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [OCS.ae_ne_real a₁] with t ht ht'
    have : t ≤ a₁ := by
      rw [Set.mem_uIoc] at ht'
      rcases ht' with h | h <;> linarith [h.2]
    exact dens_eq_one_of_lt h₂ h₁ (lt_of_le_of_ne this ht)
  rw [this]; simp

theorem multPrim_dens_stretch {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) {x : ℝ}
    (hx : x ∈ Icc (2 * a₁) a₂) : OCS.multPrim (dens a₁ a₂) x = x - 1 / 2 := by
  have ha₁ : 0 < a₁ := by linarith
  have ha₂ : 0 < a₂ := by linarith
  have hx0 : 0 ≤ x := by linarith [hx.1]
  unfold OCS.multPrim
  rw [intervalIntegral.integral_of_le hx0]
  have hint : IntegrableOn (rampMu a₁ a₂) (Ioc 0 x) := (integrable_rampMu h₁ h₂).integrableOn
  have hd : ∫ t in Ioc 0 x, dens a₁ a₂ t = x + ∫ t in Ioc 0 x, rampMu a₁ a₂ t := by
    unfold dens
    rw [integral_add (integrableOn_const (by simp)) hint]
    simp [hx0]
  rw [hd]
  have i₁ : Integrable ((Icc a₁ (2 * a₁)).indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have i₂ : Integrable ((Icc a₂ (2 * a₂)).indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hfun : rampMu a₁ a₂ = fun t ↦ -((1 / 2) / a₁) * (Icc a₁ (2 * a₁)).indicator 1 t -
    ((1 / 2) / a₂) * (Icc a₂ (2 * a₂)).indicator 1 t := rfl
  rw [hfun, integral_sub (i₁.const_mul _).integrableOn (i₂.const_mul _).integrableOn,
    integral_const_mul, integral_const_mul]
  have e1 : ∫ t in Ioc 0 x, (Icc a₁ (2 * a₁)).indicator (1 : ℝ → ℝ) t = a₁ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_indicator_one measurableSet_Icc]
    · simp only [Real.volume_real_Icc]; rw [max_eq_left (by linarith)]; ring
    · intro t ht
      have : t ∉ Icc a₁ (2 * a₁) := fun h ↦ ht ⟨by linarith [h.1], by linarith [h.2, hx.1]⟩
      rw [indicator_of_notMem this]
  have e2 : ∫ t in Ioc 0 x, (Icc a₂ (2 * a₂)).indicator (1 : ℝ → ℝ) t = 0 := by
    refine setIntegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [OCS.ae_ne_real a₂] with t ht1 ht2
    have : t ∉ Icc a₂ (2 * a₂) := fun h ↦ ht1 (le_antisymm (ht2.2.trans hx.2) h.1)
    rw [indicator_of_notMem this]
  rw [e1, e2]
  field_simp
  ring

/-- Left zeros: for `1 ≤ a₁`, `j ≤ 0`, the barycentre `γ_j = j + 1/2` (the interval `I_j = [j, j+1]`
lies in `{m = 1}`), so `testFn` vanishes at every integer `j ≤ 0`. -/
theorem multPt_dens_of {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) {j : ℤ} {y : ℝ}
    (hy : y ∈ Icc (2 * a₁) a₂) (hj : y - 1 / 2 = j) : OCS.multPt (dens a₁ a₂) j = y :=
  OCS.multPt_eq_of (dens_isMultWeight h₁ h₂) (by rw [multPrim_dens_stretch h₁ h₂ hy, hj])

theorem multBary_dens_nonpos {a₁ a₂ : ℝ} (h₁ : 2 ≤ a₁) (h₂ : 2 * a₁ < a₂) {j : ℤ} (hj : j ≤ 0) :
    OCS.multBary (dens a₁ a₂) j = j + 1 / 2 := by
  have hw := dens_isMultWeight (by linarith : 1 ≤ a₁) h₂
  have hj' : (j : ℝ) ≤ 0 := by exact_mod_cast hj
  have p0 : OCS.multPt (dens a₁ a₂) j = j :=
    OCS.multPt_eq_of hw (by rw [multPrim_dens_small h₂ (by linarith) (by linarith)])
  have p1 : OCS.multPt (dens a₁ a₂) (j + 1) = j + 1 := by
    refine OCS.multPt_eq_of hw ?_
    rw [multPrim_dens_small h₂ (by linarith) (by linarith)]; push_cast; ring
  unfold OCS.multBary
  rw [p0, p1]
  have : ∫ t in (j : ℝ)..(j + 1 : ℝ), t * dens a₁ a₂ t = ∫ t in (j : ℝ)..(j + 1 : ℝ), t := by
    refine intervalIntegral.integral_congr (fun t ht ↦ ?_)
    rw [Set.uIcc_of_le (by linarith)] at ht
    rw [dens_eq_one_of_lt h₂ (by linarith) (by linarith [ht.2]), mul_one]
  rw [this, integral_id]
  ring

theorem testFn_eq_zero_of_nonpos {a₁ a₂ : ℝ} (h₁ : 2 ≤ a₁) (h₂ : 2 * a₁ < a₂) (j : ℤ)
    (hj : j ≤ 0) : testFn a₁ a₂ (j : ℂ) = 0 := by
  have hw := dens_isMultWeight (by linarith : 1 ≤ a₁) h₂
  unfold testFn gFun
  have : OCS.multF (dens a₁ a₂) 0 ((j : ℂ) + 1 / 2) = 0 := by
    rw [OCS.multF_eq_zero_iff hw]
    refine ⟨OCS.multBary (dens a₁ a₂) j, ⟨j, rfl⟩, ?_⟩
    rw [multBary_dens_nonpos h₁ h₂ hj]; push_cast; ring
  rw [this, zero_mul]

/-- Stretch zeros: `Γ ∩ [2a₁ + 1, a₂ - 1] = ℤ + 1` (the zeros of `G`), so for the argument `x` of
the test function, `x ∈ [2a₁ + 3, a₂ - 3]`, `dist(x + 1/2, Γ) = dist(x, ℤ + 1/2)`. -/
theorem multBary_dens_stretch {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) {j : ℤ}
    (hj1 : 2 * a₁ < j + 1 / 2) (hj2 : (j : ℝ) + 3 / 2 < a₂) :
    OCS.multBary (dens a₁ a₂) j = j + 1 := by
  have p0 : OCS.multPt (dens a₁ a₂) j = j + 1 / 2 :=
    multPt_dens_of h₁ h₂ (y := j + 1 / 2) ⟨hj1.le, by linarith⟩ (by ring)
  have p1 : OCS.multPt (dens a₁ a₂) (j + 1) = j + 3 / 2 :=
    multPt_dens_of h₁ h₂ (y := j + 3 / 2) ⟨by linarith, hj2.le⟩ (by push_cast; ring)
  unfold OCS.multBary
  rw [p0, p1]
  have : ∫ t in ((j : ℝ) + 1 / 2)..((j : ℝ) + 3 / 2), t * dens a₁ a₂ t =
      ∫ t in ((j : ℝ) + 1 / 2)..((j : ℝ) + 3 / 2), t := by
    refine intervalIntegral.integral_congr (fun t ht ↦ ?_)
    rw [Set.uIcc_of_le (by linarith)] at ht
    rw [dens_eq_one_of_mem_Ioo (a₁ := a₁) ⟨by linarith [ht.1], by linarith [ht.2]⟩, mul_one]
  rw [this, integral_id]
  ring

theorem infDist_dens_stretch {a₁ a₂ : ℝ} (h₁ : 2 ≤ a₁) (h₂ : 2 * a₁ < a₂) {x : ℝ}
    (hx : x ∈ Icc (2 * a₁ + 3) (a₂ - 3)) :
    infDist (((x + 1 / 2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂)) =
      |x - 1 / 2 - round (x - 1 / 2)| := by
  have h₁' : 1 ≤ a₁ := by linarith
  have hw := dens_isMultWeight h₁' h₂
  have hy : x + 1 / 2 ∈ Icc (2 * a₁) a₂ := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hprim : OCS.multPrim (dens a₁ a₂) (x + 1 / 2) = x := by
    rw [multPrim_dens_stretch h₁' h₂ hy]; ring
  have hk : OCS.multIdx (dens a₁ a₂) (x + 1 / 2) = ⌊x⌋ := by
    unfold OCS.multIdx; rw [hprim]
  have hround : round (x - 1 / 2) = ⌊x⌋ := by
    rw [round_eq]; congr 1; ring
  obtain ⟨i, hi, hmin, hd⟩ := OCS.exists_infDist_multGammaC_eq hw (((x + 1 / 2 : ℝ)) : ℂ)
  rw [Complex.ofReal_re, hk] at hi hmin
  have hmin' := hmin ⌊x⌋ (by simp)
  simp only [Finset.mem_Icc] at hi
  have hbary : ∀ j : ℤ, ⌊x⌋ - 1 ≤ j → j ≤ ⌊x⌋ + 1 → OCS.multBary (dens a₁ a₂) j = j + 1 := by
    intro j hj1 hj2
    have f1 := Int.floor_le x
    have f2 := Int.lt_floor_add_one x
    have e1 : ((⌊x⌋ : ℤ) : ℝ) - 1 ≤ j := by exact_mod_cast hj1
    have e2 : (j : ℝ) ≤ ⌊x⌋ + 1 := by exact_mod_cast hj2
    exact multBary_dens_stretch h₁' h₂ (by linarith [hx.1]) (by linarith [hx.2])
  have hnorm : ∀ g : ℝ, ‖(((x + 1 / 2 : ℝ)) : ℂ) - (g : ℂ)‖ = |x + 1 / 2 - g| := by
    intro g; rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, hnorm, hbary i hi.1 hi.2, hbary ⌊x⌋ (by omega) (by omega)] at hmin'
  have e : x + 1 / 2 - ((i : ℝ) + 1) = x - 1 / 2 - i := by ring
  have e' : x + 1 / 2 - ((⌊x⌋ : ℝ) + 1) = x - 1 / 2 - ⌊x⌋ := by ring
  rw [e, e'] at hmin'
  rw [hd, hnorm, hbary i hi.1 hi.2, hround, e]
  refine le_antisymm hmin' ?_
  have lo := round_le (x - 1 / 2) i
  rwa [hround] at lo

/-- For every weight and real `y`, `dist(y, Γ) ≤ 1/a`. -/
theorem infDist_multGammaC_le {m : ℝ → ℝ} {a b : ℝ} (hw : OCS.IsMultWeight m a b) (y : ℝ) :
    infDist (y : ℂ) (OCS.multGammaC m) ≤ 1 / a := by
  set k := OCS.multIdx m y
  have h1 := OCS.multIdx_mem hw y
  have h2 := OCS.multBary_mem hw k
  have h3 := (OCS.multPt_succ_sub_bounds hw k).2
  have hpos : 0 < a / (2 * b ^ 2) := by have := hw.pos; have := hw.b_pos; positivity
  have hmem : ((OCS.multBary m k : ℝ) : ℂ) ∈ OCS.multGammaC m := ⟨_, ⟨k, rfl⟩, rfl⟩
  refine (infDist_le_dist_of_mem hmem).trans ?_
  rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ## Part C: `testFn ∈ PW` and its size on `ℝ` -/

/-- **Two-sided estimate on `ℝ`** with absolute constants `0 < c ≤ C`:
`c √env(x + 1/2) · dist(x + 1/2, Γ) ≤ |f(x)| ≤ C √env(x + 1/2) · dist(x + 1/2, Γ)`
(uniform in `a₁, a₂` with `1 ≤ a₁`, `2 a₁ < a₂`). -/
theorem norm_testFn_mul_exp {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (x : ℝ) :
    ‖testFn a₁ a₂ x‖ * Real.exp (-potW a₁ a₂ ((x + 1 / 2 : ℝ) : ℂ)) =
      ‖OCS.multF (dens a₁ a₂) 0 ((x + 1 / 2 : ℝ) : ℂ)‖ *
        Real.exp (-OCS.multU (dens a₁ a₂) 0 ((x + 1 / 2 : ℝ) : ℂ)) := by
  have hz : (x : ℂ) + 1 / 2 = ((x + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hn : ‖testFn a₁ a₂ x‖ = ‖OCS.multF (dens a₁ a₂) 0 ((x + 1 / 2 : ℝ) : ℂ)‖ *
      Real.exp (-(kappaMu a₁ a₂ * (x + 1 / 2))) := by
    unfold testFn gFun
    rw [norm_mul, hz, Complex.norm_exp]
    congr 2
    simp
  rw [hn, multU_dens h₁ h₂]
  simp only [Complex.ofReal_im, abs_zero, mul_zero, zero_add, Complex.ofReal_re]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem exp_potW_bounds {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (x : ℝ) :
    Real.exp (-4) * Real.sqrt (env a₁ a₂ x) ≤ Real.exp (potW a₁ a₂ (x : ℂ)) ∧
      Real.exp (potW a₁ a₂ (x : ℂ)) ≤ Real.exp 4 * Real.sqrt (env a₁ a₂ x) := by
  have ha₁ : 0 < a₁ := by linarith
  have ha₂ : 0 < a₂ := by linarith
  have henv : 0 < env a₁ a₂ x := by
    unfold env
    exact mul_pos (div_pos ha₁ (lt_of_lt_of_le ha₁ (le_max_left _ _)))
      (div_pos ha₂ (lt_of_lt_of_le ha₂ (le_max_left _ _)))
  have hs : Real.sqrt (env a₁ a₂ x) = Real.exp (Real.log (env a₁ a₂ x) / 2) := by
    rw [← Real.log_sqrt henv.le, Real.exp_log (Real.sqrt_pos.2 henv)]
  have := abs_le.1 (potW_estimate h₁ h₂ x)
  rw [hs, ← Real.exp_add, ← Real.exp_add]
  constructor <;> apply Real.exp_le_exp.2 <;> linarith [this.1, this.2]

theorem testFn_norm_real :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a₁ a₂ : ℝ, 1 ≤ a₁ → 2 * a₁ < a₂ → ∀ x : ℝ,
      c * Real.sqrt (env a₁ a₂ (x + 1 / 2)) *
          infDist (((x + 1 / 2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂)) ≤ ‖testFn a₁ a₂ x‖ ∧
      ‖testFn a₁ a₂ x‖ ≤ C * Real.sqrt (env a₁ a₂ (x + 1 / 2)) *
          infDist (((x + 1 / 2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂)) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hL⟩ := lemma3_estimate_uniform (a := 1 / 2) (b := 1) (by norm_num)
    (by norm_num)
  refine ⟨c₁ * Real.exp (-4), c₂ * Real.exp 4, by positivity, by positivity, ?_⟩
  intro a₁ a₂ h₁ h₂ x
  have hw := dens_isMultWeight h₁ h₂
  have hl := hL _ hw 0 (((x + 1 / 2 : ℝ)) : ℂ) (by simp)
  rw [← norm_testFn_mul_exp h₁ h₂ x] at hl
  have hb := exp_potW_bounds h₁ h₂ (x + 1 / 2)
  set d := infDist (((x + 1 / 2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂))
  set N := ‖testFn a₁ a₂ x‖
  set W := potW a₁ a₂ ((x + 1 / 2 : ℝ) : ℂ)
  have hNW : N = (N * Real.exp (-W)) * Real.exp W := by
    rw [mul_assoc, ← Real.exp_add]; simp
  have hd0 : 0 ≤ d := infDist_nonneg
  have hs0 := Real.sqrt_nonneg (env a₁ a₂ (x + 1 / 2))
  have hNn : 0 ≤ N * Real.exp (-W) := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  constructor
  · rw [hNW]
    calc c₁ * Real.exp (-4) * Real.sqrt (env a₁ a₂ (x + 1 / 2)) * d
        = (c₁ * d) * (Real.exp (-4) * Real.sqrt (env a₁ a₂ (x + 1 / 2))) := by ring
      _ ≤ (N * Real.exp (-W)) * Real.exp W := by
        apply mul_le_mul hl.1 hb.1 (by positivity) hNn
  · rw [hNW]
    have h := mul_le_mul hl.2 hb.2 (Real.exp_pos _).le (by positivity)
    calc (N * Real.exp (-W)) * Real.exp W ≤ (c₂ * d) * (Real.exp 4 * Real.sqrt (env a₁ a₂ (x + 1 / 2))) := h
      _ = c₂ * Real.exp 4 * Real.sqrt (env a₁ a₂ (x + 1 / 2)) * d := by ring

/-- `testFn` is entire. -/
theorem differentiable_testFn {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    Differentiable ℂ (testFn a₁ a₂) := by
  have hw := dens_isMultWeight h₁ h₂
  unfold testFn gFun
  have h1 : Differentiable ℂ (fun w : ℂ ↦ OCS.multF (dens a₁ a₂) 0 w *
      Complex.exp (-(kappaMu a₁ a₂ : ℂ) * w)) :=
    (OCS.differentiable_multF hw 0).mul ((differentiable_id.const_mul _).cexp)
  exact h1.comp (differentiable_id.add_const _)

/-- `testFn` has exponential type `≤ π`: `|f(z)| ≤ C e^{π |Im z|}`. -/
theorem norm_gFun_eq {a₁ a₂ : ℝ} (w : ℂ) :
    ‖gFun a₁ a₂ w‖ = ‖OCS.multF (dens a₁ a₂) 0 w‖ * Real.exp (-(kappaMu a₁ a₂ * w.re)) := by
  unfold gFun
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp

/-- `|F(w)| ≤ e^{U(w) + π}` away from the real axis (estimate (3) of Lemma 3). -/
theorem norm_multF_le_of_one_le_im {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) {w : ℂ}
    (hw1 : 1 ≤ |w.im|) :
    ‖OCS.multF (dens a₁ a₂) 0 w‖ ≤ Real.exp (OCS.multU (dens a₁ a₂) 0 w + Real.pi) := by
  have hw := dens_isMultWeight h₁ h₂
  have him : w.im ≠ 0 := by intro h; rw [h] at hw1; norm_num at hw1
  have h3 := OCS.multF_estimate_three hw 0 him
  have hre : (OCS.multL (dens a₁ a₂) 0 w).re - OCS.multU (dens a₁ a₂) 0 w ≤ Real.pi := by
    have h4 := Complex.re_le_norm (OCS.multL (dens a₁ a₂) 0 w - OCS.multU (dens a₁ a₂) 0 w -
      Complex.I * OCS.multV (dens a₁ a₂) 0 w)
    have h5 : (OCS.multL (dens a₁ a₂) 0 w - OCS.multU (dens a₁ a₂) 0 w -
      Complex.I * OCS.multV (dens a₁ a₂) 0 w).re =
        (OCS.multL (dens a₁ a₂) 0 w).re - OCS.multU (dens a₁ a₂) 0 w := by simp
    have h6 : Real.pi / (2 * (1 / 2)) / |w.im| ≤ Real.pi := by
      rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, div_one, div_le_iff₀ (by linarith)]
      nlinarith [Real.pi_pos]
    linarith
  rw [← OCS.exp_multL hw 0 him, Complex.norm_exp]
  exact Real.exp_le_exp.2 (by linarith)

theorem exists_norm_gFun_le {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ w : ℂ, ‖gFun a₁ a₂ w‖ ≤ C₀ * Real.exp (Real.pi * |w.im|) := by
  have hw := dens_isMultWeight h₁ h₂
  obtain ⟨c₁, c₂, hc₁, hc₂, hL⟩ := lemma3_estimate_uniform (a := 1 / 2) (b := 1) (by norm_num)
    (by norm_num)
  refine ⟨(1 + 3 * c₂) * Real.exp (Real.log (2 * a₂) + 1) * Real.exp Real.pi, by positivity, ?_⟩
  intro w
  have hP := potW_le_complex h₁ h₂ w
  have hU := multU_dens h₁ h₂ w
  have hexpP : Real.exp (potW a₁ a₂ w) ≤ Real.exp (Real.log (2 * a₂) + 1) := Real.exp_le_exp.2 hP
  have hπ1 : 1 ≤ Real.exp Real.pi := Real.one_le_exp Real.pi_pos.le
  have hgn := norm_gFun_eq (a₁ := a₁) (a₂ := a₂) w
  have hkey : ∀ B : ℝ, ‖OCS.multF (dens a₁ a₂) 0 w‖ ≤ B * Real.exp (OCS.multU (dens a₁ a₂) 0 w) →
      ‖gFun a₁ a₂ w‖ ≤ B * Real.exp (Real.pi * |w.im|) * Real.exp (potW a₁ a₂ w) := by
    intro B hB
    rw [hgn]
    calc ‖OCS.multF (dens a₁ a₂) 0 w‖ * Real.exp (-(kappaMu a₁ a₂ * w.re))
        ≤ (B * Real.exp (OCS.multU (dens a₁ a₂) 0 w)) * Real.exp (-(kappaMu a₁ a₂ * w.re)) := by
          gcongr
      _ = B * Real.exp (Real.pi * |w.im|) * Real.exp (potW a₁ a₂ w) := by
          have e : Real.exp (OCS.multU (dens a₁ a₂) 0 w) * Real.exp (-(kappaMu a₁ a₂ * w.re)) =
              Real.exp (Real.pi * |w.im|) * Real.exp (potW a₁ a₂ w) := by
            rw [← Real.exp_add, ← Real.exp_add, hU]; congr 1; ring
          rw [mul_assoc, e]; ring
  by_cases hbig : 1 ≤ |w.im|
  · have := norm_multF_le_of_one_le_im h₁ h₂ hbig
    have h' : ‖OCS.multF (dens a₁ a₂) 0 w‖ ≤ Real.exp Real.pi * Real.exp (OCS.multU (dens a₁ a₂) 0 w) := by
      rw [← Real.exp_add, add_comm]; exact this
    have := hkey _ h'
    calc ‖gFun a₁ a₂ w‖ ≤ Real.exp Real.pi * Real.exp (Real.pi * |w.im|) * Real.exp (potW a₁ a₂ w) := this
      _ ≤ _ := by
        have h0 : 0 < Real.exp (Real.pi * |w.im|) := Real.exp_pos _
        have h2 : 0 ≤ 3 * c₂ := by positivity
        have e1 : Real.exp Real.pi * Real.exp (Real.pi * |w.im|) * Real.exp (potW a₁ a₂ w) ≤
            Real.exp Real.pi * Real.exp (Real.pi * |w.im|) * Real.exp (Real.log (2 * a₂) + 1) := by
          gcongr
        refine e1.trans ?_
        have : (1 + 3 * c₂) ≥ 1 := by linarith
        nlinarith [Real.exp_pos (Real.log (2 * a₂) + 1), Real.exp_pos Real.pi,
          mul_pos h0 (Real.exp_pos (Real.log (2 * a₂) + 1)), mul_pos (mul_pos h0 (Real.exp_pos (Real.log (2 * a₂) + 1))) (Real.exp_pos Real.pi)]
  · rw [not_le] at hbig
    have hlow := (hL _ hw 0 w hbig.le).2
    have hd : infDist w (OCS.multGammaC (dens a₁ a₂)) ≤ 3 := by
      have h1 := infDist_multGammaC_le hw w.re
      have h2 : infDist w (OCS.multGammaC (dens a₁ a₂)) ≤
          infDist ((w.re : ℝ) : ℂ) (OCS.multGammaC (dens a₁ a₂)) + dist w ((w.re : ℝ) : ℂ) :=
        Metric.infDist_le_infDist_add_dist
      have h3 : dist w ((w.re : ℝ) : ℂ) = |w.im| := by
        rw [Complex.dist_eq]
        have : w - ((w.re : ℝ) : ℂ) = ((w.im : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp
        rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
      norm_num at h1
      linarith
    have h' : ‖OCS.multF (dens a₁ a₂) 0 w‖ ≤ (3 * c₂) * Real.exp (OCS.multU (dens a₁ a₂) 0 w) := by
      have e : ‖OCS.multF (dens a₁ a₂) 0 w‖ =
          (‖OCS.multF (dens a₁ a₂) 0 w‖ * Real.exp (-OCS.multU (dens a₁ a₂) 0 w)) *
            Real.exp (OCS.multU (dens a₁ a₂) 0 w) := by
        rw [mul_assoc, ← Real.exp_add]; simp
      have hX : ‖OCS.multF (dens a₁ a₂) 0 w‖ * Real.exp (-OCS.multU (dens a₁ a₂) 0 w) ≤ 3 * c₂ := by
        calc _ ≤ c₂ * infDist w (OCS.multGammaC (dens a₁ a₂)) := hlow
          _ ≤ c₂ * 3 := by gcongr
          _ = 3 * c₂ := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hX (Real.exp_pos _).le
    have := hkey _ h'
    calc ‖gFun a₁ a₂ w‖ ≤ (3 * c₂) * Real.exp (Real.pi * |w.im|) * Real.exp (potW a₁ a₂ w) := this
      _ ≤ _ := by
        have h0 : 0 < Real.exp (Real.pi * |w.im|) := Real.exp_pos _
        have e1 : (3 * c₂) * Real.exp (Real.pi * |w.im|) * Real.exp (potW a₁ a₂ w) ≤
            (3 * c₂) * Real.exp (Real.pi * |w.im|) * Real.exp (Real.log (2 * a₂) + 1) := by
          gcongr
        refine e1.trans ?_
        have hE := Real.exp_pos (Real.log (2 * a₂) + 1)
        have : (3 * c₂) * Real.exp (Real.pi * |w.im|) * Real.exp (Real.log (2 * a₂) + 1) * 1 ≤
            (3 * c₂) * Real.exp (Real.pi * |w.im|) * Real.exp (Real.log (2 * a₂) + 1) * Real.exp Real.pi := by
          gcongr
        nlinarith [mul_pos h0 hE, this]

theorem isExpTypeLE_testFn {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    IsExpTypeLE Real.pi (testFn a₁ a₂) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_norm_gFun_le h₁ h₂
  intro ε hε
  refine ⟨C₀, fun z ↦ ?_⟩
  have h1 := hC (z + 1 / 2)
  have him : (z + 1 / 2).im = z.im := by simp
  rw [him] at h1
  refine h1.trans ?_
  have := Complex.abs_im_le_norm z
  have h2 : Real.pi * |z.im| ≤ (Real.pi + ε) * ‖z‖ := by
    nlinarith [Real.pi_pos, norm_nonneg z, abs_nonneg z.im]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) hC₀.le

/-- `∫ env < ∞` and `testFn ∈ L²(ℝ)`. -/
theorem env_pos {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (x : ℝ) : 0 < env a₁ a₂ x := by
  unfold env
  exact mul_pos (div_pos ha₁ (lt_of_lt_of_le ha₁ (le_max_left _ _)))
    (div_pos ha₂ (lt_of_lt_of_le ha₂ (le_max_left _ _)))

theorem env_le_one {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (x : ℝ) : env a₁ a₂ x ≤ 1 := by
  unfold env
  have h1 : a₁ / max a₁ |x| ≤ 1 := (div_le_one (lt_of_lt_of_le ha₁ (le_max_left _ _))).2 (le_max_left _ _)
  have h2 : a₂ / max a₂ |x| ≤ 1 := (div_le_one (lt_of_lt_of_le ha₂ (le_max_left _ _))).2 (le_max_left _ _)
  have h3 : 0 ≤ a₁ / max a₁ |x| := div_nonneg ha₁.le (lt_of_lt_of_le ha₁ (le_max_left _ _)).le
  have h4 : 0 ≤ a₂ / max a₂ |x| := div_nonneg ha₂.le (lt_of_lt_of_le ha₂ (le_max_left _ _)).le
  nlinarith

theorem env_mul_le {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (h12 : a₁ ≤ a₂) (x : ℝ) :
    env a₁ a₂ x * (1 + x ^ 2) ≤ 1 + a₁ * a₂ := by
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ h12
  unfold env
  have hx : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  rw [hx]
  set u := |x| with hu
  have hu0 : 0 ≤ u := abs_nonneg x
  rcases le_total u a₁ with h | h
  · rw [max_eq_left h, max_eq_left (h.trans h12), div_self ha₁.ne', div_self ha₂.ne']
    nlinarith
  · rw [max_eq_right h]
    have hupos : 0 < u := lt_of_lt_of_le ha₁ h
    rcases le_total u a₂ with h' | h'
    · rw [max_eq_left h']
      rw [div_self ha₂.ne', mul_one, div_mul_eq_mul_div, div_le_iff₀ hupos]
      have : a₁ ≤ u := h
      nlinarith [mul_le_mul_of_nonneg_left h' ha₁.le]
    · rw [max_eq_right h']
      have : a₁ * a₂ ≤ u ^ 2 := by nlinarith
      rw [div_mul_div_comm, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_pos ha₁ ha₂]

theorem integrable_env_shift {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (h12 : a₁ ≤ a₂) :
    Integrable (fun x : ℝ ↦ env a₁ a₂ (x + 1 / 2)) := by
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ h12
  have hg : Integrable (fun x : ℝ ↦ (1 + a₁ * a₂) * (1 + (x + 1 / 2) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_add_right (1 / 2)).const_mul _
  refine hg.mono' ?_ (ae_of_all _ fun x ↦ ?_)
  · have : Measurable (env a₁ a₂) := by
      unfold env
      have h1 : Measurable fun x : ℝ ↦ max a₁ |x| := measurable_const.max measurable_id.abs
      have h2 : Measurable fun x : ℝ ↦ max a₂ |x| := measurable_const.max measurable_id.abs
      exact (measurable_const.div h1).mul (measurable_const.div h2)
    exact (this.comp (measurable_id.add_const _)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (env_pos ha₁ ha₂ _)]
    have := env_mul_le ha₁ h12 (x + 1 / 2)
    have hp : 0 < 1 + (x + 1 / 2) ^ 2 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hp]
    exact this

theorem memLp_testFn {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    MemLp (fun x : ℝ ↦ testFn a₁ a₂ x) 2 := by
  have ha₁ : 0 < a₁ := by linarith
  have ha₂ : 0 < a₂ := by linarith
  have hcont : Continuous fun x : ℝ ↦ testFn a₁ a₂ x :=
    (differentiable_testFn h₁ h₂).continuous.comp Complex.continuous_ofReal
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  obtain ⟨c, C, hc, hC, hbd⟩ := testFn_norm_real
  have hw := dens_isMultWeight h₁ h₂
  have hint := (integrable_env_shift ha₁ (by linarith : a₁ ≤ a₂)).const_mul (4 * C ^ 2)
  refine hint.mono' (hcont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have h1 := (hbd a₁ a₂ h₁ h₂ x).2
  have h2 := infDist_multGammaC_le hw (x + 1 / 2)
  have hd0 : 0 ≤ infDist (((x + 1 / 2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂)) := infDist_nonneg
  have hs := Real.sqrt_nonneg (env a₁ a₂ (x + 1 / 2))
  have h3 : ‖testFn a₁ a₂ x‖ ≤ C * Real.sqrt (env a₁ a₂ (x + 1 / 2)) * 2 := by
    refine h1.trans ?_
    have : infDist (((x + 1 / 2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂)) ≤ 2 := by
      have := h2; norm_num at this; linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h4 : ‖testFn a₁ a₂ x‖ ^ 2 ≤ (C * Real.sqrt (env a₁ a₂ (x + 1 / 2)) * 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h3 2
  refine h4.trans (le_of_eq ?_)
  have := Real.sq_sqrt (env_pos ha₁ ha₂ (x + 1 / 2)).le
  calc (C * Real.sqrt (env a₁ a₂ (x + 1 / 2)) * 2) ^ 2 =
      4 * C ^ 2 * (Real.sqrt (env a₁ a₂ (x + 1 / 2))) ^ 2 := by ring
    _ = _ := by rw [this]

theorem memPW_testFn {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    MemPW (testFn a₁ a₂) :=
  ⟨differentiable_testFn h₁ h₂, isExpTypeLE_testFn h₁ h₂, memLp_testFn h₁ h₂⟩

/-! ## Part D: norm lower bound and sampling upper bound -/

/-- **Mass.**  `‖f‖² ≥ c a₁ log(a₂/(4 a₁))` for an absolute `c > 0`. -/
theorem pwNormSq_testFn_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ a₁ a₂ : ℝ, 8 ≤ a₁ → 16 * a₁ ≤ a₂ →
      ENNReal.ofReal (c * a₁ * Real.log (a₂ / (4 * a₁))) ≤ pwNormSq (testFn a₁ a₂) := by
  sorry

/-- **Sampling sum.**  For admissible `ψ` vanishing on `(-∞, 0]`, there is `C` (depending on
`sup |ψ'|` only) such that, if `Λ(ψ)` is `η`-close to `ℤ + 1/2` on `[2a₁ + 3, a₂ - 3]`, then
`∑_{λ ∈ Λ(ψ)} |f(λ)|² ≤ C a₁ (1 + η² log(a₂/a₁))`. -/
theorem sampleSum_testFn_le {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ a₁ a₂ η : ℝ, 8 ≤ a₁ → 16 * a₁ ≤ a₂ → 0 ≤ η →
      (∀ l ∈ LambdaPsi ψ, l ∈ Icc (2 * a₁ + 3) (a₂ - 3) → ∃ k : ℤ, |l - (k + 1 / 2)| ≤ η) →
      sampleSum (LambdaPsi ψ) (testFn a₁ a₂) ≤
        ENNReal.ofReal (C * a₁ * (1 + η ^ 2 * Real.log (a₂ / a₁))) := by
  sorry

/-! ## Part E: the choice of the window -/

/-- **The window** (this is where `x ψ'(x) → 0` is used): for every `η > 0`, `s > 0`, `A₀`, there
are `a₁ ≥ A₀`, `a₂` with `16 a₁ ≤ a₂`, `log(a₂/(4a₁)) ≥ s`, such that `Λ(ψ)` is `η`-close to
`ℤ + 1/2` on `[2a₁ + 3, a₂ - 3]`. -/
theorem exists_window {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hsmall : Tendsto (fun x ↦ x * deriv ψ x) atTop (𝓝 0)) {η s : ℝ} (hη : 0 < η) (hs : 0 < s)
    (A₀ : ℝ) :
    ∃ a₁ a₂ : ℝ, A₀ ≤ a₁ ∧ 8 ≤ a₁ ∧ 16 * a₁ ≤ a₂ ∧ s ≤ Real.log (a₂ / (4 * a₁)) ∧
      ∀ l ∈ LambdaPsi ψ, l ∈ Icc (2 * a₁ + 3) (a₂ - 3) → ∃ k : ℤ, |l - (k + 1 / 2)| ≤ η :=
  T2ii.exists_window hψ h0 hsmall hη hs A₀

/-! ## Main theorem -/

/-- **Theorem 2 (ii)** (p. 801): if `ψ = 0` on `(-∞, 0]` and `ψ'(x) = o(1/x)`, then `Λ(ψ)` is not
sampling for `PW`. -/
theorem theorem2_ii (hPW : PaleyWienerThm) {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ)
    (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hsmall : Tendsto (fun x ↦ x * deriv ψ x) atTop (𝓝 0)) :
    ¬ IsSampling (LambdaPsi ψ) := by
  rintro ⟨A, B, hA, hS⟩
  obtain ⟨c, hc, hmass⟩ := pwNormSq_testFn_ge
  obtain ⟨C, hC, hsum⟩ := sampleSum_testFn_le hψ h0
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hAc : 0 < (A : ℝ) * c := mul_pos hA' hc
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set s : ℝ := max 1 (3 * C / ((A : ℝ) * c)) with hs
  have hs1 : 1 ≤ s := le_max_left _ _
  have hsC : 3 * C ≤ (A : ℝ) * c * s := by
    have h3 : 3 * C / ((A : ℝ) * c) ≤ s := le_max_right _ _
    rw [div_le_iff₀ hAc] at h3
    linarith
  have hD : 0 < 3 * C * (1 + Real.log 4) := by positivity
  set η : ℝ := Real.sqrt ((A : ℝ) * c / (3 * C * (1 + Real.log 4))) with hη
  have hηpos : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hη2 : η ^ 2 * (3 * C * (1 + Real.log 4)) = (A : ℝ) * c := by
    rw [hη, Real.sq_sqrt (by positivity)]; field_simp
  obtain ⟨a₁, a₂, -, h8, h16, hL, hwin⟩ := exists_window hψ h0 hsmall hηpos (by linarith : 0 < s) 8
  have h₁ : 1 ≤ a₁ := by linarith
  have h₂ : 2 * a₁ < a₂ := by linarith
  have hf := memPW_testFn h₁ h₂
  have hsamp := (hS _ hf).1
  have hm := hmass a₁ a₂ h8 h16
  have hsm := hsum a₁ a₂ η h8 h16 hηpos.le hwin
  set L := Real.log (a₂ / (4 * a₁)) with hLdef
  have hL1 : 1 ≤ L := hs1.trans hL
  have ha₁ : 0 < a₁ := by linarith
  have ha₂ : 0 < a₂ := by linarith
  have hch : (A : ℝ≥0∞) * ENNReal.ofReal (c * a₁ * L) ≤
      ENNReal.ofReal (C * a₁ * (1 + η ^ 2 * Real.log (a₂ / a₁))) :=
    (mul_le_mul' le_rfl hm).trans (hsamp.trans hsm)
  have hAeq : (A : ℝ≥0∞) = ENNReal.ofReal (A : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
  rw [hAeq, ← ENNReal.ofReal_mul hA'.le] at hch
  have hlogpos : 0 ≤ Real.log (a₂ / a₁) :=
    Real.log_nonneg (by rw [le_div_iff₀ ha₁]; linarith)
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg hC.le ha₁.le) (by nlinarith [sq_nonneg η]))).1 hch
  have hlogeq : Real.log (a₂ / a₁) = L + Real.log 4 := by
    rw [hLdef, show a₂ / a₁ = 4 * (a₂ / (4 * a₁)) by field_simp,
      Real.log_mul (by norm_num) (ne_of_gt (by positivity)), add_comm]
  have hlog_le : Real.log (a₂ / a₁) ≤ L * (1 + Real.log 4) := by
    rw [hlogeq]; nlinarith
  have h1 : C * a₁ * (1 + η ^ 2 * Real.log (a₂ / a₁)) ≤
      C * a₁ + C * a₁ * (η ^ 2 * (L * (1 + Real.log 4))) := by
    have : η ^ 2 * Real.log (a₂ / a₁) ≤ η ^ 2 * (L * (1 + Real.log 4)) :=
      mul_le_mul_of_nonneg_left hlog_le (sq_nonneg η)
    nlinarith [mul_pos hC ha₁]
  have h2 : C * a₁ * (η ^ 2 * (L * (1 + Real.log 4))) * 3 ≤ (A : ℝ) * c * a₁ * L := by
    have : η ^ 2 * (3 * C * (1 + Real.log 4)) * (a₁ * L) = (A : ℝ) * c * (a₁ * L) := by rw [hη2]
    nlinarith [this]
  have h3 : C * a₁ * 3 ≤ (A : ℝ) * c * a₁ * L := by
    have : 3 * C ≤ (A : ℝ) * c * L := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this ha₁.le]
  have hpos : 0 < (A : ℝ) * c * a₁ * L := by positivity
  nlinarith [hreal, h1, h2, h3, hpos]

end FF
