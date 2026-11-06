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
theorem multPrim_dens_stretch {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) {x : ℝ}
    (hx : x ∈ Icc (2 * a₁) a₂) : OCS.multPrim (dens a₁ a₂) x = x - 1 / 2 := by
  sorry

/-- Left zeros: for `1 ≤ a₁`, `j ≤ 0`, the barycentre `γ_j = j + 1/2` (the interval `I_j = [j, j+1]`
lies in `{m = 1}`), so `testFn` vanishes at every integer `j ≤ 0`. -/
theorem testFn_eq_zero_of_nonpos {a₁ a₂ : ℝ} (h₁ : 2 ≤ a₁) (h₂ : 2 * a₁ < a₂) (j : ℤ)
    (hj : j ≤ 0) : testFn a₁ a₂ (j : ℂ) = 0 := by
  sorry

/-- Stretch zeros: `Γ ∩ [2a₁ + 1, a₂ - 1] = ℤ + 1` (the zeros of `G`), so for the argument `x` of
the test function, `x ∈ [2a₁ + 3, a₂ - 3]`, `dist(x + 1/2, Γ) = dist(x, ℤ + 1/2)`. -/
theorem infDist_dens_stretch {a₁ a₂ : ℝ} (h₁ : 2 ≤ a₁) (h₂ : 2 * a₁ < a₂) {x : ℝ}
    (hx : x ∈ Icc (2 * a₁ + 3) (a₂ - 3)) :
    infDist (((x + 1 / 2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂)) =
      |x - 1 / 2 - round (x - 1 / 2)| := by
  sorry

/-- For every weight and real `y`, `dist(y, Γ) ≤ 1/a`. -/
theorem infDist_multGammaC_le {m : ℝ → ℝ} {a b : ℝ} (hw : OCS.IsMultWeight m a b) (y : ℝ) :
    infDist (y : ℂ) (OCS.multGammaC m) ≤ 1 / a := by
  sorry

/-! ## Part C: `testFn ∈ PW` and its size on `ℝ` -/

/-- **Two-sided estimate on `ℝ`** with absolute constants `0 < c ≤ C`:
`c √env(x + 1/2) · dist(x + 1/2, Γ) ≤ |f(x)| ≤ C √env(x + 1/2) · dist(x + 1/2, Γ)`
(uniform in `a₁, a₂` with `1 ≤ a₁`, `2 a₁ < a₂`). -/
theorem testFn_norm_real :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a₁ a₂ : ℝ, 1 ≤ a₁ → 2 * a₁ < a₂ → ∀ x : ℝ,
      c * Real.sqrt (env a₁ a₂ (x + 1 / 2)) *
          infDist (((x + 1 / 2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂)) ≤ ‖testFn a₁ a₂ x‖ ∧
      ‖testFn a₁ a₂ x‖ ≤ C * Real.sqrt (env a₁ a₂ (x + 1 / 2)) *
          infDist (((x + 1 / 2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂)) := by
  sorry

/-- `testFn` is entire. -/
theorem differentiable_testFn {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    Differentiable ℂ (testFn a₁ a₂) := by
  sorry

/-- `testFn` has exponential type `≤ π`: `|f(z)| ≤ C e^{π |Im z|}`. -/
theorem isExpTypeLE_testFn {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    IsExpTypeLE Real.pi (testFn a₁ a₂) := by
  sorry

/-- `∫ env < ∞` and `testFn ∈ L²(ℝ)`. -/
theorem memLp_testFn {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    MemLp (fun x : ℝ ↦ testFn a₁ a₂ x) 2 := by
  sorry

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
  sorry

end FF
