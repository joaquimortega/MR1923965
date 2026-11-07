import FourierFrames.Cited.Pavlov.BMO
import FourierFrames.Cited.Pavlov.BMOLogIntegrable
import FourierFrames.Cited.Pavlov.PoissonBMOFar
import FourierFrames.Cited.Pavlov.Schwarz
import FourierFrames.Cited.Pavlov.PoissonBMONear

/-!
# Uniform BMO bounds for normalized conjugate Poisson integrals

The near and far estimates use ordinary absolutely convergent integrals.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace FF.Pavlov

/-- Difference of two normalized integrands is the unregularized kernel difference. -/
theorem conjugatePoisson_difference_integrable {u : ℝ → ℝ} {y x c : ℝ}
    (hx : Integrable (fun t ↦ ((x-t)/((x-t)^2+y^2)+t/(1+t^2))*u t))
    (hc : Integrable (fun t ↦ ((c-t)/((c-t)^2+y^2)+t/(1+t^2))*u t)) :
    Integrable (fun t ↦ conjugatePoissonFarFraction y x c t*u t) := by
  apply (hx.sub hc).congr
  filter_upwards with t
  simp only [Pi.sub_apply, conjugatePoissonFarFraction]
  ring

/-- Centered differences eliminate the regularization without splitting divergent integrals. -/
theorem conjugatePoisson_sub_eq_integral {u : ℝ → ℝ} {y x c : ℝ}
    (hx : Integrable (fun t ↦ ((x-t)/((x-t)^2+y^2)+t/(1+t^2))*u t))
    (hc : Integrable (fun t ↦ ((c-t)/((c-t)^2+y^2)+t/(1+t^2))*u t)) :
    conjugatePoisson u y x-conjugatePoisson u y c =
      Real.pi⁻¹ * ∫ t, conjugatePoissonFarFraction y x c t*u t := by
  unfold conjugatePoisson
  rw [← mul_sub, ← integral_sub hx hc]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [conjugatePoissonFarFraction]
  ring

/-- The centered difference splits into its local and distant ordinary integrals. -/
theorem conjugatePoisson_sub_eq_near_add_far {u : ℝ → ℝ} {y x c : ℝ} {J : Set ℝ}
    (hJ : MeasurableSet J)
    (hx : Integrable (fun t ↦ ((x-t)/((x-t)^2+y^2)+t/(1+t^2))*u t))
    (hc : Integrable (fun t ↦ ((c-t)/((c-t)^2+y^2)+t/(1+t^2))*u t)) :
    conjugatePoisson u y x-conjugatePoisson u y c =
      Real.pi⁻¹ * (∫ t in J, conjugatePoissonFarFraction y x c t*u t) +
      Real.pi⁻¹ * (∫ t in Jᶜ, conjugatePoissonFarFraction y x c t*u t) := by
  rw [conjugatePoisson_sub_eq_integral hx hc, ← mul_add,
    integral_add_compl hJ (conjugatePoisson_difference_integrable hx hc)]

/-- An integrable near contribution and a uniformly bounded remainder control oscillation. -/
theorem meanOsc_le_of_near_and_bounded {f n : ℝ → ℝ}
    (hf : LocallyIntegrable f) {a b : ℝ} (hn : IntervalIntegrable n volume a b)
    (hab : a < b) {c A B : ℝ}
    (hcmp : ∀ x ∈ Icc a b, |f x-c| ≤ |n x|+B)
    (hnear : (∫ x in a..b, |n x|) ≤ A*(b-a)) :
    meanOsc f a b ≤ 2*(A+B) := by
  have hi : IntervalIntegrable f volume a b :=
    (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hcomp : (∫ x in a..b, |f x-c|) ≤ (A+B)*(b-a) := by
    calc
      _ ≤ ∫ x in a..b, (|n x|+B) := by
        exact intervalIntegral.integral_mono_on hab.le (hi.sub intervalIntegrable_const).abs
          (hn.abs.add intervalIntegrable_const) hcmp
      _ = (∫ x in a..b, |n x|)+(b-a)*B := by
        rw [intervalIntegral.integral_add hn.abs intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul]
      _ ≤ A*(b-a)+(b-a)*B := add_le_add_left hnear _
      _ = _ := by ring
  apply (meanOsc_le_twice_comparison hf hab c).trans
  have hL : 0 < b-a := sub_pos.mpr hab
  have hb := mul_le_mul_of_nonneg_left hcomp (inv_nonneg.mpr hL.le)
  have he : (b-a)⁻¹*((A+B)*(b-a)) = A+B := by field_simp
  rw [he] at hb
  linarith

/-- Exact near/far decomposition with a finite interval-dependent comparison constant. -/
theorem conjugatePoisson_eq_near_add_far {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) (hlog : LogIntegrable u) {y : ℝ} (hy : 0 < y)
    (c r x : ℝ) :
    conjugatePoisson u y x -
      (conjugatePoisson (fun t ↦ u t-intervalMean u (c-2*r) (c+2*r)) y c -
        nearConjugatePoisson u y c r c) =
      nearConjugatePoisson u y c r x + Real.pi⁻¹ *
        ∫ t in (Icc (c-2*r) (c+2*r))ᶜ, conjugatePoissonFarFraction y x c t *
          (u t-intervalMean u (c-2*r) (c+2*r)) := by
  let m := intervalMean u (c-2*r) (c+2*r)
  let v := fun t ↦ u t-m
  have hvlog : LogIntegrable v := hlog.sub_const m
  have hs := conjugatePoisson_sub_eq_near_add_far (J := Icc (c-2*r) (c+2*r))
    measurableSet_Icc (conjugatePoisson_integrand_integrable hvlog hy x)
    (conjugatePoisson_integrand_integrable hvlog hy c)
  have hn : Real.pi⁻¹ * (∫ t in Icc (c-2*r) (c+2*r),
      conjugatePoissonFarFraction y x c t*v t) =
      nearConjugatePoisson u y c r x-nearConjugatePoisson u y c r c := by
    rw [nearConjugatePoisson_eq_fraction, nearConjugatePoisson_eq_fraction,
      ← mul_sub, ← integral_sub (nearConjugatePoisson_fraction_integrable hu hy c r x)
        (nearConjugatePoisson_fraction_integrable hu hy c r c)]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    dsimp [v, m, conjugatePoissonFarFraction]
    ring
  rw [conjugatePoisson_sub_const hlog m hy x, hn] at hs
  dsimp [v, m] at hs
  linarith

/-- The conjugate Poisson BMO bound is independent of the positive height. -/
theorem meanOsc_conjugatePoisson_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ), LocallyIntegrable u →
      ∀ M : ℝ, 0 < M →
      (∀ a b : ℝ, a < b → meanOsc u a b ≤ M) →
      ∀ y : ℝ, 0 < y → ∀ a b : ℝ, a < b →
        meanOsc (conjugatePoisson u y) a b ≤ C*M := by
  obtain ⟨C, hC, hnear⟩ := bmo_near_conjugatePoisson_bound
  refine ⟨2*(C+40/Real.pi), by positivity, ?_⟩
  intro u hu M hM hosc y hy a b hab
  have hlog := memBMO_logIntegrable (show FF.MemBMO u from ⟨hu, M, hosc⟩)
  have hf : LocallyIntegrable (conjugatePoisson u y) :=
    (continuous_conjugatePoisson hlog hy).locallyIntegrable
  let c := (a+b)/2
  let r := (b-a)/2
  have hr : 0 < r := by dsimp [r]; linarith
  have ha : c-r = a := by dsimp [c, r]; ring
  have hb : c+r = b := by dsimp [c, r]; ring
  obtain ⟨hni, hnav⟩ := hnear u hu M hM hosc y hy c r hr
  have hN : IntervalIntegrable (nearConjugatePoisson u y c r) volume a b := by
    rw [ha, hb] at hni
    exact (show IntegrableOn (nearConjugatePoisson u y c r) (uIcc a b) by
      simpa only [uIcc_of_le hab.le] using hni).intervalIntegrable
  have hNbound : (∫ x in a..b, |nearConjugatePoisson u y c r x|) ≤ (C*M)*(b-a) := by
    rw [ha, hb] at hnav
    have hh := (inv_mul_le_iff₀ (by positivity : 0 < 2*r)).mp hnav
    have he : b-a = 2*r := by dsimp [r]; ring
    rw [he]
    nlinarith
  let A := conjugatePoisson (fun t ↦ u t-intervalMean u (c-2*r) (c+2*r)) y c -
    nearConjugatePoisson u y c r c
  have hcmp : ∀ x ∈ Icc a b, |conjugatePoisson u y x-A| ≤
      |nearConjugatePoisson u y c r x| + (40/Real.pi)*M := by
    intro x hx
    have hxc : |x-c| ≤ r := by
      apply abs_le.mpr
      dsimp [c, r]
      constructor <;> linarith [hx.1, hx.2]
    obtain ⟨hfi, hfb⟩ := conjugatePoissonFarFraction_integrable_bound hu hM.le hosc hy hr hxc
    have hnorm : |Real.pi⁻¹ *
        ∫ t in (Icc (c-2*r) (c+2*r))ᶜ, conjugatePoissonFarFraction y x c t *
          (u t-intervalMean u (c-2*r) (c+2*r))| ≤ (40/Real.pi)*M := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr Real.pi_pos)]
      have hi := norm_integral_le_integral_norm
        (f := fun t ↦ conjugatePoissonFarFraction y x c t *
          (u t-intervalMean u (c-2*r) (c+2*r)))
        (μ := volume.restrict (Icc (c-2*r) (c+2*r))ᶜ)
      simp only [Real.norm_eq_abs] at hi
      have hh := mul_le_mul_of_nonneg_left (hi.trans hfb) (inv_nonneg.mpr Real.pi_pos.le)
      convert hh using 1
      ring
    change |conjugatePoisson u y x-
      (conjugatePoisson (fun t ↦ u t-intervalMean u (c-2*r) (c+2*r)) y c -
        nearConjugatePoisson u y c r c)| ≤ _
    rw [conjugatePoisson_eq_near_add_far hu hlog hy c r x]
    exact (abs_add_le _ _).trans (add_le_add_right hnorm _)
  have hout := meanOsc_le_of_near_and_bounded hf hN hab hcmp hNbound
  convert hout using 1
  ring

/-- A single BMO witness controls all positive-height conjugate Poisson integrals. -/
theorem conjugatePoisson_uniform_bmo {u : ℝ → ℝ} (hu : FF.MemBMO u) :
    ∃ M : ℝ, 0 < M ∧ ∀ y : ℝ, 0 < y →
      LocallyIntegrable (conjugatePoisson u y) ∧
      ∀ a b : ℝ, a < b → meanOsc (conjugatePoisson u y) a b ≤ M := by
  obtain ⟨C, hC, hb⟩ := meanOsc_conjugatePoisson_le
  obtain ⟨hlocal, M, hM⟩ := hu
  let N := max M 1
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ N := by
    intro a b hab
    exact (hM a b hab).trans (le_max_left M 1)
  have hlog := memBMO_logIntegrable (show FF.MemBMO u from ⟨hlocal, M, hM⟩)
  refine ⟨C*N, mul_pos hC hN, ?_⟩
  intro y hy
  exact ⟨(continuous_conjugatePoisson hlog hy).locallyIntegrable,
    hb u hlocal N hN hosc y hy⟩

theorem memBMO_conjugatePoisson {u : ℝ → ℝ} (hu : FF.MemBMO u)
    {y : ℝ} (hy : 0 < y) : FF.MemBMO (conjugatePoisson u y) := by
  obtain ⟨M, _, hM⟩ := conjugatePoisson_uniform_bmo hu
  exact ⟨(hM y hy).1, M, (hM y hy).2⟩

/-- The uniform estimate passes to any a.e. limit along positive heights. -/
theorem memBMO_of_conjugatePoisson_ae_limit {u g : ℝ → ℝ} (hu : FF.MemBMO u)
    (hg : LocallyIntegrable g) {y : ℕ → ℝ} (hy : ∀ n, 0 < y n)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ conjugatePoisson u (y n) t) atTop (𝓝 (g t))) :
    FF.MemBMO g := by
  obtain ⟨M, _, hM⟩ := conjugatePoisson_uniform_bmo hu
  exact memBMO_of_ae_tendsto (fun n ↦ (hM (y n) (hy n)).1) hg hlim
    (fun n ↦ (hM (y n) (hy n)).2)

end FF.Pavlov
