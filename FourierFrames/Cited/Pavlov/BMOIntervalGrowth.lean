import FourierFrames.Cited.JohnNirenberg

/-!
# Growth of BMO interval means

Restriction to nested intervals controls the difference of their means.
-/

open MeasureTheory Set Filter

noncomputable section

namespace FF.Pavlov

/-- Difference of means on nested intervals, with their length ratio explicit. -/
theorem abs_intervalMean_sub_le_length_ratio {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {M a b c d : ℝ}
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M)
    (hab : a < b) (hcd : c < d) (hca : c ≤ a) (hbd : b ≤ d) :
    |intervalMean u a b - intervalMean u c d| ≤ (b-a)⁻¹ * (M*(d-c)) := by
  have hi₀ : IntegrableOn (fun t ↦ u t - intervalMean u c d) (Icc c d) :=
    (hu.integrableOn_isCompact isCompact_Icc).sub
      (integrableOn_const isCompact_Icc.measure_lt_top.ne)
  have hi : IntegrableOn (fun t ↦ |u t - intervalMean u c d|) (Ioc c d) := by
    have hi₁ : IntegrableOn (fun t ↦ |u t - intervalMean u c d|) (Icc c d) := hi₀.abs
    exact hi₁.mono_set Ioc_subset_Icc_self
  have hsub : Ioc a b ⊆ Ioc c d := by
    intro x hx
    exact ⟨lt_of_le_of_lt hca hx.1, hx.2.trans hbd⟩
  calc
    _ ≤ (b-a)⁻¹ * ∫ t in Ioc a b, |u t - intervalMean u c d| :=
      FF.abs_intervalMean_sub_le hu hab _
    _ ≤ (b-a)⁻¹ * ∫ t in Ioc c d, |u t - intervalMean u c d| := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sub_pos.mpr hab).le)
      exact setIntegral_mono_set hi (Eventually.of_forall fun _ ↦ abs_nonneg _) (Eventually.of_forall hsub)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sub_pos.mpr hab).le)
      exact FF.integral_osc_le hosc hcd

/-- A doubling of a centered interval changes its BMO mean by at most `2M`. -/
theorem abs_intervalMean_center_double_sub_le {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {M c r : ℝ}
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M) (hr : 0 < r) :
    |intervalMean u (c-r) (c+r) - intervalMean u (c-2*r) (c+2*r)| ≤ 2*M := by
  have hb := abs_intervalMean_sub_le_length_ratio hu hosc
    (show c-r < c+r by linarith) (show c-2*r < c+2*r by linarith)
    (show c-2*r ≤ c-r by linarith) (show c+r ≤ c+2*r by linarith)
  convert hb using 1
  field_simp [hr.ne']
  ring

/-- Dyadic expansion of a centered interval has at most linear mean growth. -/
theorem abs_intervalMean_center_pow_sub_le {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {M c r : ℝ}
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M) (hr : 0 < r) (k : ℕ) :
    |intervalMean u (c-(2:ℝ)^k*r) (c+(2:ℝ)^k*r) -
      intervalMean u (c-r) (c+r)| ≤ 2*(k:ℝ)*M := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := abs_intervalMean_center_double_sub_le (c := c) hu hosc
      (show 0 < (2:ℝ)^k*r by positivity)
    have he : 2*((2:ℝ)^k*r) = (2:ℝ)^(k+1)*r := by rw [pow_succ]; ring
    rw [he] at hstep
    have ht := abs_sub_le
      (intervalMean u (c-(2:ℝ)^(k+1)*r) (c+(2:ℝ)^(k+1)*r))
      (intervalMean u (c-(2:ℝ)^k*r) (c+(2:ℝ)^k*r))
      (intervalMean u (c-r) (c+r))
    rw [abs_sub_comm] at hstep
    push_cast
    linarith

/-- Integral oscillation about a fixed smaller centered interval mean. -/
theorem integral_abs_sub_center_mean_le {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {M c r : ℝ}
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M) (hr : 0 < r) (k : ℕ) :
    (∫ t in Ioc (c-(2:ℝ)^k*r) (c+(2:ℝ)^k*r),
      |u t - intervalMean u (c-r) (c+r)|) ≤
        (1+2*(k:ℝ))*M * (2*((2:ℝ)^k*r)) := by
  let a := c-(2:ℝ)^k*r
  let b := c+(2:ℝ)^k*r
  let m := intervalMean u (c-r) (c+r)
  have hab : a < b := by
    have hp : 0 < (2:ℝ)^k*r := by positivity
    dsimp [a, b]
    linarith
  have hi (v : ℝ) : IntegrableOn (fun t ↦ |u t-v|) (Ioc a b) := by
    have h₀ : IntegrableOn (fun t ↦ u t-v) (Ioc a b) :=
      (hu.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self |>.sub
        (integrableOn_const (by simp))
    exact h₀.abs
  have hj : IntegrableOn (fun t ↦ |u t-intervalMean u a b| +
      |intervalMean u a b-m|) (Ioc a b) :=
    (hi _).add (integrableOn_const (by simp))
  have hg : |intervalMean u a b-m| ≤ 2*(k:ℝ)*M :=
    abs_intervalMean_center_pow_sub_le hu hosc hr k
  calc
    _ ≤ ∫ t in Ioc a b, (|u t-intervalMean u a b| + |intervalMean u a b-m|) := by
      exact setIntegral_mono_on (hi m) hj measurableSet_Ioc
        (fun t _ ↦ abs_sub_le (u t) (intervalMean u a b) m)
    _ = (∫ t in Ioc a b, |u t-intervalMean u a b|) +
        (b-a)*|intervalMean u a b-m| := by
      rw [integral_add (hi _) (integrableOn_const (by simp)), setIntegral_const]
      simp [Real.volume_real_Ioc, hab.le, smul_eq_mul]
    _ ≤ M*(b-a) + (b-a)*(2*(k:ℝ)*M) := by
      exact add_le_add (FF.integral_osc_le hosc hab)
        (mul_le_mul_of_nonneg_left hg (sub_pos.mpr hab).le)
    _ = _ := by dsimp [a, b]; ring

/-- Absolute integrals on centered dyadic intervals grow at most logarithmically in radius. -/
theorem integral_abs_center_pow_le {u : ℝ → ℝ} (hu : LocallyIntegrable u) {M : ℝ}
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M) (k : ℕ) :
    (∫ t in Icc (-(2:ℝ)^k) ((2:ℝ)^k), |u t|) ≤
      ((1+2*(k:ℝ))*M + |intervalMean u (-1) 1|) * (2*(2:ℝ)^k) := by
  let a := -(2:ℝ)^k
  let b := (2:ℝ)^k
  let m := intervalMean u (-1) 1
  have hp : 0 < (2:ℝ)^k := by positivity
  have hab : a < b := by dsimp [a, b]; linarith
  have hu₀ : IntegrableOn u (Ioc a b) :=
    (hu.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hi₀ : IntegrableOn (fun t ↦ u t-m) (Ioc a b) :=
    hu₀.sub (integrableOn_const (by simp))
  have hi : IntegrableOn (fun t ↦ |u t-m| + |m|) (Ioc a b) :=
    hi₀.abs.add (integrableOn_const (by simp))
  have hg := integral_abs_sub_center_mean_le hu hosc (c := 0) (r := 1) (by norm_num) k
  simp only [zero_sub, zero_add, mul_one] at hg
  rw [integral_Icc_eq_integral_Ioc]
  calc
    _ ≤ ∫ t in Ioc a b, (|u t-m| + |m|) := by
      apply setIntegral_mono_on hu₀.abs hi measurableSet_Ioc
      intro t _
      simpa only [sub_zero] using abs_sub_le (u t) m 0
    _ = (∫ t in Ioc a b, |u t-m|) + (b-a)*|m| := by
      rw [integral_add hi₀.abs (integrableOn_const (by simp)), setIntegral_const]
      simp [Real.volume_real_Ioc, hab.le, smul_eq_mul]
    _ ≤ ((1+2*(k:ℝ))*M)*(2*(2:ℝ)^k) + (b-a)*|m| :=
      add_le_add_left hg _
    _ = _ := by dsimp [a, b, m]; ring

end FF.Pavlov
