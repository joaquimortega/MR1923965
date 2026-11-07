import FourierFrames.Cited.Pavlov.BMOIntervalGrowth
import FourierFrames.Cited.Pavlov.PoissonBMOKernel

/-!
# Dyadic far-field estimates for the regularized conjugate Poisson integral
-/

open MeasureTheory Set Filter
noncomputable section
namespace FF.Pavlov

/-- Centered shells outside twice the target interval radius. -/
def bmoCenteredShell (c r : ℝ) (k : ℕ) : Set ℝ :=
  {t | (2:ℝ)^(k+1)*r ≤ |t-c| ∧ |t-c| ≤ (2:ℝ)^(k+2)*r}

lemma bmoCenteredShell_measurable (c r : ℝ) (k : ℕ) :
    MeasurableSet (bmoCenteredShell c r k) := by
  exact (isClosed_le continuous_const (continuous_id.sub continuous_const).abs).measurableSet.inter
    (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet

lemma bmoCenteredShell_subset (c r : ℝ) (k : ℕ) :
    bmoCenteredShell c r k ⊆ Icc (c-(2:ℝ)^(k+2)*r) (c+(2:ℝ)^(k+2)*r) := by
  intro t ht
  have h := abs_le.mp ht.2
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The difference kernel before division by `π`. -/
def conjugatePoissonFarFraction (y x c t : ℝ) : ℝ :=
  (x-t)/((x-t)^2+y^2) - (c-t)/((c-t)^2+y^2)

lemma continuous_conjugatePoissonFarFraction {y : ℝ} (hy : 0 < y) (x c : ℝ) :
    Continuous (conjugatePoissonFarFraction y x c) := by
  have hc (a : ℝ) : Continuous (fun t : ℝ ↦ (a-t)/((a-t)^2+y^2)) := by
    apply Continuous.div₀ (by fun_prop) (by fun_prop)
    intro t
    exact ne_of_gt (by positivity)
  exact (hc x).sub (hc c)

lemma abs_conjugatePoissonFarFraction_shell_le {y x c r : ℝ}
    (hy : 0 < y) (hr : 0 < r) (hx : |x-c| ≤ r) {k : ℕ} {t : ℝ}
    (ht : t ∈ bmoCenteredShell c r k) :
    |conjugatePoissonFarFraction y x c t| ≤
      2*r / (((2:ℝ)^(k+1)*r)^2) := by
  have hp : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  have hlo : 2*r ≤ (2:ℝ)^(k+1)*r := by rw [pow_succ]; nlinarith
  have hsep : 2*|x-c| ≤ |c-t| := by rw [abs_sub_comm c t]; linarith [ht.1]
  have hs : c-t ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hct
    change (2:ℝ)^(k+1)*r ≤ |t-c| ∧ _ at ht
    rw [← hct, sub_self, abs_zero] at ht
    linarith [ht.1]
  have hb := abs_conjugatePoissonFraction_shift_sub_le hy hs hsep
  have he : (c-t)+(x-c) = x-t := by ring
  rw [he] at hb
  apply hb.trans
  have hspos : 0 < (c-t)^2 := sq_pos_of_ne_zero hs
  have hrpos : 0 < ((2:ℝ)^(k+1)*r)^2 := by positivity
  apply (div_le_div_iff₀ hspos hrpos).mpr
  have hsq : ((2:ℝ)^(k+1)*r)^2 ≤ (c-t)^2 := by
    have hh : 0 ≤ (2:ℝ)^(k+1)*r := by positivity
    nlinarith [ht.1, sq_abs (t-c), sq_nonneg ((2:ℝ)^(k+1)*r-|t-c|)]
  nlinarith [mul_le_mul_of_nonneg_right hx (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hrpos.le),
    mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hr.le)]

/-- One dyadic shell contributes a summable geometric bound to the far field. -/
theorem integral_conjugatePoissonFarFraction_shell_le {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {M y x c r : ℝ}
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M)
    (hy : 0 < y) (hr : 0 < r) (hx : |x-c| ≤ r) (k : ℕ) :
    (∫ t in bmoCenteredShell c r k,
      |conjugatePoissonFarFraction y x c t *
        (u t-intervalMean u (c-2*r) (c+2*r))|) ≤
      4*((1:ℝ)/2)^k*(3+2*(k:ℝ))*M := by
  let m := intervalMean u (c-2*r) (c+2*r)
  let v := fun t ↦ u t-m
  let J := Icc (c-(2:ℝ)^(k+2)*r) (c+(2:ℝ)^(k+2)*r)
  let D := bmoCenteredShell c r k
  let B := 2*r / (((2:ℝ)^(k+1)*r)^2)
  have hv : LocallyIntegrable v := hu.sub (locallyIntegrable_const _)
  have hiJ : IntegrableOn v J := hv.integrableOn_isCompact isCompact_Icc
  have hiD : IntegrableOn v D := hiJ.mono_set (bmoCenteredShell_subset c r k)
  have hprod : LocallyIntegrable (fun t ↦ conjugatePoissonFarFraction y x c t*v t) :=
    LocallyIntegrable.continuous_mul (continuous_conjugatePoissonFarFraction hy x c) hv
  have hiprod : IntegrableOn (fun t ↦ conjugatePoissonFarFraction y x c t*v t) D :=
    (hprod.integrableOn_isCompact isCompact_Icc).mono_set (bmoCenteredShell_subset c r k)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg := integral_abs_sub_center_mean_le hu hosc
    (c := c) (r := 2*r) (by positivity) (k+1)
  have he : (2:ℝ)^(k+1)*(2*r) = (2:ℝ)^(k+2)*r := by
    rw [show k+2 = (k+1)+1 by omega, pow_succ]
    ring
  rw [he, ← integral_Icc_eq_integral_Ioc] at hg
  calc
    _ ≤ ∫ t in D, B*|v t| := by
      apply setIntegral_mono_on hiprod.abs (hiD.abs.const_mul _) (bmoCenteredShell_measurable c r k)
      intro t ht
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_conjugatePoissonFarFraction_shell_le hy hr hx ht)
        (abs_nonneg _)
    _ = B * ∫ t in D, |v t| := integral_const_mul _ _
    _ ≤ B * ∫ t in J, |v t| := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact setIntegral_mono_set hiJ.abs (Eventually.of_forall fun _ ↦ abs_nonneg _)
        (Eventually.of_forall (bmoCenteredShell_subset c r k))
    _ ≤ B * ((1+2*((k+1:ℕ):ℝ))*M * (2*((2:ℝ)^(k+2)*r))) :=
      mul_le_mul_of_nonneg_left hg hB
    _ = _ := by
      dsimp [B]
      push_cast
      simp only [pow_succ, div_pow]
      field_simp
      ring

lemma hasSum_bmoFarBound (M : ℝ) :
    HasSum (fun k : ℕ ↦ 4*((1:ℝ)/2)^k*(3+2*(k:ℝ))*M) (40*M) := by
  have hg : HasSum (fun k : ℕ ↦ ((1:ℝ)/2)^k) 2 := by
    convert hasSum_geometric_of_norm_lt_one (ξ := (1:ℝ)/2) (by norm_num) using 1
    norm_num
  have hk : HasSum (fun k : ℕ ↦ (k:ℝ)*((1:ℝ)/2)^k) 2 := by
    convert hasSum_pow_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
      (r := (1:ℝ)/2) (by norm_num) using 1 <;> norm_num [Finset.sum_range_succ, Nat.stirlingSecond]
  convert (hg.mul_left (12*M)).add (hk.mul_left (8*M)) using 1
  · funext k; ring
  · ring

/-- A countable cover bounds the absolute integral by summable local bounds. -/
theorem integrableOn_and_integral_abs_le_of_cover {f : ℝ → ℝ} {s : ℕ → Set ℝ}
    {A : Set ℝ} {B : ℕ → ℝ} (hi : ∀ k, IntegrableOn f (s k))
    (hB : ∀ k, 0 ≤ B k) (hsum : Summable B)
    (hbound : ∀ k, (∫ t in s k, |f t|) ≤ B k) (hcover : A ⊆ ⋃ k, s k) :
    IntegrableOn f A ∧ (∫ t in A, |f t|) ≤ ∑' k, B k := by
  have hsumf : Summable (fun k ↦ ∫ t in s k, ‖f t‖) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) _ hsum
    simpa only [Real.norm_eq_abs] using hbound
  have hU := integrableOn_iUnion_of_summable_integral_norm hi hsumf
  have hA := hU.mono_set hcover
  refine ⟨hA, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg hB)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hA.abs
    (Eventually.of_forall fun _ ↦ abs_nonneg _), ENNReal.ofReal_tsum_of_nonneg hB hsum]
  calc
    _ ≤ ∫⁻ t in ⋃ k, s k, ENNReal.ofReal |f t| :=
      lintegral_mono_set hcover
    _ ≤ ∑' k, ∫⁻ t in s k, ENNReal.ofReal |f t| := lintegral_iUnion_le _ _
    _ = ∑' k, ENNReal.ofReal (∫ t in s k, |f t|) := by
      apply tsum_congr
      intro k
      exact (ofReal_integral_eq_lintegral_ofReal (hi k).abs
        (Eventually.of_forall fun _ ↦ abs_nonneg _)).symm
    _ ≤ _ := ENNReal.tsum_le_tsum (fun k ↦ ENNReal.ofReal_le_ofReal (hbound k))

/-- Every point outside the doubled interval belongs to a dyadic far shell. -/
lemma bmoCenteredShell_cover {c r : ℝ} (hr : 0 < r) :
    (Icc (c-2*r) (c+2*r))ᶜ ⊆ ⋃ k, bmoCenteredShell c r k := by
  intro t ht
  have hlo : 2*r < |t-c| := by
    by_contra h
    have habs := abs_le.mp (le_of_not_gt h)
    exact ht ⟨by linarith [habs.1], by linarith [habs.2]⟩
  have hratio : 1 ≤ |t-c|/(2*r) :=
    (le_div_iff₀ (by positivity)).mpr (by linarith)
  obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ)<2)
  have h₁ := (le_div_iff₀ (by positivity : 0 < 2*r)).mp hk₁
  have h₂ := (div_lt_iff₀ (by positivity : 0 < 2*r)).mp hk₂
  apply mem_iUnion.mpr
  refine ⟨k, ?_, ?_⟩
  · rw [pow_succ]
    nlinarith
  · rw [show k+2 = (k+1)+1 by omega, pow_succ]
    nlinarith

/-- The far-field integral is absolutely convergent and uniformly bounded. -/
theorem conjugatePoissonFarFraction_integrable_bound {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {M y x c r : ℝ} (hM : 0 ≤ M)
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M)
    (hy : 0 < y) (hr : 0 < r) (hx : |x-c| ≤ r) :
    IntegrableOn (fun t ↦ conjugatePoissonFarFraction y x c t *
      (u t-intervalMean u (c-2*r) (c+2*r))) (Icc (c-2*r) (c+2*r))ᶜ ∧
    (∫ t in (Icc (c-2*r) (c+2*r))ᶜ,
      |conjugatePoissonFarFraction y x c t *
        (u t-intervalMean u (c-2*r) (c+2*r))|) ≤ 40*M := by
  let f := fun t ↦ conjugatePoissonFarFraction y x c t *
    (u t-intervalMean u (c-2*r) (c+2*r))
  have hv : LocallyIntegrable (fun t ↦ u t-intervalMean u (c-2*r) (c+2*r)) :=
    hu.sub (locallyIntegrable_const _)
  have hf : LocallyIntegrable f :=
    LocallyIntegrable.continuous_mul (continuous_conjugatePoissonFarFraction hy x c) hv
  have hi : ∀ k, IntegrableOn f (bmoCenteredShell c r k) := by
    intro k
    exact (hf.integrableOn_isCompact isCompact_Icc).mono_set (bmoCenteredShell_subset c r k)
  have hb (k : ℕ) : 0 ≤ 4*((1:ℝ)/2)^k*(3+2*(k:ℝ))*M := by positivity
  have hout := integrableOn_and_integral_abs_le_of_cover hi hb
    (hasSum_bmoFarBound M).summable
    (integral_conjugatePoissonFarFraction_shell_le hu hosc hy hr hx)
    (bmoCenteredShell_cover hr)
  rw [(hasSum_bmoFarBound M).tsum_eq] at hout
  exact hout

end FF.Pavlov
