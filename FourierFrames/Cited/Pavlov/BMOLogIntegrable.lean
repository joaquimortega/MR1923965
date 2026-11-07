import FourierFrames.Cited.Pavlov.Basic
import FourierFrames.Cited.Pavlov.BMOIntervalGrowth

/-!
# Weighted integrability of real BMO functions
-/

open MeasureTheory Set Filter

noncomputable section
namespace FF.Pavlov

/-- Closed dyadic shells; their harmless overlaps are endpoints. -/
def bmoDyadicShell (k : ℕ) : Set ℝ :=
  {t | (2:ℝ)^k ≤ |t| ∧ |t| ≤ (2:ℝ)^(k+1)}

lemma bmoDyadicShell_measurable (k : ℕ) : MeasurableSet (bmoDyadicShell k) := by
  exact (isClosed_le continuous_const continuous_abs).measurableSet.inter
    (isClosed_le continuous_abs continuous_const).measurableSet

lemma bmoDyadicShell_subset (k : ℕ) :
    bmoDyadicShell k ⊆ Icc (-(2:ℝ)^(k+1)) ((2:ℝ)^(k+1)) := by
  intro t ht
  exact abs_le.mp ht.2

lemma bmo_weight_locallyIntegrable {u : ℝ → ℝ} (hu : LocallyIntegrable u) :
    LocallyIntegrable (fun t ↦ u t/(1+t^2)) := by
  have hc₀ : Continuous (fun t : ℝ ↦ 1+t^2) := by fun_prop
  have hc : Continuous (fun t : ℝ ↦ (1+t^2)⁻¹) :=
    hc₀.inv₀ (fun t ↦ ne_of_gt (by positivity))
  simpa only [div_eq_mul_inv] using LocallyIntegrable.mul_continuous hc hu

lemma integral_bmo_weight_shell_le {u : ℝ → ℝ} (hu : LocallyIntegrable u) (k : ℕ) :
    (∫ t in bmoDyadicShell k, ‖u t/(1+t^2)‖) ≤
      ((2:ℝ)^k)^(-2:ℤ) *
        ∫ t in Icc (-(2:ℝ)^(k+1)) ((2:ℝ)^(k+1)), |u t| := by
  let D := bmoDyadicShell k
  let J := Icc (-(2:ℝ)^(k+1)) ((2:ℝ)^(k+1))
  have hiJ : IntegrableOn u J := hu.integrableOn_isCompact isCompact_Icc
  have hiD : IntegrableOn u D := hiJ.mono_set (bmoDyadicShell_subset k)
  have hw : IntegrableOn (fun t ↦ u t/(1+t^2)) D :=
    ((bmo_weight_locallyIntegrable hu).integrableOn_isCompact isCompact_Icc).mono_set
      (bmoDyadicShell_subset k)
  have hp : 0 < (2:ℝ)^k := by positivity
  have hcoef : 0 ≤ ((2:ℝ)^k)^(-2:ℤ) := by positivity
  calc
    _ ≤ ∫ t in D, ((2:ℝ)^k)^(-2:ℤ) * |u t| := by
      apply setIntegral_mono_on hw.norm (hiD.abs.const_mul _) (bmoDyadicShell_measurable k)
      intro t ht
      have hsq : ((2:ℝ)^k)^2 ≤ t^2 := by nlinarith [sq_abs t, ht.1]
      have he : ((2:ℝ)^k)^(-2:ℤ) = (((2:ℝ)^k)^2)⁻¹ := by simp
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < 1+t^2), he]
      rw [div_eq_mul_inv, mul_comm |u t|]
      exact mul_le_mul_of_nonneg_right
        (inv_le_inv₀ (by positivity) (by positivity) |>.mpr (by linarith)) (abs_nonneg _)
    _ = ((2:ℝ)^k)^(-2:ℤ) * ∫ t in D, |u t| := integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      exact setIntegral_mono_set hiJ.abs (Eventually.of_forall fun _ ↦ abs_nonneg _)
        (Eventually.of_forall (bmoDyadicShell_subset k))

lemma integral_bmo_weight_shell_le_geometric {u : ℝ → ℝ} (hu : LocallyIntegrable u)
    {M : ℝ} (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M) (k : ℕ) :
    (∫ t in bmoDyadicShell k, ‖u t/(1+t^2)‖) ≤
      4 * ((1:ℝ)/2)^k * ((3+2*(k:ℝ))*M + |intervalMean u (-1) 1|) := by
  apply (integral_bmo_weight_shell_le hu k).trans
  have hb := mul_le_mul_of_nonneg_left (integral_abs_center_pow_le hu hosc (k+1))
    (show 0 ≤ ((2:ℝ)^k)^(-2:ℤ) by positivity)
  apply hb.trans_eq
  push_cast
  simp only [zpow_neg, zpow_ofNat, pow_succ, div_pow]
  field_simp
  ring

/-- Real BMO functions are absolutely integrable against the half-plane boundary weight. -/
theorem memBMO_logIntegrable {u : ℝ → ℝ} (hu : FF.MemBMO u) : LogIntegrable u := by
  obtain ⟨hu, M, hM⟩ := hu
  let m := intervalMean u (-1) 1
  have hg : Summable (fun k : ℕ ↦ ((1:ℝ)/2)^k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hk : Summable (fun k : ℕ ↦ (k:ℝ)*((1:ℝ)/2)^k) := by
    simpa only [pow_one] using
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (1:ℝ)/2) (by norm_num)
  have hs : Summable (fun k : ℕ ↦
      4*((1:ℝ)/2)^k*((3+2*(k:ℝ))*M+|m|)) := by
    convert (hg.mul_left (4*(3*M+|m|))).add (hk.mul_left (8*M)) using 1
    funext k
    ring
  have hsum : Summable (fun k : ℕ ↦ ∫ t in bmoDyadicShell k, ‖u t/(1+t^2)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun k ↦ integral_bmo_weight_shell_le_geometric hu hM k) hs
  have hi : ∀ k, IntegrableOn (fun t ↦ u t/(1+t^2)) (bmoDyadicShell k) := by
    intro k
    exact ((bmo_weight_locallyIntegrable hu).integrableOn_isCompact isCompact_Icc).mono_set
      (bmoDyadicShell_subset k)
  have hcover : (univ : Set ℝ) ⊆ Icc (-1) 1 ∪ ⋃ k, bmoDyadicShell k := by
    intro t _
    by_cases ht : |t| ≤ 1
    · exact Or.inl (abs_le.mp ht)
    · obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near (le_of_not_ge ht) (by norm_num : (1:ℝ)<2)
      exact Or.inr (mem_iUnion.mpr ⟨k, hk₁, hk₂.le⟩)
  have hinit : IntegrableOn (fun t ↦ u t/(1+t^2)) (Icc (-1) 1) :=
    (bmo_weight_locallyIntegrable hu).integrableOn_isCompact isCompact_Icc
  exact integrableOn_univ.mp ((hinit.union
    (integrableOn_iUnion_of_summable_integral_norm hi hsum)).mono_set hcover)

end FF.Pavlov
