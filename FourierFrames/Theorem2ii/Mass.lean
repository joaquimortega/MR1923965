import FourierFrames.Defs

/-!
# M09 helper: integrals of the distance to `ℤ + 1/2`

`dev x = dist(x, ℤ + 1/2) = |fract x - 1/2|`, with `∫_k^{k+1} dev² = 1/12`, and the harmonic-sum
comparison used for the lower bound on the mass of the test function.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped Interval

noncomputable section

namespace FF

namespace T2ii

/-- `dev x = |fract x - 1/2|`, the distance from `x` to `ℤ + 1/2`. -/
def dev (x : ℝ) : ℝ := |Int.fract x - 1 / 2|

lemma dev_eq_round (x : ℝ) : |x - 1 / 2 - round (x - 1 / 2)| = dev x := by
  have : round (x - 1 / 2) = ⌊x⌋ := by rw [round_eq]; congr 1; ring
  rw [this]; unfold dev; rw [Int.fract]; congr 1; ring

lemma measurable_dev : Measurable dev := by
  unfold dev
  exact (measurable_fract.sub_const _).abs

lemma dev_nonneg (x : ℝ) : 0 ≤ dev x := abs_nonneg _

lemma dev_le (x : ℝ) : dev x ≤ 1 / 2 := by
  unfold dev
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [abs_le]; constructor <;> linarith

lemma intervalIntegrable_dev_sq (u v : ℝ) :
    IntervalIntegrable (fun x ↦ dev x ^ 2) volume u v := by
  have hbound : ∀ w z : ℝ, IntegrableOn (fun x ↦ dev x ^ 2) (Ioc w z) := by
    intro w z
    refine Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ ?_
    · exact (measurable_dev.pow_const 2).aestronglyMeasurable
    · refine ae_of_all _ fun x ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have := dev_le x; have := dev_nonneg x; nlinarith
  exact ⟨hbound _ _, hbound _ _⟩

lemma integral_dev_sq_cell (k : ℤ) :
    ∫ x in (k : ℝ)..(k : ℝ) + 1, dev x ^ 2 = 1 / 12 := by
  have h1 : ∫ x in (k : ℝ)..(k : ℝ) + 1, dev x ^ 2 =
      ∫ x in (k : ℝ)..(k : ℝ) + 1, (x - ((k : ℝ) + 1 / 2)) ^ 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ x : ℝ, x ≠ (k : ℝ) + 1 := by simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hx hx'
    rw [Set.uIoc_of_le (by linarith)] at hx'
    have hfl : ⌊x⌋ = k := by
      rw [Int.floor_eq_iff]
      exact ⟨hx'.1.le, lt_of_le_of_ne hx'.2 hx⟩
    unfold dev
    rw [Int.fract, hfl, sq_abs]; ring
  rw [h1, intervalIntegral.integral_comp_sub_right (fun x ↦ x ^ 2), integral_pow]
  ring

lemma intervalIntegrable_dev_weight {a₁ : ℝ} {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    IntervalIntegrable (fun x ↦ a₁ * dev x ^ 2 / (x + 1 / 2)) volume u v := by
  have h1 : IntervalIntegrable (fun x ↦ a₁ * dev x ^ 2) volume u v :=
    (intervalIntegrable_dev_sq u v).const_mul a₁
  have h2 : ContinuousOn (fun x : ℝ ↦ (x + 1 / 2)⁻¹) (Set.uIcc u v) := by
    refine ContinuousOn.inv₀ (by fun_prop) (fun x hx ↦ ?_)
    have : 0 ≤ x := by
      rcases le_total u v with h | h
      · rw [Set.uIcc_of_le h] at hx; linarith [hx.1]
      · rw [Set.uIcc_of_ge h] at hx; linarith [hx.1]
    linarith
  simpa [div_eq_mul_inv] using h1.mul_continuousOn h2

lemma integral_dev_weight_ge {a₁ : ℝ} (ha₁ : 0 < a₁) (m n : ℕ) :
    (a₁ / 12) * Real.log (((m : ℝ) + 3 / 2 + n) / ((m : ℝ) + 3 / 2)) ≤
      ∫ x in (m : ℝ)..(m : ℝ) + n, a₁ * dev x ^ 2 / (x + 1 / 2) := by
  set g : ℝ → ℝ := fun x ↦ a₁ * dev x ^ 2 / (x + 1 / 2) with hg
  have hcell : ∀ i : ℕ, (a₁ / 12) * (1 / ((m : ℝ) + 3 / 2 + i)) ≤
      ∫ x in ((m : ℝ) + i)..((m : ℝ) + ((i + 1 : ℕ) : ℝ)), g x := by
    intro i
    have hm0 : (0 : ℝ) ≤ (m : ℝ) + i := by positivity
    have e : ((m : ℝ) + ((i + 1 : ℕ) : ℝ)) = ((m : ℝ) + i) + 1 := by push_cast; ring
    rw [e]
    have hc := integral_dev_sq_cell ((m + i : ℕ) : ℤ)
    push_cast at hc
    have hlow : ∫ x in ((m : ℝ) + i)..((m : ℝ) + i) + 1, a₁ * dev x ^ 2 / ((m : ℝ) + 3 / 2 + i) =
        (a₁ / 12) * (1 / ((m : ℝ) + 3 / 2 + i)) := by
      have : ∀ x : ℝ, a₁ * dev x ^ 2 / ((m : ℝ) + 3 / 2 + i) =
          (a₁ / ((m : ℝ) + 3 / 2 + i)) * dev x ^ 2 := by intro x; ring
      simp_rw [this]
      rw [intervalIntegral.integral_const_mul, hc]; ring
    rw [← hlow]
    refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
    · have h := (intervalIntegrable_dev_sq ((m : ℝ) + i) (((m : ℝ) + i) + 1)).const_mul
        (a₁ / ((m : ℝ) + 3 / 2 + i))
      convert h using 2 with x
      ring
    · exact intervalIntegrable_dev_weight hm0 (by linarith)
    · intro x hx
      have hx0 : 0 < x + 1 / 2 := by linarith [hx.1]
      have hx1 : x + 1 / 2 ≤ (m : ℝ) + 3 / 2 + i := by linarith [hx.2]
      simp only [hg]
      have : 0 ≤ a₁ * dev x ^ 2 := by positivity
      exact div_le_div_of_nonneg_left this hx0 hx1
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ ↦ (m : ℝ) + i)
    (μ := volume) (f := g) (n := n) (fun k _ ↦ by
      simp only [Nat.cast_add, Nat.cast_one]
      exact intervalIntegrable_dev_weight (by positivity) (by positivity))
  simp only [Nat.cast_zero, add_zero] at hsum
  rw [← hsum]
  have hx₀ : 0 < (m : ℝ) + 3 / 2 := by positivity
  have hanti : AntitoneOn (fun s : ℝ ↦ 1 / s) (Set.Icc ((m : ℝ) + 3 / 2) ((m : ℝ) + 3 / 2 + n)) := by
    intro s hs t ht hst
    have : 0 < s := lt_of_lt_of_le hx₀ hs.1
    exact one_div_le_one_div_of_le this hst
  have hint := hanti.integral_le_sum
  rw [integral_one_div_of_pos hx₀ (by positivity)] at hint
  calc (a₁ / 12) * Real.log (((m : ℝ) + 3 / 2 + n) / ((m : ℝ) + 3 / 2))
      ≤ (a₁ / 12) * ∑ i ∈ Finset.range n, 1 / ((m : ℝ) + 3 / 2 + i) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = ∑ i ∈ Finset.range n, (a₁ / 12) * (1 / ((m : ℝ) + 3 / 2 + i)) := by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun i _ ↦ hcell i

end T2ii

end FF
