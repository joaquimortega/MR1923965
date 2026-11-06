import FourierFrames.Defs
import OrtegaCerdaSeip.Lemma3.Main

/-!
# M09 helper: `U_1(z) = π |Im z|`

`∫ [log|1 - z/t| + (1 - χ_{[-1,1]}(t)) Re(z/t)] dt = π |Im z|`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped Interval

noncomputable section

namespace FF

namespace T2ii

/-- `G_y(s) = log(s² + y²)/2 = log |s - i y|`. -/
def Gy (y s : ℝ) : ℝ := Real.log (s ^ 2 + y ^ 2) / 2

lemma Gy_neg (y s : ℝ) : Gy y (-s) = Gy y s := by simp [Gy]

lemma Gy_eq_log_norm (y : ℝ) :
    Gy y = fun t : ℝ ↦ Real.log ‖(t : ℂ) - ⟨0, y⟩‖ := by
  funext t; rw [OCS.log_norm_ofReal_sub]; simp [Gy]

lemma intervalIntegrable_Gy (y u v : ℝ) : IntervalIntegrable (Gy y) volume u v := by
  rw [Gy_eq_log_norm]; exact OCS.intervalIntegrable_log_norm_sub _ u v

lemma log_sub_le_div {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : Real.log A - Real.log B ≤ (A - B) / B := by
  rw [← Real.log_div hA.ne' hB.ne']
  have := Real.log_le_sub_one_of_pos (div_pos hA hB)
  have h2 : A / B - 1 = (A - B) / B := by field_simp
  linarith

lemma abs_log_sub_log_le {A B r : ℝ} (hr : 0 < r) (hA : r ≤ A) (hB : r ≤ B) :
    |Real.log A - Real.log B| ≤ |A - B| / r := by
  have hA0 : 0 < A := lt_of_lt_of_le hr hA
  have hB0 : 0 < B := lt_of_lt_of_le hr hB
  rw [abs_le]
  have h1 := log_sub_le_div hA0 hB0
  have h2 := log_sub_le_div hB0 hA0
  have h3 : (A - B) / B ≤ |A - B| / r := by
    calc (A - B) / B ≤ |A - B| / B := by gcongr; exact le_abs_self _
      _ ≤ |A - B| / r := by gcongr
  have h4 : (B - A) / A ≤ |A - B| / r := by
    calc (B - A) / A ≤ |B - A| / A := by gcongr; exact le_abs_self _
      _ ≤ |A - B| / r := by rw [abs_sub_comm]; gcongr
  constructor <;> linarith

/-- Lipschitz-type bound for `G_y` away from `0`. -/
lemma abs_Gy_sub_le (y : ℝ) {p q r : ℝ} (hr : 0 < r) (hp : r ≤ p) (hq : r ≤ q) :
    |Gy y p - Gy y q| ≤ |p ^ 2 - q ^ 2| / (2 * r ^ 2) := by
  have hA : r ^ 2 ≤ p ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y]
  have hB : r ^ 2 ≤ q ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y]
  have := abs_log_sub_log_le (by positivity) hA hB
  have h1 : Gy y p - Gy y q = (Real.log (p ^ 2 + y ^ 2) - Real.log (q ^ 2 + y ^ 2)) / 2 := by
    simp only [Gy]; ring
  rw [h1, abs_div, abs_two]
  have h2 : p ^ 2 + y ^ 2 - (q ^ 2 + y ^ 2) = p ^ 2 - q ^ 2 := by ring
  rw [h2] at this
  calc _ ≤ (|p ^ 2 - q ^ 2| / r ^ 2) / 2 := by gcongr
    _ = _ := by field_simp

lemma shift_eq (y x R : ℝ) :
    ∫ t in (-R)..R, (Gy y (t - x) - Gy y t) =
      ∫ u in (0 : ℝ)..x, (Gy y (R + u) - Gy y (R - x + u)) := by
  have hI := intervalIntegrable_Gy y
  have h1 : IntervalIntegrable (fun t ↦ Gy y (t - x)) volume (-R) R := by
    have := (hI (-R - x) (R - x)).comp_sub_right x
    simpa using this
  have hA : IntervalIntegrable (fun u ↦ Gy y (R + u)) volume 0 x := by
    have := (hI R (R + x)).comp_add_left R
    simpa using this
  have hB : IntervalIntegrable (fun u ↦ Gy y (R - x + u)) volume 0 x := by
    have := (hI (R - x) R).comp_add_left (R - x)
    simpa using this
  rw [intervalIntegral.integral_sub h1 (hI _ _), intervalIntegral.integral_sub hA hB,
    intervalIntegral.integral_comp_sub_right (Gy y) x,
    intervalIntegral.integral_comp_add_left (Gy y) R,
    intervalIntegral.integral_comp_add_left (Gy y) (R - x)]
  have h3 : ∫ s in R..R + x, Gy y s = ∫ s in (-(R + x))..(-R), Gy y s := by
    rw [← intervalIntegral.integral_comp_neg (fun s ↦ Gy y s)]
    exact intervalIntegral.integral_congr (fun s _ ↦ (Gy_neg y s).symm)
  have e1 : ∫ s in (-R - x)..(R - x), Gy y s = (∫ s in (-R - x)..(-R), Gy y s) +
      (∫ s in (-R)..R, Gy y s) + ∫ s in R..(R - x), Gy y s := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hI _ _) (hI _ _),
      intervalIntegral.integral_add_adjacent_intervals (hI _ _) (hI _ _)]
  have e2 : ∫ s in R..(R - x), Gy y s = -∫ s in (R - x)..R, Gy y s :=
    intervalIntegral.integral_symm _ _
  have e3 : -R - x = -(R + x) := by ring
  have e4 : R + 0 = R := by ring
  have e5 : R + x = R + x := rfl
  have e6 : R - x + 0 = R - x := by ring
  have e7 : R - x + x = R := by ring
  rw [e4, e6, e7]
  rw [e1, e2, e3, ← h3]
  ring

lemma abs_shift_le (y : ℝ) {x R : ℝ} (hR : 0 < R) (hxR : 4 * |x| ≤ R) :
    |∫ t in (-R)..R, (Gy y (t - x) - Gy y t)| ≤ 6 * x ^ 2 / R := by
  rw [shift_eq]
  have hb : ∀ u ∈ Ι (0 : ℝ) x, ‖Gy y (R + u) - Gy y (R - x + u)‖ ≤ 6 * |x| / R := by
    intro u hu
    have hu' : |u| ≤ |x| := by
      rw [Set.uIoc] at hu
      rcases le_total 0 x with h | h
      · rw [min_eq_left h, max_eq_right h] at hu
        rw [abs_of_nonneg h, abs_of_pos hu.1]; exact hu.2
      · rw [min_eq_right h, max_eq_left h] at hu
        rw [abs_of_nonpos h, abs_of_nonpos hu.2]; linarith [hu.1]
    have hu1 := abs_le.1 hu'
    have hx1 := abs_le.1 (le_refl |x|)
    have hxa := abs_nonneg x
    have hr : 0 < R / 2 := by positivity
    have hp : R / 2 ≤ R + u := by linarith [hu1.1]
    have hq : R / 2 ≤ R - x + u := by
      have := neg_abs_le x; have := le_abs_self x; linarith [hu1.1]
    have := abs_Gy_sub_le y hr hp hq
    rw [Real.norm_eq_abs]
    refine this.trans ?_
    have h1 : (R + u) ^ 2 - (R - x + u) ^ 2 = x * (2 * R + 2 * u - x) := by ring
    rw [h1, abs_mul]
    have h2 : |2 * R + 2 * u - x| ≤ 3 * R := by
      rw [abs_le]; constructor <;> nlinarith [le_abs_self x, neg_abs_le x, hu1.1, hu1.2]
    have h3 : (2 * (R / 2) ^ 2) = R ^ 2 / 2 := by ring
    rw [h3, div_div_eq_mul_div]
    rw [div_le_div_iff₀ (by positivity) hR]
    nlinarith [abs_nonneg x, abs_nonneg (2 * R + 2 * u - x), mul_le_mul_of_nonneg_left h2 (abs_nonneg x)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  have e : 6 * |x| / R * |x - 0| = 6 * x ^ 2 / R := by
    rw [sub_zero]; have := sq_abs x; field_simp; nlinarith [this]
  rw [e]

/-- Antiderivative of `log (t² + c²) - 2 log t`. -/
def Bf (c t : ℝ) : ℝ := t * Real.log (t ^ 2 + c ^ 2) - 2 * (t * Real.log t) + 2 * c * Real.arctan (t / c)

lemma hasDerivAt_Bf {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Bf c) (Real.log (t ^ 2 + c ^ 2) - 2 * Real.log t) t := by
  have h1 : HasDerivAt (fun t : ℝ ↦ t ^ 2 + c ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_id t).pow 2).add_const (c ^ 2)
  have hpos : 0 < t ^ 2 + c ^ 2 := by positivity
  have h2 : HasDerivAt (fun y : ℝ ↦ y * Real.log (y ^ 2 + c ^ 2))
      (1 * Real.log (t ^ 2 + c ^ 2) + t * (2 * t / (t ^ 2 + c ^ 2))) t :=
    (hasDerivAt_id' t).mul (h1.log hpos.ne')
  have h3 : HasDerivAt (fun y : ℝ ↦ 2 * (y * Real.log y)) (2 * (Real.log t + 1)) t :=
    (Real.hasDerivAt_mul_log ht.ne').const_mul 2
  have h4 : HasDerivAt (fun t : ℝ ↦ Real.arctan (t / c)) (1 / (1 + (t / c) ^ 2) * (1 / c)) t :=
    ((hasDerivAt_id' t).div_const c).arctan
  have h5 : HasDerivAt (Bf c) (1 * Real.log (t ^ 2 + c ^ 2) + t * (2 * t / (t ^ 2 + c ^ 2)) -
      2 * (Real.log t + 1) + 2 * c * (1 / (1 + (t / c) ^ 2) * (1 / c))) t :=
    (h2.sub h3).add (h4.const_mul (2 * c))
  convert h5 using 1
  field_simp
  ring

lemma continuous_Bf {c : ℝ} (hc : 0 < c) : Continuous (Bf c) := by
  unfold Bf
  have h1 : Continuous fun t : ℝ ↦ t * Real.log (t ^ 2 + c ^ 2) := by
    refine continuous_id.mul (Continuous.log (by fun_prop) fun t ↦ ?_)
    positivity
  exact (h1.sub (continuous_const.mul Real.continuous_mul_log)).add
    (continuous_const.mul (Real.continuous_arctan.comp (continuous_id.div_const c)))

lemma Bf_zero (c : ℝ) : Bf c 0 = 0 := by simp [Bf]

lemma Gy_sub_Gy_zero (c t : ℝ) : 2 * (Gy c t - Gy 0 t) = Real.log (t ^ 2 + c ^ 2) - 2 * Real.log t := by
  simp only [Gy]
  have : Real.log (t ^ 2 + 0 ^ 2) = 2 * Real.log t := by simp [Real.log_pow]
  rw [this]; ring

lemma integral_Gy_sub_Gy_zero {c : ℝ} (hc : 0 < c) {R : ℝ} (hR : 0 < R) :
    ∫ t in (-R)..R, (Gy c t - Gy 0 t) = Bf c R := by
  have hI := intervalIntegrable_Gy
  have hint : IntervalIntegrable (fun t ↦ Gy c t - Gy 0 t) volume 0 R := (hI c _ _).sub (hI 0 _ _)
  have hint' : IntervalIntegrable (fun t ↦ Gy c t - Gy 0 t) volume (-R) 0 := (hI c _ _).sub (hI 0 _ _)
  have h1 : ∫ t in (-R)..0, (Gy c t - Gy 0 t) = ∫ t in (0 : ℝ)..R, (Gy c t - Gy 0 t) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := R) (fun t ↦ Gy c t - Gy 0 t)
    simp only [Gy_neg, neg_zero] at this
    exact this.symm
  have h2 : ∫ t in (0 : ℝ)..R, 2 * (Gy c t - Gy 0 t) = Bf c R := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le
      (f := Bf c) (f' := fun t ↦ 2 * (Gy c t - Gy 0 t)) (continuous_Bf hc).continuousOn
      (fun t ht ↦ by
        have := hasDerivAt_Bf hc ht.1
        rwa [← Gy_sub_Gy_zero] at this)
      (hint.const_mul 2)]
    rw [Bf_zero, sub_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint' hint, h1, ← h2,
    intervalIntegral.integral_const_mul]
  ring

lemma tendsto_Bf {c : ℝ} (hc : 0 < c) : Tendsto (Bf c) atTop (𝓝 (Real.pi * c)) := by
  have h1 : Tendsto (fun R : ℝ ↦ 2 * c * Real.arctan (R / c)) atTop (𝓝 (2 * c * (Real.pi / 2))) :=
    (((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const hc)).const_mul (2 * c))
  have h2 : Tendsto (fun R : ℝ ↦ R * (Real.log (R ^ 2 + c ^ 2) - 2 * Real.log R)) atTop (𝓝 0) := by
    have hup : Tendsto (fun R : ℝ ↦ c ^ 2 / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with R hR
      have : 2 * Real.log R ≤ Real.log (R ^ 2 + c ^ 2) := by
        have : Real.log (R ^ 2) = 2 * Real.log R := by simp [Real.log_pow]
        rw [← this]
        exact Real.log_le_log (by positivity) (by nlinarith [sq_nonneg c])
      exact mul_nonneg hR.le (by linarith)
    · filter_upwards [eventually_gt_atTop 0] with R hR
      have h3 : Real.log (R ^ 2 + c ^ 2) - 2 * Real.log R ≤ c ^ 2 / R ^ 2 := by
        have : Real.log (R ^ 2) = 2 * Real.log R := by simp [Real.log_pow]
        rw [← this, ← Real.log_div (by positivity) (by positivity)]
        have := Real.log_le_sub_one_of_pos (show 0 < (R ^ 2 + c ^ 2) / R ^ 2 by positivity)
        have e : (R ^ 2 + c ^ 2) / R ^ 2 - 1 = c ^ 2 / R ^ 2 := by field_simp; ring
        linarith
      calc R * (Real.log (R ^ 2 + c ^ 2) - 2 * Real.log R) ≤ R * (c ^ 2 / R ^ 2) := by gcongr
        _ = c ^ 2 / R := by field_simp
  have := h2.add h1
  have e : (0 : ℝ) + 2 * c * (Real.pi / 2) = Real.pi * c := by ring
  rw [e] at this
  refine this.congr' ?_
  filter_upwards with R
  simp only [Bf]
  ring

lemma tendsto_integral_Gy_sub_Gy_zero (y : ℝ) :
    Tendsto (fun R : ℝ ↦ ∫ t in (-R)..R, (Gy y t - Gy 0 t)) atTop (𝓝 (Real.pi * |y|)) := by
  rcases (abs_nonneg y).eq_or_lt with h | h
  · have hy : y = 0 := abs_eq_zero.1 h.symm
    subst hy
    simp [← h]
  · have hG : Gy y = Gy |y| := by funext t; simp [Gy]
    rw [hG]
    refine (tendsto_Bf h).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact (integral_Gy_sub_Gy_zero h hR).symm

lemma intervalIntegrable_Gy_sub (y x u v : ℝ) :
    IntervalIntegrable (fun t ↦ Gy y (t - x)) volume u v := by
  have := (intervalIntegrable_Gy y (u - x) (v - x)).comp_sub_right x
  simpa using this

/-- The odd truncated kernel integrates to zero on symmetric intervals. -/
lemma integral_kernel_symm (R : ℝ) :
    ∫ t in (-R)..R, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹ = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
    (fun t : ℝ ↦ (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹)
  have h2 : ∀ t : ℝ, (1 - (Icc (-1 : ℝ) 1).indicator 1 (-t)) * (-t)⁻¹ =
      -((1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹) := by
    intro t
    have : (Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) (-t) = (Icc (-1 : ℝ) 1).indicator 1 t := by
      by_cases ht : t ∈ Icc (-1 : ℝ) 1
      · have : -t ∈ Icc (-1 : ℝ) 1 := by
          simp only [mem_Icc] at ht ⊢; constructor <;> linarith [ht.1, ht.2]
        rw [indicator_of_mem ht, indicator_of_mem this]; rfl
      · have : -t ∉ Icc (-1 : ℝ) 1 := by
          simp only [mem_Icc, not_and_or, not_le] at ht ⊢
          rcases ht with h | h
          · right; linarith
          · left; linarith
        rw [indicator_of_notMem ht, indicator_of_notMem this]
    rw [this, inv_neg]; ring
  simp only [h2, intervalIntegral.integral_neg, neg_neg] at h
  linarith

lemma integral_trunc_eq (z : ℂ) (R : ℝ) :
    ∫ t in (-R)..R, OCS.multUIntegrand (fun _ ↦ (1 : ℝ)) z t =
      (∫ t in (-R)..R, (Gy z.im (t - z.re) - Gy z.im t)) +
        (∫ t in (-R)..R, (Gy z.im t - Gy 0 t)) := by
  have hI := intervalIntegrable_Gy
  have h1 : ∫ t in (-R)..R, OCS.multUIntegrand (fun _ ↦ (1 : ℝ)) z t =
      ∫ t in (-R)..R, ((Gy z.im (t - z.re) - Gy 0 t) +
        z.re * ((1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [OCS.multUIntegrand_ae_eq (m := fun _ ↦ (1 : ℝ)) z] with t ht _
    rw [ht, OCS.log_norm_ofReal_sub z t, OCS.log_norm_ofReal_sub 0 t]
    simp [Gy]
  rw [h1, intervalIntegral.integral_add ((intervalIntegrable_Gy_sub _ _ _ _).sub (hI _ _ _))
    ((OCS.intervalIntegrable_one_sub_indicator_mul_inv _ _).const_mul _),
    intervalIntegral.integral_const_mul, integral_kernel_symm, mul_zero, add_zero,
    ← intervalIntegral.integral_add ((intervalIntegrable_Gy_sub _ _ _ _).sub (hI _ _ _))
      ((hI _ _ _).sub (hI _ _ _))]
  congr 1; funext t; ring

theorem multUIntegrand_one (z : ℂ) :
    ∫ t : ℝ, OCS.multUIntegrand (fun _ ↦ (1 : ℝ)) z t = Real.pi * |z.im| := by
  have hw : OCS.IsMultWeight (fun _ : ℝ ↦ (1 : ℝ)) 1 1 :=
    ⟨measurable_const, one_pos, fun _ ↦ le_rfl, fun _ ↦ le_rfl⟩
  have hint := OCS.integrable_multUIntegrand hw z
  have hlim := intervalIntegral_tendsto_integral hint
    (tendsto_neg_atTop_atBot : Tendsto (fun R : ℝ ↦ -R) atTop atBot) tendsto_id
  have hlim2 : Tendsto (fun R : ℝ ↦ ∫ t in (-R)..R, OCS.multUIntegrand (fun _ ↦ (1 : ℝ)) z t)
      atTop (𝓝 (Real.pi * |z.im|)) := by
    have h0 : Tendsto (fun R : ℝ ↦ ∫ t in (-R)..R, (Gy z.im (t - z.re) - Gy z.im t))
        atTop (𝓝 0) := by
      have hup : Tendsto (fun R : ℝ ↦ 6 * z.re ^ 2 / R) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      refine squeeze_zero_norm' ?_ hup
      filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (4 * |z.re|)] with R hR hR4
      rw [Real.norm_eq_abs]
      exact abs_shift_le z.im hR hR4
    have := h0.add (tendsto_integral_Gy_sub_Gy_zero z.im)
    rw [zero_add] at this
    refine this.congr (fun R ↦ ?_)
    rw [integral_trunc_eq]
  exact tendsto_nhds_unique hlim hlim2

end T2ii

end FF
