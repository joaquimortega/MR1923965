import OrtegaCerdaSeip.Lemma3.Partition

/-!
# M07 (Lemma 3) — the potential `U` and the Cauchy-type integral `G`

See `blueprint/M07_Lemma3.md`, §1.5–§1.8.  Paper, pp. 405–407.

* `integrable_multU_integrand`: the integrand of `multU` is integrable for every `z`
  (log singularities at `t = 0` and `t = z`; `O(|z|²/t²)` at infinity);
* `multU_conj`: `U(z̄) = U(z)`;
* `hasSum_multU`: `U(z) − C = ∑_j ∫_{I_j} (…)`;
* the linear coefficients `c_j = 1/γ_j − ∫_{I_j} (1 − χ_{[−1,1]}) m/t`, `κ = ∑ c_j`
  (`multLinCoeff`, `multKappa`), and the constant `∑_j E_j(log|·|) = −∫ H/t²` (`multLogConst`);
* `multG z = ∫ H(t)/(z − t)² dt`: holomorphic off `ℝ`, `|G(z)| ≤ π/(2a|Im z|)`,
  `G(z̄) = conj G(z)`, and `∑_j E_j(log|· − z|) = −Re G(z)` (the paper's (4), summed, with the
  sign corrected).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-- The integrand of `multU`: `[log|1 − z/t| + (1 − χ_{[−1,1]}(t)) Re(z/t)] m(t)`. -/
def multUIntegrand (m : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  (Real.log ‖1 - z / t‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).re) * m t

theorem multU_eq (m : ℝ → ℝ) (C : ℝ) (z : ℂ) :
    multU m C z = (∫ t : ℝ, multUIntegrand m z t) + C := rfl

/-- The linear coefficient `c_j = γ_j⁻¹ − ∫_{I_j} (1 − χ_{[−1,1]}(t)) t⁻¹ m(t) dt`. -/
def multLinCoeff (m : ℝ → ℝ) (j : ℤ) : ℝ :=
  (multBary m j)⁻¹ -
    ∫ t in multPt m j..multPt m (j + 1), (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹ * m t

/-- `κ = ∑_j c_j`. -/
def multKappa (m : ℝ → ℝ) : ℝ :=
  ∑' j : ℤ, multLinCoeff m j

/-- `∑_j E_j(log|·|) = ∑_j (log|γ_j| − ∫_{I_j} log|t| m(t) dt)`; it equals `−c₀ = −∫ H/t²`. -/
def multLogConst (m : ℝ → ℝ) : ℝ :=
  ∑' j : ℤ, multErr m (fun t ↦ Real.log |t|) j

/-- `G(z) = ∫_ℝ H(t)/(z − t)² dt`. -/
def multG (m : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (multPeanoH m t : ℂ) / (z - t) ^ 2

/-! ## The potential `U` -/

/-! ## General tools -/

theorem hasSum_integral_multPt {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} (hf : Integrable f) :
    HasSum (fun j : ℤ ↦ ∫ t in multPt m j..multPt m (j + 1), f t) (∫ t, f t) := by
  have hdisj : Pairwise (Function.onFun Disjoint fun j : ℤ ↦ Ico (multPt m j) (multPt m (j + 1))) := by
    intro i k hik
    refine Set.disjoint_left.2 fun t hi hk ↦ hik ?_
    exact ((multIdx_eq_iff hw).2 hi).symm.trans ((multIdx_eq_iff hw).2 hk)
  have hU : (⋃ j : ℤ, Ico (multPt m j) (multPt m (j + 1))) = univ :=
    eq_univ_of_forall fun t ↦ mem_iUnion.2 ⟨multIdx m t, (multIdx_eq_iff hw).1 rfl⟩
  have h := hasSum_integral_iUnion (fun j ↦ measurableSet_Ico) hdisj
    (by rw [hU]; exact hf.integrableOn)
  rw [hU, setIntegral_univ] at h
  convert h using 2 with j
  rw [intervalIntegral.integral_of_le (multPt_lt_succ hw j).le, integral_Ico_eq_integral_Ioc]

theorem integrable_indicator_inv_sq {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    Integrable (fun t ↦ {s : ℝ | δ ≤ |s - x|}.indicator (fun s ↦ ((s - x) ^ 2)⁻¹) t) := by
  have hint : Integrable (fun t : ℝ ↦ (1 + (δ ^ 2)⁻¹) * (1 + (t - x) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_sub_right x).const_mul _
  refine hint.mono' ?_ (ae_of_all _ fun t ↦ ?_)
  · exact (Measurable.indicator (by fun_prop)
      (measurableSet_le measurable_const (by fun_prop))).aestronglyMeasurable
  · simp only [indicator, mem_ofPred_eq]
    split_ifs with h
    · have hu : δ ^ 2 ≤ (t - x) ^ 2 := by
        rw [← sq_abs (t - x)]; exact pow_le_pow_left₀ hδ.le h 2
      have hu0 : 0 < (t - x) ^ 2 := lt_of_lt_of_le (by positivity) hu
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu0)]
      rw [inv_le_iff_one_le_mul₀' hu0]
      have : (t - x) ^ 2 * ((1 + (δ ^ 2)⁻¹) * (1 + (t - x) ^ 2)⁻¹) =
          ((t - x) ^ 2 + (t - x) ^ 2 / δ ^ 2) / (1 + (t - x) ^ 2) := by
        field_simp
      rw [this, le_div_iff₀ (by positivity), one_mul]
      have : 1 ≤ (t - x) ^ 2 / δ ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    · simp only [norm_zero]; positivity

theorem intervalIntegrable_log_norm_sub (z : ℂ) (u v : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ Real.log ‖(t : ℂ) - z‖) volume u v := by
  apply MeromorphicOn.intervalIntegrable_log_norm (f := fun t : ℝ ↦ (t : ℂ) - z)
  intro t _
  exact ((Complex.ofRealCLM.analyticAt t).sub analyticAt_const).meromorphicAt

theorem log_norm_ofReal_sub (z : ℂ) (t : ℝ) :
    Real.log ‖(t : ℂ) - z‖ = Real.log ((t - z.re) ^ 2 + z.im ^ 2) / 2 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Real.log_sqrt (by positivity)]
  simp

theorem ae_ne_real (c : ℝ) : ∀ᵐ t : ℝ, t ≠ c := by
  simp [ae_iff, measure_singleton]

/-- `log|1 − z/t| = log|t − z| − log|t|` for `t ∉ {0, Re z}`. -/
theorem log_norm_one_sub_div (z : ℂ) {t : ℝ} (h0 : t ≠ 0) (hz : (t : ℂ) ≠ z) :
    Real.log ‖1 - z / t‖ = Real.log ‖(t : ℂ) - z‖ - Real.log ‖(t : ℂ) - 0‖ := by
  have ht : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr h0
  have htz : (t : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz
  rw [show (1 : ℂ) - z / t = ((t : ℂ) - z) / t by field_simp, norm_div, sub_zero,
    Real.log_div (norm_ne_zero_iff.mpr htz) (norm_ne_zero_iff.mpr ht)]

/-- The truncated kernel `(1 − χ_{[−1,1]}(t)) t⁻¹` is bounded by `1`. -/
theorem abs_one_sub_indicator_mul_inv_le (t : ℝ) :
    |(1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹| ≤ 1 := by
  by_cases h : t ∈ Icc (-1 : ℝ) 1
  · simp [indicator_of_mem h]
  · rw [indicator_of_notMem h, sub_zero, one_mul, abs_inv]
    have : 1 < |t| := by
      simp only [mem_Icc, not_and_or, not_le] at h
      rcases h with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    exact inv_le_one_of_one_le₀ this.le

theorem measurable_one_sub_indicator_mul_inv :
    Measurable fun t : ℝ ↦ (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹ :=
  (measurable_const.sub (measurable_const.indicator measurableSet_Icc)).mul measurable_inv

theorem intervalIntegrable_one_sub_indicator_mul_inv (u v : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹) volume u v := by
  have : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume u v := intervalIntegrable_const
  refine this.mono_fun measurable_one_sub_indicator_mul_inv.aestronglyMeasurable
    (ae_of_all _ fun t ↦ ?_)
  dsimp only
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one]
  exact abs_one_sub_indicator_mul_inv_le t

theorem measurable_multUIntegrand {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (z : ℂ) :
    Measurable (multUIntegrand m z) := by
  unfold multUIntegrand
  refine Measurable.mul ?_ hw.measurable
  refine Measurable.add ?_ ((measurable_const.sub (measurable_const.indicator measurableSet_Icc)).mul
    ?_)
  · exact Real.measurable_log.comp (measurable_const.sub (measurable_const.div
      Complex.measurable_ofReal)).norm
  · exact Complex.measurable_re.comp (measurable_const.div Complex.measurable_ofReal)

/-- The integrand of `multU`, rewritten off the null set `{0, Re z}`. -/
theorem multUIntegrand_eq {m : ℝ → ℝ} (z : ℂ) {t : ℝ} (h0 : t ≠ 0) (hz : t ≠ z.re) :
    multUIntegrand m z t = (Real.log ‖(t : ℂ) - z‖ - Real.log ‖(t : ℂ) - 0‖) * m t +
      z.re * ((1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹ * m t) := by
  have hz' : (t : ℂ) ≠ z := by
    intro h; apply hz; rw [← h, ofReal_re]
  rw [multUIntegrand, log_norm_one_sub_div z h0 hz', Complex.div_ofReal_re]
  ring

theorem multUIntegrand_ae_eq {m : ℝ → ℝ} (z : ℂ) : ∀ᵐ t : ℝ, multUIntegrand m z t =
    (Real.log ‖(t : ℂ) - z‖ - Real.log ‖(t : ℂ) - 0‖) * m t +
      z.re * ((1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹ * m t) := by
  filter_upwards [ae_ne_real 0, ae_ne_real z.re] with t h0 hz
  exact multUIntegrand_eq z h0 hz

theorem intervalIntegrable_multUIntegrand {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b)
    (z : ℂ) (u v : ℝ) : IntervalIntegrable (multUIntegrand m z) volume u v := by
  have h1 : IntervalIntegrable (fun t : ℝ ↦ (Real.log ‖(t : ℂ) - z‖ - Real.log ‖(t : ℂ) - 0‖) *
      m t + z.re * ((1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹ * m t)) volume u v :=
    (hw.intervalIntegrable_mul ((intervalIntegrable_log_norm_sub z u v).sub
      (intervalIntegrable_log_norm_sub 0 u v))).add
      ((hw.intervalIntegrable_mul (intervalIntegrable_one_sub_indicator_mul_inv u v)).const_mul _)
  refine h1.congr_ae ?_
  filter_upwards [ae_restrict_of_ae (multUIntegrand_ae_eq (m := m) z)] with t ht
  exact ht.symm

/-- Far from the origin: `|u_z(t)| ≤ 2b|z|²/(1 + t²)` for `|t| ≥ 2|z| + 2`. -/
theorem abs_multUIntegrand_le_far {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (z : ℂ)
    {t : ℝ} (ht : 2 * ‖z‖ + 2 ≤ |t|) :
    |multUIntegrand m z t| ≤ 2 * b * ‖z‖ ^ 2 * (1 + t ^ 2)⁻¹ := by
  have ht1 : 1 < |t| := by linarith [norm_nonneg z]
  have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at ht1; linarith
  have hχ : t ∉ Icc (-1 : ℝ) 1 := by
    intro h; have := abs_le.mpr ⟨h.1, h.2⟩; linarith
  set w : ℂ := z / t with hw_def
  have hwn : ‖w‖ = ‖z‖ / |t| := by rw [hw_def, norm_div, Complex.norm_real, Real.norm_eq_abs]
  have hw2 : ‖w‖ ≤ 1 / 2 := by
    rw [hwn, div_le_iff₀ (by linarith)]; linarith [norm_nonneg z]
  have hlog : Real.log ‖1 - w‖ + w.re = ((Complex.log (1 + -w)) - (-w)).re := by
    rw [sub_re, Complex.log_re, neg_re, ← sub_eq_add_neg]; ring
  have hbd : |Real.log ‖1 - w‖ + w.re| ≤ ‖w‖ ^ 2 := by
    rw [hlog]
    refine (Complex.abs_re_le_norm _).trans ?_
    have hn : ‖-w‖ < 1 := by rw [norm_neg]; linarith
    refine (Complex.norm_log_one_add_sub_self_le hn).trans ?_
    rw [norm_neg]
    have h1 : (1 - ‖w‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h2 : 0 ≤ ‖w‖ ^ 2 := by positivity
    nlinarith
  have hw2' : ‖w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 * (1 + t ^ 2)⁻¹ := by
    rw [hwn, div_pow, sq_abs]
    have htt : 1 ≤ t ^ 2 := by rw [← sq_abs]; nlinarith
    rw [div_le_iff₀ (by positivity)]
    have : 2 * ‖z‖ ^ 2 * (1 + t ^ 2)⁻¹ * t ^ 2 = ‖z‖ ^ 2 * (2 * t ^ 2 / (1 + t ^ 2)) := by
      field_simp
    rw [this]
    have : 1 ≤ 2 * t ^ 2 / (1 + t ^ 2) := by rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith [sq_nonneg ‖z‖]
  rw [multUIntegrand, indicator_of_notMem hχ, sub_zero, one_mul, abs_mul, abs_of_nonneg (hw.nonneg t)]
  calc |Real.log ‖1 - w‖ + w.re| * m t ≤ (2 * ‖z‖ ^ 2 * (1 + t ^ 2)⁻¹) * b :=
        mul_le_mul (hbd.trans hw2') (hw.ge t) (hw.nonneg t) (by positivity)
    _ = 2 * b * ‖z‖ ^ 2 * (1 + t ^ 2)⁻¹ := by ring

theorem integrable_multUIntegrand {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (z : ℂ) :
    Integrable (multUIntegrand m z) := by
  set R := 2 * ‖z‖ + 2 with hR
  have hR0 : 0 ≤ R := by positivity
  rw [← integrableOn_univ, ← Set.union_compl_self (Icc (-R) R)]
  refine IntegrableOn.union ?_ ?_
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
      (intervalIntegrable_multUIntegrand hw z (-R) R)
  · have hint : Integrable (fun t : ℝ ↦ 2 * b * ‖z‖ ^ 2 * (1 + t ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul _
    refine hint.integrableOn.mono' (measurable_multUIntegrand hw z).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
    rw [Real.norm_eq_abs]
    refine abs_multUIntegrand_le_far hw z ?_
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

/-- `U(z̄) = U(z)` (no hypothesis: the integrands agree pointwise). -/
theorem multU_conj (m : ℝ → ℝ) (C : ℝ) (z : ℂ) : multU m C (conj z) = multU m C z := by
  rw [multU_eq, multU_eq]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
  simp only [multUIntegrand]
  have h : (starRingEnd ℂ) z / (t : ℂ) = (starRingEnd ℂ) (z / t) := by
    rw [map_div₀, Complex.conj_ofReal]
  have h2 : ‖1 - (starRingEnd ℂ) z / (t : ℂ)‖ = ‖1 - z / t‖ := by
    rw [h, ← Complex.norm_conj, map_sub, map_one, Complex.conj_conj]
  have h3 : ((starRingEnd ℂ) z / (t : ℂ)).re = (z / t).re := by rw [h, Complex.conj_re]
  rw [h2, h3]

/-- `U(z) − C = ∑_j ∫_{I_j} (…)`. -/
theorem hasSum_multU {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (C : ℝ) (z : ℂ) :
    HasSum (fun j : ℤ ↦ ∫ t in multPt m j..multPt m (j + 1), multUIntegrand m z t)
      (multU m C z - C) := by
  rw [multU_eq, add_sub_cancel_right]
  exact hasSum_integral_multPt hw (integrable_multUIntegrand hw z)

/-! ## Second derivatives of `log|· − z|` and the far intervals -/

theorem hasDerivAt_logDist (z : ℂ) {t : ℝ} (ht : (t - z.re) ^ 2 + z.im ^ 2 ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ Real.log ‖(s : ℂ) - z‖)
      ((t - z.re) / ((t - z.re) ^ 2 + z.im ^ 2)) t := by
  have h1 : HasDerivAt (fun s : ℝ ↦ (s - z.re) ^ 2 + z.im ^ 2) (2 * (t - z.re)) t := by
    have h := (hasDerivAt_id' t).sub_const z.re
    have := (h.mul h).add_const (z.im ^ 2)
    convert this using 1
    · funext s; simp only [Pi.mul_apply]; ring
    · ring
  have h2 := (h1.log ht).div_const 2
  convert h2 using 1
  · funext s; exact log_norm_ofReal_sub z s
  · field_simp

theorem hasDerivAt_logDist_deriv (z : ℂ) {t : ℝ} (ht : (t - z.re) ^ 2 + z.im ^ 2 ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ (s - z.re) / ((s - z.re) ^ 2 + z.im ^ 2))
      ((z.im ^ 2 - (t - z.re) ^ 2) / ((t - z.re) ^ 2 + z.im ^ 2) ^ 2) t := by
  have h0 : HasDerivAt (fun s : ℝ ↦ s - z.re) 1 t := (hasDerivAt_id t).sub_const z.re
  have h1 : HasDerivAt (fun s : ℝ ↦ (s - z.re) ^ 2 + z.im ^ 2) (2 * (t - z.re)) t := by
    have h := (hasDerivAt_id' t).sub_const z.re
    have := (h.mul h).add_const (z.im ^ 2)
    convert this using 1
    · funext s; simp only [Pi.mul_apply]; ring
    · ring
  convert h0.div h1 ht using 1
  ring

theorem abs_logDist_deriv2_le (z : ℂ) {t : ℝ} (ht : t ≠ z.re) :
    |(z.im ^ 2 - (t - z.re) ^ 2) / ((t - z.re) ^ 2 + z.im ^ 2) ^ 2| ≤ ((t - z.re) ^ 2)⁻¹ := by
  have hu : 0 < (t - z.re) ^ 2 := by
    have : t - z.re ≠ 0 := sub_ne_zero.mpr ht
    positivity
  have hq : 0 < (t - z.re) ^ 2 + z.im ^ 2 := by positivity
  rw [abs_div, abs_of_pos (pow_pos hq 2), div_le_iff₀ (pow_pos hq 2), inv_mul_eq_div,
    le_div_iff₀ hu]
  have h1 : |z.im ^ 2 - (t - z.re) ^ 2| ≤ (t - z.re) ^ 2 + z.im ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg z.im]
  have h2 : (t - z.re) ^ 2 ≤ (t - z.re) ^ 2 + z.im ^ 2 := by nlinarith [sq_nonneg z.im]
  calc |z.im ^ 2 - (t - z.re) ^ 2| * (t - z.re) ^ 2
      ≤ ((t - z.re) ^ 2 + z.im ^ 2) * ((t - z.re) ^ 2 + z.im ^ 2) :=
        mul_le_mul h1 h2 hu.le hq.le
    _ = ((t - z.re) ^ 2 + z.im ^ 2) ^ 2 := by ring

/-- An interval `I_j` with `|j − j(x)| ≥ 2` stays at distance `≥ 1/b` from `x`. -/
theorem le_abs_sub_of_two_le {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {x : ℝ} {j : ℤ}
    (hj : 2 ≤ |j - multIdx m x|) {t : ℝ} (ht : t ∈ Icc (multPt m j) (multPt m (j + 1))) :
    1 / b ≤ |t - x| := by
  set k := multIdx m x with hk_def
  have hk : multPt m k ≤ x ∧ x < multPt m (k + 1) := multIdx_mem hw x
  have hmono := (strictMono_multPt hw).monotone
  have hb : 0 < 1 / b := one_div_pos.mpr hw.b_pos
  rcases le_or_gt k j with h | h
  · have hj' : k + 2 ≤ j := by rw [abs_of_nonneg (by omega)] at hj; omega
    have h1 := (multPt_succ_sub_bounds hw (k + 1)).1
    have h2 : multPt m (k + 1 + 1) ≤ multPt m j := hmono (by omega)
    rw [abs_of_pos (by linarith [ht.1])]
    linarith [ht.1]
  · have hj' : j + 2 ≤ k := by rw [abs_of_neg (by omega)] at hj; omega
    have h1 := (multPt_succ_sub_bounds hw (k - 1)).1
    have h2 : multPt m (j + 1) ≤ multPt m (k - 1) := hmono (by omega)
    have h3 : k - 1 + 1 = k := by ring
    rw [h3] at h1
    rw [abs_of_neg (by linarith [ht.2])]
    linarith [ht.2]

/-- The far intervals: `|E_j(log|· − z|)| ≤ (1/(2a)) ∫_{I_j} 1_{|t−x| ≥ 1/b} (t − x)⁻²`. -/
theorem abs_multErr_logDist_le {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (z : ℂ) {j : ℤ}
    (hj : 2 ≤ |j - multIdx m z.re|) :
    |multErr m (fun t ↦ Real.log ‖(t : ℂ) - z‖) j| ≤
      1 / (2 * a) * ∫ t in multPt m j..multPt m (j + 1),
        {s : ℝ | 1 / b ≤ |s - z.re|}.indicator (fun s ↦ ((s - z.re) ^ 2)⁻¹) t := by
  have hb := hw.b_pos
  have hx : multPt m j ≤ multPt m (j + 1) := (multPt_lt_succ hw j).le
  have hfar : ∀ t ∈ Icc (multPt m j) (multPt m (j + 1)), 1 / b ≤ |t - z.re| :=
    fun t ht ↦ le_abs_sub_of_two_le hw hj ht
  have hne : ∀ t ∈ Icc (multPt m j) (multPt m (j + 1)), t ≠ z.re := by
    intro t ht h
    have := hfar t ht
    rw [h, sub_self, abs_zero] at this
    have : 0 < 1 / b := by positivity
    linarith
  have hq : ∀ t ∈ Icc (multPt m j) (multPt m (j + 1)), (t - z.re) ^ 2 + z.im ^ 2 ≠ 0 := by
    intro t ht
    have : t - z.re ≠ 0 := sub_ne_zero.mpr (hne t ht)
    positivity
  set g'' : ℝ → ℝ := fun t ↦ (z.im ^ 2 - (t - z.re) ^ 2) / ((t - z.re) ^ 2 + z.im ^ 2) ^ 2
  have hcont : ContinuousOn g'' (Icc (multPt m j) (multPt m (j + 1))) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht; exact pow_ne_zero 2 (hq t ht)
  have hint : IntervalIntegrable g'' volume (multPt m j) (multPt m (j + 1)) :=
    (hcont.mono (by rw [uIcc_of_le hx])).intervalIntegrable
  refine (abs_multErr_le hw j (g' := fun t ↦ (t - z.re) / ((t - z.re) ^ 2 + z.im ^ 2))
    (g'' := g'') (fun t ht ↦ hasDerivAt_logDist z (hq t ht))
    (fun t ht ↦ hasDerivAt_logDist_deriv z (hq t ht)) hint).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity [hw.pos])
  refine intervalIntegral.integral_mono_on hx hint.abs
    ((integrable_indicator_inv_sq (one_div_pos.mpr hb) z.re).intervalIntegrable) fun t ht ↦ ?_
  have hmem : t ∈ {s : ℝ | 1 / b ≤ |s - z.re|} := hfar t ht
  rw [indicator_of_mem hmem]
  exact abs_logDist_deriv2_le z (hne t ht)

/-- Summability from bounds by integrals over the partition of an integrable function. -/
theorem summable_abs_of_le_integral {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b)
    {F : ℝ → ℝ} (hF : Integrable F) {e : ℤ → ℝ} {C : ℝ}
    (h : ∀ᶠ j in cofinite, |e j| ≤ C * ∫ t in multPt m j..multPt m (j + 1), F t) :
    Summable fun j ↦ |e j| := by
  refine Summable.of_norm_bounded_eventually
    ((hasSum_integral_multPt hw hF).summable.mul_left C) ?_
  filter_upwards [h] with j hj
  rwa [Real.norm_eq_abs, abs_abs]

theorem finite_setOf_not_two_le (k : ℤ) : {j : ℤ | ¬ 2 ≤ |j - k|}.Finite := by
  refine (Set.finite_Icc (k - 1) (k + 1)).subset fun j hj ↦ ?_
  simp only [Set.mem_ofPred_eq, not_le, abs_lt] at hj
  exact ⟨by omega, by omega⟩

theorem eventually_two_le (k : ℤ) : ∀ᶠ j in cofinite, 2 ≤ |j - k| := by
  have := (finite_setOf_not_two_le k).compl_mem_cofinite
  filter_upwards [this] with j hj
  simp only [mem_compl_iff, mem_ofPred_eq, not_not] at hj
  exact hj

theorem multErr_log_eq (m : ℝ → ℝ) (j : ℤ) :
    multErr m (fun t ↦ Real.log |t|) j = multErr m (fun t : ℝ ↦ Real.log ‖(t : ℂ) - 0‖) j := by
  have : (fun t : ℝ ↦ Real.log |t|) = fun t : ℝ ↦ Real.log ‖(t : ℂ) - 0‖ := by
    funext t; rw [sub_zero, Complex.norm_real, Real.norm_eq_abs]
  rw [this]

/-- The intervals away from `[−1, 1]`: for `b < j` or `j + 1 < −b`, `|t| > 1` on `Ī_j`. -/
theorem one_lt_abs_of_far {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {j : ℤ}
    (hj : b < j ∨ (j : ℝ) + 1 < -b) {t : ℝ} (ht : t ∈ Icc (multPt m j) (multPt m (j + 1))) :
    1 < |t| := by
  have hb := hw.b_pos
  have hmono := (strictMono_multPt hw).monotone
  rcases hj with hj | hj
  · have hj0 : (0 : ℤ) ≤ j := by
      have : (0 : ℝ) < j := hb.trans hj
      exact_mod_cast this.le
    have h1 : multPt m 0 ≤ multPt m j := hmono hj0
    rw [multPt_zero hw] at h1
    have h2 := abs_multPt_ge hw j
    rw [abs_of_nonneg h1, abs_of_nonneg (by exact_mod_cast hj0)] at h2
    have h3 : 1 < (j : ℝ) / b := by rw [lt_div_iff₀ hb]; linarith
    rw [abs_of_pos (by linarith [ht.1])]
    linarith [ht.1]
  · have hj0 : j + 1 ≤ (0 : ℤ) := by
      have : (j : ℝ) + 1 < 0 := by linarith
      exact_mod_cast this.le
    have h1 : multPt m (j + 1) ≤ multPt m 0 := hmono hj0
    rw [multPt_zero hw] at h1
    have h2 := abs_multPt_ge hw (j + 1)
    rw [abs_of_nonpos h1, abs_of_nonpos (by exact_mod_cast hj0)] at h2
    push_cast at h2
    have h3 : 1 < -((j : ℝ) + 1) / b := by rw [lt_div_iff₀ hb]; linarith
    rw [abs_of_neg (by linarith [ht.2])]
    linarith [ht.2]

theorem eventually_far_one {b : ℝ} : ∀ᶠ j : ℤ in cofinite, b < j ∨ (j : ℝ) + 1 < -b := by
  have hfin : {j : ℤ | ¬ (b < j ∨ (j : ℝ) + 1 < -b)}.Finite := by
    refine (Set.finite_Icc (-⌈b⌉ - 1) ⌈b⌉).subset fun j hj ↦ ?_
    simp only [Set.mem_ofPred_eq, not_or, not_lt] at hj
    have h1 : (j : ℝ) ≤ ⌈b⌉ := hj.1.trans (Int.le_ceil b)
    have h2 : -(⌈b⌉ : ℝ) ≤ j + 1 := by linarith [Int.le_ceil b, hj.2]
    have h3 : ((-⌈b⌉ - 1 : ℤ) : ℝ) ≤ j := by push_cast; linarith
    exact ⟨by exact_mod_cast h3, by exact_mod_cast h1⟩
  filter_upwards [hfin.compl_mem_cofinite] with j hj
  simp only [mem_compl_iff, mem_ofPred_eq, not_not] at hj
  exact hj

/-- `∑ |c_j| < ∞` (`c_j = −∫_{I_j} (t − γ_j)² m/(γ_j² t) = O(|j|⁻³)` once `I_j ∩ [−1,1] = ∅`). -/
theorem summable_multLinCoeff {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    Summable fun j : ℤ ↦ |multLinCoeff m j| := by
  refine summable_abs_of_le_integral hw ((integrable_indicator_inv_sq one_pos 0).const_mul 2)
    (C := 1 / (2 * a)) ?_
  filter_upwards [eventually_far_one (b := b)] with j hj
  have hx : multPt m j ≤ multPt m (j + 1) := (multPt_lt_succ hw j).le
  have h1 : ∀ t ∈ Icc (multPt m j) (multPt m (j + 1)), 1 < |t| :=
    fun t ht ↦ one_lt_abs_of_far hw hj ht
  have h0 : ∀ t ∈ Icc (multPt m j) (multPt m (j + 1)), t ≠ 0 := by
    intro t ht h; have := h1 t ht; rw [h, abs_zero] at this; linarith
  -- `c_j = E_j(t⁻¹)` on such intervals
  have hc : multLinCoeff m j = multErr m (fun t ↦ t⁻¹) j := by
    rw [multLinCoeff, multErr]
    congr 1
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    have : t ∉ Icc (-1 : ℝ) 1 := by
      intro h; have := abs_le.mpr ⟨h.1, h.2⟩; linarith [h1 t ht]
    simp only [indicator_of_notMem this, sub_zero, one_mul]
  set g'' : ℝ → ℝ := fun t ↦ 2 * t / (t ^ 2) ^ 2
  have hcont : ContinuousOn g'' (Icc (multPt m j) (multPt m (j + 1))) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht; exact pow_ne_zero 2 (pow_ne_zero 2 (h0 t ht))
  have hint : IntervalIntegrable g'' volume (multPt m j) (multPt m (j + 1)) :=
    (hcont.mono (by rw [uIcc_of_le hx])).intervalIntegrable
  rw [hc]
  refine (abs_multErr_le hw j (g' := fun t ↦ -(t ^ 2)⁻¹) (g'' := g'')
    (fun t ht ↦ hasDerivAt_inv (h0 t ht)) (fun t ht ↦ ?_) hint).trans ?_
  · convert ((hasDerivAt_pow 2 t).inv (pow_ne_zero 2 (h0 t ht))).neg using 1
    simp only [g'', Nat.cast_ofNat, neg_div, neg_neg]; ring
  refine mul_le_mul_of_nonneg_left ?_ (by positivity [hw.pos])
  refine intervalIntegral.integral_mono_on hx hint.abs
    (((integrable_indicator_inv_sq one_pos 0).const_mul 2).intervalIntegrable) fun t ht ↦ ?_
  have ht1 := h1 t ht
  have hmem : t ∈ {s : ℝ | 1 ≤ |s - 0|} := by
    show 1 ≤ |t - 0|; rw [sub_zero]; exact ht1.le
  rw [indicator_of_mem hmem, sub_zero]
  have ht2 : 0 < t ^ 2 := by positivity [h0 t ht]
  simp only [g'']
  rw [abs_div, abs_mul, abs_two, abs_of_pos (pow_pos ht2 2), ← sq_abs t]
  rw [div_le_iff₀ (by positivity)]
  have : 0 < |t| := by linarith
  have e : 2 * (|t| ^ 2)⁻¹ * (|t| ^ 2) ^ 2 = 2 * |t| ^ 2 := by field_simp
  rw [e]
  nlinarith

/-- `∑ |E_j(log|·|)| < ∞` (Peano bound for `|j| ≥ 2`). -/
theorem summable_multErr_log {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    Summable fun j : ℤ ↦ |multErr m (fun t ↦ Real.log |t|) j| := by
  simp_rw [multErr_log_eq m]
  refine summable_abs_of_le_integral hw
    (integrable_indicator_inv_sq (one_div_pos.mpr hw.b_pos) (0 : ℂ).re) (C := 1 / (2 * a)) ?_
  filter_upwards [eventually_two_le (multIdx m (0 : ℂ).re)] with j hj
  exact abs_multErr_logDist_le hw 0 hj

/-- For every `z`, `∑_j |E_j(log|· − z|)| < ∞`. -/
theorem summable_multErr_logDist {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (z : ℂ) :
    Summable fun j : ℤ ↦ |multErr m (fun t ↦ Real.log ‖(t : ℂ) - z‖) j| := by
  refine summable_abs_of_le_integral hw
    (integrable_indicator_inv_sq (one_div_pos.mpr hw.b_pos) z.re) (C := 1 / (2 * a)) ?_
  filter_upwards [eventually_two_le (multIdx m z.re)] with j hj
  exact abs_multErr_logDist_le hw z hj

/-- The decomposition of the summand of `hasSum_multU`: for every `j` and `z ∉ Γ`,
`log|1 − z/γ_j| + Re z/γ_j − ∫_{I_j}(…) = E_j(log|· − z|) − E_j(log|·|) + c_j Re z`. -/
theorem multErr_decomp {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) (z : ℂ)
    (hz : z ≠ multBary m j) :
    Real.log ‖1 - z / multBary m j‖ + z.re / multBary m j -
        ∫ t in multPt m j..multPt m (j + 1), multUIntegrand m z t =
      multErr m (fun t ↦ Real.log ‖(t : ℂ) - z‖) j - multErr m (fun t ↦ Real.log |t|) j +
        multLinCoeff m j * z.re := by
  set x₀ := multPt m j
  set x₁ := multPt m (j + 1)
  have hγ0 : multBary m j ≠ 0 := fun h ↦ zero_notMem_multGamma hw ⟨j, h⟩
  have hγz : ((multBary m j : ℝ) : ℂ) ≠ z := fun h ↦ hz h.symm
  have i1 : IntervalIntegrable (fun t : ℝ ↦ Real.log ‖(t : ℂ) - z‖ * m t) volume x₀ x₁ :=
    hw.intervalIntegrable_mul (intervalIntegrable_log_norm_sub z _ _)
  have i2 : IntervalIntegrable (fun t : ℝ ↦ Real.log ‖(t : ℂ) - 0‖ * m t) volume x₀ x₁ :=
    hw.intervalIntegrable_mul (intervalIntegrable_log_norm_sub 0 _ _)
  have i3 : IntervalIntegrable
      (fun t : ℝ ↦ (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹ * m t) volume x₀ x₁ :=
    hw.intervalIntegrable_mul (intervalIntegrable_one_sub_indicator_mul_inv _ _)
  have hU : ∫ t in x₀..x₁, multUIntegrand m z t =
      (∫ t in x₀..x₁, Real.log ‖(t : ℂ) - z‖ * m t) -
        (∫ t in x₀..x₁, Real.log ‖(t : ℂ) - 0‖ * m t) +
        z.re * ∫ t in x₀..x₁, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹ * m t := by
    rw [← intervalIntegral.integral_sub i1 i2, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (i1.sub i2) (i3.const_mul _)]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [multUIntegrand_ae_eq (m := m) z] with t ht _
    rw [ht]; ring
  rw [hU, multErr_log_eq m j, multErr, multErr, multLinCoeff,
    log_norm_one_sub_div z hγ0 hγz, div_eq_mul_inv]
  ring

/-! ## The function `G` -/

/-! ## The Poisson-type kernel `((t − x)² + y²)⁻¹` -/

theorem integrable_inv_sq_add_sq (z : ℂ) (hz : z.im ≠ 0) :
    Integrable fun t : ℝ ↦ ((t - z.re) ^ 2 + z.im ^ 2)⁻¹ := by
  have h := ((integrable_inv_one_add_mul_sq (inv_ne_zero hz)).comp_sub_right z.re).const_mul
    ((z.im ^ 2)⁻¹)
  refine h.congr (ae_of_all _ fun t ↦ ?_)
  simp only
  field_simp
  ring

theorem integral_inv_sq_add_sq (z : ℂ) (hz : z.im ≠ 0) :
    ∫ t : ℝ, ((t - z.re) ^ 2 + z.im ^ 2)⁻¹ = Real.pi / |z.im| := by
  have e : (fun t : ℝ ↦ ((t - z.re) ^ 2 + z.im ^ 2)⁻¹) =
      fun t ↦ (z.im ^ 2)⁻¹ * (1 + (z.im⁻¹ * (t - z.re)) ^ 2)⁻¹ := by
    funext t; field_simp; ring
  rw [e, integral_const_mul,
    integral_sub_right_eq_self (fun t ↦ (1 + (z.im⁻¹ * t) ^ 2)⁻¹) z.re,
    integral_univ_inv_one_add_mul_sq, abs_inv, ← sq_abs z.im]
  have : 0 < |z.im| := abs_pos.mpr hz
  field_simp

theorem norm_ofReal_sub_sq (z : ℂ) (t : ℝ) : ‖z - t‖ ^ 2 = (t - z.re) ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
  ring

/-- The integrand of `G`, bounded by `(1/(2a)) ((t − x)² + y²)⁻¹`. -/
theorem norm_multPeanoH_div_le {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (z : ℂ)
    (t : ℝ) : ‖(multPeanoH m t : ℂ) / (z - t) ^ 2‖ ≤
      1 / (2 * a) * ((t - z.re) ^ 2 + z.im ^ 2)⁻¹ := by
  rw [norm_div, norm_pow, norm_ofReal_sub_sq, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (abs_multPeanoH_le hw t) (by positivity)

theorem integrable_multG_integrand {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {z : ℂ}
    (hz : z.im ≠ 0) : Integrable fun t : ℝ ↦ (multPeanoH m t : ℂ) / (z - t) ^ 2 := by
  refine ((integrable_inv_sq_add_sq z hz).const_mul (1 / (2 * a))).mono' ?_
    (ae_of_all _ (norm_multPeanoH_div_le hw z))
  exact ((Complex.measurable_ofReal.comp (measurable_multPeanoH hw)).div
    ((measurable_const.sub Complex.measurable_ofReal).pow_const 2)).aestronglyMeasurable

theorem norm_sub_ge_half {z z₀ : ℂ} {t : ℝ} (hz : z ∈ ball z₀ (|z₀.im| / 2)) :
    ‖z₀ - t‖ / 2 ≤ ‖z - t‖ := by
  rw [mem_ball, dist_eq_norm] at hz
  have h1 : ‖z₀ - t‖ ≤ ‖z - t‖ + ‖z - z₀‖ := by
    calc ‖z₀ - t‖ = ‖(z - t) - (z - z₀)‖ := by ring_nf
      _ ≤ ‖z - t‖ + ‖z - z₀‖ := norm_sub_le _ _
  have h2 : |z₀.im| ≤ ‖z₀ - t‖ := by
    have := Complex.abs_im_le_norm (z₀ - t)
    simpa using this
  linarith

theorem hasDerivAt_const_div_sub_sq (c t z : ℂ) (hz : z ≠ t) :
    HasDerivAt (fun w : ℂ ↦ c / (w - t) ^ 2) (-2 * c / (z - t) ^ 3) z := by
  have h1 : HasDerivAt (fun w : ℂ ↦ (w - t) ^ 2) (2 * (z - t)) z := by
    have h := (hasDerivAt_id' z).sub_const t
    convert h.mul h using 1
    · funext w; simp only [Pi.mul_apply]; ring
    · ring
  have hne : (z - t) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hz)
  have h2 := (h1.inv hne).const_mul c
  convert h2 using 1
  · funext w; simp [div_eq_mul_inv]
  · have : z - t ≠ 0 := sub_ne_zero.mpr hz
    field_simp

theorem measurable_multG_integrand {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (c : ℂ)
    (n : ℕ) (z : ℂ) : Measurable fun t : ℝ ↦ c * (multPeanoH m t : ℂ) / (z - t) ^ n :=
  (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_multPeanoH hw))).div
    ((measurable_const.sub Complex.measurable_ofReal).pow_const n)

theorem differentiableOn_multG {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    DifferentiableOn ℂ (multG m) {z | z.im ≠ 0} := by
  intro z₀ hz₀
  have hy : z₀.im ≠ 0 := hz₀
  have hy0 : 0 < |z₀.im| := abs_pos.mpr hy
  set r := |z₀.im| / 2 with hr_def
  have hr : 0 < r := by positivity
  have ha := hw.pos
  refine DifferentiableAt.differentiableWithinAt ?_
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z (t : ℝ) ↦ (multPeanoH m t : ℂ) / (z - t) ^ 2)
    (F' := fun z (t : ℝ) ↦ -2 * (multPeanoH m t : ℂ) / (z - t) ^ 3) (x₀ := z₀)
    (s := ball z₀ r)
    (bound := fun t ↦ 8 / (a * |z₀.im|) * ((t - z₀.re) ^ 2 + z₀.im ^ 2)⁻¹)
    (ball_mem_nhds z₀ hr)
    (Eventually.of_forall fun z ↦ by
      simpa using (measurable_multG_integrand hw 1 2 z).aestronglyMeasurable)
    (integrable_multG_integrand hw hy)
    (measurable_multG_integrand hw (-2) 3 z₀).aestronglyMeasurable ?_
    ((integrable_inv_sq_add_sq z₀ hy).const_mul _) ?_
  · exact key.2.differentiableAt
  · refine ae_of_all _ fun t z hz ↦ ?_
    have h1 := norm_sub_ge_half (t := t) hz
    have h2 : |z₀.im| ≤ ‖z₀ - t‖ := by
      have := Complex.abs_im_le_norm (z₀ - t)
      simpa using this
    have h3 : 0 < ‖z₀ - t‖ := hy0.trans_le h2
    have hq : ‖z₀ - t‖ ^ 2 = (t - z₀.re) ^ 2 + z₀.im ^ 2 := norm_ofReal_sub_sq z₀ t
    rw [← hq, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_neg,
      Complex.norm_ofNat]
    have hH := abs_multPeanoH_le hw t
    have h4 : 0 < ‖z - t‖ := by linarith
    rw [div_le_iff₀ (pow_pos h4 3)]
    have h5 : ‖z₀ - t‖ ^ 3 / 8 ≤ ‖z - t‖ ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) h1 3
      linarith [show (‖z₀ - t‖ / 2) ^ 3 = ‖z₀ - t‖ ^ 3 / 8 by ring]
    have h6 : 2 * |multPeanoH m t| ≤ 1 / a := by
      have : 2 * (1 / (2 * a)) = 1 / a := by field_simp
      linarith
    calc 2 * |multPeanoH m t| ≤ 1 / a := h6
      _ = 8 / (a * |z₀.im|) * (‖z₀ - t‖ ^ 2)⁻¹ * (‖z₀ - t‖ ^ 3 / 8) *
            (|z₀.im|⁻¹ * ‖z₀ - t‖)⁻¹ := by field_simp
      _ ≤ 8 / (a * |z₀.im|) * (‖z₀ - t‖ ^ 2)⁻¹ * (‖z₀ - t‖ ^ 3 / 8) * 1 := by
          gcongr
          rw [inv_le_one₀ (by positivity), le_inv_mul_iff₀ hy0, mul_one]
          exact h2
      _ ≤ 8 / (a * |z₀.im|) * (‖z₀ - t‖ ^ 2)⁻¹ * ‖z - t‖ ^ 3 := by
          rw [mul_one]; gcongr
  · refine ae_of_all _ fun t z hz ↦ ?_
    have h1 := norm_sub_ge_half (t := t) hz
    have h2 : |z₀.im| ≤ ‖z₀ - t‖ := by
      have := Complex.abs_im_le_norm (z₀ - t)
      simpa using this
    have h4 : 0 < ‖z - t‖ := by linarith
    exact hasDerivAt_const_div_sub_sq _ _ _ (sub_ne_zero.mp (norm_pos_iff.mp h4))

/-- `|G(z)| ≤ ‖H‖_∞ ∫ dt/|z − t|² ≤ π/(2a|Im z|)`. -/
theorem norm_multG_le {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {z : ℂ} (hz : z.im ≠ 0) :
    ‖multG m z‖ ≤ Real.pi / (2 * a) / |z.im| := by
  unfold multG
  refine (norm_integral_le_of_norm_le ((integrable_inv_sq_add_sq z hz).const_mul (1 / (2 * a)))
    (ae_of_all _ (norm_multPeanoH_div_le hw z))).trans_eq ?_
  rw [integral_const_mul, integral_inv_sq_add_sq z hz]
  ring

/-- `G(z̄) = conj G(z)` (no hypothesis: `H` is real and `integral_conj`). -/
theorem multG_conj (m : ℝ → ℝ) (z : ℂ) : multG m (conj z) = conj (multG m z) := by
  unfold multG
  rw [← integral_conj]
  congr 1
  funext t
  rw [map_div₀, map_pow, map_sub, Complex.conj_ofReal, Complex.conj_ofReal]

/-- The Peano identity for `g_z = log|· − z|`, `z ∉ ℝ`, on one interval:
`E_j(g_z) = ∫_{I_j} H(t) g_z''(t) dt`. -/
theorem multErr_logDist_eq_integral {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {z : ℂ}
    (hz : z.im ≠ 0) (j : ℤ) :
    multErr m (fun t ↦ Real.log ‖(t : ℂ) - z‖) j =
      ∫ t in multPt m j..multPt m (j + 1), multPeanoH m t *
        ((z.im ^ 2 - (t - z.re) ^ 2) / ((t - z.re) ^ 2 + z.im ^ 2) ^ 2) := by
  have hq : ∀ t : ℝ, (t - z.re) ^ 2 + z.im ^ 2 ≠ 0 := fun t ↦ by positivity
  have hx : multPt m j ≤ multPt m (j + 1) := (multPt_lt_succ hw j).le
  have hcont : Continuous fun t : ℝ ↦
      (z.im ^ 2 - (t - z.re) ^ 2) / ((t - z.re) ^ 2 + z.im ^ 2) ^ 2 :=
    Continuous.div (by fun_prop) (by fun_prop) fun t ↦ pow_ne_zero 2 (hq t)
  rw [multErr_eq_integral_peano hw j (g' := fun t ↦ (t - z.re) / ((t - z.re) ^ 2 + z.im ^ 2))
    (fun t _ ↦ hasDerivAt_logDist z (hq t)) (fun t _ ↦ hasDerivAt_logDist_deriv z (hq t))
    (hcont.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le hx] at ht
  rw [multPeanoH_eq hw ht]

/-- **The paper's (4), summed** (sign corrected): for `z ∉ ℝ`,
`∑_j E_j(log|· − z|) = −Re ∫ H(t)/(z − t)² dt`. -/
theorem hasSum_multErr_logDist {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {z : ℂ}
    (hz : z.im ≠ 0) :
    HasSum (fun j : ℤ ↦ multErr m (fun t ↦ Real.log ‖(t : ℂ) - z‖) j) (-(multG m z).re) := by
  set φ : ℝ → ℝ := fun t ↦ multPeanoH m t *
    ((z.im ^ 2 - (t - z.re) ^ 2) / ((t - z.re) ^ 2 + z.im ^ 2) ^ 2) with hφ_def
  have hq : ∀ t : ℝ, (t - z.re) ^ 2 + z.im ^ 2 ≠ 0 := fun t ↦ by positivity
  have hφ : ∀ t, φ t = -((multPeanoH m t : ℂ) / (z - t) ^ 2).re := by
    intro t
    have h1 : ((z - t) ^ 2).re = (t - z.re) ^ 2 - z.im ^ 2 := by
      simp only [pow_two, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]; ring
    have h2 : Complex.normSq ((z - t) ^ 2) = ((t - z.re) ^ 2 + z.im ^ 2) ^ 2 := by
      rw [map_pow, Complex.normSq_apply]
      simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]; ring
    rw [hφ_def, Complex.div_re, h1, h2]
    simp only [ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
    ring
  have hint : Integrable φ :=
    (integrable_multG_integrand hw hz).re.neg.congr (ae_of_all _ fun t ↦ (hφ t).symm)
  have hsum := hasSum_integral_multPt hw hint
  have htot : ∫ t, φ t = -(multG m z).re := by
    simp_rw [hφ]
    rw [integral_neg]
    congr 1
    exact integral_re (integrable_multG_integrand hw hz)
  rw [htot] at hsum
  convert hsum using 1
  funext j
  rw [multErr_logDist_eq_integral hw hz j]

/-! ## The constant `∑_j E_j(log|·|)` -/

/-- Quadratic vanishing of `H` at the endpoints: `|H_j(x)| ≤ b (x − x_j)²/2` and
`|H_j(x)| ≤ b (x_{j+1} − x)²/2` on `Ī_j`. -/
theorem abs_multPeanoLoc_le_sq {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) {x : ℝ}
    (hx : x ∈ Icc (multPt m j) (multPt m (j + 1))) :
    |multPeanoLoc m j x| ≤ b * (x - multPt m j) ^ 2 / 2 ∧
      |multPeanoLoc m j x| ≤ b * (multPt m (j + 1) - x) ^ 2 / 2 := by
  have hH := (multPeanoLoc_bounds hw j hx).1
  rw [abs_of_nonpos hH]
  set A := ∫ t in multPt m j..x, (x - t) * m t with hA_def
  set B := ∫ t in x..multPt m (j + 1), (t - x) * m t with hB_def
  have hc : IntervalIntegrable (fun t : ℝ ↦ t) volume (multPt m j) x :=
    continuous_id.intervalIntegrable _ _
  have hc' : IntervalIntegrable (fun t : ℝ ↦ t) volume x (multPt m (j + 1)) :=
    continuous_id.intervalIntegrable _ _
  have hA : A ≤ b * (x - multPt m j) ^ 2 / 2 := by
    have h1 : A ≤ ∫ t in multPt m j..x, (x - t) * b :=
      intervalIntegral.integral_mono_on hx.1
        (hw.intervalIntegrable_mul (intervalIntegrable_const.sub hc))
        ((intervalIntegrable_const.sub hc).mul_const _)
        fun t ht ↦ mul_le_mul_of_nonneg_left (hw.ge t) (by linarith [ht.2])
    have h2 : ∫ t in multPt m j..x, (x - t) * b = b * (x - multPt m j) ^ 2 / 2 := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub (f := fun _ ↦ x)
        (g := fun t ↦ t) intervalIntegrable_const hc]
      simp [integral_id]
      ring
    linarith
  have hB : B ≤ b * (multPt m (j + 1) - x) ^ 2 / 2 := by
    have h1 : B ≤ ∫ t in x..multPt m (j + 1), (t - x) * b :=
      intervalIntegral.integral_mono_on hx.2
        (hw.intervalIntegrable_mul (hc'.sub intervalIntegrable_const))
        ((hc'.sub intervalIntegrable_const).mul_const _)
        fun t ht ↦ mul_le_mul_of_nonneg_left (hw.ge t) (by linarith [ht.1])
    have h2 : ∫ t in x..multPt m (j + 1), (t - x) * b = b * (multPt m (j + 1) - x) ^ 2 / 2 := by
      simp [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub, integral_id]
      ring
    linarith
  have eA : multPeanoLoc m j x = max (x - multBary m j) 0 - A := rfl
  have eB : multPeanoLoc m j x = max (multBary m j - x) 0 - B := multPeanoLoc_eq_right hw j x
  constructor
  · rw [eA]; linarith [le_max_right (x - multBary m j) 0]
  · rw [eB]; linarith [le_max_right (multBary m j - x) 0]

/-- `H(t)/t²` is integrable: it is bounded by `b/2` on `[x_{−1}, x_1]` and by
`(1/(2a)) t⁻²` outside. -/
theorem integrable_multPeanoH_div_sq {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    Integrable fun t ↦ multPeanoH m t / t ^ 2 := by
  have hb := hw.b_pos
  have ha := hw.pos
  have h0 := multPt_zero hw
  set F : ℝ → ℝ := fun t ↦ {s : ℝ | 1 / b ≤ |s - 0|}.indicator (fun s ↦ ((s - 0) ^ 2)⁻¹) t
  have hF : Integrable F := integrable_indicator_inv_sq (one_div_pos.mpr hb) 0
  have hF0 : ∀ t, 0 ≤ F t := fun t ↦ by simp only [F, indicator]; split_ifs <;> positivity
  have hI : Integrable ((Icc (multPt m (-1)) (multPt m 1)).indicator fun _ ↦ b / 2) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  refine (hI.add (hF.const_mul (1 / (2 * a)))).mono'
    ((measurable_multPeanoH hw).div (measurable_id.pow_const 2)).aestronglyMeasurable
    (ae_of_all _ fun t ↦ ?_)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
  have hx1 := (multPt_succ_sub_bounds hw 0).1
  have hx2 := (multPt_succ_sub_bounds hw (-1)).1
  simp only [zero_add, show (-1 : ℤ) + 1 = 0 by norm_num, h0] at hx1 hx2
  by_cases ht : t ∈ Icc (multPt m (-1)) (multPt m 1)
  · rw [Pi.add_apply, indicator_of_mem ht]
    have hsq : |multPeanoH m t| ≤ b * t ^ 2 / 2 := by
      rcases le_total 0 t with h | h
      · have ht' : t ∈ Icc (multPt m 0) (multPt m (0 + 1)) := by
          rw [h0, zero_add]; exact ⟨h, ht.2⟩
        rw [multPeanoH_eq hw ht']
        have := (abs_multPeanoLoc_le_sq hw 0 ht').1
        rwa [h0, sub_zero] at this
      · have ht' : t ∈ Icc (multPt m (-1)) (multPt m (-1 + 1)) := by
          rw [show (-1 : ℤ) + 1 = 0 by norm_num, h0]; exact ⟨ht.1, h⟩
        rw [multPeanoH_eq hw ht']
        have := (abs_multPeanoLoc_le_sq hw (-1) ht').2
        rwa [show (-1 : ℤ) + 1 = 0 by norm_num, h0, zero_sub, neg_sq] at this
    have : |multPeanoH m t| / t ^ 2 ≤ b / 2 := by
      rcases eq_or_lt_of_le (sq_nonneg t) with h | h
      · rw [← h, div_zero]; positivity
      · rw [div_le_iff₀ h]; linarith
    have := hF0 t
    have : 0 ≤ 1 / (2 * a) * F t := by positivity
    linarith
  · rw [Pi.add_apply, indicator_of_notMem ht, zero_add]
    have hb' : 0 < 1 / b := one_div_pos.mpr hb
    have hfar : 1 / b ≤ |t| := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hmem : t ∈ {s : ℝ | 1 / b ≤ |s - 0|} := by
      show 1 / b ≤ |t - 0|; rwa [sub_zero]
    simp only [F]
    rw [indicator_of_mem hmem, sub_zero]
    have htpos : 0 < t ^ 2 := by
      have : 0 < |t| := lt_of_lt_of_le hb' hfar
      rw [← sq_abs]; exact pow_pos this 2
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (abs_multPeanoH_le hw t) (by positivity)

/-- `E_j(log|·|) = −∫_{I_j} H(t)/t² dt` for every `j`: let `z = iε → 0` in
`multErr_logDist_eq_integral` (dominated convergence on both sides). -/
theorem multErr_log_eq_neg_integral {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) :
    multErr m (fun t ↦ Real.log |t|) j =
      -∫ t in multPt m j..multPt m (j + 1), multPeanoH m t / t ^ 2 := by
  set x₀ := multPt m j
  set x₁ := multPt m (j + 1)
  have hb := hw.b_pos
  set p : ℝ → ℂ := fun ε ↦ (ε : ℂ) * I with hp_def
  have hpre : ∀ ε, (p ε).re = 0 := fun ε ↦ by simp [hp_def]
  have hpim : ∀ ε, (p ε).im = ε := fun ε ↦ by simp [hp_def]
  set l := 𝓝[>] (0 : ℝ)
  have hl : Tendsto p l (𝓝 0) := by
    have : Tendsto p (𝓝 0) (𝓝 (p 0)) := (by fun_prop : Continuous p).continuousAt.tendsto
    rw [show p 0 = 0 by simp [hp_def]] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ ε in l, ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- the identity for `ε > 0`
  have hid : (fun ε ↦ multErr m (fun t ↦ Real.log ‖(t : ℂ) - p ε‖) j) =ᶠ[l]
      fun ε ↦ ∫ t in x₀..x₁, multPeanoH m t *
        (((p ε).im ^ 2 - (t - (p ε).re) ^ 2) / ((t - (p ε).re) ^ 2 + (p ε).im ^ 2) ^ 2) := by
    filter_upwards [hsmall] with ε hε
    exact multErr_logDist_eq_integral hw (by rw [hpim]; exact hε.1.ne') j
  -- limit of the left side
  have hL : Tendsto (fun ε ↦ multErr m (fun t ↦ Real.log ‖(t : ℂ) - p ε‖) j) l
      (𝓝 (multErr m (fun t : ℝ ↦ Real.log ‖(t : ℂ) - 0‖) j)) := by
    unfold multErr
    refine Tendsto.sub ?_ ?_
    · have hγ : ((multBary m j : ℝ) : ℂ) - 0 ≠ 0 := by
        rw [sub_zero, Complex.ofReal_ne_zero]
        exact fun h ↦ zero_notMem_multGamma hw ⟨j, h⟩
      have : ContinuousAt (fun z : ℂ ↦ Real.log ‖((multBary m j : ℝ) : ℂ) - z‖) 0 :=
        ContinuousAt.log (by fun_prop) (norm_ne_zero_iff.mpr hγ)
      exact this.tendsto.comp hl
    · refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun t ↦ (|Real.log ‖(t : ℂ) - 0‖| + |t| + 1) * b) ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun ε ↦ ((Real.measurable_log.comp
          ((Complex.measurable_ofReal.sub_const _).norm)).mul hw.measurable).aestronglyMeasurable
      · filter_upwards [hsmall] with ε hε
        filter_upwards [ae_ne_real 0] with t ht _
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw.nonneg t)]
        refine mul_le_mul ?_ (hw.ge t) (hw.nonneg t) (by positivity)
        have h1 : ‖(t : ℂ) - 0‖ = |t| := by rw [sub_zero, Complex.norm_real, Real.norm_eq_abs]
        have ht0 : 0 < |t| := abs_pos.mpr ht
        have hlow : |t| ≤ ‖(t : ℂ) - p ε‖ := by
          have := Complex.abs_re_le_norm ((t : ℂ) - p ε)
          simpa [hpre] using this
        have hup : ‖(t : ℂ) - p ε‖ ≤ |t| + 1 := by
          refine (norm_sub_le _ _).trans ?_
          rw [Complex.norm_real, Real.norm_eq_abs, hp_def, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε.1]
          linarith [hε.2]
        have l1 : Real.log |t| ≤ Real.log ‖(t : ℂ) - p ε‖ := Real.log_le_log ht0 hlow
        have l2 : Real.log ‖(t : ℂ) - p ε‖ ≤ |t| := by
          have hpos : 0 < ‖(t : ℂ) - p ε‖ := ht0.trans_le hlow
          linarith [Real.log_le_sub_one_of_pos hpos]
        rw [h1, abs_le]
        constructor
        · linarith [neg_abs_le (Real.log |t|)]
        · linarith [abs_nonneg (Real.log |t|)]
      · exact (((intervalIntegrable_log_norm_sub 0 _ _).abs.add
          (continuous_abs.intervalIntegrable _ _)).add intervalIntegrable_const).mul_const _
      · filter_upwards [ae_ne_real 0] with t ht _
        have hne : (t : ℂ) - 0 ≠ 0 := by rw [sub_zero]; exact_mod_cast ht
        have : ContinuousAt (fun z : ℂ ↦ Real.log ‖(t : ℂ) - z‖) 0 :=
          ContinuousAt.log (by fun_prop) (norm_ne_zero_iff.mpr hne)
        exact (this.tendsto.comp hl).mul_const _
  -- limit of the right side
  have hR : Tendsto (fun ε ↦ ∫ t in x₀..x₁, multPeanoH m t *
        (((p ε).im ^ 2 - (t - (p ε).re) ^ 2) / ((t - (p ε).re) ^ 2 + (p ε).im ^ 2) ^ 2)) l
      (𝓝 (-∫ t in x₀..x₁, multPeanoH m t / t ^ 2)) := by
    have hlim : (∫ t in x₀..x₁, multPeanoH m t *
        (((0 : ℂ).im ^ 2 - (t - (0 : ℂ).re) ^ 2) / ((t - (0 : ℂ).re) ^ 2 + (0 : ℂ).im ^ 2) ^ 2)) =
        -∫ t in x₀..x₁, multPeanoH m t / t ^ 2 := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ ↦ ?_
      simp only [Complex.zero_re, Complex.zero_im, sub_zero]
      rcases eq_or_ne t 0 with h | h
      · simp [h]
      · field_simp
        ring
    rw [← hlim]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t ↦ |multPeanoH m t / t ^ 2|) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun ε ↦ ((measurable_multPeanoH hw).mul
        (by fun_prop)).aestronglyMeasurable
    · filter_upwards [hsmall] with ε hε
      filter_upwards [ae_ne_real 0] with t ht _
      have htre : t ≠ (p ε).re := by rw [hpre]; exact ht
      have := abs_logDist_deriv2_le (p ε) htre
      rw [hpre, sub_zero] at this
      rw [hpre, sub_zero, Real.norm_eq_abs, abs_mul, abs_div (multPeanoH m t),
        abs_of_nonneg (sq_nonneg t), div_eq_mul_inv |multPeanoH m t|]
      exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
    · exact (integrable_multPeanoH_div_sq hw).abs.intervalIntegrable
    · filter_upwards [ae_ne_real 0] with t ht _
      have hden : ((t - (0 : ℂ).re) ^ 2 + (0 : ℂ).im ^ 2) ^ 2 ≠ 0 := by
        simp only [Complex.zero_re, Complex.zero_im, sub_zero]
        positivity
      have : ContinuousAt (fun z : ℂ ↦ multPeanoH m t *
          ((z.im ^ 2 - (t - z.re) ^ 2) / ((t - z.re) ^ 2 + z.im ^ 2) ^ 2)) 0 :=
        continuousAt_const.mul (ContinuousAt.div (by fun_prop) (by fun_prop) hden)
      exact this.tendsto.comp hl
  rw [multErr_log_eq m j]
  exact tendsto_nhds_unique hL (hR.congr' hid.symm)

/-- The constant: `∑_j E_j(log|·|) = −∫ H(t)/t² dt` (documentation of README §4; not needed for
`lemma3`). -/
theorem multLogConst_eq {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    multLogConst m = -∫ t : ℝ, multPeanoH m t / t ^ 2 := by
  have h := ((hasSum_integral_multPt hw (integrable_multPeanoH_div_sq hw)).neg)
  rw [multLogConst, ← h.tsum_eq]
  exact tsum_congr fun j ↦ multErr_log_eq_neg_integral hw j

end OCS
