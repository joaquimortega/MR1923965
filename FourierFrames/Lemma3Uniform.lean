import OrtegaCerdaSeip.Lemma3.Main

/-!
# Uniform form of estimate (2) of [OS99, Lemma 3]

The vendored `OCS.multF_estimate_two` states `∃ c₁ c₂` *after* fixing the weight `m`.  Its proof
(`OCS.exists_abs_sum_multErr_sub_log_infDist_le`) produces `c₁ = e^{-K}`, `c₂ = e^{K}` with `K`
an explicit expression in `a, b` only (the constants `K₁, K₂, K₃` of that proof), so the constants
can be chosen uniformly over all weights `m` with `a ≤ m ≤ b`.  This uniform form is what M09
(`Theorem2ii.lean`) needs.  The file is not part of the vendored library, which must not be edited;
its proof is "re-run the proof of `OCS.multF_estimate_two` with `K` taken from the explicit
formula" and is left as `sorry` in the scaffold.
-/

open MeasureTheory Metric Set Complex Filter Topology

noncomputable section

namespace FF

open OCS

/-- Uniform version of `OCS.exists_abs_sum_multErr_sub_log_infDist_le`: the constant
`K = K₃ + 3 K₁ + 3 K₂` depends only on `(a, b)`.  (Proof copied from the vendored one, with the
constants `K₁ K₂ K₃` fixed before `m` is introduced.) -/
theorem exists_abs_sum_multErr_sub_log_infDist_le_uniform {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℝ, ∀ (m : ℝ → ℝ), OCS.IsMultWeight m a b → ∀ z : ℂ, |z.im| ≤ 1 → z ∉ OCS.multGammaC m →
      |(∑' j : ℤ, OCS.multErr m (fun t ↦ Real.log ‖(t : ℂ) - z‖) j) -
          Real.log (infDist z (OCS.multGammaC m))| ≤ K := by
  set K₁ := Real.log (3 / a + 1) + b * ∫ s in (-(3 / a))..(3 / a), |Real.log ‖(s : ℂ) - 0‖|
  set K₂ := |Real.log (a / (2 * b ^ 2))| + |Real.log (3 / a + 1)|
  set K₃ := 1 / (2 * a) *
    ∫ t, {s : ℝ | 1 / b ≤ |s - 0|}.indicator (fun s ↦ ((s - 0) ^ 2)⁻¹) t
  refine ⟨K₃ + 3 * K₁ + 3 * K₂, fun m hw z hz1 _ ↦ ?_⟩
  set k := multIdx m z.re with hk_def
  set N := Finset.Icc (k - 1) (k + 1) with hN
  set E : ℤ → ℝ := fun j ↦ multErr m (fun t ↦ Real.log ‖(t : ℂ) - z‖) j with hE_def
  have hE : Summable E := (summable_multErr_logDist hw z).of_abs
  obtain ⟨i, hi, hmin, hd⟩ := exists_infDist_multGammaC_eq hw z
  -- the far part
  set F : ℝ → ℝ := fun t ↦ {s : ℝ | 1 / b ≤ |s - z.re|}.indicator (fun s ↦ ((s - z.re) ^ 2)⁻¹) t
  have hF : Integrable F := integrable_indicator_inv_sq (one_div_pos.mpr hb) z.re
  have hF0 : ∀ t, 0 ≤ F t := fun t ↦ by
    simp only [F, indicator]; split_ifs <;> positivity
  set far : ℤ → ℝ := fun j ↦ if j ∈ N then 0 else E j with hfar
  set near : ℤ → ℝ := fun j ↦ if j ∈ N then E j else 0 with hnear
  have hsplit : E = fun j ↦ near j + far j := by
    funext j; simp only [hnear, hfar]; split_ifs <;> simp
  have hnear_s : Summable near := summable_of_ne_finset_zero (s := N) fun j hj ↦ by
    simp [hnear, hj]
  have hnear_sum : ∑' j, near j = ∑ j ∈ N, E j := by
    rw [tsum_eq_sum (s := N) fun j hj ↦ by simp [hnear, hj]]
    exact Finset.sum_congr rfl fun j hj ↦ by simp [hnear, hj]
  have hbound : ∀ j, |far j| ≤ 1 / (2 * a) * ∫ t in multPt m j..multPt m (j + 1), F t := by
    intro j
    by_cases hj : j ∈ N
    · simp only [hfar, hj, ↓reduceIte, abs_zero]
      exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg
        (multPt_lt_succ hw j).le fun t _ ↦ hF0 t)
    · simp only [hfar, hj, ↓reduceIte]
      have h2 : 2 ≤ |j - k| := by
        simp only [hN, Finset.mem_Icc, not_and_or, not_le] at hj
        rcases hj with h | h
        · rw [abs_of_neg (by omega)]; omega
        · rw [abs_of_pos (by omega)]; omega
      exact abs_multErr_logDist_le hw z h2
  have hsumF := (hasSum_integral_multPt hw hF).mul_left (1 / (2 * a))
  have hfar_abs : Summable fun j ↦ |far j| :=
    Summable.of_nonneg_of_le (fun j ↦ abs_nonneg _) hbound hsumF.summable
  have hfar_s : Summable far := hfar_abs.of_abs
  have hfar_le : |∑' j, far j| ≤ K₃ := by
    calc |∑' j, far j| ≤ ∑' j, |far j| := by
          simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := far) hfar_abs
      _ ≤ ∑' j, 1 / (2 * a) * ∫ t in multPt m j..multPt m (j + 1), F t :=
          hfar_abs.tsum_le_tsum hbound hsumF.summable
      _ = K₃ := by
          rw [hsumF.tsum_eq, integral_indicator_inv_sq_translate]
  -- the near part
  have hcard : (N.erase i).card ≤ 3 := by
    refine (Finset.card_erase_le).trans ?_
    rw [hN, Int.card_Icc, show k + 1 + 1 - (k - 1) = 3 by ring]
    rfl
  have hcardN : N.card ≤ 3 := by
    rw [hN, Int.card_Icc, show k + 1 + 1 - (k - 1) = 3 by ring]
    rfl
  have hpts : |∑ j ∈ N.erase i, Real.log ‖((multBary m j : ℝ) : ℂ) - z‖| ≤ 3 * K₂ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ K₂ fun j hj ↦ ?_).trans ?_
    · exact abs_log_norm_sub_le_of_near hw hz1 (Finset.mem_of_mem_erase hj)
        (Finset.ne_of_mem_erase hj) (hmin j (Finset.mem_of_mem_erase hj))
    · rw [nsmul_eq_mul]
      have : 0 ≤ K₂ := by positivity
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) this
  have hints : |∑ j ∈ N, ∫ t in multPt m j..multPt m (j + 1), Real.log ‖(t : ℂ) - z‖ * m t|
      ≤ 3 * K₁ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ K₁ fun j hj ↦
      abs_integral_logDist_le_of_near hw hz1 hj).trans ?_
    rw [nsmul_eq_mul]
    have h3a : 0 < 3 / a := by positivity
    have : 0 ≤ K₁ := by
      have h1 : 0 ≤ Real.log (3 / a + 1) := Real.log_nonneg (by linarith)
      have h2 : 0 ≤ ∫ s in (-(3 / a))..(3 / a), |Real.log ‖(s : ℂ) - 0‖| :=
        intervalIntegral.integral_nonneg (by linarith) fun _ _ ↦ abs_nonneg _
      positivity
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardN) this
  have hnear_eq : ∑ j ∈ N, E j - Real.log (infDist z (multGammaC m)) =
      (∑ j ∈ N.erase i, Real.log ‖((multBary m j : ℝ) : ℂ) - z‖) -
        ∑ j ∈ N, ∫ t in multPt m j..multPt m (j + 1), Real.log ‖(t : ℂ) - z‖ * m t := by
    simp only [hE_def, multErr, Finset.sum_sub_distrib]
    rw [← Finset.add_sum_erase N _ hi, hd, norm_sub_rev]
    ring
  have htsum : ∑' j, E j = ∑ j ∈ N, E j + ∑' j, far j := by
    have : ∑' j, E j = ∑' j, (near j + far j) := by rw [hsplit]
    rw [this, hnear_s.tsum_add hfar_s, hnear_sum]
  rw [show (∑' j : ℤ, multErr m (fun t ↦ Real.log ‖(t : ℂ) - z‖) j) = ∑' j, E j from rfl, htsum]
  have : (∑ j ∈ N, E j + ∑' j, far j) - Real.log (infDist z (multGammaC m)) =
      ((∑ j ∈ N.erase i, Real.log ‖((multBary m j : ℝ) : ℂ) - z‖) -
        ∑ j ∈ N, ∫ t in multPt m j..multPt m (j + 1), Real.log ‖(t : ℂ) - z‖ * m t) +
        ∑' j, far j := by
    rw [← hnear_eq]; ring
  rw [this]
  calc _ ≤ |(∑ j ∈ N.erase i, Real.log ‖((multBary m j : ℝ) : ℂ) - z‖) -
        ∑ j ∈ N, ∫ t in multPt m j..multPt m (j + 1), Real.log ‖(t : ℂ) - z‖ * m t| +
        |∑' j, far j| := abs_add_le _ _
    _ ≤ (3 * K₂ + 3 * K₁) + K₃ := by
        gcongr
        exact (abs_sub _ _).trans (add_le_add hpts hints)
    _ = K₃ + 3 * K₁ + 3 * K₂ := by ring

/-- **Lemma 3, estimate (2), with constants depending only on `(a, b)`.** -/
theorem lemma3_estimate_uniform {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (m : ℝ → ℝ), OCS.IsMultWeight m a b → ∀ C : ℝ, ∀ z : ℂ,
      |z.im| ≤ 1 →
        c₁ * infDist z (OCS.multGammaC m) ≤ ‖OCS.multF m C z‖ * Real.exp (-OCS.multU m C z) ∧
        ‖OCS.multF m C z‖ * Real.exp (-OCS.multU m C z) ≤ c₂ * infDist z (OCS.multGammaC m) := by
  obtain ⟨K, hK⟩ := exists_abs_sum_multErr_sub_log_infDist_le_uniform ha hb
  refine ⟨Real.exp (-K), Real.exp K, Real.exp_pos _, Real.exp_pos _, fun m hw C z hz ↦ ?_⟩
  by_cases hzΓ : z ∈ multGammaC m
  · have hF : multF m C z = 0 := (multF_eq_zero_iff hw C z).2 (mem_multGammaC_iff.1 hzΓ)
    have hd : infDist z (multGammaC m) = 0 := infDist_zero_of_mem hzΓ
    simp [hF, hd]
  · have hF0 : multF m C z ≠ 0 := fun h ↦
      hzΓ (mem_multGammaC_iff.2 ((multF_eq_zero_iff hw C z).1 h))
    have hS := hK m hw z hz hzΓ
    rw [← log_norm_multF_sub_multU hw C hzΓ] at hS
    obtain ⟨i, _, _, hd⟩ := exists_infDist_multGammaC_eq hw z
    have hdpos : 0 < infDist z (multGammaC m) := by
      rw [hd, norm_pos_iff, sub_ne_zero]
      intro h; exact hzΓ ⟨multBary m i, ⟨i, rfl⟩, h.symm⟩
    have hexp : ‖multF m C z‖ * Real.exp (-multU m C z) =
        Real.exp (Real.log ‖multF m C z‖ - multU m C z) := by
      rw [Real.exp_sub, Real.exp_log (norm_pos_iff.mpr hF0), Real.exp_neg, div_eq_mul_inv]
    rw [hexp]
    rw [abs_le] at hS
    constructor
    · calc Real.exp (-K) * infDist z (multGammaC m) =
            Real.exp (Real.log (infDist z (multGammaC m)) - K) := by
            rw [Real.exp_sub, Real.exp_log hdpos, Real.exp_neg]; ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    · calc Real.exp (Real.log ‖multF m C z‖ - multU m C z) ≤
            Real.exp (Real.log (infDist z (multGammaC m)) + K) := Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp K * infDist z (multGammaC m) := by
            rw [Real.exp_add, Real.exp_log hdpos]; ring

end FF
