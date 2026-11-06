import Mathlib

/-!
# Rigidity of phases under uniform convergence (aux file for `Construction.lean`, M07 §2.7(b))

If `E_k → w e^{-iπ x}` uniformly on `[-2, 2]` (`w ≠ 0`) and `φ_k` are continuous phase functions of
`E_k`, then `φ_k(x) - φ_k(0) - π x → 0` uniformly on `[-2, 2]`.
-/

open Complex Filter Topology Set

noncomputable section

namespace FF

namespace Rigidity

theorem norm_exp_neg_I_mul_sub_one (θ : ℝ) :
    ‖Complex.exp (-(Complex.I * θ)) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have := Complex.norm_exp_I_mul_ofReal_sub_one (-θ)
  rw [show Complex.I * ((-θ : ℝ) : ℂ) = -(Complex.I * θ) by push_cast; ring] at this
  rw [this, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, neg_div, Real.sin_neg, abs_neg]
  simp

/-- **Lemma B.** A continuous `g` on `[-2, 2]` with `g 0 = 0` and `‖e^{-ig} - 1‖ ≤ η < 1` is
bounded by `π η / 2`. -/
theorem abs_le_of_norm_exp_sub_one_le {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-2) 2)) (h0 : g 0 = 0)
    {η : ℝ} (hη : η < 1)
    (h : ∀ x ∈ Icc (-2 : ℝ) 2, ‖Complex.exp (-(Complex.I * g x)) - 1‖ ≤ η) :
    ∀ x ∈ Icc (-2 : ℝ) 2, |g x| ≤ Real.pi / 2 * η := by
  have hsmall : ∀ x ∈ Icc (-2 : ℝ) 2, |g x| < Real.pi / 3 := by
    intro x₁ hx₁
    by_contra hcon
    push Not at hcon
    have hsub : uIcc 0 x₁ ⊆ Icc (-2 : ℝ) 2 := by
      refine (uIcc_subset_Icc ⟨by linarith [hx₁.1], by linarith [hx₁.2]⟩ hx₁)
    have hcont : ContinuousOn g (uIcc 0 x₁) := hg.mono hsub
    have hmem0 : (0 : ℝ) ∈ Icc (-2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
    rcases le_or_gt 0 (g x₁) with hpos | hneg
    · have hge : Real.pi / 3 ≤ g x₁ := by
        rw [abs_of_nonneg hpos] at hcon; exact hcon
      have := intermediate_value_uIcc hcont (show Real.pi / 3 ∈ uIcc (g 0) (g x₁) by
        rw [h0, Set.mem_uIcc]; exact Or.inl ⟨by positivity, hge⟩)
      obtain ⟨y, hy, hgy⟩ := this
      have := h y (hsub hy)
      rw [hgy, norm_exp_neg_I_mul_sub_one] at this
      have hs : Real.sin (Real.pi / 3 / 2) = 1 / 2 := by
        rw [show Real.pi / 3 / 2 = Real.pi / 6 by ring, Real.sin_pi_div_six]
      rw [hs, abs_of_pos (by norm_num)] at this
      linarith
    · have hle : g x₁ ≤ -(Real.pi / 3) := by
        rw [abs_of_neg hneg] at hcon; linarith
      have := intermediate_value_uIcc hcont (show -(Real.pi / 3) ∈ uIcc (g 0) (g x₁) by
        rw [h0, Set.mem_uIcc]; exact Or.inr ⟨hle, by linarith [Real.pi_pos]⟩)
      obtain ⟨y, hy, hgy⟩ := this
      have := h y (hsub hy)
      rw [hgy, norm_exp_neg_I_mul_sub_one] at this
      have hs : Real.sin (-(Real.pi / 3) / 2) = -(1 / 2) := by
        rw [show -(Real.pi / 3) / 2 = -(Real.pi / 6) by ring, Real.sin_neg, Real.sin_pi_div_six]
      rw [hs, abs_neg, abs_of_pos (by norm_num)] at this
      linarith
  intro x hx
  have hb := h x hx
  rw [norm_exp_neg_I_mul_sub_one] at hb
  have hgx := hsmall x hx
  -- Jordan: `sin t ≥ (2/π) t` for `0 ≤ t ≤ π/2`
  have hsin : Real.sin (|g x| / 2) = |Real.sin (g x / 2)| := by
    rcases le_or_gt 0 (g x) with hp | hn
    · rw [abs_of_nonneg hp, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos, abs_of_nonneg hp, hgx])
    · have hs : Real.sin (g x / 2) ≤ 0 := by
        have := abs_of_neg hn
        exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by
          linarith [Real.pi_pos, abs_of_neg hn])
      rw [abs_of_nonpos hs, abs_of_neg hn, neg_div, Real.sin_neg]
  have hj := Real.mul_le_sin (x := |g x| / 2) (by positivity) (by linarith [Real.pi_pos])
  rw [hsin] at hj
  have h2 : 2 / Real.pi * (|g x| / 2) ≤ η / 2 := by linarith
  have hpi := Real.pi_pos
  have : |g x| / Real.pi ≤ η / 2 := by
    have : 2 / Real.pi * (|g x| / 2) = |g x| / Real.pi := by field_simp
    linarith
  rw [div_le_iff₀ hpi] at this
  linarith

theorem norm_div_norm_sub_le {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖a / (‖a‖ : ℂ) - b / (‖b‖ : ℂ)‖ ≤ 2 * ‖a - b‖ / ‖b‖ := by
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnb : 0 < ‖b‖ := norm_pos_iff.2 hb
  have e : a / (‖a‖ : ℂ) - b / (‖b‖ : ℂ) =
      (a - b) / (‖b‖ : ℂ) + (a / (‖a‖ : ℂ)) * (((‖b‖ - ‖a‖ : ℝ) : ℂ) / (‖b‖ : ℂ)) := by
    have h1 : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hna.ne'
    have h2 : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hnb.ne'
    push_cast
    field_simp
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have t1 : ‖(a - b) / (‖b‖ : ℂ)‖ = ‖a - b‖ / ‖b‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnb]
  have t2 : ‖(a / (‖a‖ : ℂ)) * (((‖b‖ - ‖a‖ : ℝ) : ℂ) / (‖b‖ : ℂ))‖ = |‖b‖ - ‖a‖| / ‖b‖ := by
    rw [norm_mul, norm_div, norm_div, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hna, abs_of_pos hnb]
    field_simp
  rw [t1, t2]
  have : |‖b‖ - ‖a‖| ≤ ‖a - b‖ := by
    rw [abs_sub_comm]; exact abs_norm_sub_norm_le a b
  have : |‖b‖ - ‖a‖| / ‖b‖ ≤ ‖a - b‖ / ‖b‖ := by gcongr
  linarith [show 2 * ‖a - b‖ / ‖b‖ = ‖a - b‖ / ‖b‖ + ‖a - b‖ / ‖b‖ by ring]

/-- **Lemma A.** -/
theorem phase_drift_small {E : ℕ → ℝ → ℂ} {φ : ℕ → ℝ → ℝ} (hφc : ∀ k, Continuous (φ k))
    (hE : ∀ k x, E k x = (‖E k x‖ : ℂ) * Complex.exp (-(Complex.I * φ k x))) {w : ℂ}
    (hw : w ≠ 0)
    (hconv : TendstoUniformlyOn E (fun x : ℝ ↦ w * Complex.exp (-(Complex.I * (Real.pi * x))))
      atTop (Icc (-2) 2)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ Icc (-2 : ℝ) 2,
      |φ k x - φ k 0 - Real.pi * x| ≤ ε := by
  intro ε hε
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  set η : ℝ := min (1 / 2) (2 * ε / Real.pi) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hη2 : η ≤ 2 * ε / Real.pi := min_le_right _ _
  set δ : ℝ := ‖w‖ * η / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  rw [Metric.tendstoUniformlyOn_iff] at hconv
  filter_upwards [hconv δ hδ0] with k hk
  -- the limit unit vector
  set ū : ℂ := w / (‖w‖ : ℂ) with hū
  have hūn : ‖ū‖ = 1 := by
    rw [hū, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwn, div_self hwn.ne']
  have hW : ∀ x : ℝ, ‖w * Complex.exp (-(Complex.I * (Real.pi * x)))‖ = ‖w‖ := fun x ↦ by
    rw [norm_mul]
    have : ‖Complex.exp (-(Complex.I * ((Real.pi * x : ℝ) : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    push_cast at this
    rw [this, mul_one]
  have hunit : ∀ x : ℝ, ‖Complex.exp (-(Complex.I * φ k x))‖ = 1 := fun x ↦ by
    rw [Complex.norm_exp]; simp
  -- unit vector estimate
  have hu : ∀ x ∈ Icc (-2 : ℝ) 2,
      ‖Complex.exp (-(Complex.I * φ k x)) -
        ū * Complex.exp (-(Complex.I * (Real.pi * x)))‖ ≤ 2 * δ / ‖w‖ := by
    intro x hx
    have hd := hk x hx
    rw [dist_eq_norm] at hd
    set Wx := w * Complex.exp (-(Complex.I * (Real.pi * x))) with hWx
    have hWn : ‖Wx‖ = ‖w‖ := hW x
    have hEx : ‖E k x‖ ≥ ‖w‖ - δ := by
      have := norm_sub_norm_le Wx (E k x)
      rw [hWn] at this
      linarith
    have hEpos : 0 < ‖E k x‖ := by
      have : δ ≤ ‖w‖ / 8 := by rw [hδ]; nlinarith
      linarith
    have hE0 : E k x ≠ 0 := norm_pos_iff.1 hEpos
    have hW0 : Wx ≠ 0 := norm_pos_iff.1 (by rw [hWn]; exact hwn)
    have key := norm_div_norm_sub_le hE0 hW0
    have e1 : E k x / (‖E k x‖ : ℂ) = Complex.exp (-(Complex.I * φ k x)) := by
      have : (‖E k x‖ : ℂ) ≠ 0 := by exact_mod_cast hEpos.ne'
      rw [div_eq_iff this, mul_comm]
      exact hE k x
    have e2 : Wx / (‖Wx‖ : ℂ) = ū * Complex.exp (-(Complex.I * (Real.pi * x))) := by
      rw [hWn, hWx, hū]; ring
    rw [e1, e2] at key
    refine key.trans ?_
    rw [hWn]
    gcongr
    rw [norm_sub_rev] at hd
    exact hd.le
  -- `e^{-i g} - 1` is small
  have hmain : ∀ x ∈ Icc (-2 : ℝ) 2,
      ‖Complex.exp (-(Complex.I * ((φ k x - φ k 0 - Real.pi * x : ℝ) : ℂ))) - 1‖ ≤ η := by
    intro x hx
    have h0mem : (0 : ℝ) ∈ Icc (-2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
    set ux := Complex.exp (-(Complex.I * φ k x)) with hux
    set u0 := Complex.exp (-(Complex.I * φ k 0)) with hu0
    set px := Complex.exp (-(Complex.I * (Real.pi * x))) with hpx
    have hux1 := hu x hx
    have hu01 := hu 0 h0mem
    have hpxn : ‖px‖ = 1 := by rw [hpx, Complex.norm_exp]; simp
    have hcj : Complex.exp (-(Complex.I * ((φ k x - φ k 0 - Real.pi * x : ℝ) : ℂ))) =
        ux * (starRingEnd ℂ) u0 * (starRingEnd ℂ) px := by
      rw [hux, hu0, hpx, ← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_add,
        ← Complex.exp_add]
      congr 1
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
      push_cast
      ring
    have hone : (1 : ℂ) = ū * px * ((starRingEnd ℂ) ū * (starRingEnd ℂ) px) := by
      have h1 : ū * (starRingEnd ℂ) ū = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hūn]; simp
      have h2 : px * (starRingEnd ℂ) px = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hpxn]; simp
      calc (1 : ℂ) = (ū * (starRingEnd ℂ) ū) * (px * (starRingEnd ℂ) px) := by rw [h1, h2]; ring
        _ = _ := by ring
    have hu0' : ‖u0 - ū‖ ≤ 2 * δ / ‖w‖ := by
      have := hu 0 h0mem
      simpa using this
    have hu0n : ‖u0‖ = 1 := by rw [hu0, Complex.norm_exp]; simp
    have hcjn : ∀ z : ℂ, ‖(starRingEnd ℂ) z‖ = ‖z‖ := fun z ↦ Complex.norm_conj z
    have hexp : Complex.exp (-(Complex.I * ((φ k x - φ k 0 - Real.pi * x : ℝ) : ℂ))) - 1 =
        (ux - ū * px) * (starRingEnd ℂ) u0 * (starRingEnd ℂ) px +
          ū * px * (starRingEnd ℂ) (u0 - ū) * (starRingEnd ℂ) px := by
      rw [hcj]
      conv_lhs => rw [hone]
      rw [map_sub]
      ring
    rw [hexp]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hcjn, hcjn, hcjn, hpxn, hūn, hu0n]
    simp only [mul_one, one_mul]
    have : 4 * δ / ‖w‖ = η := by rw [hδ]; field_simp
    have h2 : 2 * δ / ‖w‖ + 2 * δ / ‖w‖ = η := by rw [← this]; ring
    linarith
  -- conclude with Lemma B
  intro x hx
  have hg : ContinuousOn (fun x ↦ φ k x - φ k 0 - Real.pi * x) (Icc (-2) 2) :=
    (((hφc k).sub continuous_const).sub (continuous_const.mul continuous_id)).continuousOn
  have hB := abs_le_of_norm_exp_sub_one_le hg (by simp) (η := η) (by linarith) hmain x hx
  refine hB.trans ?_
  have : Real.pi / 2 * η ≤ Real.pi / 2 * (2 * ε / Real.pi) := by gcongr
  refine this.trans (le_of_eq ?_)
  field_simp

end Rigidity

end FF
