import FourierFrames.Theorem2i.CellAux

/-!
# M08 helper (fork D1): cells below `|z|/2` and above `2|z|`
-/

open MeasureTheory Set Complex Filter Topology

noncomputable section

namespace FF.D1

open FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M : ℝ}

theorem logNorm_swap {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) (hwz : w ≠ z) :
    Real.log ‖1 - z / w‖ = Real.log ‖1 - w / z‖ + Real.log ‖z‖ - Real.log ‖w‖ := by
  have e : 1 - z / w = -(z / w) * (1 - w / z) := by field_simp; ring
  have h1 : ‖1 - w / z‖ ≠ 0 := by
    apply norm_ne_zero_iff.2
    intro h0
    apply hwz
    have : w / z = 1 := by linear_combination -h0
    field_simp at this
    exact this
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  rw [e, norm_mul, norm_neg, norm_div, Real.log_mul (div_ne_zero hz' hw') h1,
    Real.log_div hz' hw']
  ring

theorem rCentre_pos (ψ : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ) : 0 < rCentre ψ t n := Real.exp_pos _

theorem zPt_ne_zero (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) : zPt ψ t C n ≠ 0 := by
  intro h0
  have := h.norm_zPt hn
  rw [h0, norm_zero] at this
  exact (rCentre_pos ψ t n).ne this

theorem c_lt_one (h : RegData ψ t C M) : cAngle ψ t C < 1 := by
  have := h.cAngle_lt
  have := Real.pi_lt_four
  linarith

/-- `‖z_n - r_n‖ ≤ d_n` (from `c < 1`). -/
theorem norm_zPt_sub_le_cellLen (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    ‖zPt ψ t C n - (rCentre ψ t n : ℂ)‖ ≤ cAngle ψ t C * cellLen t n :=
  h.norm_zPt_sub_le hn

/-- Below, `n ≥ 2`. -/
theorem below_ge2 (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hzn : t n ≤ ‖z‖ / 2)
    (hz0 : z ≠ 0) :
    |cellTerm ψ t C n z| ≤ (4 + 2 * (1 + C) * Real.log (1 + C)) * (cellLen t n / ‖z‖) := by
  have hn1 : 1 ≤ n := by omega
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have ha : 0 < t (n - 1) := t_pos h (by omega)
  have hlt := h.mono (show n - 1 < n by omega)
  have hd : 0 < cellLen t n := cellLen_pos h hn1
  have hs_le : ∀ s ∈ Icc (t (n - 1)) (t n), s ≤ ‖z‖ / 2 := fun s hs => hs.2.trans hzn
  have hszne : ∀ s ∈ Icc (t (n - 1)) (t n), (s : ℂ) ≠ z := fun s hs hsz => by
    have := hs_le s hs
    have h2 : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_of_nonneg (ha.trans_le hs.1).le]
    rw [hsz] at h2
    linarith
  have hcz := cellTerm_eq h hn hszne
  -- A part
  have hA := A_bound h hn (z := z) (M' := 4 * t n / ‖z‖) (fun s hs => by
    have hs0 : 0 < s := ha.trans_le hs.1
    have h2 : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_of_nonneg hs0.le]
    have h3 : ‖z‖ - s ≤ ‖(s : ℂ) - z‖ := by
      have := norm_sub_norm_le z (s : ℂ)
      rw [norm_sub_rev, h2] at this
      exact this
    have h4 : ‖z‖ / 2 ≤ ‖(s : ℂ) - z‖ := by linarith [hs_le s hs]
    refine ⟨by linarith, ?_⟩
    have hD : ‖z‖ ^ 2 / 4 ≤ ‖(s : ℂ) - z‖ ^ 2 := by nlinarith
    rw [div_le_div_iff₀ (by nlinarith) hzpos]
    have hs1 : s ≤ t n := hs.2
    nlinarith [mul_pos hzpos hzpos])
  -- B part
  have hr_pos := rCentre_pos ψ t n
  obtain ⟨har, hrb⟩ := h.rCentre_mem hn1
  have hrz : (rCentre ψ t n : ℝ) ≤ ‖z‖ / 2 := by linarith
  have hnz := h.norm_zPt hn1
  have hznz : zPt ψ t C n ≠ 0 := zPt_ne_zero h hn1
  have hrne : ((rCentre ψ t n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr_pos.ne'
  have hr_norm : ‖((rCentre ψ t n : ℝ) : ℂ)‖ = rCentre ψ t n := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
  have hrz' : ((rCentre ψ t n : ℝ) : ℂ) ≠ z := fun e => by
    rw [e] at hr_norm; linarith
  have hznz' : zPt ψ t C n ≠ z := fun e => by
    rw [e] at hnz; linarith
  have hB : Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖ - Real.log ‖1 - z / zPt ψ t C n‖ =
      Real.log ‖1 - (rCentre ψ t n : ℂ) / z‖ - Real.log ‖1 - zPt ψ t C n / z‖ := by
    rw [logNorm_swap hz0 hrne hrz', logNorm_swap hz0 hznz hznz', hnz, hr_norm]
    ring
  have hBb : |Real.log ‖1 - (rCentre ψ t n : ℂ) / z‖ - Real.log ‖1 - zPt ψ t C n / z‖| ≤
      2 * (cAngle ψ t C * cellLen t n / ‖z‖) := by
    have hm : ∀ w : ℂ, ‖w‖ ≤ ‖z‖ / 2 → (1 : ℝ) / 2 ≤ ‖1 - w / z‖ := fun w hw => by
      have h1 : ‖w / z‖ ≤ 1 / 2 := by
        rw [norm_div, div_le_iff₀ hzpos]; linarith
      have := norm_sub_norm_le (1 : ℂ) (w / z)
      rw [norm_one] at this
      linarith
    have := abs_log_norm_sub_le (w1 := 1 - (rCentre ψ t n : ℂ) / z) (w2 := 1 - zPt ψ t C n / z)
      (m := 1 / 2) (by norm_num) (hm _ (by rw [hr_norm]; exact hrz)) (hm _ (by rw [hnz]; exact hrz))
    refine this.trans ?_
    have e : (1 - (rCentre ψ t n : ℂ) / z) - (1 - zPt ψ t C n / z) =
        (zPt ψ t C n - (rCentre ψ t n : ℂ)) / z := by ring
    rw [e, norm_div]
    have := norm_zPt_sub_le_cellLen h hn1
    have h5 : ‖zPt ψ t C n - (rCentre ψ t n : ℂ)‖ / ‖z‖ ≤ cAngle ψ t C * cellLen t n / ‖z‖ := by
      gcongr
    calc ‖zPt ψ t C n - (rCentre ψ t n : ℂ)‖ / ‖z‖ / (1 / 2)
        = 2 * (‖zPt ψ t C n - (rCentre ψ t n : ℂ)‖ / ‖z‖) := by ring
      _ ≤ _ := by linarith
  have hc1 := c_lt_one h
  have hc0 := h.cAngle_pos
  have hBb' : 2 * (cAngle ψ t C * cellLen t n / ‖z‖) ≤ 2 * (cellLen t n / ‖z‖) := by
    have : cAngle ψ t C * cellLen t n ≤ cellLen t n := by nlinarith
    have := div_le_div_of_nonneg_right this hzpos.le
    linarith
  -- bound A
  have htn : 0 < t n := ha.trans hlt
  have hlam := lam_sq_le h hn
  have hta : t n ≤ (1 + C) * t (n - 1) := h.t_le hn
  have hlog0 : 0 ≤ Real.log (1 + C) := Real.log_nonneg (by linarith [h.one_le])
  have hA2 : 4 * t n / ‖z‖ / 2 * (Real.log (t n) - Real.log (t (n - 1))) ^ 2 ≤
      2 * (1 + C) * Real.log (1 + C) * (cellLen t n / ‖z‖) := by
    have h1 : 4 * t n / ‖z‖ / 2 * (Real.log (t n) - Real.log (t (n - 1))) ^ 2 ≤
        4 * t n / ‖z‖ / 2 * (Real.log (1 + C) * (cellLen t n / t (n - 1))) :=
      mul_le_mul_of_nonneg_left hlam (by positivity)
    refine h1.trans ?_
    have h2 : t n / t (n - 1) ≤ 1 + C := by
      rw [div_le_iff₀ ha]; linarith
    have e : 4 * t n / ‖z‖ / 2 * (Real.log (1 + C) * (cellLen t n / t (n - 1))) =
        2 * Real.log (1 + C) * (cellLen t n / ‖z‖) * (t n / t (n - 1)) := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ 2 * Real.log (1 + C) * (cellLen t n / ‖z‖) := by positivity
    calc 2 * Real.log (1 + C) * (cellLen t n / ‖z‖) * (t n / t (n - 1))
        ≤ 2 * Real.log (1 + C) * (cellLen t n / ‖z‖) * (1 + C) := by gcongr
      _ = _ := by ring
  rw [hcz]
  calc |_| ≤ |∫ s in cell t n, (Real.log ‖1 - z / (s : ℂ)‖ - Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖) *
        deriv ψ s| + |Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖ - Real.log ‖1 - z / zPt ψ t C n‖| :=
        abs_add_le _ _
    _ ≤ 2 * (1 + C) * Real.log (1 + C) * (cellLen t n / ‖z‖) + 2 * (cellLen t n / ‖z‖) := by
        rw [hB]; exact add_le_add (hA.trans hA2) (hBb.trans hBb')
    _ ≤ _ := by
        have hq : 0 ≤ cellLen t n / ‖z‖ := by positivity
        linarith

theorem cell_one (t : ℕ → ℝ) (h0 : t 0 = 0) : cell t 1 = Ioc 0 (t 1) := by
  simp [cell, h0]

theorem integrableOn_log_mul_psi (h : RegData ψ t C M) :
    IntegrableOn (fun s : ℝ => Real.log s * deriv ψ s) (cell t 1) := by
  have hT : 0 < t 1 := t_pos h le_rfl
  have hlog : IntegrableOn Real.log (Icc 0 (t 1)) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).1 intervalIntegral.intervalIntegrable_log'
  have := hlog.mul_continuousOn (psi_cont h).continuousOn isCompact_Icc
  rw [cell_one t h.t0]
  exact this.mono_set Ioc_subset_Icc_self

/-- Below, `n = 1`. -/
theorem below_one (h : RegData ψ t C M) {z : ℂ} (hzn : t 1 ≤ ‖z‖ / 2) (hz0 : z ≠ 0) :
    |cellTerm ψ t C 1 z| ≤ 4 * (cellLen t 1 / ‖z‖) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hT : 0 < t 1 := t_pos h le_rfl
  have hd : cellLen t 1 = t 1 := by simp [cellLen, h.t0]
  obtain ⟨hr0, hrT⟩ := h.rCentre_mem (le_refl 1)
  have hr_pos := rCentre_pos ψ t 1
  have hnz := h.norm_zPt (le_refl 1)
  have hznz : zPt ψ t C 1 ≠ 0 := zPt_ne_zero h le_rfl
  have hrne : ((rCentre ψ t 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr_pos.ne'
  have hr_norm : ‖((rCentre ψ t 1 : ℝ) : ℂ)‖ = rCentre ψ t 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
  have hznz' : zPt ψ t C 1 ≠ z := fun e => by
    rw [e] at hnz; linarith
  have hs_norm : ∀ s : ℝ, 0 ≤ s → ‖(s : ℂ)‖ = s := fun s hs => by
    rw [Complex.norm_real, Real.norm_of_nonneg hs]
  have hsz : ∀ s ∈ Icc 0 (t 1), (s : ℂ) ≠ z := fun s hs e => by
    have := hs_norm s hs.1
    rw [e] at this
    linarith [hs.2]
  have hm : ∀ w : ℂ, ‖w‖ ≤ ‖z‖ / 2 → (1 : ℝ) / 2 ≤ ‖1 - w / z‖ := fun w hw => by
    have h1 : ‖w / z‖ ≤ 1 / 2 := by
      rw [norm_div, div_le_iff₀ hzpos]; linarith
    have := norm_sub_norm_le (1 : ℂ) (w / z)
    rw [norm_one] at this
    linarith
  set c0 := Real.log ‖1 - zPt ψ t C 1 / z‖ with hc0
  set g : ℝ → ℝ := fun s => Real.log ‖1 - (s : ℂ) / z‖ - c0 with hg
  -- pointwise rewriting
  have hpt : ∀ s ∈ cell t 1, (Real.log ‖1 - z / (s : ℂ)‖ - Real.log ‖1 - z / zPt ψ t C 1‖) *
      deriv ψ s = g s * deriv ψ s + (-((Real.log s - Real.log (rCentre ψ t 1)) * deriv ψ s)) := by
    intro s hs
    rw [cell_one t h.t0] at hs
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.1.ne'
    have hsz' := hsz s ⟨hs.1.le, hs.2⟩
    rw [logNorm_swap hz0 hs0 hsz', logNorm_swap hz0 hznz hznz', hnz]
    simp only [hg, hc0, hs_norm s hs.1.le]
    ring
  have hgc : ContinuousOn g (Icc 0 (t 1)) := by
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.log
    · exact (continuousOn_const.sub (Complex.continuous_ofReal.continuousOn.div_const z)).norm
    · intro s hs
      have := hm (s : ℂ) (by rw [hs_norm s hs.1]; linarith [hs.2])
      intro h0
      rw [h0] at this
      norm_num at this
  have hgint : IntegrableOn (fun s => g s * deriv ψ s) (cell t 1) := by
    have : ContinuousOn (fun s => g s * deriv ψ s) (Icc 0 (t 1)) :=
      hgc.mul (psi_cont h).continuousOn
    rw [cell_one t h.t0]
    exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hlint : IntegrableOn (fun s : ℝ => (Real.log s - Real.log (rCentre ψ t 1)) * deriv ψ s)
      (cell t 1) := by
    have e : (fun s : ℝ => (Real.log s - Real.log (rCentre ψ t 1)) * deriv ψ s) =
        fun s => Real.log s * deriv ψ s - Real.log (rCentre ψ t 1) * deriv ψ s := by
      funext s; ring
    rw [e]
    exact (integrableOn_log_mul_psi h).sub ((integrableOn_psi h 1).const_mul _)
  unfold cellTerm
  have hmeas : MeasurableSet (cell t 1) := measurableSet_Ioc
  have hlneg : IntegrableOn (fun s : ℝ => -((Real.log s - Real.log (rCentre ψ t 1)) * deriv ψ s))
      (cell t 1) := hlint.neg
  rw [setIntegral_congr_fun hmeas hpt, integral_add hgint hlneg, integral_neg,
    h.integral_log_sub_centre le_rfl]
  simp only [neg_zero, add_zero]
  have hbound := norm_integral_le_of_norm_le (μ := volume.restrict (cell t 1))
    (f := fun s => g s * deriv ψ s) (g := fun s => (4 * (cellLen t 1 / ‖z‖)) * deriv ψ s)
    ((integrableOn_psi h 1).const_mul _)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (psi_nonneg h s)]
      refine mul_le_mul_of_nonneg_right ?_ (psi_nonneg h s)
      have hs' : s ∈ Ioc 0 (t 1) := by
        have h00 : t (1 - 1) = 0 := h.t0
        rw [h00] at hs; exact hs
      have := abs_log_norm_sub_le (w1 := 1 - (s : ℂ) / z) (w2 := 1 - zPt ψ t C 1 / z)
        (m := 1 / 2) (by norm_num) (hm _ (by rw [hs_norm s hs'.1.le]; linarith [hs'.2]))
        (hm _ (by rw [hnz]; linarith))
      refine this.trans ?_
      have e : (1 - (s : ℂ) / z) - (1 - zPt ψ t C 1 / z) = (zPt ψ t C 1 - (s : ℂ)) / z := by ring
      rw [e, norm_div]
      have h1 : ‖zPt ψ t C 1 - (s : ℂ)‖ ≤ 2 * t 1 := by
        calc ‖zPt ψ t C 1 - (s : ℂ)‖ ≤ ‖zPt ψ t C 1‖ + ‖(s : ℂ)‖ := norm_sub_le _ _
          _ ≤ t 1 + t 1 := by rw [hnz, hs_norm s hs'.1.le]; linarith [hs'.2]
          _ = 2 * t 1 := by ring
      rw [hd]
      calc ‖zPt ψ t C 1 - (s : ℂ)‖ / ‖z‖ / (1 / 2) = 2 * (‖zPt ψ t C 1 - (s : ℂ)‖ / ‖z‖) := by ring
        _ ≤ 2 * (2 * t 1 / ‖z‖) := by gcongr
        _ = 4 * (t 1 / ‖z‖) := by ring))
  rw [integral_const_mul, h.integral_cell le_rfl, Real.norm_eq_abs] at hbound
  simpa using hbound

theorem abs_cellTerm_below (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hzn : t n ≤ ‖z‖ / 2) (hz0 : z ≠ 0) :
    |cellTerm ψ t C n z| ≤ (4 + 2 * (1 + C) * Real.log (1 + C)) * (cellLen t n / ‖z‖) := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have : n = 1 := by omega
    subst this
    have := below_one h hzn hz0
    have hq : 0 ≤ cellLen t 1 / ‖z‖ := by
      have := cellLen_pos h (le_refl 1)
      positivity
    have hlog0 : 0 ≤ Real.log (1 + C) := Real.log_nonneg (by linarith [h.one_le])
    have : 0 ≤ 2 * (1 + C) * Real.log (1 + C) := by
      have := h.one_le; positivity
    nlinarith
  · exact below_ge2 h h2 hzn hz0

/-- Above, `n ≥ 2`. -/
theorem abs_cellTerm_above (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) {z : ℂ}
    (_hz : 0 ≤ z.im) (hzn : 2 * ‖z‖ ≤ t (n - 1)) (hz0 : z ≠ 0) :
    |cellTerm ψ t C n z| ≤
      (2 * Real.log (1 + C) + 2) * (cellLen t n * ‖z‖ / t (n - 1) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have ha : 0 < t (n - 1) := t_pos h (by omega)
  have hlt := h.mono (show n - 1 < n by omega)
  have hd : 0 < cellLen t n := cellLen_pos h hn1
  have hs_ge : ∀ s ∈ Icc (t (n - 1)) (t n), 2 * ‖z‖ ≤ s := fun s hs => hzn.trans hs.1
  have hs_norm : ∀ s : ℝ, 0 ≤ s → ‖(s : ℂ)‖ = s := fun s hs => by
    rw [Complex.norm_real, Real.norm_of_nonneg hs]
  have hszne : ∀ s ∈ Icc (t (n - 1)) (t n), (s : ℂ) ≠ z := fun s hs hsz => by
    have := hs_ge s hs
    have h2 := hs_norm s (ha.trans_le hs.1).le
    rw [hsz] at h2
    linarith
  have hcz := cellTerm_eq h hn hszne
  have hA := A_bound h hn (z := z) (M' := 4 * ‖z‖ / t (n - 1)) (fun s hs => by
    have hs0 : 0 < s := ha.trans_le hs.1
    have h2 := hs_norm s hs0.le
    have h3 : s - ‖z‖ ≤ ‖(s : ℂ) - z‖ := by
      have := norm_sub_norm_le (s : ℂ) z
      rw [h2] at this
      exact this
    have h4 : s / 2 ≤ ‖(s : ℂ) - z‖ := by linarith [hs_ge s hs]
    refine ⟨by linarith, ?_⟩
    have hD : s ^ 2 / 4 ≤ ‖(s : ℂ) - z‖ ^ 2 := by nlinarith
    rw [div_le_div_iff₀ (by nlinarith) ha]
    have hs1 : t (n - 1) ≤ s := hs.1
    -- ‖z‖ s a ≤ 4 ‖z‖ D, D ≥ s²/4 ≥ s a /4
    have : s * t (n - 1) ≤ s ^ 2 := by nlinarith
    nlinarith [mul_pos hzpos hs0])
  have hr_pos := rCentre_pos ψ t n
  obtain ⟨har, hrb⟩ := h.rCentre_mem hn1
  have hnz := h.norm_zPt hn1
  have hznz : zPt ψ t C n ≠ 0 := zPt_ne_zero h hn1
  have hrne : ((rCentre ψ t n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr_pos.ne'
  have hr_norm : ‖((rCentre ψ t n : ℝ) : ℂ)‖ = rCentre ψ t n := hs_norm _ hr_pos.le
  have hzr : ‖z‖ ≤ rCentre ψ t n / 2 := by linarith
  have hzr1 : ∀ w : ℂ, ‖w‖ = rCentre ψ t n → (1 : ℝ) / 2 ≤ ‖1 - z / w‖ := fun w hw => by
    have h1 : ‖z / w‖ ≤ 1 / 2 := by
      rw [norm_div, hw, div_le_iff₀ hr_pos]; linarith
    have := norm_sub_norm_le (1 : ℂ) (z / w)
    rw [norm_one] at this
    linarith
  have hBb : |Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖ - Real.log ‖1 - z / zPt ψ t C n‖| ≤
      2 * (‖z‖ * (cAngle ψ t C * cellLen t n) / rCentre ψ t n ^ 2) := by
    have := abs_log_norm_sub_le (w1 := 1 - z / (rCentre ψ t n : ℂ)) (w2 := 1 - z / zPt ψ t C n)
      (m := 1 / 2) (by norm_num) (hzr1 _ hr_norm) (hzr1 _ hnz)
    refine this.trans ?_
    have e : (1 - z / (rCentre ψ t n : ℂ)) - (1 - z / zPt ψ t C n) =
        z * (((rCentre ψ t n : ℂ) - zPt ψ t C n)) / ((rCentre ψ t n : ℂ) * zPt ψ t C n) := by
      field_simp
      ring
    rw [e, norm_div, norm_mul, norm_mul, hr_norm, hnz, norm_sub_rev]
    have h5 := norm_zPt_sub_le_cellLen h hn1
    have h6 : ‖z‖ * ‖zPt ψ t C n - (rCentre ψ t n : ℂ)‖ / (rCentre ψ t n * rCentre ψ t n) ≤
        ‖z‖ * (cAngle ψ t C * cellLen t n) / rCentre ψ t n ^ 2 := by
      rw [sq]; gcongr
    calc ‖z‖ * ‖zPt ψ t C n - (rCentre ψ t n : ℂ)‖ / (rCentre ψ t n * rCentre ψ t n) / (1 / 2)
        = 2 * (‖z‖ * ‖zPt ψ t C n - (rCentre ψ t n : ℂ)‖ / (rCentre ψ t n * rCentre ψ t n)) := by ring
      _ ≤ _ := by linarith
  have hc1 := c_lt_one h
  have hc0 := h.cAngle_pos
  have hBb' : 2 * (‖z‖ * (cAngle ψ t C * cellLen t n) / rCentre ψ t n ^ 2) ≤
      2 * (‖z‖ * cellLen t n / t (n - 1) ^ 2) := by
    have h1 : cAngle ψ t C * cellLen t n ≤ cellLen t n := by nlinarith
    have h2 : t (n - 1) ^ 2 ≤ rCentre ψ t n ^ 2 := by gcongr
    have h3 : ‖z‖ * (cAngle ψ t C * cellLen t n) / rCentre ψ t n ^ 2 ≤
        ‖z‖ * cellLen t n / t (n - 1) ^ 2 := by
      calc ‖z‖ * (cAngle ψ t C * cellLen t n) / rCentre ψ t n ^ 2
          ≤ ‖z‖ * cellLen t n / rCentre ψ t n ^ 2 := by gcongr
        _ ≤ ‖z‖ * cellLen t n / t (n - 1) ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) h2
    linarith
  have hlam := lam_sq_le h hn
  have hlog0 : 0 ≤ Real.log (1 + C) := Real.log_nonneg (by linarith [h.one_le])
  have hA2 : 4 * ‖z‖ / t (n - 1) / 2 * (Real.log (t n) - Real.log (t (n - 1))) ^ 2 ≤
      2 * Real.log (1 + C) * (cellLen t n * ‖z‖ / t (n - 1) ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hlam (by positivity : 0 ≤ 4 * ‖z‖ / t (n - 1) / 2)
    refine h1.trans (le_of_eq ?_)
    field_simp
    ring
  rw [hcz]
  calc |_| ≤ |∫ s in cell t n, (Real.log ‖1 - z / (s : ℂ)‖ - Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖) *
        deriv ψ s| + |Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖ - Real.log ‖1 - z / zPt ψ t C n‖| :=
        abs_add_le _ _
    _ ≤ 2 * Real.log (1 + C) * (cellLen t n * ‖z‖ / t (n - 1) ^ 2) +
        2 * (‖z‖ * cellLen t n / t (n - 1) ^ 2) :=
        add_le_add (hA.trans hA2) (hBb.trans hBb')
    _ = _ := by ring

end FF.D1
