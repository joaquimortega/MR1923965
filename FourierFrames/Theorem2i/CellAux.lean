import FourierFrames.Theorem2i.Taylor

/-!
# M08 helper (fork D1): the `A_n`/`B_n` decomposition of the cell term
-/

open MeasureTheory Set Complex Filter Topology

noncomputable section

namespace FF.D1

open FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M : ℝ}

theorem t_pos (h : RegData ψ t C M) {k : ℕ} (hk : 1 ≤ k) : 0 < t k := by
  have := h.mono (Nat.pos_of_ne_zero (by omega) : 0 < k)
  rwa [h.t0] at this

theorem cellLen_pos (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) : 0 < cellLen t n := by
  unfold cellLen
  have := h.mono (show n - 1 < n by omega)
  linarith

theorem psi_cont (h : RegData ψ t C M) : Continuous (deriv ψ) :=
  h.adm.1.continuous_deriv le_rfl

theorem psi_nonneg (h : RegData ψ t C M) (s : ℝ) : 0 ≤ deriv ψ s :=
  h.adm.2.1.deriv_nonneg

theorem integrableOn_psi (h : RegData ψ t C M) (n : ℕ) : IntegrableOn (deriv ψ) (cell t n) :=
  ((psi_cont h).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self

theorem cell_subset (n : ℕ) : cell t n ⊆ Icc (t (n - 1)) (t n) := Ioc_subset_Icc_self

/-- Continuity of `s ↦ log ‖1 - z / s‖` on an interval of positive reals avoiding `z`. -/
theorem continuousOn_logNorm (z : ℂ) {a b : ℝ} (ha : 0 < a)
    (hz : ∀ s ∈ Icc a b, (s : ℂ) ≠ z) :
    ContinuousOn (fun s : ℝ => Real.log ‖1 - z / (s : ℂ)‖) (Icc a b) := by
  have hs0 : ∀ s ∈ Icc a b, (s : ℂ) ≠ 0 := fun s hs => by
    exact_mod_cast (ha.trans_le hs.1).ne'
  apply ContinuousOn.log
  · exact (continuousOn_const.sub (continuousOn_const.div Complex.continuous_ofReal.continuousOn hs0)).norm
  · intro s hs
    have hs' := hs0 s hs
    have h1 : 1 - z / (s : ℂ) = ((s : ℂ) - z) / s := by field_simp
    rw [h1]
    exact norm_ne_zero_iff.2 (div_ne_zero (sub_ne_zero.2 (hz s hs)) hs')

theorem sqrt_re_im (z : ℂ) : Real.sqrt (z.re ^ 2 + z.im ^ 2) = ‖z‖ := by
  rw [← Real.sqrt_sq (norm_nonneg z), Complex.sq_norm, Complex.normSq_apply]
  congr 1
  ring

/-- Taylor estimate for the smeared term `A_n`. -/
theorem A_bound (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) {z : ℂ} {M' : ℝ}
    (hz : ∀ s ∈ Icc (t (n - 1)) (t n),
      0 < ‖(s : ℂ) - z‖ ∧ ‖z‖ * s / ‖(s : ℂ) - z‖ ^ 2 ≤ M') :
    |∫ s in cell t n, (Real.log ‖1 - z / (s : ℂ)‖ - Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖) *
        deriv ψ s| ≤
      M' / 2 * (Real.log (t n) - Real.log (t (n - 1))) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  set a := t (n - 1) with ha_def
  set b := t n with hb_def
  set r := rCentre ψ t n with hr_def
  have ha : 0 < a := t_pos h (by omega)
  obtain ⟨har, hrb⟩ := h.rCentre_mem hn1
  have hr_mem : r ∈ Icc a b := ⟨har.le, hrb.le⟩
  have hszne : ∀ s ∈ Icc a b, (s : ℂ) ≠ z := fun s hs hsz => by
    have := (hz s hs).1
    rw [hsz, sub_self, norm_zero] at this
    exact lt_irrefl _ this
  have hspos : ∀ s ∈ Icc a b, 0 < s := fun s hs => ha.trans_le hs.1
  have hM'0 : 0 ≤ M' := by
    have h1 := (hz a ⟨le_rfl, (h.mono (show n - 1 < n by omega)).le⟩).2
    have h2 : 0 ≤ ‖z‖ * a / ‖(a : ℂ) - z‖ ^ 2 := by positivity
    linarith
  set F : ℝ → ℝ := fun s => Real.log ‖1 - z / (s : ℂ)‖ with hF
  have hFc : ContinuousOn F (Icc a b) := continuousOn_logNorm z ha hszne
  set HH := Hfun z.re z.im with hHH
  have hFH : ∀ s ∈ Icc a b, F s = HH (Real.log s) := fun s hs =>
    log_norm_one_sub_div_eq z (hspos s hs) (hszne s hs)
  set σ0 := Real.log r with hσ0
  have hlog_mem : ∀ s ∈ Icc a b, Real.log s ∈ Icc (Real.log a) (Real.log b) := fun s hs =>
    ⟨Real.log_le_log ha hs.1, Real.log_le_log (hspos s hs) hs.2⟩
  have hb : 0 < b := ha.trans_le (h.mono (show n - 1 < n by omega)).le
  have hexp_mem : ∀ σ ∈ Icc (Real.log a) (Real.log b), Real.exp σ ∈ Icc a b := fun σ hσ =>
    ⟨(Real.exp_log ha).symm.le.trans (Real.exp_le_exp.2 hσ.1),
     (Real.exp_le_exp.2 hσ.2).trans (Real.exp_log hb).le⟩
  have hD : ∀ σ ∈ Icc (Real.log a) (Real.log b), Dd z.re z.im σ ≠ 0 := fun σ hσ => by
    have hm := hexp_mem σ hσ
    have := Dd_log z (Real.exp σ) (Real.exp_pos σ)
    rw [Real.log_exp] at this
    rw [this]
    exact pow_ne_zero 2 (hz _ hm).1.ne'
  have h1 : ∀ σ ∈ Icc (Real.log a) (Real.log b), HasDerivAt HH (H1 z.re z.im σ) σ :=
    fun σ hσ => hasDerivAt_Hfun (hD σ hσ)
  have h2 : ∀ σ ∈ Icc (Real.log a) (Real.log b), HasDerivAt (H1 z.re z.im) (H2 z.re z.im σ) σ :=
    fun σ hσ => hasDerivAt_H1 (hD σ hσ)
  have hM2 : ∀ σ ∈ Icc (Real.log a) (Real.log b), |H2 z.re z.im σ| ≤ M' := fun σ hσ => by
    have hm := hexp_mem σ hσ
    have hpos := Dd_pos (hD σ hσ)
    refine (abs_H2_le hpos).trans ?_
    have := (hz _ hm).2
    have e := Dd_log z (Real.exp σ) (Real.exp_pos σ)
    rw [Real.log_exp] at e
    rw [e, sqrt_re_im]
    exact this
  have hσ0m : σ0 ∈ Icc (Real.log a) (Real.log b) := hlog_mem r hr_mem
  set lam := Real.log b - Real.log a with hlam
  -- pointwise Taylor bound
  have hT : ∀ s ∈ Icc a b, |HH (Real.log s) - HH σ0 - H1 z.re z.im σ0 * (Real.log s - σ0)| ≤
      M' / 2 * lam ^ 2 := by
    intro s hs
    have := taylor2 h1 h2 hM2 hσ0m (hlog_mem s hs)
    refine this.trans ?_
    have hl := hlog_mem s hs
    have hsq : (Real.log s - σ0) ^ 2 ≤ lam ^ 2 := by
      apply sq_le_sq'
      · linarith [hl.1, hl.2, hσ0m.1, hσ0m.2]
      · linarith [hl.1, hl.2, hσ0m.1, hσ0m.2]
    nlinarith
  -- integrals
  have hgint : IntegrableOn (fun s : ℝ => (Real.log s - σ0) * deriv ψ s) (cell t n) := by
    have : ContinuousOn (fun s : ℝ => (Real.log s - σ0) * deriv ψ s) (Icc a b) := by
      apply ContinuousOn.mul
      · exact (Real.continuousOn_log.mono (fun s hs => (hspos s hs).ne')).sub continuousOn_const
      · exact (psi_cont h).continuousOn
    exact this.integrableOn_Icc.mono_set (cell_subset n)
  have hf1int : IntegrableOn (fun s : ℝ => (F s - F r) * deriv ψ s) (cell t n) := by
    have : ContinuousOn (fun s : ℝ => (F s - F r) * deriv ψ s) (Icc a b) :=
      (hFc.sub continuousOn_const).mul (psi_cont h).continuousOn
    exact this.integrableOn_Icc.mono_set (cell_subset n)
  have hg0 : ∫ s in cell t n, (Real.log s - σ0) * deriv ψ s = 0 := h.integral_log_sub_centre hn1
  have hsplit : ∫ s in cell t n, (F s - F r) * deriv ψ s =
      ∫ s in cell t n, (HH (Real.log s) - HH σ0 - H1 z.re z.im σ0 * (Real.log s - σ0)) *
        deriv ψ s := by
    have e1 : ∫ s in cell t n, (HH (Real.log s) - HH σ0 -
        H1 z.re z.im σ0 * (Real.log s - σ0)) * deriv ψ s =
        ∫ s in cell t n, ((F s - F r) * deriv ψ s -
          H1 z.re z.im σ0 * ((Real.log s - σ0) * deriv ψ s)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      have hs' := cell_subset n hs
      simp only
      rw [← hFH s hs', hFH r hr_mem]
      ring
    rw [e1, integral_sub hf1int (hgint.const_mul _), integral_const_mul, hg0]
    ring
  rw [hsplit]
  have hbound := norm_integral_le_of_norm_le (μ := volume.restrict (cell t n))
    (f := fun s : ℝ => (HH (Real.log s) - HH σ0 - H1 z.re z.im σ0 * (Real.log s - σ0)) *
        deriv ψ s)
    (g := fun s : ℝ => (M' / 2 * lam ^ 2) * deriv ψ s)
    ((integrableOn_psi h n).const_mul _)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (psi_nonneg h s)]
      exact mul_le_mul_of_nonneg_right (hT s (cell_subset n hs)) (psi_nonneg h s)))
  rw [integral_const_mul, h.integral_cell hn1, Real.norm_eq_abs] at hbound
  simpa using hbound

/-- `cellTerm = A_n + B_n`. -/
theorem cellTerm_eq (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) {z : ℂ}
    (hz : ∀ s ∈ Icc (t (n - 1)) (t n), (s : ℂ) ≠ z) :
    cellTerm ψ t C n z =
      (∫ s in cell t n, (Real.log ‖1 - z / (s : ℂ)‖ - Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖) *
        deriv ψ s) +
      (Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖ - Real.log ‖1 - z / zPt ψ t C n‖) := by
  have hn1 : 1 ≤ n := by omega
  have ha : 0 < t (n - 1) := t_pos h (by omega)
  obtain ⟨har, hrb⟩ := h.rCentre_mem hn1
  have hr_mem : rCentre ψ t n ∈ Icc (t (n - 1)) (t n) := ⟨har.le, hrb.le⟩
  have hFc := continuousOn_logNorm z ha hz
  have hf1int : IntegrableOn (fun s : ℝ =>
      (Real.log ‖1 - z / (s : ℂ)‖ - Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖) * deriv ψ s)
      (cell t n) := by
    have : ContinuousOn (fun s : ℝ =>
      (Real.log ‖1 - z / (s : ℂ)‖ - Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖) * deriv ψ s)
        (Icc (t (n - 1)) (t n)) :=
      (hFc.sub continuousOn_const).mul (psi_cont h).continuousOn
    exact this.integrableOn_Icc.mono_set (cell_subset n)
  unfold cellTerm
  have e : ∫ s in cell t n, (Real.log ‖1 - z / (s : ℂ)‖ - Real.log ‖1 - z / zPt ψ t C n‖) *
      deriv ψ s = ∫ s in cell t n,
        ((Real.log ‖1 - z / (s : ℂ)‖ - Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖) * deriv ψ s +
        (Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖ - Real.log ‖1 - z / zPt ψ t C n‖) *
          deriv ψ s) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s _
    simp only
    ring
  rw [e, integral_add hf1int ((integrableOn_psi h n).const_mul _), integral_const_mul,
    h.integral_cell hn1]
  ring

theorem lam_nonneg (h : RegData ψ t C M) {n : ℕ} (hn2 : 2 ≤ n) :
    0 ≤ Real.log (t n) - Real.log (t (n - 1)) := by
  have ha : 0 < t (n - 1) := t_pos h (by omega)
  have := h.mono (show n - 1 < n by omega)
  linarith [Real.log_le_log ha this.le]

theorem lam_le_log (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) :
    Real.log (t n) - Real.log (t (n - 1)) ≤ Real.log (1 + C) := by
  have ha : 0 < t (n - 1) := t_pos h (by omega)
  have hb : 0 < t n := t_pos h (by omega)
  have := h.t_le hn
  have hC := h.one_le
  have h1 : Real.log (t n) ≤ Real.log ((1 + C) * t (n - 1)) := Real.log_le_log hb this
  rw [Real.log_mul (by linarith) ha.ne'] at h1
  linarith

theorem lam_le_div (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) :
    Real.log (t n) - Real.log (t (n - 1)) ≤ cellLen t n / t (n - 1) := by
  have ha : 0 < t (n - 1) := t_pos h (by omega)
  have hb : 0 < t n := t_pos h (by omega)
  rw [← Real.log_div hb.ne' ha.ne']
  have := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have e : t n / t (n - 1) - 1 = cellLen t n / t (n - 1) := by unfold cellLen; field_simp
  linarith

theorem lam_sq_le (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) :
    (Real.log (t n) - Real.log (t (n - 1))) ^ 2 ≤
      Real.log (1 + C) * (cellLen t n / t (n - 1)) := by
  have h0 := lam_nonneg h hn
  rw [sq]
  exact mul_le_mul (lam_le_log h hn) (lam_le_div h hn) h0 ((h0.trans (lam_le_log h hn)))

end FF.D1
