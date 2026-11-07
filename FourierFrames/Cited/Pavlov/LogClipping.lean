import FourierFrames.Cited.Pavlov.Basic

/-!
# Continuous compact cutoffs of a logarithmic boundary deficit

The positive clipping floor makes the cutoff continuous even at zeros.
See `blueprint/P5_LogClipping.md`.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace FF.Pavlov

/-- A continuous cutoff equal to one on `[-n,n]` and zero outside radius `n+1`. -/
def logClipCutoff (n : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 ((n:ℝ)+1-|t|))

/-- Continuous compact approximation of `log M-log ‖A‖`, including boundary zeros. -/
def logClip (M : ℝ) (A : ℂ → ℂ) (n : ℕ) (t : ℝ) : ℝ :=
  logClipCutoff n t *
    (Real.log M-Real.log (max ‖A t‖ (M*Real.exp (-(n:ℝ)))))

theorem logClipCutoff_nonneg (n : ℕ) (t : ℝ) : 0 ≤ logClipCutoff n t :=
  le_max_left _ _

theorem logClipCutoff_le_one (n : ℕ) (t : ℝ) : logClipCutoff n t ≤ 1 := by
  exact max_le (by norm_num) (min_le_left _ _)

theorem logClipCutoff_monotone (t : ℝ) : Monotone (fun n : ℕ ↦ logClipCutoff n t) := by
  intro m n hmn
  apply max_le_max le_rfl
  apply min_le_min le_rfl
  have he : (m:ℝ) ≤ n := by exact_mod_cast hmn
  linarith

theorem logClipCutoff_eq_one {n : ℕ} {t : ℝ} (h : |t| ≤ (n:ℝ)) :
    logClipCutoff n t = 1 := by
  unfold logClipCutoff
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem logClipCutoff_eq_zero {n : ℕ} {t : ℝ} (h : (n:ℝ)+1 ≤ |t|) :
    logClipCutoff n t = 0 := by
  unfold logClipCutoff
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

theorem continuous_logClipCutoff (n : ℕ) : Continuous (logClipCutoff n) := by
  unfold logClipCutoff
  fun_prop

private theorem logClip_floor_pos {M : ℝ} (hM : 0 < M) (A : ℂ → ℂ) (n : ℕ) (t : ℝ) :
    0 < max ‖A t‖ (M*Real.exp (-(n:ℝ))) :=
  (mul_pos hM (Real.exp_pos _)).trans_le (le_max_right _ _)

private theorem logClip_floor_le {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hbd : ∀ t : ℝ, ‖A t‖ ≤ M) (n : ℕ) (t : ℝ) :
    max ‖A t‖ (M*Real.exp (-(n:ℝ))) ≤ M := by
  apply max_le (hbd t)
  have he : Real.exp (-(n:ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg n)
  exact mul_le_of_le_one_right hM.le he

private theorem logClip_deficit_nonneg {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hbd : ∀ t : ℝ, ‖A t‖ ≤ M) (n : ℕ) (t : ℝ) :
    0 ≤ Real.log M-Real.log (max ‖A t‖ (M*Real.exp (-(n:ℝ)))) := by
  exact sub_nonneg.mpr (Real.log_le_log (logClip_floor_pos hM A n t)
    (logClip_floor_le hM hbd n t))

theorem logClip_nonneg {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hbd : ∀ t : ℝ, ‖A t‖ ≤ M) (n : ℕ) (t : ℝ) : 0 ≤ logClip M A n t := by
  exact mul_nonneg (logClipCutoff_nonneg n t) (logClip_deficit_nonneg hM hbd n t)

theorem logClip_monotone {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hbd : ∀ t : ℝ, ‖A t‖ ≤ M) (t : ℝ) :
    Monotone (fun n : ℕ ↦ logClip M A n t) := by
  intro m n hmn
  have hfloor : max ‖A t‖ (M*Real.exp (-(n:ℝ))) ≤
      max ‖A t‖ (M*Real.exp (-(m:ℝ))) := by
    apply max_le_max le_rfl
    apply mul_le_mul_of_nonneg_left _ hM.le
    apply Real.exp_le_exp.mpr
    have he : (m:ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  apply mul_le_mul (logClipCutoff_monotone t hmn) _
    (logClip_deficit_nonneg hM hbd m t) (logClipCutoff_nonneg n t)
  exact sub_le_sub_left (Real.log_le_log (logClip_floor_pos hM A n t) hfloor) _

theorem continuous_logClip {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hA : Continuous (fun t : ℝ ↦ A t)) (n : ℕ) : Continuous (logClip M A n) := by
  have hc : Continuous (fun t : ℝ ↦ max ‖A t‖ (M*Real.exp (-(n:ℝ)))) :=
    hA.norm.max continuous_const
  exact (continuous_logClipCutoff n).mul
    (continuous_const.sub (hc.log (fun t ↦ (logClip_floor_pos hM A n t).ne')))

theorem logClip_eq_zero_of_abs_ge {M : ℝ} {A : ℂ → ℂ} {n : ℕ} {t : ℝ}
    (h : (n:ℝ)+1 ≤ |t|) : logClip M A n t = 0 := by
  simp only [logClip, logClipCutoff_eq_zero h, zero_mul]

theorem hasCompactSupport_logClip (M : ℝ) (A : ℂ → ℂ) (n : ℕ) :
    HasCompactSupport (logClip M A n) := by
  apply HasCompactSupport.intro (K := Icc (-((n:ℝ)+1)) ((n:ℝ)+1)) isCompact_Icc
  intro t ht
  apply logClip_eq_zero_of_abs_ge
  by_contra hn
  have h := abs_lt.mp (not_le.mp hn)
  exact ht ⟨h.1.le, h.2.le⟩

theorem integrable_logClip {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hA : Continuous (fun t : ℝ ↦ A t)) (n : ℕ) : Integrable (logClip M A n) :=
  (continuous_logClip hM hA n).integrable_of_hasCompactSupport (hasCompactSupport_logClip M A n)

theorem logIntegrable_logClip {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hA : Continuous (fun t : ℝ ↦ A t)) (n : ℕ) : LogIntegrable (logClip M A n) := by
  have hc : Continuous (fun t : ℝ ↦ logClip M A n t / (1+t^2)) :=
    (continuous_logClip hM hA n).div (by fun_prop) (fun t ↦ by positivity)
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (-((n:ℝ)+1)) ((n:ℝ)+1)) isCompact_Icc
  intro t ht
  have hz : logClip M A n t = 0 := by
    apply logClip_eq_zero_of_abs_ge
    by_contra hn
    have h := abs_lt.mp (not_le.mp hn)
    exact ht ⟨h.1.le, h.2.le⟩
  simp only [hz, zero_div]

/-- Each approximation has an explicit uniform bound. -/
theorem logClip_le_nat {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hbd : ∀ t : ℝ, ‖A t‖ ≤ M) (n : ℕ) (t : ℝ) : logClip M A n t ≤ n := by
  apply le_trans (mul_le_of_le_one_left (logClip_deficit_nonneg hM hbd n t)
    (logClipCutoff_le_one n t))
  have he := Real.log_le_log (mul_pos hM (Real.exp_pos (-(n:ℝ))))
    (le_max_right ‖A t‖ (M*Real.exp (-(n:ℝ))))
  rw [Real.log_mul hM.ne' (Real.exp_ne_zero _), Real.log_exp] at he
  linarith

/-- The clipped deficit is bounded by the genuine deficit away from zeros. -/
theorem logClip_le_deficit {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hbd : ∀ t : ℝ, ‖A t‖ ≤ M) (n : ℕ) {t : ℝ} (ht : A t ≠ 0) :
    logClip M A n t ≤ Real.log M-Real.log ‖A t‖ := by
  apply le_trans (mul_le_of_le_one_left (logClip_deficit_nonneg hM hbd n t)
    (logClipCutoff_le_one n t))
  exact sub_le_sub_left (Real.log_le_log (norm_pos_iff.mpr ht) (le_max_left _ _)) _

/-- The boundary comparison is valid even at zeros of the analytic function. -/
theorem logClip_boundary_bound {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hbd : ∀ t : ℝ, ‖A t‖ ≤ M) (n : ℕ) (t : ℝ) :
    ‖A t‖^2 * Real.exp (2*logClip M A n t) ≤ M^2 := by
  let r := max ‖A t‖ (M*Real.exp (-(n:ℝ)))
  have hr : 0 < r := logClip_floor_pos hM A n t
  have hg : logClip M A n t ≤ Real.log M-Real.log r :=
    mul_le_of_le_one_left (logClip_deficit_nonneg hM hbd n t) (logClipCutoff_le_one n t)
  have he : Real.exp (logClip M A n t) ≤ M/r := by
    calc
      _ ≤ Real.exp (Real.log M-Real.log r) := Real.exp_le_exp.mpr hg
      _ = M/r := by rw [Real.exp_sub, Real.exp_log hM, Real.exp_log hr]
  have hmul : ‖A t‖*Real.exp (logClip M A n t) ≤ M := by
    calc
      _ ≤ r*(M/r) := mul_le_mul (le_max_left _ _) he (Real.exp_pos _).le hr.le
      _ = M := by field_simp
  have hsq := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hmul 2
  convert hsq using 1
  rw [mul_pow]
  congr 1
  simpa using (Real.exp_nat_mul (logClip M A n t) 2)

/-- Away from zeros, the clipping eventually disappears exactly. -/
theorem eventually_logClip_eq {M : ℝ} {A : ℂ → ℂ}
    {t : ℝ} (ht : A t ≠ 0) :
    ∀ᶠ n : ℕ in atTop, logClip M A n t = Real.log M-Real.log ‖A t‖ := by
  have hlim : Tendsto (fun n : ℕ ↦ M*Real.exp (-(n:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using tendsto_const_nhds.mul
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop)
  have hfloor := hlim.eventually_lt_const (norm_pos_iff.mpr ht)
  have hcut : ∀ᶠ n : ℕ in atTop, |t| ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |t|)
  filter_upwards [hfloor, hcut] with n hn hc
  simp only [logClip, logClipCutoff_eq_one hc, max_eq_left hn.le, one_mul]

/-- Convergence is claimed only at nonzero boundary points. -/
theorem tendsto_logClip {M : ℝ} {A : ℂ → ℂ}
    {t : ℝ} (ht : A t ≠ 0) :
    Tendsto (fun n : ℕ ↦ logClip M A n t) atTop (𝓝 (Real.log M-Real.log ‖A t‖)) :=
by
  have heq : (fun n : ℕ ↦ logClip M A n t) =ᶠ[atTop]
      (fun _ ↦ Real.log M-Real.log ‖A t‖) := eventually_logClip_eq ht
  exact Tendsto.congr' heq.symm tendsto_const_nhds

end FF.Pavlov
