import FourierFrames.Corollary2
import OrtegaCerdaSeip.Products.Canonical

/-!
# M08 helper: data, partition, zeros

See `blueprint/M08_Theorem2i.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Data: cells, log-centres, zeros, convergence factors -/

/-- The `n`-th cell `(t_{n-1}, t_n]` (`n ≥ 1`). -/
def cell (t : ℕ → ℝ) (n : ℕ) : Set ℝ := Ioc (t (n - 1)) (t n)

/-- Its length `d_n = t_n - t_{n-1}`. -/
def cellLen (t : ℕ → ℝ) (n : ℕ) : ℝ := t n - t (n - 1)

/-- The log-centre `r_n`, formula (9): `log r_n = ∫_{t_{n-1}}^{t_n} log s dψ(s)`. -/
def rCentre (ψ : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (∫ s in cell t n, Real.log s * deriv ψ s)

/-- `κ ≥ sup_n t_n / r_n` (`C` is the regularity constant of `d_n ≃ d_{n+1}`). -/
def kappa (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) : ℝ := max (1 + C) (t 1 / rCentre ψ t 1)

/-- The constant `c = π / (4 κ)`, so that `c d_n / r_n ≤ π/4` and `c < π/4`. -/
def cAngle (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) : ℝ := Real.pi / (4 * kappa ψ t C)

/-- The zero `z_n = r_n e^{-i c d_n / r_n} ∈ ℂ₋`. -/
def zPt (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) (n : ℕ) : ℂ :=
  (rCentre ψ t n : ℂ) *
    Complex.exp (-(Complex.I * ((cAngle ψ t C * cellLen t n / rCentre ψ t n : ℝ) : ℂ)))

/-- The (real) convergence factor `c_n = ∫_{cell n, s > 1} dψ(s)/s`, matching `UPsi`. -/
def convFac (ψ : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∫ s in cell t n, (1 - (Icc (-1 : ℝ) 1).indicator 1 s) / s * deriv ψ s

/-- The set of zeros. -/
def zSet (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) : Set ℂ := {a | ∃ n : ℕ, 1 ≤ n ∧ zPt ψ t C n = a}

open Classical in
/-- The convergence factor as a function of the zero (`zPt` is injective on `n ≥ 1`). -/
def convFun (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) (a : ℂ) : ℂ :=
  if h : ∃ n : ℕ, 1 ≤ n ∧ zPt ψ t C n = a then (convFac ψ t (Classical.choose h) : ℂ) else 0

/-- The function `f = ∏_n (1 - z/z_n) e^{c_n z}` of the proof. -/
def fProd (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) : ℂ → ℂ :=
  OCS.canonicalProd (zSet ψ t C) (convFun ψ t C)

/-- The cell term `j_n(z) = ∫_{cell n} (log|1 - z/s| - log|1 - z/z_n|) dψ(s)`
(corrected (10): the cell is `(t_{n-1}, t_n]`, not `(r_{n-1}, r_n]`). -/
def cellTerm (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) (n : ℕ) (z : ℂ) : ℝ :=
  ∫ s in cell t n, (Real.log ‖1 - z / s‖ - Real.log ‖1 - z / zPt ψ t C n‖) * deriv ψ s

/-- Standing hypotheses on `ψ` and the partition `t` (a repackaging of the hypotheses of
`theorem2_i`; `1 ≤ C`). -/
structure RegData (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C M : ℝ) : Prop where
  adm : IsAdmissiblePsi ψ
  zero : ∀ x : ℝ, x ≤ 0 → ψ x = 0
  one_le : 1 ≤ C
  t0 : t 0 = 0
  mono : StrictMono t
  psi_t : ∀ n : ℕ, 1 ≤ n → ψ (t n) = n
  ratio : ∀ n : ℕ, 1 ≤ n →
    t (n + 1) - t n ≤ C * (t n - t (n - 1)) ∧ t n - t (n - 1) ≤ C * (t (n + 1) - t n)
  sum_le : ∀ x : ℝ, 0 < x →
    ∑' n : {n : ℕ | 1 ≤ n ∧ x / 2 < t n ∧ t n < 2 * x},
        ENNReal.ofReal ((t n - t (n - 1)) ^ 2 / ((x - t n) ^ 2 + (t n - t (n - 1)) ^ 2)) ≤
      ENNReal.ofReal M

/-- The local density bound `ψ' ≤ K / d_n` on `[t_{n-1}, t_n]` (NOT a hypothesis of `theorem2_i`). -/
def DensBound (ψ : ℝ → ℝ) (t : ℕ → ℝ) (K : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ s ∈ Icc (t (n - 1)) (t n), deriv ψ s ≤ K / cellLen t n

/-! ## §1. The partition data -/

theorem RegData.of_isLogRegularPartition {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ)
    (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0) (hreg : IsLogRegularPartition ψ) :
    ∃ (t : ℕ → ℝ) (C M : ℝ), RegData ψ t C M := by
  obtain ⟨t, ht0, hmono, hpsi, ⟨C0, hC0⟩, M, hM⟩ := hreg
  refine ⟨t, max C0 1, M, ⟨hψ, h0, le_max_right _ _, ht0, hmono, hpsi, ?_, hM⟩⟩
  intro n hn
  obtain ⟨h1, h2⟩ := hC0 n hn
  have d1 : 0 ≤ t n - t (n - 1) := by
    have := hmono.monotone (Nat.sub_le n 1); linarith
  have d2 : 0 ≤ t (n + 1) - t n := by
    have := hmono.monotone (Nat.le_succ n); linarith
  constructor
  · calc _ ≤ C0 * (t n - t (n - 1)) := h1
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) d1
  · calc _ ≤ C0 * (t (n + 1) - t n) := h2
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) d2

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

/-! ### Basic helpers (prefix `A_`) -/

theorem RegData.A_t_nonneg (h : RegData ψ t C M) (n : ℕ) : 0 ≤ t n := by
  have := h.mono.monotone (Nat.zero_le n)
  rwa [h.t0] at this

theorem RegData.A_t_pos (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) : 0 < t n := by
  have := h.mono (show 0 < n by omega)
  rwa [h.t0] at this

theorem RegData.A_cellLen_pos (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) : 0 < cellLen t n := by
  have := h.mono (show n - 1 < n by omega)
  unfold cellLen; linarith

theorem RegData.A_cellLen_le (h : RegData ψ t C M) (n : ℕ) : cellLen t n ≤ t n := by
  unfold cellLen; linarith [h.A_t_nonneg (n - 1)]

theorem RegData.A_deriv_nonneg (h : RegData ψ t C M) (s : ℝ) : 0 ≤ deriv ψ s :=
  h.adm.2.1.deriv_nonneg

theorem RegData.A_differentiable (h : RegData ψ t C M) : Differentiable ℝ ψ :=
  (contDiff_one_iff_deriv.1 h.adm.1).1

theorem RegData.A_continuous_deriv (h : RegData ψ t C M) : Continuous (deriv ψ) :=
  (contDiff_one_iff_deriv.1 h.adm.1).2

theorem RegData.A_psi_t (h : RegData ψ t C M) (n : ℕ) : ψ (t n) = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [h.t0, h.zero 0 le_rfl]
  · exact h.psi_t n hn

theorem RegData.A_integrableOn_deriv (h : RegData ψ t C M) (a b : ℝ) :
    IntegrableOn (deriv ψ) (Ioc a b) :=
  h.A_continuous_deriv.integrableOn_Ioc

theorem RegData.A_integrableOn_deriv_cell (h : RegData ψ t C M) (n : ℕ) :
    IntegrableOn (deriv ψ) (cell t n) :=
  h.A_integrableOn_deriv _ _

theorem A_cell_succ (n : ℕ) : cell t (n + 1) = Ioc (t n) (t (n + 1)) := by
  simp [cell]

/-- `ψ'` is eventually small. -/
theorem RegData.A_deriv_small (h : RegData ψ t C M) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ s : ℝ, T ≤ s → deriv ψ s ≤ ε := by
  have h1 := h.adm.2.2.2
  have h2 : Tendsto (deriv ψ) atTop (𝓝 0) :=
    h1.mono_left atTop_le_cocompact
  have := (h2.eventually (gt_mem_nhds hε))
  rcases Filter.eventually_atTop.1 this with ⟨T, hT⟩
  exact ⟨T, fun s hs => (hT s hs).le⟩

/-- Each cell has `ψ`-mass `1`. -/
theorem RegData.integral_cell (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    ∫ s in cell t n, deriv ψ s = 1 := by
  have hd : ∀ x ∈ uIcc (t (n - 1)) (t n), HasDerivAt ψ (deriv ψ x) x :=
    fun x _ => (h.A_differentiable x).hasDerivAt
  have hle : t (n - 1) ≤ t n := h.mono.monotone (Nat.sub_le n 1)
  have hint : IntervalIntegrable (deriv ψ) volume (t (n - 1)) (t n) :=
    h.A_continuous_deriv.intervalIntegrable _ _
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_of_le hle] at this
  unfold cell
  rw [this, h.A_psi_t, h.A_psi_t, Nat.cast_sub hn]
  simp

/-- Integral of a bounded function against the cell measure. -/
theorem RegData.A_abs_integral_le (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) {g : ℝ → ℝ} {B : ℝ}
    (hB : ∀ s ∈ cell t n, |g s| ≤ B) :
    |∫ s in cell t n, g s * deriv ψ s| ≤ B := by
  have hB0 : IntegrableOn (fun s => B * deriv ψ s) (cell t n) :=
    (h.A_integrableOn_deriv_cell n).const_mul B
  have h1 : ‖∫ s in cell t n, g s * deriv ψ s‖ ≤ ∫ s in cell t n, B * deriv ψ s := by
    refine norm_integral_le_of_norm_le hB0 ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.A_deriv_nonneg s)]
    exact mul_le_mul_of_nonneg_right (hB s hs) (h.A_deriv_nonneg s)
  rw [integral_const_mul, h.integral_cell hn, mul_one] at h1
  simpa using h1


theorem RegData.A_integrableOn_log_mul (h : RegData ψ t C M) (n : ℕ) :
    IntegrableOn (fun s => Real.log s * deriv ψ s) (cell t n) := by
  have hle : t (n - 1) ≤ t n := h.mono.monotone (Nat.sub_le n 1)
  have h1 : IntervalIntegrable (fun s => Real.log s * deriv ψ s) volume (t (n - 1)) (t n) :=
    (intervalIntegral.intervalIntegrable_log').mul_continuousOn h.A_continuous_deriv.continuousOn
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 h1

theorem RegData.A_integral_pos (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) {g : ℝ → ℝ}
    (hint : IntegrableOn (fun s => g s * deriv ψ s) (cell t n))
    (hg0 : ∀ s ∈ cell t n, 0 ≤ g s)
    (hgpos : ∀ᵐ s ∂(volume.restrict (cell t n)), 0 < g s) :
    0 < ∫ s in cell t n, g s * deriv ψ s := by
  have hnn : 0 ≤ᵐ[volume.restrict (cell t n)] fun s => g s * deriv ψ s := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    exact mul_nonneg (hg0 s hs) (h.A_deriv_nonneg s)
  have hge : 0 ≤ ∫ s in cell t n, g s * deriv ψ s := integral_nonneg_of_ae hnn
  refine lt_of_le_of_ne hge fun h0 => ?_
  have h1 := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0.symm
  have h2 : deriv ψ =ᵐ[volume.restrict (cell t n)] 0 := by
    filter_upwards [h1, hgpos] with s hs hg
    simp only [Pi.zero_apply, mul_eq_zero] at hs
    exact hs.resolve_left hg.ne'
  have := integral_congr_ae h2
  rw [h.integral_cell hn] at this
  simp at this

theorem RegData.A_log_gt (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) :
    Real.log (t (n - 1)) < ∫ s in cell t n, Real.log s * deriv ψ s := by
  have hpos := h.A_t_pos (n := n - 1) (by omega)
  have hint : IntegrableOn (fun s => (Real.log s - Real.log (t (n - 1))) * deriv ψ s) (cell t n) := by
    have : IntegrableOn (fun s => Real.log s * deriv ψ s - Real.log (t (n - 1)) * deriv ψ s)
        (cell t n) :=
      (h.A_integrableOn_log_mul n).sub ((h.A_integrableOn_deriv_cell n).const_mul _)
    refine this.congr_fun (fun s _ => by simp only; ring) measurableSet_Ioc
  have := h.A_integral_pos (n := n) (by omega) (g := fun s => Real.log s - Real.log (t (n - 1))) hint
    (fun s hs => by
      have := Real.log_le_log hpos hs.1.le
      linarith)
    (by
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
      have := Real.log_lt_log hpos hs.1
      linarith)
  have e : ∫ s in cell t n, (Real.log s - Real.log (t (n - 1))) * deriv ψ s
      = (∫ s in cell t n, Real.log s * deriv ψ s) - Real.log (t (n - 1)) := by
    simp only [sub_mul]
    rw [integral_sub (h.A_integrableOn_log_mul n) ((h.A_integrableOn_deriv_cell n).const_mul _),
      integral_const_mul, h.integral_cell (by omega), mul_one]
  linarith

theorem RegData.A_log_lt (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    ∫ s in cell t n, Real.log s * deriv ψ s < Real.log (t n) := by
  have hpos := h.A_t_pos hn
  have hint : IntegrableOn (fun s => (Real.log (t n) - Real.log s) * deriv ψ s) (cell t n) := by
    have : IntegrableOn (fun s => Real.log (t n) * deriv ψ s - Real.log s * deriv ψ s)
        (cell t n) :=
      ((h.A_integrableOn_deriv_cell n).const_mul _).sub (h.A_integrableOn_log_mul n)
    refine this.congr_fun (fun s _ => by simp only; ring) measurableSet_Ioc
  have := h.A_integral_pos hn (g := fun s => Real.log (t n) - Real.log s) hint
    (fun s hs => by
      have hs0 : 0 < s := lt_of_le_of_lt (h.A_t_nonneg _) hs.1
      have := Real.log_le_log hs0 hs.2
      linarith)
    (by
      have hae : ∀ᵐ s ∂(volume.restrict (cell t n)), s ≠ t n := by
        refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
        have : ∀ᵐ s : ℝ, s ≠ t n := by
          simpa using (Set.countable_singleton (t n)).ae_notMem (μ := volume)
        filter_upwards [this] with s hs _ using hs
      filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with s hs hmem
      have hs0 : 0 < s := lt_of_le_of_lt (h.A_t_nonneg _) hmem.1
      have := Real.log_lt_log hs0 (lt_of_le_of_ne hmem.2 hs)
      linarith)
  have e : ∫ s in cell t n, (Real.log (t n) - Real.log s) * deriv ψ s
      = Real.log (t n) - (∫ s in cell t n, Real.log s * deriv ψ s) := by
    simp only [sub_mul]
    rw [integral_sub ((h.A_integrableOn_deriv_cell n).const_mul _) (h.A_integrableOn_log_mul n),
      integral_const_mul, h.integral_cell hn, mul_one]
  linarith


theorem RegData.tendsto_t (h : RegData ψ t C M) : Tendsto t atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨⌈ψ b⌉₊ + 1, fun n hn => ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 : ψ (t n) ≤ ψ b := h.adm.2.1 hlt.le
  rw [h.A_psi_t] at h1
  have h2 : ψ b ≤ ⌈ψ b⌉₊ := Nat.le_ceil _
  have h3 : ((⌈ψ b⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at h3
  linarith

/-- `d_n → ∞` (from `ψ' → 0`). -/
theorem RegData.tendsto_cellLen (h : RegData ψ t C M) : Tendsto (cellLen t) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  have hb : 0 < max b 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨T, hT⟩ := h.A_deriv_small (inv_pos.2 hb)
  have hev : ∀ᶠ n in atTop, T ≤ t n ∧ 1 ≤ n + 1 := by
    filter_upwards [h.tendsto_t.eventually_ge_atTop T, eventually_ge_atTop 0] with n h1 _
    exact ⟨h1, by omega⟩
  rw [Filter.eventually_atTop] at hev ⊢
  obtain ⟨N, hN⟩ := hev
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm := (hN m (by omega)).1
  have hint := h.integral_cell (n := m + 1) (by omega)
  have hle : ∫ s in cell t (m + 1), deriv ψ s ≤ ∫ s in cell t (m + 1), (max b 1)⁻¹ := by
    refine setIntegral_mono_on (h.A_integrableOn_deriv_cell _) ?_ measurableSet_Ioc ?_
    · exact integrableOn_const (by simp [cell])
    · intro s hs
      exact hT s (le_trans hm (by simp [cell] at hs; exact hs.1.le))
  rw [hint, setIntegral_const] at hle
  have hlen : cellLen t (m + 1) = (volume (cell t (m + 1))).toReal := by
    rw [A_cell_succ]; simp [cellLen, h.mono.monotone (Nat.le_succ m)]
  simp only [smul_eq_mul, Measure.real, ← hlen] at hle
  have : max b 1 ≤ cellLen t (m + 1) := by
    rw [← div_eq_mul_inv] at hle
    exact (one_le_div hb).1 hle
  exact le_trans (le_max_left _ _) this

/-- `t_n ≤ (1 + C) t_{n-1}` for `n ≥ 2` (so `hlow` is not needed). -/
theorem RegData.t_le (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) :
    t n ≤ (1 + C) * t (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := h.ratio (m + 0) (by omega)
  have h2 := h.A_t_nonneg (m - 1)
  have hm : m + 1 - 1 = m := by omega
  simp only [hm, add_zero] at h1 ⊢
  have h3 := h1.1
  have hC := h.one_le
  have h4 : t m - t (m - 1) ≤ t m := by linarith
  have h5 : C * (t m - t (m - 1)) ≤ C * t m := mul_le_mul_of_nonneg_left h4 (by linarith)
  nlinarith

theorem RegData.rCentre_mem (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    t (n - 1) < rCentre ψ t n ∧ rCentre ψ t n < t n := by
  have hpos := h.A_t_pos hn
  unfold rCentre
  constructor
  · rcases Nat.lt_or_ge n 2 with h1 | h1
    · have : n = 1 := by omega
      subst this
      simp [h.t0, Real.exp_pos]
    · have hp := h.A_t_pos (n := n - 1) (by omega)
      exact (Real.log_lt_iff_lt_exp hp).1 (h.A_log_gt h1)
  · exact (Real.lt_log_iff_exp_lt hpos).1 (h.A_log_lt hn)

/-- The defining property (9) of the log-centre. -/
theorem RegData.integral_log_sub_centre (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    ∫ s in cell t n, (Real.log s - Real.log (rCentre ψ t n)) * deriv ψ s = 0 := by
  simp only [sub_mul]
  rw [integral_sub (h.A_integrableOn_log_mul n) ((h.A_integrableOn_deriv_cell n).const_mul _),
    integral_const_mul, h.integral_cell hn, mul_one, rCentre, Real.log_exp, sub_self]

theorem RegData.t_le_kappa_mul (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    t n ≤ kappa ψ t C * rCentre ψ t n := by
  have hr := h.rCentre_mem hn
  have hr0 : 0 < rCentre ψ t n := lt_of_le_of_lt (h.A_t_nonneg _) hr.1
  rcases Nat.lt_or_ge n 2 with h1 | h1
  · have : n = 1 := by omega
    subst this
    have : t 1 / rCentre ψ t 1 ≤ kappa ψ t C := le_max_right _ _
    rwa [div_le_iff₀ hr0] at this
  · have h2 := h.t_le h1
    have h3 : (1 + C) ≤ kappa ψ t C := le_max_left _ _
    have : (1 + C) * t (n - 1) ≤ kappa ψ t C * rCentre ψ t n := by
      have := h.A_t_nonneg (n - 1)
      have : (1 + C) * t (n - 1) ≤ (1 + C) * rCentre ψ t n :=
        mul_le_mul_of_nonneg_left hr.1.le (by linarith [h.one_le])
      nlinarith
    linarith

theorem RegData.one_lt_kappa (h : RegData ψ t C M) : 1 < kappa ψ t C := by
  have hr := h.rCentre_mem (n := 1) le_rfl
  have hr0 : 0 < rCentre ψ t 1 := lt_of_le_of_lt (h.A_t_nonneg _) hr.1
  have : 1 < t 1 / rCentre ψ t 1 := by
    rw [lt_div_iff₀ hr0]; linarith [hr.2]
  exact lt_of_lt_of_le this (le_max_right _ _)

theorem RegData.cAngle_pos (h : RegData ψ t C M) : 0 < cAngle ψ t C := by
  unfold cAngle
  have := h.one_lt_kappa
  positivity

theorem RegData.cAngle_lt (h : RegData ψ t C M) : cAngle ψ t C < Real.pi / 4 := by
  unfold cAngle
  have := h.one_lt_kappa
  have hpi := Real.pi_pos
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

/-- The angle `θ_n = c d_n / r_n ≤ π/4`. -/
theorem RegData.angle_le (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    cAngle ψ t C * cellLen t n / rCentre ψ t n ≤ Real.pi / 4 := by
  have hr := h.rCentre_mem hn
  have hr0 : 0 < rCentre ψ t n := lt_of_le_of_lt (h.A_t_nonneg _) hr.1
  have hk := h.one_lt_kappa
  have h1 := h.t_le_kappa_mul hn
  have h2 := h.A_cellLen_le n
  have hc := h.cAngle_pos
  rw [div_le_iff₀ hr0]
  have : cAngle ψ t C * kappa ψ t C = Real.pi / 4 := by
    unfold cAngle; field_simp
  calc cAngle ψ t C * cellLen t n ≤ cAngle ψ t C * (kappa ψ t C * rCentre ψ t n) :=
        mul_le_mul_of_nonneg_left (h2.trans h1) hc.le
    _ = _ := by rw [← mul_assoc, this]

theorem RegData.A_r_pos (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) : 0 < rCentre ψ t n :=
  lt_of_le_of_lt (h.A_t_nonneg _) (h.rCentre_mem hn).1

/-- The angle `θ_n`. -/
def thetaA (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) (n : ℕ) : ℝ :=
  cAngle ψ t C * cellLen t n / rCentre ψ t n

theorem RegData.A_theta_nonneg (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ thetaA ψ t C n := by
  unfold thetaA
  have := h.A_r_pos hn
  have := h.A_cellLen_pos hn
  have := h.cAngle_pos
  positivity

theorem RegData.A_theta_le (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    thetaA ψ t C n ≤ Real.pi / 4 := h.angle_le hn

theorem RegData.A_r_theta (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    rCentre ψ t n * thetaA ψ t C n = cAngle ψ t C * cellLen t n := by
  have := (h.A_r_pos hn).ne'
  unfold thetaA; field_simp

theorem A_zPt_re (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) (n : ℕ) :
    (zPt ψ t C n).re = rCentre ψ t n * Real.cos (thetaA ψ t C n) := by
  simp [zPt, thetaA, Complex.exp_re, Complex.mul_re]

theorem A_zPt_im (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) (n : ℕ) :
    (zPt ψ t C n).im = -(rCentre ψ t n * Real.sin (thetaA ψ t C n)) := by
  simp [zPt, thetaA, Complex.exp_im, Complex.mul_im]


/-! ## §2. The zeros -/

theorem RegData.norm_zPt (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    ‖zPt ψ t C n‖ = rCentre ψ t n := by
  have hr := h.A_r_pos hn
  have : Complex.exp (-(Complex.I * ((cAngle ψ t C * cellLen t n / rCentre ψ t n : ℝ) : ℂ)))
      = Complex.exp (((-(thetaA ψ t C n) : ℝ) : ℂ) * Complex.I) := by
    congr 1; simp [thetaA]; ring
  rw [zPt, this, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr, mul_one]

/-- `Im z_n = -r_n sin θ_n < 0`, and `Im z_n ≤ -(2/π) c d_n`. -/
theorem RegData.im_zPt_le (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    (zPt ψ t C n).im ≤ -(2 / Real.pi * (cAngle ψ t C * cellLen t n)) := by
  have hr := h.A_r_pos hn
  have h0 := h.A_theta_nonneg hn
  have h1 := h.A_theta_le hn
  have hpi := Real.pi_pos
  rw [A_zPt_im, neg_le_neg_iff]
  have := Real.mul_le_sin h0 (by linarith)
  have e := h.A_r_theta hn
  calc 2 / Real.pi * (cAngle ψ t C * cellLen t n) = rCentre ψ t n * (2 / Real.pi * thetaA ψ t C n) := by
        rw [← e]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hr.le

theorem RegData.im_zPt_ge (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    -(cAngle ψ t C * cellLen t n) ≤ (zPt ψ t C n).im := by
  have hr := h.A_r_pos hn
  have h0 := h.A_theta_nonneg hn
  rw [A_zPt_im, neg_le_neg_iff]
  have := Real.sin_le h0
  rw [← h.A_r_theta hn]
  exact mul_le_mul_of_nonneg_left this hr.le

/-- `|z_n - r_n| ≤ c d_n` (chord ≤ arc). -/
theorem RegData.norm_zPt_sub_le (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    ‖zPt ψ t C n - (rCentre ψ t n : ℂ)‖ ≤ cAngle ψ t C * cellLen t n := by
  have hr := h.A_r_pos hn
  have h0 := h.A_theta_nonneg hn
  have : zPt ψ t C n - (rCentre ψ t n : ℂ)
      = (rCentre ψ t n : ℂ) * (Complex.exp (Complex.I * ((-(thetaA ψ t C n) : ℝ) : ℂ)) - 1) := by
    rw [zPt, mul_sub, mul_one]
    congr 2
    simp [thetaA]
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(thetaA ψ t C n))
  rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg h0] at this
  calc _ ≤ rCentre ψ t n * thetaA ψ t C n := mul_le_mul_of_nonneg_left this hr.le
    _ = _ := h.A_r_theta hn

/-- `Re z_n ≥ r_n / √2 > 0`. -/
theorem RegData.re_zPt_ge (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    rCentre ψ t n / Real.sqrt 2 ≤ (zPt ψ t C n).re := by
  have hr := h.A_r_pos hn
  have h0 := h.A_theta_nonneg hn
  have h1 := h.A_theta_le hn
  have hpi := Real.pi_pos
  rw [A_zPt_re]
  have hc : Real.sqrt 2 / 2 ≤ Real.cos (thetaA ψ t C n) := by
    rw [← Real.cos_pi_div_four]
    exact Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith) h1
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have h3 : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp; rw [Real.sq_sqrt (by norm_num)]
  rw [div_eq_mul_one_div, h3]
  exact mul_le_mul_of_nonneg_left hc hr.le

theorem RegData.zPt_injOn (h : RegData ψ t C M) : Set.InjOn (zPt ψ t C) (Set.Ici 1) := by
  have key : ∀ m n : ℕ, 1 ≤ m → m < n → rCentre ψ t m < rCentre ψ t n := by
    intro m n hm hmn
    have h1 := (h.rCentre_mem hm).2
    have h2 := (h.rCentre_mem (n := n) (by omega)).1
    have h3 : t m ≤ t (n - 1) := h.mono.monotone (by omega)
    linarith
  intro a ha b hb hab
  have hn : ‖zPt ψ t C a‖ = ‖zPt ψ t C b‖ := by rw [hab]
  rw [h.norm_zPt ha, h.norm_zPt hb] at hn
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd hn (key a b ha hlt).ne
  · exact heq
  · exact absurd hn (key b a hb hgt).ne'

/-- `∑ 1/r_n² < ∞`, `∑ d_n / r_n² < ∞`. -/
theorem RegData.summable_cellLen_div_sq (h : RegData ψ t C M) :
    Summable fun n : ℕ => cellLen t (n + 1) / rCentre ψ t (n + 1) ^ 2 := by
  rw [← summable_nat_add_iff 1]
  have hk := h.one_lt_kappa
  have hf : ∀ n : ℕ, cellLen t (n + 1 + 1) / rCentre ψ t (n + 1 + 1) ^ 2 ≤
      kappa ψ t C * (1 / t (n + 1) - 1 / t (n + 2)) := by
    intro n
    have ha := h.A_t_pos (n := n + 1) (by omega)
    have hb := h.t_le_kappa_mul (n := n + 2) (by omega)
    have hr := (h.rCentre_mem (n := n + 2) (by omega)).1
    have hr' : t (n + 1) < rCentre ψ t (n + 2) := by simpa using hr
    have hab : t (n + 1) < t (n + 2) := h.mono (by omega)
    have hbpos : 0 < t (n + 2) := h.A_t_pos (by omega)
    have hrpos : 0 < rCentre ψ t (n + 2) := by linarith
    have hd : cellLen t (n + 1 + 1) = t (n + 2) - t (n + 1) := by simp [cellLen]
    have e : kappa ψ t C * (1 / t (n + 1) - 1 / t (n + 2))
        = kappa ψ t C * (t (n + 2) - t (n + 1)) / (t (n + 1) * t (n + 2)) := by
      field_simp
    rw [e, hd, show n + 1 + 1 = n + 2 by rfl, div_le_div_iff₀ (by positivity) (by positivity)]
    have : t (n + 1) * t (n + 2) ≤ kappa ψ t C * rCentre ψ t (n + 2) ^ 2 := by
      calc t (n + 1) * t (n + 2) ≤ rCentre ψ t (n + 2) * (kappa ψ t C * rCentre ψ t (n + 2)) :=
            mul_le_mul hr'.le hb hbpos.le hrpos.le
        _ = _ := by ring
    have h5 : 0 ≤ t (n + 2) - t (n + 1) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this h5]
  have hnn : ∀ n : ℕ, 0 ≤ cellLen t (n + 1 + 1) / rCentre ψ t (n + 1 + 1) ^ 2 := fun n =>
    div_nonneg (h.A_cellLen_pos (by omega)).le (sq_nonneg _)
  refine summable_of_sum_range_le hnn (c := kappa ψ t C * (1 / t 1)) fun N => ?_
  calc _ ≤ ∑ n ∈ Finset.range N, kappa ψ t C * (1 / t (n + 1) - 1 / t (n + 2)) :=
        Finset.sum_le_sum fun n _ => hf n
    _ = kappa ψ t C * (1 / t 1 - 1 / t (N + 1)) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_range_sub' (fun n => 1 / t (n + 1)) N
    _ ≤ _ := by
        have : 0 < t (N + 1) := h.A_t_pos (by omega)
        have : 0 < 1 / t (N + 1) := by positivity
        nlinarith

theorem RegData.summable_inv_sq (h : RegData ψ t C M) :
    Summable fun n : ℕ => (rCentre ψ t (n + 1))⁻¹ ^ 2 := by
  refine Summable.of_norm_bounded_eventually_nat h.summable_cellLen_div_sq ?_
  have := h.tendsto_cellLen.eventually_ge_atTop 1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 this
  filter_upwards [eventually_ge_atTop N] with n hn0
  have hn := hN (n + 1) (by omega)
  have hr := h.A_r_pos (n := n + 1) (by omega)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow, ← one_div]
  exact div_le_div_of_nonneg_right hn (by positivity)

theorem RegData.A_convFac_sub_le (h : RegData ψ t C M) {k : ℕ} (hk : 2 ≤ k) (h1 : 1 ≤ t (k - 1)) :
    |convFac ψ t k - (rCentre ψ t k)⁻¹| ≤
      (1 + C) * cellLen t k / rCentre ψ t k ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hr := h.rCentre_mem hk1
  have hr0 := h.A_r_pos hk1
  have ht := h.t_le hk
  have hC := h.one_le
  set r := rCentre ψ t k with hrdef
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (Icc (t (k - 1)) (t k)) →
      IntegrableOn (fun s => g s * deriv ψ s) (cell t k) := by
    intro g hg
    exact ((hg.mul h.A_continuous_deriv.continuousOn).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hne : ∀ s ∈ Icc (t (k - 1)) (t k), s ≠ 0 := fun s hs => by
    have := hs.1; intro h0; rw [h0] at this; linarith
  have hconv : convFac ψ t k = ∫ s in cell t k, (1 / s) * deriv ψ s := by
    unfold convFac
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have : s ∉ Icc (-1 : ℝ) 1 := by
      intro hm
      have := hs.1
      linarith [hm.2]
    simp [Set.indicator_of_notMem this]
  have hint1 : IntegrableOn (fun s => (1 / s) * deriv ψ s) (cell t k) :=
    hcont (fun s => 1 / s) (continuousOn_const.div continuousOn_id fun s hs => hne s hs)
  have e : convFac ψ t k - r⁻¹ = ∫ s in cell t k, (1 / s - r⁻¹) * deriv ψ s := by
    simp only [sub_mul]
    rw [integral_sub hint1 ((h.A_integrableOn_deriv_cell k).const_mul _), integral_const_mul,
      h.integral_cell hk1, mul_one, hconv]
  rw [e]
  refine h.A_abs_integral_le hk1 (fun s hs => ?_)
  have hs1 : t (k - 1) < s := hs.1
  have hs2 : s ≤ t k := hs.2
  have hspos : 0 < s := by linarith
  have hlo : r / (1 + C) ≤ t (k - 1) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [hr.2]
  have hd : |r - s| ≤ cellLen t k := by
    rw [abs_le]; unfold cellLen; constructor <;> linarith [hr.1, hr.2]
  have : |1 / s - r⁻¹| = |r - s| / (s * r) := by
    rw [show 1 / s - r⁻¹ = (r - s) / (s * r) by field_simp, abs_div, abs_of_pos (show 0 < s * r by positivity)]
  rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : r / (1 + C) < s := lt_of_le_of_lt hlo hs1
  rw [div_lt_iff₀ (by linarith)] at h2
  have hd0 : 0 ≤ cellLen t k := (h.A_cellLen_pos hk1).le
  calc |r - s| * r ^ 2 ≤ cellLen t k * r ^ 2 := mul_le_mul_of_nonneg_right hd (by positivity)
    _ ≤ (1 + C) * cellLen t k * (s * r) := by nlinarith [mul_nonneg hd0 hr0.le]

theorem A_zPt_inv (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) (n : ℕ) :
    (zPt ψ t C n)⁻¹ = ((rCentre ψ t n : ℝ) : ℂ)⁻¹ * Complex.exp (Complex.I * (thetaA ψ t C n : ℝ)) := by
  rw [zPt, mul_inv, ← Complex.exp_neg]
  simp [thetaA]

theorem RegData.A_inv_sub_le (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    ‖((rCentre ψ t n : ℝ) : ℂ)⁻¹ - (zPt ψ t C n)⁻¹‖ ≤ cAngle ψ t C * cellLen t n / rCentre ψ t n ^ 2 := by
  have hr := h.A_r_pos hn
  have h0 := h.A_theta_nonneg hn
  have : ((rCentre ψ t n : ℝ) : ℂ)⁻¹ - (zPt ψ t C n)⁻¹ =
      -(((rCentre ψ t n : ℝ) : ℂ)⁻¹ * (Complex.exp (Complex.I * (thetaA ψ t C n : ℝ)) - 1)) := by
    rw [A_zPt_inv]; ring
  rw [this, norm_neg, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := thetaA ψ t C n)
  rw [Real.norm_eq_abs, abs_of_nonneg h0] at this
  calc (rCentre ψ t n)⁻¹ * _ ≤ (rCentre ψ t n)⁻¹ * thetaA ψ t C n :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by
        have := h.A_r_theta hn
        unfold thetaA; field_simp


/-- `|c_n - 1/r_n| ≲ d_n / r_n²`; hence `∑ |c_n - 1/z_n| < ∞`. -/
theorem RegData.summable_convFac_sub (h : RegData ψ t C M) :
    Summable fun n : ℕ => ‖(convFac ψ t (n + 1) : ℂ) - (zPt ψ t C (n + 1))⁻¹‖ := by
  refine Summable.of_norm_bounded_eventually_nat (h.summable_cellLen_div_sq.mul_left (2 + C)) ?_
  have := h.tendsto_t.eventually_ge_atTop 1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 this
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn0
  have h1 : 1 ≤ t n := hN n (by omega)
  have hk : 2 ≤ n + 1 := by omega
  have hA := h.A_convFac_sub_le hk (by simpa using h1)
  have hB := h.A_inv_sub_le (n := n + 1) (by omega)
  have hc := h.cAngle_lt
  have hr := h.A_r_pos (n := n + 1) (by omega)
  have hd := h.A_cellLen_pos (n := n + 1) (by omega)
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have e : (convFac ψ t (n + 1) : ℂ) - (zPt ψ t C (n + 1))⁻¹ =
      (((convFac ψ t (n + 1) - (rCentre ψ t (n + 1))⁻¹ : ℝ)) : ℂ) +
        (((rCentre ψ t (n + 1) : ℝ) : ℂ)⁻¹ - (zPt ψ t C (n + 1))⁻¹) := by
    push_cast; ring
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), e]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h2 : cAngle ψ t C * cellLen t (n + 1) / rCentre ψ t (n + 1) ^ 2 ≤
      1 * cellLen t (n + 1) / rCentre ψ t (n + 1) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) hd.le
  have e2 : (2 + C) * (cellLen t (n + 1) / rCentre ψ t (n + 1) ^ 2) =
      (1 + C) * cellLen t (n + 1) / rCentre ψ t (n + 1) ^ 2 + 1 * cellLen t (n + 1) / rCentre ψ t (n + 1) ^ 2 := by
    ring
  rw [e2]
  linarith

theorem RegData.convFun_zPt (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    convFun ψ t C (zPt ψ t C n) = (convFac ψ t n : ℂ) := by
  have hex : ∃ m : ℕ, 1 ≤ m ∧ zPt ψ t C m = zPt ψ t C n := ⟨n, hn, rfl⟩
  unfold convFun
  simp only [hex, ↓reduceDIte]
  have := Classical.choose_spec hex
  have e := h.zPt_injOn (by simpa [Set.mem_Ici] using this.1) (by simpa [Set.mem_Ici] using hn) this.2
  rw [e]

theorem RegData.isGenusOneData (h : RegData ψ t C M) :
    OCS.IsGenusOneData (zSet ψ t C) (convFun ψ t C) := by
  have hz : ∀ n, 1 ≤ n → ‖zPt ψ t C n‖ = rCentre ψ t n := fun n hn => h.norm_zPt hn
  -- reindexing equivalence ℕ ≃ ↥(zSet)
  let e : ℕ → zSet ψ t C := fun n => ⟨zPt ψ t C (n + 1), n + 1, by omega, rfl⟩
  have he : Function.Bijective e := by
    constructor
    · intro a b hab
      have := congrArg Subtype.val hab
      have := h.zPt_injOn (by simp [Set.mem_Ici]) (by simp [Set.mem_Ici]) this
      omega
    · rintro ⟨a, n, hn, rfl⟩
      exact ⟨n - 1, Subtype.ext (by simp only [e]; congr 2; omega)⟩
  let E := Equiv.ofBijective e he
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨n, hn, h0⟩
    have := h.norm_zPt hn
    rw [h0, norm_zero] at this
    exact (h.A_r_pos hn).ne this
  · rw [← E.summable_iff]
    have : (fun a : zSet ψ t C => ‖(a : ℂ)‖⁻¹ ^ 2) ∘ E = fun n : ℕ => (rCentre ψ t (n + 1))⁻¹ ^ 2 := by
      funext n
      simp [E, e, h.norm_zPt (n := n + 1) (by omega)]
    rw [this]; exact h.summable_inv_sq
  · rw [← E.summable_iff]
    have : (fun a : zSet ψ t C => ‖convFun ψ t C a - (a : ℂ)⁻¹‖) ∘ E =
        fun n : ℕ => ‖(convFac ψ t (n + 1) : ℂ) - (zPt ψ t C (n + 1))⁻¹‖ := by
      funext n
      simp only [Function.comp, E, Equiv.ofBijective_apply, e]
      rw [h.convFun_zPt (by omega)]
    rw [this]; exact h.summable_convFac_sub


end FF
