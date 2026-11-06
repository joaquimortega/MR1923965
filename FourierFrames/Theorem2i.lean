import FourierFrames.Corollary2
import OrtegaCerdaSeip.Products.Canonical

/-!
# M08 — Theorem 2 (i)

See `blueprint/M08_Theorem2i.md`.  Construction of the canonical product `f` with zeros
`z_n = r_n e^{-i c d_n / r_n}` (one zero per cell `(t_{n-1}, t_n]` of `ψ`-mass `1`) such that
`|U_ψ - log|f|| ≲ 1` on `Im z ≥ 0`, and application of Corollary 2.

**Warning (see the blueprint, "Issues in the source", §A).**  The estimate of the cells at
distance `≲ d_n` from `z` needs the local density bound `ψ' ≲ 1/d_n` on `[t_{n-1}, t_n]`
(`DensBound`), which is *not* implied by the hypotheses of `theorem2_i`.  All lemmas below that
need it carry `hK : DensBound ψ t K`.  `theorem2_i_of_regular` is the provable statement;
`theorem2_i` (identical to `comparator/statements.lean`) has no honest proof from the paper's
argument unless `DensBound` can be derived or added to the hypotheses.
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
  sorry

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

/-- Each cell has `ψ`-mass `1`. -/
theorem RegData.integral_cell (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    ∫ s in cell t n, deriv ψ s = 1 := by
  sorry

theorem RegData.tendsto_t (h : RegData ψ t C M) : Tendsto t atTop atTop := by
  sorry

/-- `d_n → ∞` (from `ψ' → 0`). -/
theorem RegData.tendsto_cellLen (h : RegData ψ t C M) : Tendsto (cellLen t) atTop atTop := by
  sorry

/-- `t_n ≤ (1 + C) t_{n-1}` for `n ≥ 2` (so `hlow` is not needed). -/
theorem RegData.t_le (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) :
    t n ≤ (1 + C) * t (n - 1) := by
  sorry

theorem RegData.rCentre_mem (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    t (n - 1) < rCentre ψ t n ∧ rCentre ψ t n < t n := by
  sorry

/-- The defining property (9) of the log-centre. -/
theorem RegData.integral_log_sub_centre (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    ∫ s in cell t n, (Real.log s - Real.log (rCentre ψ t n)) * deriv ψ s = 0 := by
  sorry

theorem RegData.t_le_kappa_mul (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    t n ≤ kappa ψ t C * rCentre ψ t n := by
  sorry

theorem RegData.one_lt_kappa (h : RegData ψ t C M) : 1 < kappa ψ t C := by
  sorry

theorem RegData.cAngle_pos (h : RegData ψ t C M) : 0 < cAngle ψ t C := by
  sorry

theorem RegData.cAngle_lt (h : RegData ψ t C M) : cAngle ψ t C < Real.pi / 4 := by
  sorry

/-- The angle `θ_n = c d_n / r_n ≤ π/4`. -/
theorem RegData.angle_le (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    cAngle ψ t C * cellLen t n / rCentre ψ t n ≤ Real.pi / 4 := by
  sorry

/-! ## §2. The zeros -/

theorem RegData.norm_zPt (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    ‖zPt ψ t C n‖ = rCentre ψ t n := by
  sorry

/-- `Im z_n = -r_n sin θ_n < 0`, and `Im z_n ≤ -(2/π) c d_n`. -/
theorem RegData.im_zPt_le (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    (zPt ψ t C n).im ≤ -(2 / Real.pi * (cAngle ψ t C * cellLen t n)) := by
  sorry

theorem RegData.im_zPt_ge (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    -(cAngle ψ t C * cellLen t n) ≤ (zPt ψ t C n).im := by
  sorry

/-- `|z_n - r_n| ≤ c d_n` (chord ≤ arc). -/
theorem RegData.norm_zPt_sub_le (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    ‖zPt ψ t C n - (rCentre ψ t n : ℂ)‖ ≤ cAngle ψ t C * cellLen t n := by
  sorry

/-- `Re z_n ≥ r_n / √2 > 0`. -/
theorem RegData.re_zPt_ge (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    rCentre ψ t n / Real.sqrt 2 ≤ (zPt ψ t C n).re := by
  sorry

theorem RegData.zPt_injOn (h : RegData ψ t C M) : Set.InjOn (zPt ψ t C) (Set.Ici 1) := by
  sorry

/-- `∑ 1/r_n² < ∞`, `∑ d_n / r_n² < ∞`. -/
theorem RegData.summable_cellLen_div_sq (h : RegData ψ t C M) :
    Summable fun n : ℕ => cellLen t (n + 1) / rCentre ψ t (n + 1) ^ 2 := by
  sorry

theorem RegData.summable_inv_sq (h : RegData ψ t C M) :
    Summable fun n : ℕ => (rCentre ψ t (n + 1))⁻¹ ^ 2 := by
  sorry

/-- `|c_n - 1/r_n| ≲ d_n / r_n²`; hence `∑ |c_n - 1/z_n| < ∞`. -/
theorem RegData.summable_convFac_sub (h : RegData ψ t C M) :
    Summable fun n : ℕ => ‖(convFac ψ t (n + 1) : ℂ) - (zPt ψ t C (n + 1))⁻¹‖ := by
  sorry

theorem RegData.isGenusOneData (h : RegData ψ t C M) :
    OCS.IsGenusOneData (zSet ψ t C) (convFun ψ t C) := by
  sorry

theorem RegData.convFun_zPt (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) :
    convFun ψ t C (zPt ψ t C n) = (convFac ψ t n : ℂ) := by
  sorry

/-! ## §3. The function `f` -/

theorem RegData.differentiable_fProd (h : RegData ψ t C M) : Differentiable ℂ (fProd ψ t C) := by
  sorry

theorem RegData.fProd_ne_zero (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    fProd ψ t C z ≠ 0 := by
  sorry

theorem RegData.isHB_fProd (h : RegData ψ t C M) : IsHB (fProd ψ t C) := by
  sorry

theorem RegData.hasSum_log_fProd (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    HasSum (fun n : ℕ => Real.log ‖1 - z / zPt ψ t C (n + 1)‖ + z.re * convFac ψ t (n + 1))
      (Real.log ‖fProd ψ t C z‖) := by
  sorry

/-- `φ_f'(x) = ∑ |Im z_n| / |x - z_n|²`. -/
theorem RegData.hasSum_phaseDeriv_fProd (h : RegData ψ t C M) (x : ℝ) :
    HasSum (fun n : ℕ => -(zPt ψ t C (n + 1)).im / ‖(x : ℂ) - zPt ψ t C (n + 1)‖ ^ 2)
      (phaseDeriv (fProd ψ t C) x) := by
  sorry

theorem RegData.tendsto_phaseDeriv_fProd (h : RegData ψ t C M) :
    Tendsto (phaseDeriv (fProd ψ t C)) (cocompact ℝ) (𝓝 0) := by
  sorry

/-! ## §4. `U_ψ` as a sum over cells -/

theorem RegData.integrable_UPsi (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    Integrable fun s : ℝ =>
      (Real.log ‖1 - z / s‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 s) * (z / s).re) * deriv ψ s := by
  sorry

theorem RegData.hasSum_UPsi (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    HasSum (fun n : ℕ => ∫ s in cell t (n + 1),
        (Real.log ‖1 - z / s‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 s) * (z / s).re) * deriv ψ s)
      (UPsi ψ z) := by
  sorry

/-- `U_ψ - log|f| = ∑ j_n`. -/
theorem RegData.hasSum_cellTerm (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    HasSum (fun n : ℕ => cellTerm ψ t C (n + 1) z)
      (UPsi ψ z - Real.log ‖fProd ψ t C z‖) := by
  sorry

/-! ## §5. Estimates of `j_n(z)`, `Im z ≥ 0`, `z ≠ 0`

Constants: `ρ₁ = 2 (1 + C)`, `K₀ = 8 + 2 ρ₁`, `c = cAngle`. -/

/-- Constant `ρ₁`. -/
def rho1 (C : ℝ) : ℝ := 2 * (1 + C)
/-- Constant `K₀`. -/
def K0 (C : ℝ) : ℝ := 8 + 2 * rho1 C

/-- Cells below `|z|/2`. -/
theorem RegData.abs_cellTerm_below (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : 0 ≤ z.im) (hzn : t n ≤ ‖z‖ / 2) (hz0 : z ≠ 0) :
    |cellTerm ψ t C n z| ≤ (4 + 2 * (1 + C) * Real.log (1 + C)) * (cellLen t n / ‖z‖) := by
  sorry

/-- Cells above `2|z|`. -/
theorem RegData.abs_cellTerm_above (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) {z : ℂ}
    (hz : 0 ≤ z.im) (hzn : 2 * ‖z‖ ≤ t (n - 1)) (hz0 : z ≠ 0) :
    |cellTerm ψ t C n z| ≤
      (2 * Real.log (1 + C) + 2) * (cellLen t n * ‖z‖ / t (n - 1) ^ 2) := by
  sorry

/-- Cells comparable to `|z|` and at distance `≥ K₀ d_n`. -/
theorem RegData.abs_cellTerm_far (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) {z : ℂ}
    (hz : 0 ≤ z.im) (hz1 : ‖z‖ ≤ rho1 C * rCentre ψ t n) (hz2 : rCentre ψ t n ≤ rho1 C * ‖z‖)
    (hfar : K0 C * cellLen t n ≤ ‖z - rCentre ψ t n‖) :
    |cellTerm ψ t C n z| ≤
      (2 * rho1 C * (1 + C) ^ 3 + (3 + rho1 C)) * (cellLen t n ^ 2 / ‖z - rCentre ψ t n‖ ^ 2)
        + 2 * (cellLen t n * z.im / ‖z - rCentre ψ t n‖ ^ 2) := by
  sorry

/-- Cells at distance `< K₀ d_n` (needs `DensBound`). Also valid for `n = 1`. -/
theorem RegData.abs_cellTerm_near (h : RegData ψ t C M) (hK : DensBound ψ t K) {n : ℕ}
    (hn : 1 ≤ n) {z : ℂ} (hz : 0 ≤ z.im)
    (hnear : ‖z - rCentre ψ t n‖ < K0 C * cellLen t n) :
    |cellTerm ψ t C n z| ≤ 2 * K + Real.log (K0 C + 1) +
      Real.log (Real.pi / (2 * cAngle ψ t C)) := by
  sorry

/-- Counting: the number of `n ∈ W(z)` with `‖z - r_n‖ < K₀ d_n` is at most `3 (1 + K₀²) M`,
and `∑_{n ∈ W(z), far} d_n² / ‖z - r_n‖² ≤ 3 (1 + K₀⁻²) M`. -/
theorem RegData.card_near_le (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0) :
    ((({n : ℕ | 1 ≤ n ∧ ‖z‖ / 2 < t n ∧ t n < 2 * ‖z‖ ∧
        ‖z - rCentre ψ t n‖ < K0 C * cellLen t n}) : Set ℕ).ncard : ℝ) ≤
      3 * (1 + K0 C ^ 2) * M := by
  sorry

theorem RegData.sum_far_le (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0) :
    ∑' n : {n : ℕ | 1 ≤ n ∧ ‖z‖ / 2 < t n ∧ t n < 2 * ‖z‖ ∧
        K0 C * cellLen t n ≤ ‖z - rCentre ψ t n‖},
      cellLen t n ^ 2 / ‖z - rCentre ψ t n‖ ^ 2 ≤ 3 * (1 + (K0 C)⁻¹ ^ 2) * M := by
  sorry

/-- The Riemann-sum bound `∑_n d_n y / |z - r_n|² ≤ (9/4) π` over far `n`. -/
theorem RegData.sum_far_im_le (h : RegData ψ t C M) {z : ℂ} :
    ∑' n : {n : ℕ | 1 ≤ n ∧ K0 C * cellLen t n ≤ ‖z - rCentre ψ t n‖},
      cellLen t n * z.im / ‖z - rCentre ψ t n‖ ^ 2 ≤ 9 / 4 * Real.pi := by
  sorry

/-- The key estimate: `∑_n |j_n(z)| ≤ B` for `Im z ≥ 0`, with `B` depending only on `C, M, K, c`. -/
theorem RegData.exists_bound_cellTerm (h : RegData ψ t C M) (hK : DensBound ψ t K) :
    ∃ B : ℝ, ∀ z : ℂ, 0 ≤ z.im → ∑' n : ℕ, |cellTerm ψ t C (n + 1) z| ≤ B := by
  sorry

/-- `|U_ψ - log|f|| ≤ B` on `Im z ≥ 0`. -/
theorem RegData.exists_approx (h : RegData ψ t C M) (hK : DensBound ψ t K) :
    ∃ B : ℝ, ∀ z : ℂ, 0 ≤ z.im → |UPsi ψ z - Real.log ‖fProd ψ t C z‖| ≤ B := by
  sorry

/-! ## §6. Theorem 2 (i) -/

/-- The provable version of Theorem 2 (i), with the extra local regularity `DensBound`
(`RegData` is produced from the hypotheses of `theorem2_i` by `RegData.of_isLogRegularPartition`). -/
theorem theorem2_i_of_regular (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ} (h : RegData ψ t C M) (hK : DensBound ψ t K) :
    IsSampling (LambdaPsi ψ) := by
  sorry

/-- An eventually nonincreasing `ψ'` gives the local density bound: on `[t_{n-1}, t_n]`,
`ψ' ≤ ψ'(t_{n-1}) ≤ 1/d_{n-1} ≤ C/d_n` for the cells beyond `X` (the previous cell has mass `1`
and `ψ' ≥ ψ'(t_{n-1})` on it), and `ψ'` is bounded on the finitely many cells before `X`. -/
theorem RegData.densBound_of_antitoneOn (h : RegData ψ t C M)
    (hmono : ∃ X : ℝ, AntitoneOn (deriv ψ) (Set.Ici X)) : ∃ K : ℝ, DensBound ψ t K := by
  sorry

/-- **Theorem 2 (i)** (p. 801), identical to `comparator/statements.lean`.  The paper's argument
needs `DensBound`, which follows from `hmono` (NOTEBOOK N-22). -/
theorem theorem2_i (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x → c / x ≤ deriv ψ x)
    (hreg : IsLogRegularPartition ψ) (hmono : ∃ X : ℝ, AntitoneOn (deriv ψ) (Set.Ici X)) :
    IsSampling (LambdaPsi ψ) := by
  sorry

end FF
