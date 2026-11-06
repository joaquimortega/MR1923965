import FourierFrames.Construction
import FourierFrames.HB.Comparable
import FourierFrames.Theorem1.Sufficiency

/-!
# M06 — the example `Λ = {k + log⁺|k|}` of p. 798 and the sharpness of Landau's inequality

See `blueprint/M06_LogExample.md`.

* §1  the points `λ_k = k + log⁺|k|`, their gaps, separation, counting;
* §2  invariance of sampling / complete interpolation under real translations;
* §3  the step density `m` whose barycentre sequence is `Λ + 1/2` exactly;
* §4  the potential estimate `U(z) = π Im z + κ Re z + O(1)` for `Im z ≥ 0`;
* §5  the Hermite–Biehler function `E` with `H(E) = PW` and zero set `Λ + 1/2`;
* §6  Theorem E at the phase level `π/2`: sampling and complete interpolation;
* §7  the main statements `logExample_count`, `logExample_isCompleteInterpolating`,
  `landau_sharp`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## §1  The points `λ_k = k + log⁺|k|` -/

/-- `λ_k = k + log⁺|k|`. -/
def logLam (k : ℤ) : ℝ := (k : ℝ) + Real.posLog |(k : ℝ)|

/-- The gap `g_k = λ_{k+1} - λ_k`. -/
def logGap (k : ℤ) : ℝ := logLam (k + 1) - logLam k

theorem logExample_eq_range : logExample = Set.range logLam := rfl

/-- `1 - log 2 ≤ g_k ≤ 1 + log 2`; in particular `3/10 ≤ g_k ≤ 17/10`. -/
theorem logGap_bounds (k : ℤ) : 3 / 10 ≤ logGap k ∧ logGap k ≤ 17 / 10 := by
  sorry

/-- `|g_k - 1| ≤ 3/(1 + |k|)`. -/
theorem abs_logGap_sub_one_le (k : ℤ) : |logGap k - 1| ≤ 3 / (1 + |(k : ℝ)|) := by
  sorry

theorem logLam_sub_ge {a b : ℤ} (hab : a < b) : 3 / 10 * ((b : ℝ) - a) ≤ logLam b - logLam a := by
  sorry

theorem strictMono_logLam : StrictMono logLam := by
  sorry

theorem logLam_pos_iff (k : ℤ) : 0 < logLam k ↔ 1 ≤ k := by
  sorry

theorem logLam_nonpos_iff (k : ℤ) : logLam k ≤ 0 ↔ k ≤ 0 := by
  sorry

theorem logExample_isSeparated : IsSeparated logExample := by
  sorry

theorem ncard_logExample_inter_Ioc_pos (R : ℝ) :
    (logExample ∩ Ioc 0 R).ncard = {k : ℤ | 1 ≤ k ∧ (k : ℝ) + Real.log k ≤ R}.ncard := by
  sorry

theorem ncard_logExample_inter_Ioc_neg (R : ℝ) :
    (logExample ∩ Ioc (-R) 0).ncard = {k : ℤ | k ≤ 0 ∧ -R < logLam k}.ncard := by
  sorry

theorem card_pos_bounds {R : ℝ} (hR : 1 ≤ R) :
    |(({k : ℤ | 1 ≤ k ∧ (k : ℝ) + Real.log k ≤ R}.ncard : ℕ) : ℝ) - (R - Real.log R)| ≤ 2 := by
  sorry

theorem card_neg_bounds {R : ℝ} (hR : 1 ≤ R) :
    |(({k : ℤ | k ≤ 0 ∧ -R < logLam k}.ncard : ℕ) : ℝ) - (R + Real.log R)| ≤ 2 := by
  sorry

/-- **The example of p. 798**: `n_Λ(R) = R - log R + O(1)` and `-n_Λ(-R) = R + log R + O(1)` for
`Λ = {k + log⁺|k|}`. -/
theorem logExample_count : ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
    |((logExample ∩ Ioc 0 R).ncard : ℝ) - (R - Real.log R)| ≤ C ∧
      |((logExample ∩ Ioc (-R) 0).ncard : ℝ) - (R + Real.log R)| ≤ C := by
  sorry

/-! ## §2  Translation invariance -/

theorem isSampling_image_add (s : ℝ) {Λ : Set ℝ} (h : IsSampling Λ) :
    IsSampling ((fun x : ℝ ↦ x + s) '' Λ) := by
  sorry

theorem isCompleteInterpolating_image_add (s : ℝ) {Λ : Set ℝ} (h : IsCompleteInterpolating Λ) :
    IsCompleteInterpolating ((fun x : ℝ ↦ x + s) '' Λ) := by
  sorry

theorem isSampling_of_image_add (s : ℝ) {Λ : Set ℝ} (h : IsSampling ((fun x : ℝ ↦ x + s) '' Λ)) :
    IsSampling Λ := by
  sorry

theorem isCompleteInterpolating_of_image_add (s : ℝ) {Λ : Set ℝ}
    (h : IsCompleteInterpolating ((fun x : ℝ ↦ x + s) '' Λ)) : IsCompleteInterpolating Λ := by
  sorry

/-! ## §3  The step density with barycentre sequence `Λ + 1/2` -/

/-- Partition points `p_j = (λ_{j-1} + λ_j + 1)/2` (`p_0 = 0`). -/
def logPt (j : ℤ) : ℝ := (logLam (j - 1) + logLam j + 1) / 2

/-- Target barycentres `β_j = λ_j + 1/2`. -/
def logBary (j : ℤ) : ℝ := logLam j + 1 / 2

/-- The index `j` with `p_j ≤ t < p_{j+1}`. -/
def logIdx (t : ℝ) : ℤ := sSup {j : ℤ | logPt j ≤ t}

/-- Value of the density on `[p_j, β_j)`: `2 g_j / (g_{j-1}(g_{j-1} + g_j))`. -/
def logWeightL (j : ℤ) : ℝ := 2 * logGap j / (logGap (j - 1) * (logGap (j - 1) + logGap j))

/-- Value of the density on `[β_j, p_{j+1})`: `2 g_{j-1} / (g_j(g_{j-1} + g_j))`. -/
def logWeightR (j : ℤ) : ℝ := 2 * logGap (j - 1) / (logGap j * (logGap (j - 1) + logGap j))

/-- The step density `m`. -/
def logDensity (t : ℝ) : ℝ :=
  if t < logBary (logIdx t) then logWeightL (logIdx t) else logWeightR (logIdx t)

theorem logPt_zero : logPt 0 = 0 := by
  sorry

theorem strictMono_logPt : StrictMono logPt := by
  sorry

theorem logPt_lt_logBary (j : ℤ) : logPt j < logBary j ∧ logBary j < logPt (j + 1) := by
  sorry

theorem logIdx_spec (t : ℝ) : logPt (logIdx t) ≤ t ∧ t < logPt (logIdx t + 1) := by
  sorry

theorem logIdx_eq_iff {t : ℝ} {j : ℤ} : logIdx t = j ↔ t ∈ Ico (logPt j) (logPt (j + 1)) := by
  sorry

theorem measurable_logDensity : Measurable logDensity := by
  sorry

/-- `1/10 ≤ m ≤ 20`. -/
theorem logDensity_bounds (t : ℝ) : 1 / 10 ≤ logDensity t ∧ logDensity t ≤ 20 := by
  sorry

theorem isMultWeight_logDensity : OCS.IsMultWeight logDensity (1 / 10) 20 :=
  ⟨measurable_logDensity, by norm_num, fun t ↦ (logDensity_bounds t).1,
    fun t ↦ (logDensity_bounds t).2⟩

/-- `|m(t) - 1| ≤ C_m / (1 + |t|)` (one can take `C_m = 1100`). -/
theorem abs_logDensity_sub_one_le (t : ℝ) : |logDensity t - 1| ≤ 1100 / (1 + |t|) := by
  sorry

theorem tendsto_logDensity : Tendsto logDensity (cocompact ℝ) (𝓝 1) := by
  sorry

/-- `∫_{p_j}^{p_{j+1}} m = 1`. -/
theorem integral_logDensity_logPt (j : ℤ) : ∫ t in logPt j..logPt (j + 1), logDensity t = 1 := by
  sorry

/-- `∫_{p_j}^{p_{j+1}} t m(t) dt = β_j`. -/
theorem integral_mul_logDensity_logPt (j : ℤ) :
    ∫ t in logPt j..logPt (j + 1), t * logDensity t = logBary j := by
  sorry

theorem multPrim_logDensity_logPt (j : ℤ) : OCS.multPrim logDensity (logPt j) = j := by
  sorry

theorem multPt_logDensity (j : ℤ) : OCS.multPt logDensity j = logPt j := by
  sorry

theorem multBary_logDensity (j : ℤ) : OCS.multBary logDensity j = logLam j + 1 / 2 := by
  sorry

/-- The barycentre sequence of `m` is `Λ + 1/2`, exactly. -/
theorem multGamma_logDensity :
    OCS.multGamma logDensity = (fun x : ℝ ↦ x + 1 / 2) '' logExample := by
  sorry

/-! ## §4  The potential estimate -/

/-- `W(t) = M(t) - t` where `M = ∫_0^t m`. -/
def logW (t : ℝ) : ℝ := OCS.multPrim logDensity t - t

/-- `W` is Lipschitz with `W' = m - 1` a.e. -/
theorem logW_lipschitz : LipschitzWith 19 logW := by
  sorry

/-- `W(t) = -log⁺|t| + ρ(t)` with `|ρ(t)| ≤ C_ρ min(|t|, (1+|t|)^{-1/2})`. -/
theorem abs_logW_add_posLog_le : ∃ Cρ : ℝ, ∀ t : ℝ,
    |logW t + Real.posLog (|t|)| ≤ Cρ * min |t| (1 / Real.sqrt (1 + |t|)) := by
  sorry

/-- `κ = ∫_{|t|>1} (m(t) - 1)/t dt` (absolutely convergent). -/
def logKappa : ℝ :=
  ∫ t : ℝ, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((logDensity t - 1) / t)

theorem integrable_logKappa :
    Integrable (fun t : ℝ ↦ (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((logDensity t - 1) / t)) := by
  sorry

/-- The model computation: for `m ≡ 1`, `U(z) = π |Im z|`. -/
theorem multU_model {z : ℂ} (hz : 0 < z.im) :
    ∫ t : ℝ, OCS.multUIntegrand (fun _ ↦ 1) z t = Real.pi * z.im := by
  sorry

theorem integrable_log_mul_sub_one {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ ↦ Real.log ‖1 - z / t‖ * (logDensity t - 1)) := by
  sorry

/-- `U(z) = π Im z + κ Re z + V(z)` for `Im z > 0`, `V(z) = ∫ log|1 - z/t| (m(t) - 1) dt`. -/
theorem multU_logDensity_eq {z : ℂ} (hz : 0 < z.im) :
    OCS.multU logDensity 0 z = Real.pi * z.im + logKappa * z.re +
      ∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1) := by
  sorry

/-- The kernel `K_z(t) = (t - x)/((t - x)² + y²) - 1/t = Re(z / (t (t - z)))`. -/
def logKernel (z : ℂ) (t : ℝ) : ℝ := (t - z.re) / ((t - z.re) ^ 2 + z.im ^ 2) - 1 / t

theorem abs_logKernel_le {z : ℂ} (hz : 0 < z.im) {t : ℝ} (ht : t ≠ 0) :
    |logKernel z t| ≤ ‖z‖ / (|t| * ‖(t : ℂ) - z‖) := by
  sorry

/-- Integration by parts: `V(z) = -∫ W(t) K_z(t) dt`. -/
theorem integral_log_mul_sub_one_eq {z : ℂ} (hz : 0 < z.im) :
    ∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1) = -∫ t : ℝ, logW t * logKernel z t := by
  sorry

/-- `∫_0^∞ log((1+σ)/|1-σ|) dσ/σ < ∞` (its value is `π²/2`). -/
theorem integrableOn_log_ratio_div :
    IntegrableOn (fun σ : ℝ ↦ Real.log ((1 + σ) / |1 - σ|) / σ) (Ioi 0) := by
  sorry

/-- The Hilbert-transform estimate for `log⁺|t|`: `|∫ log⁺|t| K_z(t) dt| ≤ C` for `Im z ≥ 1`. -/
theorem abs_integral_posLog_mul_logKernel_le : ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im →
    Integrable (fun t : ℝ ↦ Real.posLog |t| * logKernel z t) ∧
      |∫ t : ℝ, Real.posLog |t| * logKernel z t| ≤ C := by
  sorry

/-- `∫ |ρ| |K_z| ≤ C` for `Im z ≥ 1`, for `ρ` as in `abs_logW_add_posLog_le`. -/
theorem integral_abs_rho_logKernel_le : ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im →
    Integrable (fun t : ℝ ↦ |logW t + Real.posLog (|t|)| * |logKernel z t|) ∧
      ∫ t : ℝ, |logW t + Real.posLog (|t|)| * |logKernel z t| ≤ C := by
  sorry

theorem abs_integral_log_mul_sub_one_le : ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im →
    |∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1)| ≤ C := by
  sorry

/-- Comparison in the strip: `|U(x + iy) - U(x + i)| ≤ 20 π` for `0 ≤ y ≤ 1`. -/
theorem abs_multU_sub_multU_le {z : ℂ} (h0 : 0 ≤ z.im) (h1 : z.im ≤ 1) :
    |OCS.multU logDensity 0 z - OCS.multU logDensity 0 ((z.re : ℂ) + Complex.I)| ≤ 20 * Real.pi := by
  sorry

/-- **The sine-type estimate**: `U(z) = π Im z + κ Re z + O(1)` for `Im z ≥ 0`. -/
theorem logDensity_U_estimate : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
    |OCS.multU logDensity 0 z - Real.pi * z.im - logKappa * z.re| ≤ C := by
  sorry

/-! ## §5  The Hermite–Biehler function -/

/-- The function `E` of the example: `H(E) = PW`, no real zeros, zero set of `E + E^*` equal to
`Λ + 1/2`, with a phase function. -/
theorem exists_E_logExample (hPW : PaleyWienerThm) :
    ∃ E : ℂ → ℂ, IsHB E ∧ (∀ x : ℝ, E x ≠ 0) ∧ HEEqPW E ∧
      (∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
        c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) ∧
      (∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ (fun x : ℝ ↦ x + 1 / 2) '' logExample, z = (γ : ℂ)) ∧
      ∃ φ : ℝ → ℝ, IsPhaseFunction E φ := by
  sorry

/-! ## §6  Theorem E at the phase level `π/2` -/

theorem phaseLevel_eq_of_zero_set {E : ℂ → ℂ} {φ : ℝ → ℝ} {Γ : Set ℝ}
    (h0 : ∀ x : ℝ, E x ≠ 0) (hφ : IsPhaseFunction E φ)
    (hΓ : ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ Γ, z = (γ : ℂ)) :
    phaseLevel φ (Real.pi / 2) = Γ := by
  sorry

/-- `E + E^*` is not in `H(E)`: `|E + E^*| = 2|E||cos φ|` is not square integrable on `ℝ`,
because `φ' ≃ 1`. -/
theorem not_memHE_sAlpha (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ} {φ : ℝ → ℝ}
    (hHB : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (hEPW : HEEqPW E) (hφ : IsPhaseFunction E φ)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) :
    ¬ MemHE E (fun z ↦ Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * E z -
      Complex.exp (-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ))) * fstar E z) := by
  sorry

theorem eq_zero_of_pwNormSq_eq_zero {f : ℂ → ℂ} (hf : MemPW f) (h : pwNormSq f = 0) :
    ∀ z, f z = 0 := by
  sorry

/-- From `H(E) = PW`, `|E| ≃ 1` on `ℝ`, `φ_E' |E|² ≃ 1`, `E + E^* ∉ H(E)`: the zero set of
`E + E^*` is sampling and complete interpolating for `PW`. -/
theorem sampling_cis_of_zero_set (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ} {φ : ℝ → ℝ}
    {Γ : Set ℝ} (hHB : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (hEPW : HEEqPW E)
    (hφ : IsPhaseFunction E φ)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im))
    (hΓ : ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ Γ, z = (γ : ℂ)) :
    IsSampling Γ ∧ IsCompleteInterpolating Γ := by
  sorry

/-! ## §7  Main statements -/

theorem logExample_shift_sampling_cis (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsSampling ((fun x : ℝ ↦ x + 1 / 2) '' logExample) ∧
      IsCompleteInterpolating ((fun x : ℝ ↦ x + 1 / 2) '' logExample) := by
  sorry

/-- **The example of p. 798**: `{k + log⁺|k|}` is a complete interpolating sequence. -/
theorem logExample_isCompleteInterpolating (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsCompleteInterpolating logExample := by
  sorry

theorem logExample_isSampling (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsSampling logExample := by
  sorry

/-- **Landau's inequality is best possible** (p. 798): `{k + log⁺|k|}` is a separated sampling
sequence for which the logarithmic term cannot be removed. -/
theorem landau_sharp (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsSeparated logExample ∧ IsSampling logExample ∧
      ∀ A : ℝ, A < 1 → ¬ ∃ B : ℝ, ∀ a b : ℝ, a < b →
        ENNReal.ofReal (b - a - A * Real.posLog (b - a) - B) ≤
          ((logExample ∩ Ioc a b).encard : ℝ≥0∞) := by
  sorry

end FF
