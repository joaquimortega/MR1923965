import FourierFrames.Cited.DeBrangesDE.Space

/-!
# P3 — Theorem E, part 1: the orthogonal system `{K(γ, ·)}_{γ ∈ Γ}` and the function `h = D/S`

See `blueprint/P3_DeBrangesDE.md`, §5.  With `U = e^{iα} E`, `V = e^{-iα} E^*`, `C = (U+V)/2`,
`S = (U-V)/(2i)` (both real entire) one has `K(w,z) π (z - w̄) = C(z) conj S(w) - S(z) conj C(w)`.
`Γ = {φ ∈ α + πℤ}` is the zero set of `S`; `K(γ, ·) = -C(γ) S(·)/(π (· - γ))`; the `K(γ, ·)` are
pairwise orthogonal with `‖K_γ‖² = φ'(γ)|E(γ)|²/π`.  The Mittag-Leffler series
`R = Σ c_γ (1+γz)/(1+γ²) · S(z)/(z-γ)` (with `c_γ = 1/(πφ'(γ))`) is entire, `D = C + πR` vanishes
on `Γ`, hence `h = D/S` is entire, real, and the "defect kernel"
`Q(w,z) = K(w,z) - Σ_γ K(w,γ)K(γ,z)/K(γ,γ)` equals `S(z) conj S(w) (h(z) - conj h(w))/(π(z - w̄))`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- The standing hypotheses of Theorem E: `E` strict without real zeros, with phase function `φ`. -/
structure DBData (E : ℂ → ℂ) (φ : ℝ → ℝ) : Prop where
  strict : IsStrictHB E
  noZero : ∀ x : ℝ, E x ≠ 0
  phase : IsPhaseFunction E φ

/-- `C = (e^{iα} E + e^{-iα} E^*)/2`. -/
def cFun (E : ℂ → ℂ) (α : ℝ) : ℂ → ℂ :=
  fun z ↦ (Complex.exp (I * α) * E z + Complex.exp (-(I * α)) * fstar E z) / 2

/-- `S = (e^{iα} E - e^{-iα} E^*)/(2i)`; `2i S` is the function `S_α` of Theorem E. -/
def sFun (E : ℂ → ℂ) (α : ℝ) : ℂ → ℂ :=
  fun z ↦ (Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z) / (2 * I)

/-- The weight `wt(γ) = π / (φ'(γ) |E(γ)|²) = 1 / K(γ,γ)` (real form of `orthWeight`). -/
def wt (E : ℂ → ℂ) (x : ℝ) : ℝ := Real.pi / (phaseDeriv E x * ‖E x‖ ^ 2)

/-- The coefficients `c_γ = 1/(π φ'(γ))` of the Mittag-Leffler series. -/
def cLev (E : ℂ → ℂ) (x : ℝ) : ℝ := 1 / (Real.pi * phaseDeriv E x)

/-- The `γ`-th term `c_γ (1 + γ z)/(1 + γ²) · S(z)/(z - γ)` of the Mittag-Leffler series
(`S(z)/(z - γ)` is `dslope S γ z`, entire as `S(γ) = 0`). -/
def rTerm (E : ℂ → ℂ) (α : ℝ) (γ : ℝ) (z : ℂ) : ℂ :=
  ((cLev E γ : ℝ) : ℂ) * (1 + (γ : ℂ) * z) / (1 + (γ : ℂ) ^ 2) * dslope (sFun E α) (γ : ℂ) z

/-- The Mittag-Leffler series `R(z) = Σ_γ rTerm γ z`. -/
def rFun (E : ℂ → ℂ) (φ : ℝ → ℝ) (α : ℝ) (z : ℂ) : ℂ :=
  ∑' γ : phaseLevel φ α, rTerm E α γ z

/-- `D = C + π R`. -/
def dFun (E : ℂ → ℂ) (φ : ℝ → ℝ) (α : ℝ) (z : ℂ) : ℂ :=
  cFun E α z + Real.pi * rFun E φ α z

/-- The defect kernel `Q(w,z) = K(w,z) - Σ_γ K(w,γ) K(γ,z) wt(γ)`. -/
def defectKer (E : ℂ → ℂ) (φ : ℝ → ℝ) (α : ℝ) (w z : ℂ) : ℂ :=
  deBrangesKernel E w z - ∑' γ : phaseLevel φ α,
    deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * ((wt E γ : ℝ) : ℂ)

variable {E : ℂ → ℂ} {φ : ℝ → ℝ} {α : ℝ}

/-! ## 5.1 Algebra of `C`, `S` and the kernel -/

theorem fstar_cFun (E : ℂ → ℂ) (α : ℝ) : fstar (cFun E α) = cFun E α := by
  sorry

theorem fstar_sFun (E : ℂ → ℂ) (α : ℝ) : fstar (sFun E α) = sFun E α := by
  sorry

theorem differentiable_cFun (hE : Differentiable ℂ E) (α : ℝ) : Differentiable ℂ (cFun E α) := by
  sorry

theorem differentiable_sFun (hE : Differentiable ℂ E) (α : ℝ) : Differentiable ℂ (sFun E α) := by
  sorry

/-- The function of Theorem E is `2i S`. -/
theorem sAlpha_eq (E : ℂ → ℂ) (α : ℝ) :
    (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z) =
      fun z ↦ (2 * I) * sFun E α z := by
  sorry

/-- `E = e^{-iα}(C + iS)`, `E^* = e^{iα}(C - iS)`. -/
theorem E_eq_CS (E : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    E z = Complex.exp (-(I * α)) * (cFun E α z + I * sFun E α z) := by
  sorry

/-- **Christoffel–Darboux form**: `K(w,z) π (z - w̄) = C(z) conj S(w) - S(z) conj C(w)`. -/
theorem kernel_mul_CS (E : ℂ → ℂ) (α : ℝ) (w z : ℂ) :
    deBrangesKernel E w z * (Real.pi * (z - conj w)) =
      cFun E α z * conj (sFun E α w) - sFun E α z * conj (cFun E α w) := by
  sorry

/-! ## 5.2 The level set `Γ`, zeros of `S`, values at `Γ` -/

/-- `S(z) = 0` iff `z ∈ Γ` (as a complex number): `HB/Phase.zero_set_eq_phaseLevel` for the
rotated function `e^{i(α - π/2)} E`. -/
theorem sFun_eq_zero_iff (D : DBData E φ) (z : ℂ) :
    sFun E α z = 0 ↔ z ∈ Complex.ofReal '' phaseLevel φ α := by
  sorry

/-- On `Γ`: `C(γ)` is real with `C(γ)² = |E(γ)|²`. -/
theorem cFun_level (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    (cFun E α γ).im = 0 ∧ (cFun E α γ).re ^ 2 = ‖E γ‖ ^ 2 := by
  sorry

/-- On `Γ`: `S'(γ) = - C(γ) φ'(γ)`; in particular `S'(γ) ≠ 0`, the zeros of `S` are simple. -/
theorem deriv_sFun_level (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    deriv (sFun E α) (γ : ℂ) = -(cFun E α γ) * (phaseDeriv E γ : ℂ) := by
  sorry

/-- `K(γ, z) π (z - γ) = - C(γ) S(z)` for `γ ∈ Γ`. -/
theorem kernel_level_mul (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (z : ℂ) :
    deBrangesKernel E (γ : ℂ) z * (Real.pi * (z - γ)) = -(cFun E α γ) * sFun E α z := by
  sorry

/-- **Orthogonality**: `K(γ, γ') = 0` for `γ ≠ γ'` in `Γ`. -/
theorem kernel_level_orth (D : DBData E φ) {γ γ' : ℝ} (hγ : γ ∈ phaseLevel φ α)
    (hγ' : γ' ∈ phaseLevel φ α) (hne : γ ≠ γ') : deBrangesKernel E (γ : ℂ) γ' = 0 := by
  sorry

/-- `K(γ, z) = -(C(γ)/π) · dslope S γ z` for all `z` (also at `z = γ`, by `deriv_sFun_level`). -/
theorem kernel_level_eq_dslope (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (z : ℂ) :
    deBrangesKernel E (γ : ℂ) z = -(cFun E α γ / Real.pi) * dslope (sFun E α) (γ : ℂ) z := by
  sorry

theorem wt_pos (D : DBData E φ) (x : ℝ) : 0 < wt E x := by
  sorry

/-- `K(x,x) wt(x) = 1`. -/
theorem kernel_diag_mul_wt (D : DBData E φ) (x : ℝ) :
    deBrangesKernel E (x : ℂ) x * (wt E x : ℂ) = 1 := by
  sorry

/-- `orthWeight` is `ofReal wt`. -/
theorem orthWeight_eq (E : ℂ → ℂ) (x : ℝ) : orthWeight E x = ENNReal.ofReal (wt E x) := by
  sorry

/-- `Γ ∩ [a, b]` is finite (`φ` strictly increasing and continuous). -/
theorem phaseLevel_inter_Icc_finite (D : DBData E φ) (α a b : ℝ) :
    (phaseLevel φ α ∩ Icc a b).Finite := by
  sorry

/-! ## 5.3 Bessel's inequality and the summability of `c_γ / |w - γ|²` -/

/-- Finite orthonormal expansion: `Σ_{γ ∈ F} wt(γ) |f(γ)|² ≤ ‖f‖²_E`. -/
theorem bessel_finite (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f)
    (F : Finset (phaseLevel φ α)) :
    ∑ γ ∈ F, wt E γ * ‖f γ‖ ^ 2 ≤ (heNormSq E f).toReal := by
  sorry

/-- Pythagoras for the partial sums `s_F = Σ_{γ ∈ F} a_γ wt(γ) K_γ`. -/
theorem heNormSq_partialSum (D : DBData E φ) (a : ℝ → ℂ) (F : Finset (phaseLevel φ α)) :
    (heNormSq E (fun z ↦ ∑ γ ∈ F, a γ * (wt E γ : ℂ) * deBrangesKernel E (γ : ℂ) z)).toReal =
      ∑ γ ∈ F, wt E γ * ‖a γ‖ ^ 2 := by
  sorry

theorem memHE_partialSum (D : DBData E φ) (a : ℝ → ℂ) (F : Finset (phaseLevel φ α)) :
    MemHE E (fun z ↦ ∑ γ ∈ F, a γ * (wt E γ : ℂ) * deBrangesKernel E (γ : ℂ) z) := by
  sorry

/-- `⟨f, s_F⟩ = Σ_{γ ∈ F} conj(a_γ) wt(γ) f(γ)`. -/
theorem heInner_partialSum (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f) (a : ℝ → ℂ)
    (F : Finset (phaseLevel φ α)) :
    heInner E f (fun z ↦ ∑ γ ∈ F, a γ * (wt E γ : ℂ) * deBrangesKernel E (γ : ℂ) z) =
      ∑ γ ∈ F, conj (a γ) * (wt E γ : ℂ) * f γ := by
  sorry

/-- For nonreal `w`: `Σ_γ c_γ / |w - γ|² ≤ K(w,w) / |S(w)|²` (Bessel for `f = K_w`;
`wt(γ) |K(w,γ)|² = |S(w)|² c_γ / |w - γ|²`). -/
theorem summable_cLev_div (D : DBData E φ) {w : ℂ} (hw : w.im ≠ 0) :
    Summable (fun γ : phaseLevel φ α ↦ cLev E γ / ‖w - (γ : ℂ)‖ ^ 2) ∧
    ‖sFun E α w‖ ^ 2 * ∑' γ : phaseLevel φ α, cLev E γ / ‖w - (γ : ℂ)‖ ^ 2 ≤
      (deBrangesKernel E w w).re := by
  sorry

theorem summable_cLev_div_one_add_sq (D : DBData E φ) :
    Summable (fun γ : phaseLevel φ α ↦ cLev E γ / (1 + (γ : ℝ) ^ 2)) := by
  sorry

/-! ## 5.4 The entire function `D` and the quotient `h = D/S` -/

/-- Local uniform summability (M-test: for `|z| ≤ ρ`, `|γ| ≥ max (2ρ, 1)`,
`|rTerm γ z| ≤ 2 M_ρ (1 + ρ) c_γ / (1 + γ²)`, `M_ρ = sup_{|z| ≤ ρ} |S|`; finitely many other `γ`). -/
theorem summable_rTerm (D : DBData E φ) (α : ℝ) (z : ℂ) :
    Summable fun γ : phaseLevel φ α ↦ rTerm E α γ z := by
  sorry

/-- Each term of the series for `R` is entire and the series converges locally uniformly
(M-test with `Σ c_γ/(1 + γ²) < ∞`); hence `R` and `D` are entire. -/
theorem differentiable_rFun (D : DBData E φ) (α : ℝ) : Differentiable ℂ (rFun E φ α) := by
  sorry

theorem differentiable_dFun (D : DBData E φ) (α : ℝ) : Differentiable ℂ (dFun E φ α) := by
  sorry

theorem fstar_dFun (D : DBData E φ) (α : ℝ) : fstar (dFun E φ α) = dFun E φ α := by
  sorry

/-- `D(γ) = C(γ) + π S'(γ) c_γ = 0` for `γ ∈ Γ`. -/
theorem dFun_level (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    dFun E φ α γ = 0 := by
  sorry

/-- **`h = D/S` is entire**, real on `ℝ`. -/
theorem exists_hFun (D : DBData E φ) (α : ℝ) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∀ z, dFun E φ α z = h z * sFun E α z) ∧
      ∀ z, h (conj z) = conj (h z) := by
  sorry

/-! ## 5.5 The defect kernel -/

theorem summable_defect (D : DBData E φ) (w z : ℂ) :
    Summable (fun γ : phaseLevel φ α ↦
      deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * ((wt E γ : ℝ) : ℂ)) := by
  sorry

/-- Termwise identity: for `γ ∈ Γ`,
`(z - w̄) K(w,γ) K(γ,z) wt(γ) = S(z) conj (r_γ(w)) - conj S(w) r_γ(z)`
(`K(γ,z) = -(C(γ)/π) dslope S γ z`, `C(γ)² wt(γ) = π² c_γ`, and
`(z - w̄) = (z - γ) - (w̄ - γ)` with `(z - γ) dslope S γ z = S(z)`; the regularizing factors
`(1 + γ z)/(1 + γ²)` drop out because `γ [S(z) conj S(w) - conj S(w) S(z)] = 0`). -/
theorem term_identity (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (w z : ℂ) :
    (z - conj w) * (deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * (wt E γ : ℂ)) =
      sFun E α z * conj (rTerm E α γ w) - conj (sFun E α w) * rTerm E α γ z := by
  sorry

/-- **Mittag-Leffler identity**: `Q(w,z) π (z - w̄) = S(z) conj S(w) (h(z) - conj h(w))`
(`h` as in `exists_hFun`; partial fractions `(z - w̄)/((z-γ)(w̄-γ)) = 1/(w̄-γ) - 1/(z-γ)`). -/
theorem defectKer_mul (D : DBData E φ) {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) (w z : ℂ) :
    defectKer E φ α w z * (Real.pi * (z - conj w)) =
      sFun E α z * conj (sFun E α w) * (h z - conj (h w)) := by
  sorry

/-- `Q(w, w) = ‖K_w‖² - Σ_γ wt(γ) |K(w,γ)|² ≥ 0`. -/
theorem defectKer_diag (D : DBData E φ) (w : ℂ) :
    (defectKer E φ α w w).re =
      (deBrangesKernel E w w).re - ∑' γ : phaseLevel φ α,
        wt E γ * ‖deBrangesKernel E w γ‖ ^ 2 := by
  sorry

theorem defectKer_diag_nonneg (D : DBData E φ) (w : ℂ) : 0 ≤ (defectKer E φ α w w).re := by
  sorry

/-- `Im h(w) ≥ 0` on `ℂ₊`:
`Q(w,w) = |S(w)|² Im h(w) / (π Im w)`. -/
theorem im_hFun_nonneg (D : DBData E φ) {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) {w : ℂ} (hw : 0 < w.im) : 0 ≤ (h w).im := by
  sorry

end FF
