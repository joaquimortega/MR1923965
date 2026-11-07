import FourierFrames.Cited.DeBrangesDE.EAux.KernelSymm

/-!
# P3 — Theorem E, part 1: the orthogonal system `{K(γ, ·)}_{γ ∈ Γ}` and the function `h = D/S`

See `blueprint/P3_DeBrangesDE.md`, §5.  With `U = e^{iα} E`, `V = e^{-iα} E^* = U^*`,
`C = (U+V)/2`, `S = (U-V)/(2i)` (both real entire) one has
`K(w,z) π (z - w̄) = C(z) conj S(w) - S(z) conj C(w)`.
`Γ = {φ ∈ α + πℤ}` is the zero set of `S`; `K(γ, ·) = -(C(γ)/π) dslope S γ`; the `K(γ, ·)` are
pairwise orthogonal with `‖K_γ‖² = K(γ,γ) = φ'(γ)|E(γ)|²/π = 1/wt(γ)`.  The Mittag-Leffler series
`R = Σ c_γ (1+γz)/(1+γ²) · S(z)/(z-γ)` (with `c_γ = 1/(πφ'(γ))`) is entire, `D = C + πR` vanishes
on `Γ`, hence `h = D/S` is entire, real, and the "defect kernel"
`Q(w,z) = K(w,z) - Σ_γ K(w,γ)K(γ,z) wt(γ)` satisfies
`Q(w,z) π (z - w̄) = S(z) conj S(w) (h(z) - conj h(w))`.  Bessel's inequality gives
`Q(w,w) ≥ 0`, i.e. `Im h ≥ 0` on `ℂ₊`.
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

/-- Partial sum `s_F = Σ_{γ ∈ F} a_γ wt(γ) K_γ` of an orthogonal expansion. -/
def partialSum (E : ℂ → ℂ) (φ : ℝ → ℝ) (α : ℝ) (a : ℝ → ℂ) (F : Finset (phaseLevel φ α)) :
    ℂ → ℂ :=
  fun z ↦ ∑ γ ∈ F, a γ * ((wt E γ : ℝ) : ℂ) * deBrangesKernel E (γ : ℂ) z

variable {E : ℂ → ℂ} {φ : ℝ → ℝ} {α : ℝ}

/-! ## 5.1 Algebra of `C`, `S` and the kernel (no hypothesis on `E` except entire) -/

theorem conj_exp_I_mul (α : ℝ) : conj (Complex.exp (I * α)) = Complex.exp (-(I * α)) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]

theorem conj_exp_neg_I_mul (α : ℝ) : conj (Complex.exp (-(I * α))) = Complex.exp (I * α) := by
  rw [← Complex.exp_conj, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul,
    neg_neg]

theorem exp_neg_mul_exp (α : ℝ) : Complex.exp (-(I * α)) * Complex.exp (I * α) = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

theorem fstar_cFun (E : ℂ → ℂ) (α : ℝ) : fstar (cFun E α) = cFun E α := by
  funext z
  simp only [fstar, cFun, map_div₀, map_add, map_mul, conj_exp_I_mul, conj_exp_neg_I_mul,
    Complex.conj_conj, map_ofNat]
  ring

theorem fstar_sFun (E : ℂ → ℂ) (α : ℝ) : fstar (sFun E α) = sFun E α := by
  funext z
  simp only [fstar, sFun, map_div₀, map_sub, map_mul, conj_exp_I_mul, conj_exp_neg_I_mul,
    Complex.conj_conj, map_ofNat, Complex.conj_I]
  have hI : I ≠ 0 := Complex.I_ne_zero
  field_simp
  ring

theorem differentiable_cFun (hE : Differentiable ℂ E) (α : ℝ) : Differentiable ℂ (cFun E α) := by
  unfold cFun
  exact ((hE.const_mul _).add ((Differentiable.fstar hE).const_mul _)).div_const _

theorem differentiable_sFun (hE : Differentiable ℂ E) (α : ℝ) : Differentiable ℂ (sFun E α) := by
  unfold sFun
  exact ((hE.const_mul _).sub ((Differentiable.fstar hE).const_mul _)).div_const _

/-- The function of Theorem E is `2i S`. -/
theorem sAlpha_eq (E : ℂ → ℂ) (α : ℝ) :
    (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z) =
      fun z ↦ (2 * I) * sFun E α z := by
  funext z
  unfold sFun
  rw [mul_div_cancel₀ _ (mul_ne_zero two_ne_zero Complex.I_ne_zero)]

/-- `E = e^{-iα}(C + iS)`. -/
theorem E_eq_CS (E : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    E z = Complex.exp (-(I * α)) * (cFun E α z + I * sFun E α z) := by
  have hI : I ≠ 0 := Complex.I_ne_zero
  have h : cFun E α z + I * sFun E α z = Complex.exp (I * α) * E z := by
    unfold cFun sFun
    field_simp
    ring
  rw [h, ← mul_assoc, exp_neg_mul_exp, one_mul]

/-- **Christoffel–Darboux form**: `K(w,z) π (z - w̄) = C(z) conj S(w) - S(z) conj C(w)`. -/
theorem kernel_mul_CS (E : ℂ → ℂ) (α : ℝ) (w z : ℂ) :
    deBrangesKernel E w z * (Real.pi * (z - conj w)) =
      cFun E α z * conj (sFun E α w) - sFun E α z * conj (cFun E α w) := by
  rw [deBrangesKernel_mul]
  unfold kernelNum cFun sFun
  simp only [map_div₀, map_add, map_sub, map_mul, conj_exp_I_mul, conj_exp_neg_I_mul, map_ofNat,
    Complex.conj_I]
  rw [Complex.exp_neg]
  have ha : Complex.exp (I * α) ≠ 0 := Complex.exp_ne_zero _
  have hI : I ≠ 0 := Complex.I_ne_zero
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## 5.2 The level set `Γ`, zeros of `S`, values at `Γ` -/

/-- `e^{i(α - π/2)} = -i e^{iα}`. -/
theorem exp_I_mul_sub_pi_div_two (α : ℝ) :
    Complex.exp (I * ((α - Real.pi / 2 : ℝ) : ℂ)) = -I * Complex.exp (I * α) := by
  have h : I * ((α - Real.pi / 2 : ℝ) : ℂ) = I * α - Real.pi / 2 * I := by push_cast; ring
  rw [h, Complex.exp_sub, Complex.exp_pi_div_two_mul_I, div_eq_iff Complex.I_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `S(z) = 0` iff `z ∈ Γ` (as a complex number): `HB/Phase.zero_set_eq_phaseLevel` with the
constant `F = e^{i(α - π/2)}` (phase `π/2 - α`), since `E F + E^* F^* = 2 S`. -/
theorem sFun_eq_zero_iff (D : DBData E φ) (z : ℂ) :
    sFun E α z = 0 ↔ z ∈ Complex.ofReal '' phaseLevel φ α := by
  set θ : ℝ := α - Real.pi / 2 with hθ
  set F : ℂ → ℂ := fun z ↦ Complex.exp (I * θ) * (fun _ : ℂ ↦ (1 : ℂ)) z with hF_def
  have hF : IsHB F := isHB_one.rotate θ
  have hF0 : ∀ x : ℝ, F x ≠ 0 := fun x ↦ by simp [F, Complex.exp_ne_zero]
  have hφ1 : IsPhaseFunction (fun _ : ℂ ↦ (1 : ℂ)) (fun _ ↦ 0) :=
    ⟨continuous_const, fun x ↦ by simp⟩
  have hφF := hφ1.rotate θ
  have key := zero_set_eq_phaseLevel D.strict hF D.noZero hF0 D.phase hφF z
  have hsum : E z * F z + fstar E z * fstar F z = 2 * sFun E α z := by
    have hI : I ≠ 0 := Complex.I_ne_zero
    simp only [hF_def, fstar, mul_one, map_mul, hθ, exp_I_mul_sub_pi_div_two]
    rw [conj_exp_I_mul, map_neg, Complex.conj_I]
    unfold sFun fstar
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have hlev : phaseLevel (fun t ↦ φ t + (0 - θ)) (Real.pi / 2) = phaseLevel φ α := by
    ext x
    simp only [phaseLevel, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, by rw [hθ] at hk; linarith⟩
    · rintro ⟨k, hk⟩; exact ⟨k, by rw [hθ]; linarith⟩
  rw [hsum, hlev] at key
  rw [← key]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h; exact (mul_eq_zero.mp h).resolve_left two_ne_zero

/-- `S` does not vanish off the real axis. -/
theorem sFun_ne_zero (D : DBData E φ) {w : ℂ} (hw : w.im ≠ 0) : sFun E α w ≠ 0 := by
  intro h
  obtain ⟨x, _, rfl⟩ := (sFun_eq_zero_iff D w).mp h
  simp at hw

/-- On `ℝ`, `C = Re U` with `U = e^{iα} E`. -/
theorem cFun_ofReal (E : ℂ → ℂ) (α x : ℝ) :
    cFun E α x = (((Complex.exp (I * α) * E x).re : ℝ) : ℂ) := by
  unfold cFun
  rw [fstar_ofReal, ← conj_exp_I_mul, ← map_mul, Complex.add_conj]
  push_cast
  ring

/-- On `ℝ`, `S = Im U` with `U = e^{iα} E`. -/
theorem sFun_ofReal (E : ℂ → ℂ) (α x : ℝ) :
    sFun E α x = (((Complex.exp (I * α) * E x).im : ℝ) : ℂ) := by
  unfold sFun
  rw [fstar_ofReal, ← conj_exp_I_mul, ← map_mul, Complex.sub_conj]
  have hI : I ≠ 0 := Complex.I_ne_zero
  field_simp
  push_cast
  ring

theorem sFun_level (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) : sFun E α γ = 0 :=
  (sFun_eq_zero_iff D γ).mpr ⟨γ, hγ, rfl⟩

/-- At a point of `Γ`, `U(γ) = e^{iα} E(γ)` is real. -/
theorem im_U_level (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    (Complex.exp (I * α) * E γ).im = 0 := by
  have hS := sFun_level D hγ
  rw [sFun_ofReal] at hS
  exact_mod_cast hS

/-- On `Γ`: `C(γ)` is real with `C(γ)² = |E(γ)|²` (on `ℝ`, `C = Re U`, `S = Im U`). -/
theorem cFun_level (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    (cFun E α γ).im = 0 ∧ (cFun E α γ).re ^ 2 = ‖E γ‖ ^ 2 := by
  have him := im_U_level D hγ
  rw [cFun_ofReal]
  refine ⟨by simp, ?_⟩
  simp only [Complex.ofReal_re]
  have hn : ‖Complex.exp (I * α) * E γ‖ = ‖E γ‖ := by
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  rw [← hn, Complex.sq_norm, Complex.normSq_apply, him]
  ring

/-- `C(γ) = ↑(C(γ).re)` on `Γ`. -/
theorem cFun_level_real (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    cFun E α γ = (((cFun E α γ).re : ℝ) : ℂ) :=
  (Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr (cFun_level D hγ).1)).symm

theorem conj_cFun_level (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    conj (cFun E α γ) = cFun E α γ :=
  Complex.conj_eq_iff_im.mpr (cFun_level D hγ).1

/-- `‖C(γ)‖² = ‖E(γ)‖²` on `Γ` (as real numbers). -/
theorem norm_cFun_level_sq (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    ‖cFun E α γ‖ ^ 2 = ‖E γ‖ ^ 2 := by
  rw [cFun_level_real D hγ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact (cFun_level D hγ).2

theorem hasDerivAt_sFun (hE : Differentiable ℂ E) (α : ℝ) (z : ℂ) :
    HasDerivAt (sFun E α) ((Complex.exp (I * α) * deriv E z -
      Complex.exp (-(I * α)) * deriv (fstar E) z) / (2 * I)) z := by
  unfold sFun
  exact (((hE z).hasDerivAt.const_mul _).sub
    (((Differentiable.fstar hE) z).hasDerivAt.const_mul _)).div_const _

/-- On `ℝ`, `S' = Im U'`. -/
theorem deriv_sFun_ofReal (hE : Differentiable ℂ E) (α x : ℝ) :
    deriv (sFun E α) (x : ℂ) = (((Complex.exp (I * α) * deriv E x).im : ℝ) : ℂ) := by
  rw [(hasDerivAt_sFun hE α x).deriv, deriv_fstar_ofReal, ← conj_exp_I_mul, ← map_mul,
    Complex.sub_conj]
  have hI : I ≠ 0 := Complex.I_ne_zero
  field_simp
  push_cast
  ring

/-- On `Γ`: `S'(γ) = - C(γ) φ'(γ)` (`S' = Im U'` on `ℝ`, `U'(γ) = C(γ) E'(γ)/E(γ)`); in particular
`S'(γ) ≠ 0`, the zeros of `S` are simple. -/
theorem deriv_sFun_level (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    deriv (sFun E α) (γ : ℂ) = -(cFun E α γ) * (phaseDeriv E γ : ℂ) := by
  have hE := D.strict.1.1
  have hEγ := D.noZero γ
  rw [deriv_sFun_ofReal hE, cFun_ofReal]
  set U := Complex.exp (I * α) * E γ with hU
  have him : U.im = 0 := im_U_level D hγ
  have h1 : Complex.exp (I * α) * deriv E γ = U * (deriv E γ / E γ) := by
    rw [hU]; field_simp
  rw [h1, Complex.mul_im, him, zero_mul, add_zero]
  unfold phaseDeriv
  push_cast
  ring

/-- `K(γ, z) π (z - γ) = - C(γ) S(z)` for `γ ∈ Γ`. -/
theorem kernel_level_mul (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (z : ℂ) :
    deBrangesKernel E (γ : ℂ) z * (Real.pi * (z - γ)) = -(cFun E α γ) * sFun E α z := by
  have h := kernel_mul_CS E α (γ : ℂ) z
  rw [Complex.conj_ofReal, sFun_level D hγ, map_zero, conj_cFun_level D hγ] at h
  rw [h]
  ring

/-- **Orthogonality**: `K(γ, γ') = 0` for `γ ≠ γ'` in `Γ`. -/
theorem kernel_level_orth (D : DBData E φ) {γ γ' : ℝ} (hγ : γ ∈ phaseLevel φ α)
    (hγ' : γ' ∈ phaseLevel φ α) (hne : γ ≠ γ') : deBrangesKernel E (γ : ℂ) γ' = 0 := by
  have h := kernel_level_mul D hγ (γ' : ℂ)
  rw [sFun_level D hγ', mul_zero] at h
  have hne' : (Real.pi : ℂ) * ((γ' : ℂ) - γ) ≠ 0 := by
    apply mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [sub_ne_zero]
    exact_mod_cast hne.symm
  exact (mul_eq_zero.mp h).resolve_right hne'

/-- `K(γ, z) = -(C(γ)/π) · dslope S γ z` for all `z` (also at `z = γ`, by `deriv_sFun_level` and
`deBrangesKernel_diag_real`). -/
theorem kernel_level_eq_dslope (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (z : ℂ) :
    deBrangesKernel E (γ : ℂ) z = -(cFun E α γ / Real.pi) * dslope (sFun E α) (γ : ℂ) z := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hz : z = γ
  · subst hz
    rw [dslope_same, deriv_sFun_level D hγ, deBrangesKernel_diag_real]
    have h2 : ((cFun E α γ).re : ℂ) ^ 2 = (‖E γ‖ : ℂ) ^ 2 := by
      exact_mod_cast (cFun_level D hγ).2
    rw [cFun_level_real D hγ]
    field_simp
    push_cast
    rw [div_mul_cancel₀ _ hπ]
    linear_combination (-(phaseDeriv E γ : ℂ)) * h2
  · rw [dslope_of_ne _ hz, slope_def_field, sFun_level D hγ, sub_zero]
    have h := kernel_level_mul D hγ z
    have hzγ : z - γ ≠ 0 := sub_ne_zero.mpr hz
    field_simp
    linear_combination h

theorem wt_pos (D : DBData E φ) (x : ℝ) : 0 < wt E x := by
  have h1 := D.strict.phaseDeriv_pos (D.noZero x)
  have h2 : 0 < ‖E x‖ := norm_pos_iff.mpr (D.noZero x)
  unfold wt
  positivity

theorem cLev_pos (D : DBData E φ) (x : ℝ) : 0 < cLev E x := by
  have h1 := D.strict.phaseDeriv_pos (D.noZero x)
  unfold cLev
  positivity

/-- `K(x,x) wt(x) = 1`. -/
theorem kernel_diag_mul_wt (D : DBData E φ) (x : ℝ) :
    deBrangesKernel E (x : ℂ) x * (wt E x : ℂ) = 1 := by
  have h1 := (D.strict.phaseDeriv_pos (D.noZero x)).ne'
  have h2 : ‖E x‖ ≠ 0 := norm_ne_zero_iff.mpr (D.noZero x)
  rw [deBrangesKernel_diag_real, ← Complex.ofReal_mul]
  unfold wt
  rw [Complex.ofReal_eq_one]
  field_simp

/-- `wt(γ) |K(γ, z)|² = c_γ |dslope S γ z|²` for `γ ∈ Γ` (`C(γ)² = |E(γ)|²`). -/
theorem wt_mul_norm_kernel_level_sq (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (z : ℂ) :
    wt E γ * ‖deBrangesKernel E (γ : ℂ) z‖ ^ 2 =
      cLev E γ * ‖dslope (sFun E α) (γ : ℂ) z‖ ^ 2 := by
  have h1 := (D.strict.phaseDeriv_pos (D.noZero γ)).ne'
  have h2 : ‖E γ‖ ≠ 0 := norm_ne_zero_iff.mpr (D.noZero γ)
  rw [kernel_level_eq_dslope D hγ, norm_mul, norm_neg, norm_div, mul_pow, div_pow,
    norm_cFun_level_sq D hγ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  unfold wt cLev
  field_simp

/-- `orthWeight` is `ofReal wt`. -/
theorem orthWeight_eq (E : ℂ → ℂ) (x : ℝ) : orthWeight E x = ENNReal.ofReal (wt E x) := rfl

/-- `Γ ∩ [a, b]` is finite (`φ` strictly increasing: `IsPhaseFunction.strictMono_of_isStrictHB`). -/
theorem phaseLevel_inter_Icc_finite (D : DBData E φ) (α a b : ℝ) :
    (phaseLevel φ α ∩ Icc a b).Finite := by
  have hmono := D.phase.strictMono_of_isStrictHB D.strict D.noZero
  set T : Set ℝ := (fun k : ℤ ↦ α + k * Real.pi) ''
    (Finset.Icc ⌈(φ a - α) / Real.pi⌉ ⌊(φ b - α) / Real.pi⌋ : Set ℤ) with hT
  have hTf : T.Finite := (Finset.finite_toSet _).image _
  refine (hTf.preimage hmono.injective.injOn).subset ?_
  rintro x ⟨⟨k, hk⟩, hxa, hxb⟩
  have hφa := hmono.monotone hxa
  have hφb := hmono.monotone hxb
  refine ⟨k, ?_, hk.symm⟩
  simp only [Finset.coe_Icc, Set.mem_Icc]
  constructor
  · rw [Int.ceil_le, div_le_iff₀ Real.pi_pos]; linarith
  · rw [Int.le_floor, le_div_iff₀ Real.pi_pos]; linarith

/-! ## 5.3 Partial sums, Bessel's inequality -/

theorem memHE_partialSum (D : DBData E φ) (a : ℝ → ℂ) (F : Finset (phaseLevel φ α)) :
    MemHE E (partialSum E φ α a F) :=
  MemHE.finset_sum (f := fun γ z ↦ a γ * (wt E γ : ℂ) * deBrangesKernel E (γ : ℂ) z) F
    fun γ _ ↦ (memHE_deBrangesKernel D.strict.1 D.noZero γ).const_mul (a γ * (wt E γ : ℂ))

/-- `s_F(γ) = a(γ)` for `γ ∈ F` (orthogonality and `K(γ,γ) wt(γ) = 1`). -/
theorem partialSum_level (D : DBData E φ) (a : ℝ → ℂ) {F : Finset (phaseLevel φ α)}
    {γ : phaseLevel φ α} (hγ : γ ∈ F) : partialSum E φ α a F γ = a γ := by
  unfold partialSum
  rw [Finset.sum_eq_single γ]
  · rw [mul_assoc, mul_comm (wt E γ : ℂ), kernel_diag_mul_wt D γ, mul_one]
  · intro γ' _ hne
    rw [kernel_level_orth D γ'.2 γ.2 (fun h ↦ hne (Subtype.ext h)), mul_zero]
  · intro h; exact absurd hγ h

/-- `⟨f, s_F⟩ = Σ_{γ ∈ F} conj(a_γ) wt(γ) f(γ)`. -/
theorem heInner_partialSum (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f) (a : ℝ → ℂ)
    (F : Finset (phaseLevel φ α)) :
    heInner E f (partialSum E φ α a F) = ∑ γ ∈ F, conj (a γ) * (wt E γ : ℂ) * f γ := by
  have hE := D.strict.1
  have h0 := D.noZero
  have hK : ∀ γ ∈ F, MemHE E (fun z ↦ a γ * (wt E γ : ℂ) * deBrangesKernel E (γ : ℂ) z) :=
    fun γ _ ↦ (memHE_deBrangesKernel hE h0 γ).const_mul _
  rw [show partialSum E φ α a F = fun z ↦ ∑ γ ∈ F,
      (fun γ z ↦ a γ * (wt E γ : ℂ) * deBrangesKernel E (γ : ℂ) z) γ z from rfl,
    heInner_sum_right hE h0 F hf hK]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  rw [heInner_smul_right, heInner_kernel hE h0 hf, map_mul, Complex.conj_ofReal]

/-- `conj(a) wt a = wt |a|²`. -/
theorem conj_mul_wt_mul (a : ℂ) (w : ℝ) :
    conj a * (w : ℂ) * a = ((w * ‖a‖ ^ 2 : ℝ) : ℂ) := by
  rw [show conj a * (w : ℂ) * a = (w : ℂ) * (a * conj a) by ring, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_mul]

/-- Pythagoras: `‖s_F‖² = Σ_{γ ∈ F} wt(γ) |a_γ|²`. -/
theorem heNormSq_partialSum (D : DBData E φ) (a : ℝ → ℂ) (F : Finset (phaseLevel φ α)) :
    (heNormSq E (partialSum E φ α a F)).toReal = ∑ γ ∈ F, wt E γ * ‖a γ‖ ^ 2 := by
  have hs := memHE_partialSum D a F
  have h1 := heInner_self D.strict.1 hs
  rw [heInner_partialSum D hs a F] at h1
  have h2 : ∑ γ ∈ F, conj (a γ) * (wt E γ : ℂ) * partialSum E φ α a F γ =
      ((∑ γ ∈ F, wt E γ * ‖a γ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun γ hγ ↦ ?_
    rw [partialSum_level D a hγ, conj_mul_wt_mul]
  rw [h2] at h1
  exact_mod_cast h1.symm

/-- Finite Bessel inequality: `Σ_{γ ∈ F} wt(γ) |f(γ)|² ≤ ‖f‖²_E`
(`0 ≤ ‖f - s_F‖²` with `a = f|_Γ`). -/
theorem bessel_finite (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f)
    (F : Finset (phaseLevel φ α)) :
    ∑ γ ∈ F, wt E γ * ‖f γ‖ ^ 2 ≤ (heNormSq E f).toReal := by
  have hE := D.strict.1
  have h0 := D.noZero
  have hs := memHE_partialSum D (fun t ↦ f t) F
  have h1 := heNormSq_sub hE h0 hf hs
  rw [heNormSq_partialSum D _ F, heInner_partialSum D hf _ F] at h1
  have h2 : (∑ γ ∈ F, conj (f γ) * (wt E γ : ℂ) * f γ).re = ∑ γ ∈ F, wt E γ * ‖f γ‖ ^ 2 := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    rw [conj_mul_wt_mul, Complex.ofReal_re]
  rw [h2] at h1
  have h3 : 0 ≤ (heNormSq E (fun z ↦ f z - partialSum E φ α (fun t ↦ f t) F z)).toReal :=
    ENNReal.toReal_nonneg
  linarith

/-- Bessel's inequality: `Σ_γ wt(γ) |f(γ)|²` converges and is `≤ ‖f‖²_E`. -/
theorem bessel (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f) :
    Summable (fun γ : phaseLevel φ α ↦ wt E γ * ‖f γ‖ ^ 2) ∧
      ∑' γ : phaseLevel φ α, wt E γ * ‖f γ‖ ^ 2 ≤ (heNormSq E f).toReal := by
  have hnn : 0 ≤ fun γ : phaseLevel φ α ↦ wt E γ * ‖f γ‖ ^ 2 := fun γ ↦
    mul_nonneg (wt_pos D γ).le (by positivity)
  exact ⟨summable_of_sum_le hnn (bessel_finite D hf), Real.tsum_le_of_sum_le hnn (bessel_finite D hf)⟩

/-- Bessel for `f = K_z`, rewritten with `wt_mul_norm_kernel_level_sq`:
`Σ_γ c_γ |dslope S γ z|² ≤ K(z, z)` for every `z ∈ ℂ`. -/
theorem summable_cLev_dslope_sq (D : DBData E φ) (z : ℂ) :
    Summable (fun γ : phaseLevel φ α ↦ cLev E γ * ‖dslope (sFun E α) (γ : ℂ) z‖ ^ 2) ∧
      ∑' γ : phaseLevel φ α, cLev E γ * ‖dslope (sFun E α) (γ : ℂ) z‖ ^ 2 ≤
        (deBrangesKernel E z z).re := by
  have hE := D.strict.1
  have h0 := D.noZero
  have hb := bessel (α := α) D (memHE_deBrangesKernel hE h0 z)
  have heq : (fun γ : phaseLevel φ α ↦ wt E γ * ‖deBrangesKernel E z γ‖ ^ 2) =
      fun γ : phaseLevel φ α ↦ cLev E γ * ‖dslope (sFun E α) (γ : ℂ) z‖ ^ 2 := by
    funext γ
    rw [← deBrangesKernel_conj_symm E (γ : ℂ) z, Complex.norm_conj,
      wt_mul_norm_kernel_level_sq D γ.2]
  rw [heq, heNormSq_kernel hE h0] at hb
  exact hb

/-- For nonreal `w`: `Σ_γ c_γ / |w - γ|² < ∞` (`dslope S γ w = S(w)/(w - γ)`, `S(w) ≠ 0`). -/
theorem summable_cLev_div (D : DBData E φ) {w : ℂ} (hw : w.im ≠ 0) :
    Summable (fun γ : phaseLevel φ α ↦ cLev E γ / ‖w - (γ : ℂ)‖ ^ 2) := by
  have hS := sFun_ne_zero (α := α) D hw
  have hSn : ‖sFun E α w‖ ≠ 0 := norm_ne_zero_iff.mpr hS
  refine ((summable_cLev_dslope_sq D w).1.mul_left ((‖sFun E α w‖ ^ 2)⁻¹)).congr fun γ ↦ ?_
  have hne : w ≠ (γ : ℂ) := by intro h; apply hw; rw [h]; simp
  have hne' : ‖w - (γ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  rw [dslope_of_ne _ hne, slope_def_field, sFun_level D γ.2, sub_zero, norm_div]
  field_simp

/-- `Σ_γ c_γ / (1 + γ²) < ∞` (`w = i`). -/
theorem summable_cLev_div_one_add_sq (D : DBData E φ) :
    Summable (fun γ : phaseLevel φ α ↦ cLev E γ / (1 + (γ : ℝ) ^ 2)) := by
  refine (summable_cLev_div (α := α) D (w := I) (by simp)).congr fun γ ↦ ?_
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-! ## 5.4 The entire function `D` and the quotient `h = D/S` -/

/-- `{γ ∈ Γ : |γ| < r}` is finite. -/
theorem finite_level_abs_lt (D : DBData E φ) (α r : ℝ) :
    {γ : phaseLevel φ α | |(γ : ℝ)| < r}.Finite := by
  refine ((phaseLevel_inter_Icc_finite D α (-r) r).preimage
    Subtype.val_injective.injOn).subset ?_
  intro γ hγ
  have h : |(γ : ℝ)| < r := hγ
  exact ⟨γ.2, (abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩

/-- M-test bound: for `‖z‖ ≤ ρ` and `|γ| ≥ 2ρ + 1`,
`‖rTerm γ z‖ ≤ 2 M (1 + ρ) c_γ / (1 + γ²)` where `‖S‖ ≤ M` on `‖z‖ ≤ ρ`. -/
theorem norm_rTerm_le (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) {ρ M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖sFun E α z‖ ≤ M) (hγρ : 2 * ρ + 1 ≤ |γ|) {z : ℂ} (hz : ‖z‖ ≤ ρ) :
    ‖rTerm E α γ z‖ ≤ 2 * M * (1 + ρ) * (cLev E γ / (1 + γ ^ 2)) := by
  have hρ : 0 ≤ ρ := (norm_nonneg z).trans hz
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simpa using hρ))
  have hγ1 : 1 ≤ |γ| := by linarith
  have hγpos : 0 < |γ| := by linarith
  have hzγ : |γ| / 2 ≤ ‖z - γ‖ := by
    have h1 : |γ| - ‖z‖ ≤ ‖z - γ‖ := by
      have := norm_sub_norm_le (γ : ℂ) z
      rwa [Complex.norm_real, Real.norm_eq_abs, norm_sub_rev] at this
    linarith
  have hzγpos : 0 < ‖z - γ‖ := by linarith
  have hne : z ≠ γ := by
    intro h; rw [h, sub_self, norm_zero] at hzγpos; exact lt_irrefl _ hzγpos
  have hc := cLev_pos D γ
  have h1 : ‖1 + (γ : ℂ) * z‖ ≤ 1 + |γ| * ρ := by
    calc ‖1 + (γ : ℂ) * z‖ ≤ ‖(1 : ℂ)‖ + ‖(γ : ℂ) * z‖ := norm_add_le _ _
      _ = 1 + |γ| * ‖z‖ := by rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 + |γ| * ρ := by gcongr
  have h2 : ‖1 + (γ : ℂ) ^ 2‖ = 1 + γ ^ 2 := by
    rw [show (1 + (γ : ℂ) ^ 2) = ((1 + γ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h3 : ‖sFun E α z‖ ≤ M := hM z hz
  unfold rTerm
  rw [dslope_of_ne _ hne, slope_def_field, sFun_level D hγ, sub_zero, norm_mul, norm_div,
    norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, h2]
  calc cLev E γ * ‖1 + ↑γ * z‖ / (1 + γ ^ 2) * (‖sFun E α z‖ / ‖z - ↑γ‖)
      ≤ cLev E γ * (1 + |γ| * ρ) / (1 + γ ^ 2) * (M / (|γ| / 2)) := by
        gcongr
    _ = 2 * M * (1 / |γ| + ρ) * (cLev E γ / (1 + γ ^ 2)) := by
        field_simp
    _ ≤ 2 * M * (1 + ρ) * (cLev E γ / (1 + γ ^ 2)) := by
        gcongr
        rw [div_le_one hγpos]
        exact hγ1

theorem summable_rTerm (D : DBData E φ) (α : ℝ) (z : ℂ) :
    Summable fun γ : phaseLevel φ α ↦ rTerm E α γ z := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) ‖z‖).exists_bound_of_continuousOn
    (differentiable_sFun D.strict.1.1 α).continuous.continuousOn
  have hM' : ∀ w : ℂ, ‖w‖ ≤ ‖z‖ → ‖sFun E α w‖ ≤ M := fun w hw ↦ hM w (by simpa using hw)
  refine Summable.of_norm_bounded_eventually
    ((summable_cLev_div_one_add_sq (α := α) D).mul_left (2 * M * (1 + ‖z‖))) ?_
  rw [Filter.eventually_cofinite]
  refine (finite_level_abs_lt D α (2 * ‖z‖ + 1)).subset fun γ hγ ↦ ?_
  by_contra hlt
  exact hγ (norm_rTerm_le D γ.2 hM' (not_lt.mp hlt) le_rfl)

theorem differentiable_dslope_sFun (hE : Differentiable ℂ E) (α : ℝ) (c : ℂ) :
    Differentiable ℂ (dslope (sFun E α) c) :=
  differentiableOn_univ.mp ((differentiableOn_dslope (Filter.univ_mem (f := 𝓝 c))).mpr
    (differentiable_sFun hE α).differentiableOn)

theorem differentiable_rTerm (hE : Differentiable ℂ E) (α γ : ℝ) :
    Differentiable ℂ (rTerm E α γ) := by
  have h := differentiable_dslope_sFun hE α (γ : ℂ)
  show Differentiable ℂ (fun z ↦ ((cLev E γ : ℝ) : ℂ) * (1 + (γ : ℂ) * z) / (1 + (γ : ℂ) ^ 2) *
    dslope (sFun E α) (γ : ℂ) z)
  fun_prop

/-- Each term of the series for `R` is entire and the series converges locally uniformly
(`differentiableOn_tsum_of_summable_norm` on balls, with `norm_rTerm_le` and finitely many
exceptional `γ`); hence `R` and `D` are entire. -/
theorem differentiable_rFun (D : DBData E φ) (α : ℝ) : Differentiable ℂ (rFun E φ α) := by
  have hE := D.strict.1.1
  have hball : ∀ ρ : ℝ, 0 < ρ → DifferentiableOn ℂ (rFun E φ α) (Metric.ball 0 ρ) := by
    intro ρ hρ
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn
      (differentiable_sFun hE α).continuous.continuousOn
    have hM' : ∀ w : ℂ, ‖w‖ ≤ ρ → ‖sFun E α w‖ ≤ M := fun w hw ↦ hM w (by simpa using hw)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM' 0 (by simpa using hρ.le))
    have hB : ∀ γ : phaseLevel φ α, ∃ B : ℝ, ∀ w ∈ Metric.closedBall (0 : ℂ) ρ,
        ‖rTerm E α γ w‖ ≤ B := fun γ ↦
      (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn
        (differentiable_rTerm hE α γ).continuous.continuousOn
    choose B hB using hB
    set g : phaseLevel φ α → ℝ := fun γ ↦ 2 * M * (1 + ρ) * (cLev E γ / (1 + (γ : ℝ) ^ 2))
      with hg_def
    have hg : Summable g := (summable_cLev_div_one_add_sq D).mul_left _
    have hg0 : ∀ γ, 0 ≤ g γ := fun γ ↦ by
      have := cLev_pos D γ
      simp only [hg_def]
      positivity
    set u : phaseLevel φ α → ℝ := fun γ ↦ if |(γ : ℝ)| < 2 * ρ + 1 then B γ else g γ
      with hu_def
    have hu : Summable u := by
      refine Summable.of_norm_bounded_eventually hg ?_
      rw [Filter.eventually_cofinite]
      refine (finite_level_abs_lt D α (2 * ρ + 1)).subset fun γ hγ ↦ ?_
      by_contra hlt
      have hlt' : ¬ |(γ : ℝ)| < 2 * ρ + 1 := hlt
      apply hγ
      show ‖(if |(γ : ℝ)| < 2 * ρ + 1 then B γ else g γ)‖ ≤ g γ
      rw [ite_eq_right hlt', Real.norm_eq_abs, abs_of_nonneg (hg0 γ)]
    have hbd : ∀ γ : phaseLevel φ α, ∀ w ∈ Metric.ball (0 : ℂ) ρ, ‖rTerm E α γ w‖ ≤ u γ := by
      intro γ w hw
      have hw' : ‖w‖ ≤ ρ := by simpa using (Metric.mem_ball.mp hw).le
      show ‖rTerm E α γ w‖ ≤ (if |(γ : ℝ)| < 2 * ρ + 1 then B γ else g γ)
      split_ifs with h
      · exact hB γ w (Metric.ball_subset_closedBall hw)
      · exact norm_rTerm_le D γ.2 hM' (not_lt.mp h) hw'
    exact differentiableOn_tsum_of_summable_norm hu
      (fun γ ↦ (differentiable_rTerm hE α γ).differentiableOn) Metric.isOpen_ball hbd
  intro z
  exact (hball (‖z‖ + 1) (by positivity)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simp))

theorem differentiable_dFun (D : DBData E φ) (α : ℝ) : Differentiable ℂ (dFun E φ α) := by
  unfold dFun
  exact (differentiable_cFun D.strict.1.1 α).add ((differentiable_rFun D α).const_mul _)

/-- `S(z̄) = conj S(z)`. -/
theorem sFun_conj (E : ℂ → ℂ) (α : ℝ) (w : ℂ) : sFun E α (conj w) = conj (sFun E α w) := by
  have h := congrFun (fstar_sFun E α) w
  simp only [fstar] at h
  rw [← h, Complex.conj_conj]

/-- `dslope S γ (z̄) = conj (dslope S γ z)` for real `γ`. -/
theorem dslope_sFun_conj (α γ : ℝ) (z : ℂ) :
    dslope (sFun E α) (γ : ℂ) (conj z) = conj (dslope (sFun E α) (γ : ℂ) z) := by
  by_cases hz : z = γ
  · subst hz
    rw [Complex.conj_ofReal, dslope_same]
    have h := deriv_fstar_ofReal (sFun E α) γ
    rwa [fstar_sFun] at h
  · have hz' : conj z ≠ γ := by
      intro h; apply hz; rw [← Complex.conj_conj z, h, Complex.conj_ofReal]
    have hγ : conj (sFun E α γ) = sFun E α γ := by rw [← sFun_conj, Complex.conj_ofReal]
    rw [dslope_of_ne _ hz, dslope_of_ne _ hz', slope_def_field, slope_def_field, sFun_conj,
      map_div₀, map_sub, map_sub, hγ, Complex.conj_ofReal]

theorem conj_rTerm_conj (α γ : ℝ) (z : ℂ) :
    conj (rTerm E α γ (conj z)) = rTerm E α γ z := by
  unfold rTerm
  simp only [map_mul, map_div₀, map_add, map_one, map_pow, Complex.conj_ofReal,
    Complex.conj_conj, dslope_sFun_conj]

theorem fstar_dFun (E : ℂ → ℂ) (φ : ℝ → ℝ) (α : ℝ) : fstar (dFun E φ α) = dFun E φ α := by
  funext z
  have hC := congrFun (fstar_cFun E α) z
  simp only [fstar] at hC ⊢
  unfold dFun rFun
  rw [map_add, map_mul, Complex.conj_ofReal, hC, Complex.conj_tsum]
  simp only [conj_rTerm_conj]

theorem rTerm_level_ne (D : DBData E φ) {γ γ' : ℝ} (hγ : γ ∈ phaseLevel φ α)
    (hγ' : γ' ∈ phaseLevel φ α) (hne : γ' ≠ γ) : rTerm E α γ' γ = 0 := by
  unfold rTerm
  rw [dslope_of_ne _ (by exact_mod_cast hne.symm : (γ : ℂ) ≠ γ'), slope_def_field,
    sFun_level D hγ, sFun_level D hγ', sub_zero, zero_div, mul_zero]

theorem rTerm_level_self (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    rTerm E α γ γ = -(cFun E α γ) / Real.pi := by
  unfold rTerm
  rw [dslope_same, deriv_sFun_level D hγ]
  have h1 : (phaseDeriv E γ : ℂ) ≠ 0 := by
    exact_mod_cast (D.strict.phaseDeriv_pos (D.noZero γ)).ne'
  have h2 : (1 + (γ : ℂ) ^ 2) ≠ 0 := by norm_cast; positivity
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold cLev
  push_cast
  field_simp

/-- `D(γ) = C(γ) + π c_γ S'(γ) = 0` for `γ ∈ Γ`. -/
theorem dFun_level (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    dFun E φ α γ = 0 := by
  unfold dFun rFun
  rw [tsum_eq_single ⟨γ, hγ⟩ (fun γ' hne ↦ rTerm_level_ne D hγ γ'.2
    (fun h ↦ hne (Subtype.ext h))), rTerm_level_self D hγ]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

theorem cFun_level_ne_zero (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    cFun E α γ ≠ 0 := by
  intro hC
  have h2 := (cFun_level D hγ).2
  rw [hC, Complex.zero_re] at h2
  have h3 : ‖E γ‖ ^ 2 = 0 := by rw [← h2]; ring
  exact D.noZero γ (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3))

/-- **`h = D/S` is entire**, real on `ℝ` (removable singularities at the simple zeros of `S`). -/
theorem exists_hFun (D : DBData E φ) (α : ℝ) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∀ z, dFun E φ α z = h z * sFun E α z) ∧
      ∀ z, h (conj z) = conj (h z) := by
  have hE := D.strict.1.1
  have hSd : Differentiable ℂ (sFun E α) := differentiable_sFun hE α
  have hDd : Differentiable ℂ (dFun E φ α) := differentiable_dFun D α
  set h : ℂ → ℂ := fun z ↦ if sFun E α z = 0 then deriv (dFun E φ α) z / deriv (sFun E α) z
    else dFun E φ α z / sFun E α z with hh
  have hzero : ∀ z, sFun E α z = 0 → ∃ γ : ℝ, γ ∈ phaseLevel φ α ∧ z = γ := fun z hz ↦ by
    obtain ⟨γ, hγ, rfl⟩ := (sFun_eq_zero_iff D z).mp hz
    exact ⟨γ, hγ, rfl⟩
  refine ⟨h, ?_, ?_, ?_⟩
  · intro z
    by_cases hz : sFun E α z = 0
    · obtain ⟨γ, hγ, rfl⟩ := hzero z hz
      have hdd : Differentiable ℂ (dslope (sFun E α) (γ : ℂ)) :=
        differentiable_dslope_sFun hE α γ
      have hδd : Differentiable ℂ (dslope (dFun E φ α) (γ : ℂ)) :=
        differentiableOn_univ.mp ((differentiableOn_dslope (Filter.univ_mem (f := 𝓝 (γ : ℂ)))).mpr
          hDd.differentiableOn)
      have hdγ : dslope (sFun E α) (γ : ℂ) γ ≠ 0 := by
        rw [dslope_same, deriv_sFun_level D hγ]
        refine mul_ne_zero (neg_ne_zero.mpr (cFun_level_ne_zero D hγ)) ?_
        exact_mod_cast (D.strict.phaseDeriv_pos (D.noZero γ)).ne'
      have hev : ∀ᶠ w in 𝓝 (γ : ℂ), dslope (sFun E α) (γ : ℂ) w ≠ 0 :=
        hdd.continuous.continuousAt.eventually_ne hdγ
      have heq : h =ᶠ[𝓝 (γ : ℂ)] fun w ↦
          dslope (dFun E φ α) (γ : ℂ) w / dslope (sFun E α) (γ : ℂ) w := by
        filter_upwards [hev] with w hw
        by_cases hwγ : w = γ
        · subst hwγ
          simp only [hh, ite_eq_left hz]
          rw [dslope_same, dslope_same]
        · have hSw : sFun E α w = (w - γ) * dslope (sFun E α) (γ : ℂ) w := by
            have := sub_smul_dslope (sFun E α) (γ : ℂ) w
            rw [smul_eq_mul, hz, sub_zero] at this
            exact this.symm
          have hDw : dFun E φ α w = (w - γ) * dslope (dFun E φ α) (γ : ℂ) w := by
            have := sub_smul_dslope (dFun E φ α) (γ : ℂ) w
            rw [smul_eq_mul, dFun_level D hγ, sub_zero] at this
            exact this.symm
          have hwγ' : w - γ ≠ 0 := sub_ne_zero.mpr hwγ
          have hSw0 : sFun E α w ≠ 0 := by rw [hSw]; exact mul_ne_zero hwγ' hw
          simp only [hh, ite_eq_right hSw0]
          rw [hSw, hDw, mul_div_mul_left _ _ hwγ']
      exact ((hδd γ).div (hdd γ) hdγ).congr_of_eventuallyEq heq
    · have hev : ∀ᶠ w in 𝓝 z, sFun E α w ≠ 0 := hSd.continuous.continuousAt.eventually_ne hz
      have heq : h =ᶠ[𝓝 z] fun w ↦ dFun E φ α w / sFun E α w := by
        filter_upwards [hev] with w hw
        simp only [hh, ite_eq_right hw]
      exact ((hDd z).div (hSd z) hz).congr_of_eventuallyEq heq
  · intro z
    by_cases hz : sFun E α z = 0
    · obtain ⟨γ, hγ, rfl⟩ := hzero z hz
      rw [hz, mul_zero]
      exact dFun_level D hγ
    · simp only [hh, ite_eq_right hz]
      rw [div_mul_cancel₀ _ hz]
  · intro z
    have hDc : dFun E φ α (conj z) = conj (dFun E φ α z) := by
      have h1 := congrFun (fstar_dFun E φ α) z
      simp only [fstar] at h1
      rw [← h1, Complex.conj_conj]
    have hdS : deriv (sFun E α) (conj z) = conj (deriv (sFun E α) z) := by
      have h1 := deriv_fstar (sFun E α) (conj z)
      rwa [Complex.conj_conj, fstar_sFun] at h1
    have hdD : deriv (dFun E φ α) (conj z) = conj (deriv (dFun E φ α) z) := by
      have h1 := deriv_fstar (dFun E φ α) (conj z)
      rwa [Complex.conj_conj, fstar_dFun E φ α] at h1
    by_cases hz : sFun E α z = 0
    · have hz' : sFun E α (conj z) = 0 := by rw [sFun_conj, hz, map_zero]
      simp only [hh, ite_eq_left hz, ite_eq_left hz']
      rw [hdS, hdD, map_div₀]
    · have hz' : sFun E α (conj z) ≠ 0 := by
        rw [sFun_conj]; exact (map_ne_zero _).mpr hz
      simp only [hh, ite_eq_right hz, ite_eq_right hz']
      rw [sFun_conj, hDc, map_div₀]

/-! ## 5.5 The defect kernel -/

/-- Termwise: `K(w,γ) K(γ,z) wt(γ) = c_γ conj(dslope S γ w) dslope S γ z`. -/
theorem defect_term_eq (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (w z : ℂ) :
    deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * (wt E γ : ℂ) =
      (cLev E γ : ℂ) * conj (dslope (sFun E α) (γ : ℂ) w) * dslope (sFun E α) (γ : ℂ) z := by
  rw [← deBrangesKernel_conj_symm E (γ : ℂ) w, kernel_level_eq_dslope D hγ w,
    kernel_level_eq_dslope D hγ z, map_mul, map_neg, map_div₀, conj_cFun_level D hγ,
    Complex.conj_ofReal, cFun_level_real D hγ]
  have hc : (cFun E α γ).re ≠ 0 := by
    intro h
    exact cFun_level_ne_zero D hγ (by rw [cFun_level_real D hγ, h, Complex.ofReal_zero])
  have h1 := (D.strict.phaseDeriv_pos (D.noZero γ)).ne'
  have hc' : ((cFun E α γ).re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have h1' : (phaseDeriv E γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold wt cLev
  rw [← (cFun_level D hγ).2]
  push_cast
  field_simp

/-- Summability of the defect series (AM–GM and `summable_cLev_dslope_sq`). -/
theorem summable_defect (D : DBData E φ) (w z : ℂ) :
    Summable (fun γ : phaseLevel φ α ↦
      deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * ((wt E γ : ℝ) : ℂ)) := by
  have hw := (summable_cLev_dslope_sq (α := α) D w).1
  have hz := (summable_cLev_dslope_sq (α := α) D z).1
  refine Summable.of_norm_bounded ((hw.add hz).div_const 2) fun γ ↦ ?_
  have hc := cLev_pos D γ
  rw [defect_term_eq D γ.2, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hc]
  nlinarith [mul_nonneg hc.le (sq_nonneg (‖dslope (sFun E α) (γ : ℂ) w‖ -
    ‖dslope (sFun E α) (γ : ℂ) z‖))]

/-- Termwise identity: for `γ ∈ Γ`,
`(z - w̄) K(w,γ) K(γ,z) wt(γ) = S(z) conj (r_γ(w)) - conj S(w) r_γ(z)`
(by `defect_term_eq`, `S(z) = (z - γ) dslope S γ z` and
`(z-γ)(1+γw̄) - (w̄-γ)(1+γz) = (z - w̄)(1+γ²)`). -/
theorem term_identity (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (w z : ℂ) :
    (z - conj w) * (deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * (wt E γ : ℂ)) =
      sFun E α z * conj (rTerm E α γ w) - conj (sFun E α w) * rTerm E α γ z := by
  rw [defect_term_eq D hγ]
  have hS : ∀ u : ℂ, sFun E α u = (u - γ) * dslope (sFun E α) (γ : ℂ) u := fun u ↦ by
    have := sub_smul_dslope (sFun E α) (γ : ℂ) u
    rw [smul_eq_mul, sFun_level D hγ, sub_zero] at this
    exact this.symm
  rw [hS z, hS w]
  unfold rTerm
  simp only [map_mul, map_div₀, map_add, map_one, map_pow, map_sub, Complex.conj_ofReal]
  have h2 : (1 + (γ : ℂ) ^ 2) ≠ 0 := by norm_cast; positivity
  field_simp
  ring

/-- **Mittag-Leffler identity**: `Q(w,z) π (z - w̄) = S(z) conj S(w) (h(z) - conj h(w))`. -/
theorem defectKer_mul (D : DBData E φ) {h : ℂ → ℂ}
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) (w z : ℂ) :
    defectKer E φ α w z * (Real.pi * (z - conj w)) =
      sFun E α z * conj (sFun E α w) * (h z - conj (h w)) := by
  have hsum : (z - conj w) * ∑' γ : phaseLevel φ α,
      deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * ((wt E γ : ℝ) : ℂ) =
      sFun E α z * conj (rFun E φ α w) - conj (sFun E α w) * rFun E φ α z := by
    rw [← tsum_mul_left, tsum_congr (fun γ : phaseLevel φ α ↦ term_identity D γ.2 w z),
      Summable.tsum_sub ((Complex.summable_conj.mpr (summable_rTerm D α w)).mul_left _)
        ((summable_rTerm D α z).mul_left _), tsum_mul_left, tsum_mul_left, ← Complex.conj_tsum]
    rfl
  have hD : ∀ u, dFun E φ α u = cFun E α u + Real.pi * rFun E φ α u := fun u ↦ rfl
  have hK := kernel_mul_CS E α w z
  unfold defectKer
  calc (deBrangesKernel E w z - ∑' γ : phaseLevel φ α,
        deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * ((wt E γ : ℝ) : ℂ)) *
        (Real.pi * (z - conj w))
      = deBrangesKernel E w z * (Real.pi * (z - conj w)) - Real.pi * ((z - conj w) *
          ∑' γ : phaseLevel φ α,
            deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * ((wt E γ : ℝ) : ℂ)) := by
        ring
    _ = (cFun E α z * conj (sFun E α w) - sFun E α z * conj (cFun E α w)) -
          Real.pi * (sFun E α z * conj (rFun E φ α w) - conj (sFun E α w) * rFun E φ α z) := by
        rw [hK, hsum]
    _ = conj (sFun E α w) * dFun E φ α z - sFun E α z * conj (dFun E φ α w) := by
        rw [hD, hD, map_add, map_mul, Complex.conj_ofReal]
        ring
    _ = sFun E α z * conj (sFun E α w) * (h z - conj (h w)) := by
        rw [hh z, hh w, map_mul]
        ring

/-- `Q(w, w) = K(w,w) - Σ_γ wt(γ) |K(w,γ)|²` (no hypothesis on `E`: the `tsum` of the real
numbers `wt |K(w,γ)|²` is cast termwise by `Complex.ofReal_tsum`). -/
theorem defectKer_diag (w : ℂ) :
    (defectKer E φ α w w).re =
      (deBrangesKernel E w w).re - ∑' γ : phaseLevel φ α,
        wt E γ * ‖deBrangesKernel E w γ‖ ^ 2 := by
  unfold defectKer
  have hterm : ∀ γ : phaseLevel φ α,
      deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) w * ((wt E γ : ℝ) : ℂ) =
        ((wt E γ * ‖deBrangesKernel E w γ‖ ^ 2 : ℝ) : ℂ) := by
    intro γ
    rw [← deBrangesKernel_conj_symm E w (γ : ℂ), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [tsum_congr hterm, ← Complex.ofReal_tsum, Complex.sub_re, Complex.ofReal_re]

/-- `Q(w, w) ≥ 0` (Bessel for `f = K_w`). -/
theorem defectKer_diag_nonneg (D : DBData E φ) (w : ℂ) : 0 ≤ (defectKer E φ α w w).re := by
  rw [defectKer_diag w]
  have hb := (bessel (α := α) D (memHE_deBrangesKernel D.strict.1 D.noZero w)).2
  rw [heNormSq_kernel D.strict.1 D.noZero] at hb
  linarith

/-- `Im h(w) ≥ 0` on `ℂ₊`: `Q(w,w) = |S(w)|² Im h(w) / (π Im w)`. -/
theorem im_hFun_nonneg (D : DBData E φ) {h : ℂ → ℂ}
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) {w : ℂ} (hw : 0 < w.im) : 0 ≤ (h w).im := by
  have h1 := defectKer_mul D hh w w
  rw [Complex.sub_conj w, Complex.sub_conj (h w), Complex.mul_conj] at h1
  have h2 := congrArg Complex.im h1
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im] at h2
  have hQ := defectKer_diag_nonneg (α := α) D w
  have hS : 0 < Complex.normSq (sFun E α w) :=
    Complex.normSq_pos.mpr (sFun_ne_zero D hw.ne')
  have hπ := Real.pi_pos
  have h3 : 0 ≤ (defectKer E φ α w w).re * (Real.pi * (2 * w.im)) := by positivity
  nlinarith

end FF
