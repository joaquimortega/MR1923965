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
    MemHE E (partialSum E φ α a F) := by
  sorry

/-- Pythagoras: `‖s_F‖² = Σ_{γ ∈ F} wt(γ) |a_γ|²`. -/
theorem heNormSq_partialSum (D : DBData E φ) (a : ℝ → ℂ) (F : Finset (phaseLevel φ α)) :
    (heNormSq E (partialSum E φ α a F)).toReal = ∑ γ ∈ F, wt E γ * ‖a γ‖ ^ 2 := by
  sorry

/-- `⟨f, s_F⟩ = Σ_{γ ∈ F} conj(a_γ) wt(γ) f(γ)`. -/
theorem heInner_partialSum (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f) (a : ℝ → ℂ)
    (F : Finset (phaseLevel φ α)) :
    heInner E f (partialSum E φ α a F) = ∑ γ ∈ F, conj (a γ) * (wt E γ : ℂ) * f γ := by
  sorry

/-- `s_F(γ) = a(γ)` for `γ ∈ F` (orthogonality and `K(γ,γ) wt(γ) = 1`). -/
theorem partialSum_level (D : DBData E φ) (a : ℝ → ℂ) {F : Finset (phaseLevel φ α)}
    {γ : phaseLevel φ α} (hγ : γ ∈ F) : partialSum E φ α a F γ = a γ := by
  sorry

/-- Finite Bessel inequality: `Σ_{γ ∈ F} wt(γ) |f(γ)|² ≤ ‖f‖²_E`
(`0 ≤ ‖f - s_F‖²` with `a = f|_Γ`). -/
theorem bessel_finite (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f)
    (F : Finset (phaseLevel φ α)) :
    ∑ γ ∈ F, wt E γ * ‖f γ‖ ^ 2 ≤ (heNormSq E f).toReal := by
  sorry

/-- Bessel's inequality: `Σ_γ wt(γ) |f(γ)|²` converges and is `≤ ‖f‖²_E`. -/
theorem bessel (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f) :
    Summable (fun γ : phaseLevel φ α ↦ wt E γ * ‖f γ‖ ^ 2) ∧
      ∑' γ : phaseLevel φ α, wt E γ * ‖f γ‖ ^ 2 ≤ (heNormSq E f).toReal := by
  sorry

/-- Bessel for `f = K_z`, rewritten with `wt_mul_norm_kernel_level_sq`:
`Σ_γ c_γ |dslope S γ z|² ≤ K(z, z)` for every `z ∈ ℂ`. -/
theorem summable_cLev_dslope_sq (D : DBData E φ) (z : ℂ) :
    Summable (fun γ : phaseLevel φ α ↦ cLev E γ * ‖dslope (sFun E α) (γ : ℂ) z‖ ^ 2) ∧
      ∑' γ : phaseLevel φ α, cLev E γ * ‖dslope (sFun E α) (γ : ℂ) z‖ ^ 2 ≤
        (deBrangesKernel E z z).re := by
  sorry

/-- For nonreal `w`: `Σ_γ c_γ / |w - γ|² < ∞` (`dslope S γ w = S(w)/(w - γ)`, `S(w) ≠ 0`). -/
theorem summable_cLev_div (D : DBData E φ) {w : ℂ} (hw : w.im ≠ 0) :
    Summable (fun γ : phaseLevel φ α ↦ cLev E γ / ‖w - (γ : ℂ)‖ ^ 2) := by
  sorry

/-- `Σ_γ c_γ / (1 + γ²) < ∞` (`w = i`). -/
theorem summable_cLev_div_one_add_sq (D : DBData E φ) :
    Summable (fun γ : phaseLevel φ α ↦ cLev E γ / (1 + (γ : ℝ) ^ 2)) := by
  sorry

/-! ## 5.4 The entire function `D` and the quotient `h = D/S` -/

/-- M-test bound: for `‖z‖ ≤ ρ` and `|γ| ≥ 2ρ + 1`,
`‖rTerm γ z‖ ≤ 2 M (1 + ρ) c_γ / (1 + γ²)` where `‖S‖ ≤ M` on `‖z‖ ≤ ρ`. -/
theorem norm_rTerm_le (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) {ρ M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖sFun E α z‖ ≤ M) (hγρ : 2 * ρ + 1 ≤ |γ|) {z : ℂ} (hz : ‖z‖ ≤ ρ) :
    ‖rTerm E α γ z‖ ≤ 2 * M * (1 + ρ) * (cLev E γ / (1 + γ ^ 2)) := by
  sorry

theorem summable_rTerm (D : DBData E φ) (α : ℝ) (z : ℂ) :
    Summable fun γ : phaseLevel φ α ↦ rTerm E α γ z := by
  sorry

/-- Each term of the series for `R` is entire and the series converges locally uniformly
(`differentiableOn_tsum_of_summable_norm` on balls, with `norm_rTerm_le` and finitely many
exceptional `γ`); hence `R` and `D` are entire. -/
theorem differentiable_rFun (D : DBData E φ) (α : ℝ) : Differentiable ℂ (rFun E φ α) := by
  sorry

theorem differentiable_dFun (D : DBData E φ) (α : ℝ) : Differentiable ℂ (dFun E φ α) := by
  sorry

theorem fstar_dFun (D : DBData E φ) (α : ℝ) : fstar (dFun E φ α) = dFun E φ α := by
  sorry

/-- `D(γ) = C(γ) + π c_γ S'(γ) = 0` for `γ ∈ Γ`. -/
theorem dFun_level (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    dFun E φ α γ = 0 := by
  sorry

/-- **`h = D/S` is entire**, real on `ℝ` (removable singularities at the simple zeros of `S`). -/
theorem exists_hFun (D : DBData E φ) (α : ℝ) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∀ z, dFun E φ α z = h z * sFun E α z) ∧
      ∀ z, h (conj z) = conj (h z) := by
  sorry

/-! ## 5.5 The defect kernel -/

/-- Termwise: `K(w,γ) K(γ,z) wt(γ) = c_γ conj(dslope S γ w) dslope S γ z`. -/
theorem defect_term_eq (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (w z : ℂ) :
    deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * (wt E γ : ℂ) =
      (cLev E γ : ℂ) * conj (dslope (sFun E α) (γ : ℂ) w) * dslope (sFun E α) (γ : ℂ) z := by
  sorry

/-- Summability of the defect series (AM–GM and `summable_cLev_dslope_sq`). -/
theorem summable_defect (D : DBData E φ) (w z : ℂ) :
    Summable (fun γ : phaseLevel φ α ↦
      deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * ((wt E γ : ℝ) : ℂ)) := by
  sorry

/-- Termwise identity: for `γ ∈ Γ`,
`(z - w̄) K(w,γ) K(γ,z) wt(γ) = S(z) conj (r_γ(w)) - conj S(w) r_γ(z)`
(by `defect_term_eq`, `S(z) = (z - γ) dslope S γ z` and
`(z-γ)(1+γw̄) - (w̄-γ)(1+γz) = (z - w̄)(1+γ²)`). -/
theorem term_identity (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (w z : ℂ) :
    (z - conj w) * (deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * (wt E γ : ℂ)) =
      sFun E α z * conj (rTerm E α γ w) - conj (sFun E α w) * rTerm E α γ z := by
  sorry

/-- **Mittag-Leffler identity**: `Q(w,z) π (z - w̄) = S(z) conj S(w) (h(z) - conj h(w))`. -/
theorem defectKer_mul (D : DBData E φ) {h : ℂ → ℂ}
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) (w z : ℂ) :
    defectKer E φ α w z * (Real.pi * (z - conj w)) =
      sFun E α z * conj (sFun E α w) * (h z - conj (h w)) := by
  sorry

/-- `Q(w, w) = K(w,w) - Σ_γ wt(γ) |K(w,γ)|²`. -/
theorem defectKer_diag (D : DBData E φ) (w : ℂ) :
    (defectKer E φ α w w).re =
      (deBrangesKernel E w w).re - ∑' γ : phaseLevel φ α,
        wt E γ * ‖deBrangesKernel E w γ‖ ^ 2 := by
  sorry

/-- `Q(w, w) ≥ 0` (Bessel for `f = K_w`). -/
theorem defectKer_diag_nonneg (D : DBData E φ) (w : ℂ) : 0 ≤ (defectKer E φ α w w).re := by
  sorry

/-- `Im h(w) ≥ 0` on `ℂ₊`: `Q(w,w) = |S(w)|² Im h(w) / (π Im w)`. -/
theorem im_hFun_nonneg (D : DBData E φ) {h : ℂ → ℂ}
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) {w : ℂ} (hw : 0 < w.im) : 0 ≤ (h w).im := by
  sorry

end FF
