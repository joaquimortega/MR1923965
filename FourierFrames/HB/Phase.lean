import FourierFrames.HB.Basic

/-!
# M02 — Phase functions of `E ∈ \overline{HB}`

See `blueprint/M02_HB.md`, §4–§5.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Existence, uniqueness and derivative of phase functions -/

/-- A continuous real function with integer values is constant. -/
theorem eq_of_continuous_int_valued {g : ℝ → ℝ} (hg : Continuous g) (hint : ∀ x, ∃ k : ℤ, g x = k)
    (x : ℝ) : g x = g 0 := by
  by_contra hne
  obtain ⟨a, ha⟩ := hint x
  obtain ⟨b, hb⟩ := hint 0
  have hpre : IsPreconnected (Set.range g) := isPreconnected_range hg
  have key : ∀ {u v : ℝ}, u ∈ Set.range g → v ∈ Set.range g → u < v → ∀ w, u ≤ w → w ≤ v → w ∈ Set.range g :=
    fun hu hv _ w h1 h2 ↦ hpre.Icc_subset hu hv ⟨h1, h2⟩
  have hab : a ≠ b := fun h ↦ hne (by rw [ha, hb, h])
  have hmem : ∀ c : ℤ, ((c : ℝ) + 1 / 2) ∈ Set.range g → False := by
    intro c ⟨y, hy⟩
    obtain ⟨m, hm⟩ := hint y
    rw [hm] at hy
    have h1 : (m : ℝ) - c = 1 / 2 := by linarith
    have h2 : ((m - c : ℤ) : ℝ) = 1 / 2 := by push_cast; exact h1
    have h3 : (m - c : ℤ) * 2 = 1 := by
      have : ((m - c : ℤ) : ℝ) * 2 = 1 := by rw [h2]; norm_num
      exact_mod_cast this
    omega
  have hxr : g x ∈ Set.range g := ⟨x, rfl⟩
  have h0r : g 0 ∈ Set.range g := ⟨0, rfl⟩
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have hlt' : (a : ℝ) + 1 ≤ b := by exact_mod_cast hlt
    exact hmem a (key hxr h0r (by rw [ha, hb]; linarith) _ (by rw [ha]; linarith)
      (by rw [hb]; linarith))
  · have hlt' : (b : ℝ) + 1 ≤ a := by exact_mod_cast hlt
    exact hmem b (key h0r hxr (by rw [ha, hb]; linarith) _ (by rw [hb]; linarith)
      (by rw [ha]; linarith))


theorem continuous_phaseDeriv {E : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0) :
    Continuous (phaseDeriv E) := by
  unfold phaseDeriv
  have h1 : Continuous fun x : ℝ ↦ deriv E (x : ℂ) :=
    (hE.contDiff.continuous_deriv le_rfl).comp Complex.continuous_ofReal
  have h2 : Continuous fun x : ℝ ↦ E (x : ℂ) := hE.continuous.comp Complex.continuous_ofReal
  exact (Complex.continuous_im.comp (h1.div h2 h0)).neg

/-- `phaseDeriv` is multiplicative-to-additive: `φ_{EF}' = φ_E' + φ_F'`. -/
theorem phaseDeriv_mul {E F : ℂ → ℂ} (hE : Differentiable ℂ E) (hF : Differentiable ℂ F)
    {x : ℝ} (hEx : E x ≠ 0) (hFx : F x ≠ 0) :
    phaseDeriv (fun z ↦ E z * F z) x = phaseDeriv E x + phaseDeriv F x := by
  unfold phaseDeriv
  rw [deriv_fun_mul (hE _) (hF _)]
  show -((deriv E (x : ℂ) * F x + E x * deriv F (x : ℂ)) / (E x * F x)).im = _
  have : (deriv E (x : ℂ) * F x + E x * deriv F (x : ℂ)) / (E x * F x) =
      deriv E (x : ℂ) / E x + deriv F (x : ℂ) / F x := by
    field_simp
  rw [this, Complex.add_im]; ring

/-- **Existence of a phase function** with `φ' = phaseDeriv E`. -/
theorem exists_isPhaseFunction {E : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0) :
    ∃ φ : ℝ → ℝ, IsPhaseFunction E φ ∧ ∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x := by
  set ρ : ℝ → ℝ := phaseDeriv E with hρ
  have hρc : Continuous ρ := continuous_phaseDeriv hE h0
  set r : ℝ → ℝ := fun x ↦ (deriv E (x : ℂ) / E x).re with hr
  have hrc : Continuous r := by
    have h1 : Continuous fun x : ℝ ↦ deriv E (x : ℂ) :=
      (hE.contDiff.continuous_deriv le_rfl).comp Complex.continuous_ofReal
    have h2 : Continuous fun x : ℝ ↦ E (x : ℂ) := hE.continuous.comp Complex.continuous_ofReal
    exact Complex.continuous_re.comp (h1.div h2 h0)
  set φ₀ : ℝ := -Complex.arg (E 0) with hφ₀
  set Φ : ℝ → ℝ := fun x ↦ φ₀ + ∫ t in (0:ℝ)..x, ρ t with hΦ
  set R : ℝ → ℝ := fun x ↦ ∫ t in (0:ℝ)..x, r t with hR
  have hΦd : ∀ x, HasDerivAt Φ (ρ x) x := fun x ↦
    ((hρc.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add φ₀
  have hRd : ∀ x, HasDerivAt R (r x) x := fun x ↦ (hrc.integral_hasStrictDerivAt 0 x).hasDerivAt
  refine ⟨Φ, ⟨(continuous_iff_continuousAt.mpr fun x ↦ (hΦd x).continuousAt), ?_⟩, hΦd⟩
  -- the function `M(x) = E(x) exp(iΦ(x) - R(x))` is constant
  set M : ℝ → ℂ := fun x ↦ E (x : ℂ) * Complex.exp (I * Φ x - R x) with hM
  have hMd : ∀ x, HasDerivAt M 0 x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ ↦ E (y : ℂ)) (deriv E (x : ℂ)) x :=
      (hE.differentiableAt.hasDerivAt).comp_ofReal
    have h2 : HasDerivAt (fun y : ℝ ↦ I * (Φ y : ℂ) - (R y : ℂ)) (I * (ρ x : ℂ) - (r x : ℂ)) x :=
      (((hΦd x).ofReal_comp).const_mul I).sub (hRd x).ofReal_comp
    have h3 := h1.mul h2.cexp
    refine h3.congr_deriv ?_
    have hρx : (ρ x : ℂ) = -((deriv E (x : ℂ) / E x).im : ℂ) := by
      simp [hρ, phaseDeriv]
    have hrx : (r x : ℂ) = ((deriv E (x : ℂ) / E x).re : ℂ) := rfl
    have hq : deriv E (x : ℂ) = (deriv E (x : ℂ) / E x) * E x := by
      field_simp [h0 x]
    rw [hρx, hrx]
    set q := deriv E (x : ℂ) / E x with hq'
    have hqq : q = (q.re : ℂ) + (q.im : ℂ) * I := (Complex.re_add_im q).symm
    rw [hq]
    nth_rewrite 1 [hqq]
    ring
  have hMc : ∀ x, M x = M 0 := fun x ↦
    is_const_of_deriv_eq_zero (fun y ↦ (hMd y).differentiableAt) (fun y ↦ (hMd y).deriv) x 0
  have hM0 : M 0 = ‖E 0‖ := by
    have hΦ0 : Φ 0 = φ₀ := by simp [hΦ]
    have hR0 : R 0 = 0 := by simp [hR]
    have : E ((0:ℝ) : ℂ) = ‖E 0‖ * Complex.exp (Complex.arg (E 0) * I) := by
      have := Complex.norm_mul_exp_arg_mul_I (E 0)
      simp at this ⊢
    simp only [hM, hΦ0, hR0]
    rw [this, mul_assoc, ← Complex.exp_add]
    have : (Complex.arg (E 0) : ℂ) * I + (I * (φ₀ : ℂ) - ((0:ℝ) : ℂ)) = 0 := by
      simp [hφ₀]; ring
    rw [this]; simp
  intro x
  have h1 : E x = ‖E 0‖ * Complex.exp (R x - I * Φ x) := by
    have := hMc x
    rw [hM0] at this
    simp only [hM] at this
    have hne : Complex.exp (I * Φ x - R x) ≠ 0 := Complex.exp_ne_zero _
    have : E x = ‖E 0‖ / Complex.exp (I * Φ x - R x) := by
      rw [eq_div_iff hne]; exact this
    rw [this, div_eq_mul_inv, ← Complex.exp_neg]
    congr 2; ring
  have h2 : ‖E x‖ = ‖E 0‖ * Real.exp (R x) := by
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    congr 1
    rw [Complex.norm_exp]
    simp
  have h3 : E x = ‖E x‖ * Complex.exp (-(I * Φ x)) := by
    rw [h2, h1]
    push_cast
    rw [sub_eq_add_neg, Complex.exp_add]
    ring
  exact h3

/-- **Uniqueness up to `2π ℤ`.** -/
theorem IsPhaseFunction.exists_int_eq_add {E : ℂ → ℂ} (h0 : ∀ x : ℝ, E x ≠ 0) {φ ψ : ℝ → ℝ}
    (hφ : IsPhaseFunction E φ) (hψ : IsPhaseFunction E ψ) :
    ∃ k : ℤ, ∀ x : ℝ, ψ x = φ x + 2 * Real.pi * k := by
  have hk : ∀ x : ℝ, ∃ k : ℤ, ψ x = φ x + 2 * Real.pi * k := by
    intro x
    have hn : (‖E x‖ : ℂ) ≠ 0 := by simpa using h0 x
    have h1 := hφ.2 x
    have h2 := hψ.2 x
    have h3 : Complex.exp (-(I * φ x)) = Complex.exp (-(I * ψ x)) :=
      mul_left_cancel₀ hn (h1.symm.trans h2)
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h3
    refine ⟨k, ?_⟩
    have : ((ψ x : ℂ)) = φ x + 2 * Real.pi * k := by
      have h4 : (I * ((ψ x : ℂ) - φ x - 2 * Real.pi * k)) = 0 := by
        linear_combination hk
      have := (mul_eq_zero.mp h4).resolve_left I_ne_zero
      linear_combination this
    exact_mod_cast this
  have hcont : Continuous fun x ↦ (ψ x - φ x) / (2 * Real.pi) :=
    (hψ.1.sub hφ.1).div_const _
  have hint : ∀ x, ∃ k : ℤ, (ψ x - φ x) / (2 * Real.pi) = k := by
    intro x
    obtain ⟨k, hk⟩ := hk x
    refine ⟨k, ?_⟩
    rw [hk]; field_simp; ring
  have hconst := FF.eq_of_continuous_int_valued hcont hint
  obtain ⟨k, hk0⟩ := hint 0
  refine ⟨k, fun x ↦ ?_⟩
  have := hconst x
  rw [hk0] at this
  field_simp at this
  linarith

/-- Every phase function of `E` (without real zeros) is differentiable with derivative
`phaseDeriv E`. -/
theorem IsPhaseFunction.hasDerivAt {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (h0 : ∀ x : ℝ, E x ≠ 0) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) (x : ℝ) :
    HasDerivAt φ (phaseDeriv E x) x := by
  obtain ⟨Φ, hΦ, hΦd⟩ := exists_isPhaseFunction hE h0
  obtain ⟨k, hk⟩ := hφ.exists_int_eq_add h0 hΦ
  have : φ = fun y ↦ Φ y + (-(2 * Real.pi * k)) := by
    funext y; rw [hk y]; ring
  rw [this]
  exact (hΦd x).add_const _

/-- Phase functions add under products. -/
theorem IsPhaseFunction.mul {E F : ℂ → ℂ} {φ ψ : ℝ → ℝ} (hφ : IsPhaseFunction E φ)
    (hψ : IsPhaseFunction F ψ) :
    IsPhaseFunction (fun z ↦ E z * F z) (fun x ↦ φ x + ψ x) := by
  refine ⟨hφ.1.add hψ.1, fun x ↦ ?_⟩
  have h1 := hφ.2 x
  have h2 := hψ.2 x
  show E x * F x = _
  rw [norm_mul]
  nth_rewrite 1 [h1, h2]
  push_cast
  rw [mul_add, neg_add, Complex.exp_add]
  ring

/-- `Re E(x) = |E(x)| cos φ(x)` on the real axis. -/
theorem IsPhaseFunction.re_eq {E : ℂ → ℂ} {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) (x : ℝ) :
    (E x).re = ‖E x‖ * Real.cos (φ x) := by
  have h1 := hφ.2 x
  have : (E x).re = ((‖E x‖ : ℂ) * Complex.exp (-(I * φ x))).re := by rw [← h1]
  rw [this, Complex.re_ofReal_mul]
  have : -(I * (φ x : ℂ)) = ((-φ x : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-! ## Sign of the phase derivative -/

/-- **`φ_F' ≥ 0`** for `F ∈ \overline{HB}` (the non-strict class) at real points where `F ≠ 0`. -/
theorem IsHB.phaseDeriv_nonneg {F : ℂ → ℂ} (hF : IsHB F) {x : ℝ} (hx : F x ≠ 0) :
    0 ≤ phaseDeriv F x := by
  sorry

/-- **`φ_E' > 0`** if `E ∈ \overline{HB}` is strict at a single point of `Im z > 0`
(i.e. `E^*/E` is not constant). -/
theorem IsHB.phaseDeriv_pos_of_exists_lt {E : ℂ → ℂ} (hE : IsHB E) {x : ℝ} (hx : E x ≠ 0)
    (h : ∃ z : ℂ, 0 < z.im ∧ ‖E (conj z)‖ < ‖E z‖) : 0 < phaseDeriv E x := by
  sorry

theorem IsStrictHB.phaseDeriv_pos {E : ℂ → ℂ} (hE : IsStrictHB E) {x : ℝ} (hx : E x ≠ 0) :
    0 < phaseDeriv E x := by
  refine hE.1.phaseDeriv_pos_of_exists_lt hx ⟨I, by simp, ?_⟩
  simpa using hE.2 I (by simp)

/-- A phase function of a strict `E` without real zeros is strictly increasing. -/
theorem IsPhaseFunction.strictMono_of_isStrictHB {E : ℂ → ℂ} (hE : IsStrictHB E)
    (h0 : ∀ x : ℝ, E x ≠ 0) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) : StrictMono φ := by
  refine strictMono_of_deriv_pos fun x ↦ ?_
  rw [(hφ.hasDerivAt hE.1.1 h0 x).deriv]
  exact hE.phaseDeriv_pos (h0 x)

/-! ## Zeros of `EF + E^*F^*` -/

/-- **Zero set of `EF + E^*F^*`** (p. 796): for `E` strict and `F ∈ \overline{HB}`, both without
real zeros, the zeros of `EF + E^*F^*` are exactly the real points where the total phase
`φ_E + φ_F` is `≡ π/2 (mod π)`. -/
theorem zero_set_eq_phaseLevel {E F : ℂ → ℂ} (hE : IsStrictHB E) (hF : IsHB F)
    (hE0 : ∀ x : ℝ, E x ≠ 0) (hF0 : ∀ x : ℝ, F x ≠ 0) {φE φF : ℝ → ℝ}
    (hφE : IsPhaseFunction E φE) (hφF : IsPhaseFunction F φF) (z : ℂ) :
    E z * F z + fstar E z * fstar F z = 0 ↔
      z ∈ Complex.ofReal '' phaseLevel (fun t ↦ φE t + φF t) (Real.pi / 2) := by
  -- norm comparison on the upper half-plane
  have hup : ∀ w : ℂ, 0 < w.im →
      ‖fstar E w * fstar F w‖ < ‖E w * F w‖ := by
    intro w hw
    rw [norm_mul, norm_mul, norm_fstar, norm_fstar]
    have h1 := hE.2 w hw
    have h2 := hF.2.2 w hw
    have h3 : 0 < ‖F w‖ := norm_pos_iff.mpr (hF.2.1 w hw)
    calc ‖E (conj w)‖ * ‖F (conj w)‖ ≤ ‖E (conj w)‖ * ‖F w‖ :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ < ‖E w‖ * ‖F w‖ := mul_lt_mul_of_pos_right h1 h3
  have hne_of_lt : ∀ {a b : ℂ}, ‖a‖ < ‖b‖ → b + a ≠ 0 := by
    intro a b hab h
    have : a = -b := by linear_combination h
    rw [this, norm_neg] at hab
    exact lt_irrefl _ hab
  have hreal : ∀ x : ℝ, E x * F x + fstar E x * fstar F x = (2 * ((E x * F x).re : ℝ) : ℝ) := by
    intro x
    rw [fstar_ofReal, fstar_ofReal]
    have := Complex.add_conj (E x * F x)
    rw [map_mul] at this
    rw [this]
    push_cast
  have hφ := hφE.mul hφF
  constructor
  · intro hz
    have him : z.im = 0 := by
      rcases lt_trichotomy z.im 0 with h | h | h
      · exfalso
        have hw : 0 < (conj z).im := by simp [h]
        have := hup (conj z) hw
        have e1 : fstar E (conj z) * fstar F (conj z) = conj (E z * F z) := by simp [fstar]
        have e2 : E (conj z) * F (conj z) = conj (fstar E z * fstar F z) := by simp [fstar]
        rw [e1, e2, Complex.norm_conj, Complex.norm_conj] at this
        exact (hne_of_lt this) (by rw [add_comm]; exact hz)
      · exact h
      · exact absurd hz (hne_of_lt (hup z h))
    have hzr : z = ((z.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hzr] at hz ⊢
    set x := z.re
    refine ⟨x, ?_, rfl⟩
    rw [hreal] at hz
    have hre : (E x * F x).re = 0 := by
      have := Complex.ofReal_eq_zero.mp hz
      linarith
    have hfn : ‖E x * F x‖ ≠ 0 := norm_ne_zero_iff.mpr (mul_ne_zero (hE0 x) (hF0 x))
    have hcos : Real.cos (φE x + φF x) = 0 := by
      have := hφ.re_eq x
      rw [hre] at this
      have h2 : ‖E x * F x‖ * Real.cos (φE x + φF x) = 0 := this.symm
      exact (mul_eq_zero.mp h2).resolve_left hfn
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hcos
    refine ⟨k, ?_⟩
    simp only
    rw [hk]; ring
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    rw [hreal]
    have hcos : Real.cos (φE x + φF x) = 0 := by
      apply Real.cos_eq_zero_iff.mpr
      exact ⟨k, by simp only at hk; rw [hk]; ring⟩
    have := hφ.re_eq x
    have hre : (E x * F x).re = 0 := by rw [this, hcos, mul_zero]
    rw [hre]; simp

/-- Added at assembly (moved from `Corollary1.lean` / `Corollary2.lean`): a phase function of
`e^{iθ} E` is `φ_E - θ`. -/
theorem IsPhaseFunction.rotate {E : ℂ → ℂ} {φ : ℝ → ℝ} (h : IsPhaseFunction E φ) (θ : ℝ) :
    IsPhaseFunction (fun z ↦ Complex.exp (I * θ) * E z) (fun x ↦ φ x - θ) := by
  refine ⟨h.1.sub continuous_const, fun x ↦ ?_⟩
  have h1 := h.2 x
  show Complex.exp (I * θ) * E x = _
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  nth_rewrite 1 [h1]
  rw [← mul_assoc, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
  push_cast
  congr 2; ring

end FF
