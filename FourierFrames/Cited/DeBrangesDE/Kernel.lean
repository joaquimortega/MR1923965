import FourierFrames.Cited.DeBrangesDE.Cauchy
import FourierFrames.HB.Phase

/-!
# P3 — Theorem D: the reproducing kernel of `H(E)`

See `blueprint/P3_DeBrangesDE.md`, §2–§3.

* §2.1 algebra of the kernel (`dslope` form, Hermitian symmetry, `K_w^* = K_{w̄}`, diagonal values,
  local bound), valid for every entire `E`;
* §2.2 `K(w, ·) ∈ H(E)` for `E ∈ \overline{HB}` and `w` nonreal or `E(w) ≠ 0` (decay criterion
  for `H²` and `|Θ| ≤ 1`);
* §2.3 the reproducing formula `⟨f, K_w⟩_E = f(w)`: for nonreal `w` by the Cauchy formulas of
  `Cauchy.lean` applied to `f/E` and `f^*/E`; for real `w` by the regularized Cauchy formula
  `IsH2Cont.cauchy_real` (no limiting argument).

Strictness of `E` is not needed in this file: Theorem D holds for `E ∈ \overline{HB}` without real
zeros.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- The inner product integral `∫_ℝ f conj g / |E|²` (meaningful for `f, g ∈ H(E)`). -/
def heInner (E f g : ℂ → ℂ) : ℂ :=
  ∫ t : ℝ, f t * conj (g t) / ((‖E t‖ ^ 2 : ℝ) : ℂ)

/-- The numerator `E(z) conj E(w) - E^*(z) conj E^*(w)` of the kernel. -/
def kernelNum (E : ℂ → ℂ) (w z : ℂ) : ℂ :=
  E z * conj (E w) - fstar E z * conj (fstar E w)

/-- `heInner` in the form `∫ (f/E) conj (g/E)` used by P4 (valid for every `E`, also at real
zeros of `E`, where both integrands are `0`). -/
theorem heInner_eq_integral_div (E f g : ℂ → ℂ) :
    heInner E f g = ∫ t : ℝ, f t / E t * conj (g t / E t) := by
  unfold heInner
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  simp only
  by_cases h : E t = 0
  · simp [h]
  · have hc : conj (E t) ≠ 0 := (map_ne_zero _).mpr h
    have : ((‖E t‖ ^ 2 : ℝ) : ℂ) = E t * conj (E t) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this, map_div₀]
    field_simp

/-! ## 2.1 Algebra of the kernel -/

theorem kernelNum_conj_self (E : ℂ → ℂ) (w : ℂ) : kernelNum E w (conj w) = 0 := by
  simp only [kernelNum, fstar, Complex.conj_conj]
  ring

/-- Off the diagonal, `K(w, z) = (i/2) kernelNum / (π (z - w̄))` (unfolding the `if`). -/
theorem deBrangesKernel_of_ne (E : ℂ → ℂ) {w z : ℂ} (hz : z ≠ conj w) :
    deBrangesKernel E w z = (I / 2) * kernelNum E w z / (Real.pi * (z - conj w)) := by
  unfold deBrangesKernel kernelNum
  rw [ite_eq_right hz]

/-- `K(w, ·) = (i/2π) · dslope (kernelNum E w) w̄`. -/
theorem deBrangesKernel_eq_dslope {E : ℂ → ℂ} (hE : Differentiable ℂ E) (w : ℂ) :
    deBrangesKernel E w = fun z ↦ (I / (2 * Real.pi)) * dslope (kernelNum E w) (conj w) z := by
  funext z
  by_cases hz : z = conj w
  · subst hz
    rw [dslope_same]
    unfold deBrangesKernel
    rw [ite_eq_left rfl]
    congr 1
    have hd1 : DifferentiableAt ℂ (fun z ↦ E z * conj (E w)) (conj w) := (hE _).mul_const _
    have hd2 : DifferentiableAt ℂ (fun z ↦ fstar E z * conj (fstar E w)) (conj w) :=
      ((Differentiable.fstar hE) _).mul_const _
    show _ = deriv (fun z ↦ E z * conj (E w) - fstar E z * conj (fstar E w)) (conj w)
    rw [deriv_fun_sub hd1 hd2, deriv_mul_const (hE _), deriv_mul_const ((Differentiable.fstar hE) _)]
  · rw [dslope_of_ne _ hz, slope_def_field, kernelNum_conj_self, sub_zero,
      deBrangesKernel_of_ne E hz]
    have : z - conj w ≠ 0 := sub_ne_zero.mpr hz
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp

theorem differentiable_deBrangesKernel {E : ℂ → ℂ} (hE : Differentiable ℂ E) (w : ℂ) :
    Differentiable ℂ (deBrangesKernel E w) := by
  rw [deBrangesKernel_eq_dslope hE w]
  have hN : Differentiable ℂ (kernelNum E w) := fun z ↦
    ((hE z).mul_const _).sub (((Differentiable.fstar hE) z).mul_const _)
  have hD : Differentiable ℂ (dslope (kernelNum E w) (conj w)) :=
    differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope Filter.univ_mem).2 hN.differentiableOn)
  exact fun z ↦ (differentiableAt_const _).mul (hD z)

/-- Multiplied form of the kernel: `K(w,z) · π (z - w̄) = (i/2) · kernelNum`, valid for all `z`. -/
theorem deBrangesKernel_mul (E : ℂ → ℂ) (w z : ℂ) :
    deBrangesKernel E w z * (Real.pi * (z - conj w)) = (I / 2) * kernelNum E w z := by
  by_cases hz : z = conj w
  · subst hz
    simp [kernelNum_conj_self]
  · rw [deBrangesKernel_of_ne E hz]
    have : z - conj w ≠ 0 := sub_ne_zero.mpr hz
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp

/-- Hermitian symmetry `conj K(w, z) = K(z, w)`. -/
theorem conj_deBrangesKernel (E : ℂ → ℂ) (w z : ℂ) :
    conj (deBrangesKernel E w z) = deBrangesKernel E z w := by
  by_cases hz : z = conj w
  · have hw : w = conj z := by rw [hz, Complex.conj_conj]
    unfold deBrangesKernel
    rw [ite_eq_left hz, ite_eq_left hw]
    subst hz
    simp only [deriv_fstar, fstar, Complex.conj_conj, map_mul, map_sub, map_div₀, Complex.conj_I,
      Complex.conj_ofReal, map_ofNat]
    ring
  · have hw : w ≠ conj z := fun h ↦ hz (by rw [h, Complex.conj_conj])
    rw [deBrangesKernel_of_ne E hz, deBrangesKernel_of_ne E hw]
    simp only [kernelNum, fstar, map_mul, map_sub, map_div₀, Complex.conj_conj, Complex.conj_I,
      Complex.conj_ofReal, map_ofNat]
    have h1 : conj z - w ≠ 0 := sub_ne_zero.mpr (fun h ↦ hw (by rw [← h]))
    have h2 : w - conj z ≠ 0 := sub_ne_zero.mpr hw
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring

/-- `K(w, ·)^* = K(w̄, ·)`. -/
theorem fstar_deBrangesKernel (E : ℂ → ℂ) (w : ℂ) :
    fstar (deBrangesKernel E w) = deBrangesKernel E (conj w) := by
  funext z
  show conj (deBrangesKernel E w (conj z)) = _
  rw [conj_deBrangesKernel E]
  by_cases h : w = z
  · subst h; rfl
  · have h1 : w ≠ conj (conj z) := by simpa using h
    have h2 : z ≠ conj (conj w) := by simpa using (Ne.symm h)
    rw [deBrangesKernel_of_ne E h1, deBrangesKernel_of_ne E h2]
    simp only [kernelNum, fstar, Complex.conj_conj]
    have : w - z ≠ 0 := sub_ne_zero.mpr h
    have : z - w ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring

/-- `K(w, w) = (|E(w)|² - |E(w̄)|²) / (4π Im w)` for nonreal `w`. -/
theorem deBrangesKernel_diag (E : ℂ → ℂ) {w : ℂ} (hw : w.im ≠ 0) :
    deBrangesKernel E w w =
      (((‖E w‖ ^ 2 - ‖E (conj w)‖ ^ 2) / (4 * Real.pi * w.im) : ℝ) : ℂ) := by
  have hne : w ≠ conj w := by
    intro h
    apply hw
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  rw [deBrangesKernel_of_ne E hne]
  simp only [kernelNum]
  rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    norm_fstar, Complex.sub_conj]
  have him : (w.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- `K(x, x) = φ'(x) |E(x)|² / π` for real `x`. -/
theorem deBrangesKernel_diag_real (E : ℂ → ℂ) (x : ℝ) :
    deBrangesKernel E x x = ((phaseDeriv E x * ‖E x‖ ^ 2 / Real.pi : ℝ) : ℂ) := by
  have hx : (x : ℂ) = conj (x : ℂ) := (Complex.conj_ofReal x).symm
  unfold deBrangesKernel
  rw [ite_eq_left hx, deriv_fstar_ofReal, fstar_ofReal, Complex.conj_conj]
  unfold phaseDeriv
  set u := deriv E (x : ℂ)
  set e := E (x : ℂ)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have key : (u / e).im * ‖e‖ ^ 2 = u.im * e.re - u.re * e.im := by
    by_cases he : e = 0
    · simp [he]
    · rw [Complex.div_im, ← Complex.normSq_eq_norm_sq]
      have : Complex.normSq e ≠ 0 := by simpa using he
      field_simp
  have h2 : u * conj e - conj u * e = 2 * I * ((u.im * e.re - u.re * e.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
    ring
  rw [h2, show -(u / e).im * ‖e‖ ^ 2 / Real.pi = -((u / e).im * ‖e‖ ^ 2) / Real.pi by ring, key]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `K(w, w) ≥ 0` for `E ∈ \overline{HB}` (real, nonnegative). -/
theorem deBrangesKernel_diag_nonneg {E : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (w : ℂ) :
    (deBrangesKernel E w w).im = 0 ∧ 0 ≤ (deBrangesKernel E w w).re := by
  rcases lt_trichotomy w.im 0 with h | h | h
  · rw [deBrangesKernel_diag E h.ne]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    have h1 := hE.2.2 (conj w) (by simpa using h)
    rw [Complex.conj_conj] at h1
    apply div_nonneg_of_nonpos
    · nlinarith [norm_nonneg (E w), norm_nonneg (E (conj w))]
    · nlinarith [Real.pi_pos]
  · obtain ⟨x, rfl⟩ : ∃ x : ℝ, (x : ℂ) = w := ⟨w.re, Complex.ext (by simp) (by simp [h])⟩
    rw [deBrangesKernel_diag_real]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    have := hE.phaseDeriv_nonneg (h0 x)
    exact div_nonneg (mul_nonneg this (sq_nonneg _)) Real.pi_pos.le
  · rw [deBrangesKernel_diag E h.ne']
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    have h1 := hE.2.2 w h
    apply div_nonneg
    · nlinarith [norm_nonneg (E w), norm_nonneg (E (conj w))]
    · positivity

/-- **Local bound**: `K` is bounded on `{‖w‖ ≤ ρ} × {‖z‖ ≤ ρ}` (mean value inequality for the
`dslope`; no joint continuity needed). -/
theorem exists_bound_deBrangesKernel {E : ℂ → ℂ} (hE : Differentiable ℂ E) (ρ : ℝ) :
    ∃ M : ℝ, ∀ w z : ℂ, ‖w‖ ≤ ρ → ‖z‖ ≤ ρ → ‖deBrangesKernel E w z‖ ≤ M := by
  sorry

/-- The integrand of `⟨f, K(w, ·)⟩_E` on `ℝ` (`t ≠ w`):
`(-i/2π) [ (f/E)(t) E(w) - conj ((f^*/E)(t)) E^*(w) ] / (t - w)`. -/
theorem integrand_eq {E : ℂ → ℂ} (w : ℂ) (f : ℂ → ℂ) {t : ℝ} (hEt : E t ≠ 0)
    (ht : (t : ℂ) ≠ w) :
    f t * conj (deBrangesKernel E w t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) =
      (-I / (2 * Real.pi)) *
        ((f t / E t * E w - conj (fstar f t / E t) * fstar E w) / ((t : ℂ) - w)) := by
  have hne : (t : ℂ) ≠ conj w := by
    intro h
    apply ht
    have := congrArg conj h
    rwa [Complex.conj_ofReal, Complex.conj_conj] at this
  have hc : conj (E t) ≠ 0 := (map_ne_zero _).mpr hEt
  have htw : (t : ℂ) - w ≠ 0 := sub_ne_zero.mpr ht
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : ((‖E t‖ ^ 2 : ℝ) : ℂ) = E t * conj (E t) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [deBrangesKernel_of_ne E hne, hn]
  simp only [kernelNum, fstar, map_mul, map_sub, map_div₀, Complex.conj_conj, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  field_simp

/-- Decomposition of the integrand at a real point `x` (`t ≠ x`), with `A = f/E`, `g = f^*/E`,
`ψ(t) = i/(t - x + i)`:
`(-i/2π) [E(x) (A(t) - A(x)ψ(t))/(t-x) - E^*(x) conj((g(t) - g(x)ψ(t))/(t-x)) + f(x) 2i/((t-x)²+1)]`. -/
theorem integrand_eq_real {E : ℂ → ℂ} (f : ℂ → ℂ) {x t : ℝ} (hEx : E x ≠ 0) (hEt : E t ≠ 0)
    (ht : t ≠ x) :
    f t * conj (deBrangesKernel E x t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) =
      (-I / (2 * Real.pi)) *
        (E x * ((f t / E t - f x / E x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x))
          - fstar E x *
            conj ((fstar f t / E t - fstar f x / E x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x))
          + f x * (2 * I / ((((t - x) ^ 2 + 1 : ℝ)) : ℂ))) := by
  have htx : (t : ℂ) ≠ (x : ℂ) := by exact_mod_cast ht
  rw [integrand_eq (x : ℂ) f hEt htx]
  have hEtc : conj (E t) ≠ 0 := (map_ne_zero _).mpr hEt
  have hExc : conj (E x) ≠ 0 := (map_ne_zero _).mpr hEx
  have hs : (t : ℂ) - x ≠ 0 := sub_ne_zero.mpr htx
  have hψ : (t : ℂ) - x + I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hψ' : (t : ℂ) - x - I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hq : ((((t - x) ^ 2 + 1 : ℝ)) : ℂ) = ((t : ℂ) - x + I) * ((t : ℂ) - x - I) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hc : conj ((t : ℂ) - x + I) = (t : ℂ) - x - I := by
    simp [map_add, map_sub, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hq]
  simp only [fstar, map_div₀, map_mul, map_sub, Complex.conj_conj, Complex.conj_ofReal,
    Complex.conj_I, hc]
  field_simp
  ring

/-! ## 2.2 `K(w, ·) ∈ H(E)` -/

/-- Decay criterion for `H²(ℂ₊)`: `G` holomorphic on `ℂ₊`, bounded by `M` on `ℂ₊ ∩ B(c, r)` and by
`A / |z - c|` on `ℂ₊ \ B(c, r)` is in `H²`.  (On a line, `1/|z - c|² ≤ 2/((x - Re c)² + r²)` for
`|z - c| ≥ r`, whose integral is `2π/r`; the near part has measure `≤ 2r`.) -/
theorem isH2Upper_of_decay {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im}) (c : ℂ)
    (A r M : ℝ) (hr : 0 < r)
    (hfar : ∀ z : ℂ, 0 < z.im → r ≤ ‖z - c‖ → ‖G z‖ ≤ A / ‖z - c‖)
    (hnear : ∀ z : ℂ, 0 < z.im → ‖z - c‖ < r → ‖G z‖ ≤ M) : IsH2Upper G := by
  sorry

/-- `K(w, z) / E(z) = (i/2π)(conj E(w) - Θ(z) conj E^*(w))/(z - w̄)`, `Θ = E^*/E`. -/
theorem kernel_div_E {E : ℂ → ℂ} (w z : ℂ) (hz : E z ≠ 0) (hne : z ≠ conj w) :
    deBrangesKernel E w z / E z =
      (I / (2 * Real.pi)) * (conj (E w) - (fstar E z / E z) * conj (fstar E w)) /
        (z - conj w) := by
  rw [deBrangesKernel_of_ne E hne]
  simp only [kernelNum]
  have : z - conj w ≠ 0 := sub_ne_zero.mpr hne
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- `K(w, ·)/E ∈ H²(ℂ₊)` for `E ∈ \overline{HB}`, if `w ∈ ℂ₊` or `E(w̄) ≠ 0` (so that `K_w/E` is
bounded near `w̄`; far away `|K_w/E| ≤ (|E(w)| + |E^*(w)|)/(2π|z - w̄|)` since `|Θ| ≤ 1`). -/
theorem isH2Upper_kernel_div {E : ℂ → ℂ} (hE : IsHB E) {w : ℂ}
    (hw : 0 < w.im ∨ E (conj w) ≠ 0) : IsH2Upper (fun z ↦ deBrangesKernel E w z / E z) := by
  sorry

/-- `K(w, ·) ∈ H(E)` for `E ∈ \overline{HB}` and `w` nonreal or `E(w) ≠ 0` (uses
`K_w^* = K_{w̄}`). -/
theorem memHE_deBrangesKernel_of_isHB {E : ℂ → ℂ} (hE : IsHB E) {w : ℂ}
    (hw : w.im ≠ 0 ∨ E w ≠ 0) : MemHE E (deBrangesKernel E w) := by
  sorry

/-- **Theorem D, part 1**: `K(w, ·) ∈ H(E)` (`E ∈ \overline{HB}` without real zeros). -/
theorem memHE_deBrangesKernel {E : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (w : ℂ) :
    MemHE E (deBrangesKernel E w) := by
  sorry

/-! ## 2.3 The reproducing formula -/

/-- `f ∈ H(E)` gives `f/E` and `f^*/E` in `IsH2Cont` (`E` without real zeros). -/
theorem isH2Cont_of_memHE {E f : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) : IsH2Cont (fun z ↦ f z / E z) ∧ IsH2Cont (fun z ↦ fstar f z / E z) := by
  sorry

/-- `t ↦ f(t)/E(t)` is in `L²(ℝ)` and `‖f‖²_E < ∞`. -/
theorem MemHE.heNormSq_lt_top {E f : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) : heNormSq E f < ⊤ := by
  sorry

/-- For `f, g ∈ H(E)` the integrand of `heInner` is integrable (AM–GM). -/
theorem integrable_heInner {E f g : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) (hg : MemHE E g) :
    Integrable fun t : ℝ ↦ f t * conj (g t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) := by
  sorry

/-- **Reproducing formula at `w ∈ ℂ₊`, general form (for P4)**: `E ∈ \overline{HB}` may have real
zeros; `A`, `B` are `IsH2Cont` functions agreeing with `f/E`, `f^*/E` on `ℂ₊` and a.e. on `ℝ`
(e.g. the continuous extensions across removable real singularities).  Proof: a.e. on `ℝ` the
integrand is `(-i/2π)[E(w) A(t) - E^*(w) conj B(t)]/(t - w)`; `cauchy_upper` for `A` and
`integral_div_lower` at `w̄` for `B`. -/
theorem heInner_kernel_upper_of_isH2Cont {E f A B : ℂ → ℂ} (hE : IsHB E)
    (hE0 : ∀ᵐ t : ℝ, E t ≠ 0) (hA : IsH2Cont A) (hB : IsH2Cont B)
    (hAu : ∀ z : ℂ, 0 < z.im → A z = f z / E z)
    (hAr : ∀ᵐ t : ℝ, A t = f t / E t) (hBr : ∀ᵐ t : ℝ, B t = fstar f t / E t)
    {w : ℂ} (hw : 0 < w.im) : heInner E f (deBrangesKernel E w) = f w := by
  sorry

/-- **Reproducing formula, `w ∈ ℂ₊`**: `cauchy_upper` for `f/E` and `integral_div_lower` (at `w̄`)
for `f^*/E` (the case `A = f/E`, `B = f^*/E` of the previous lemma). -/
theorem heInner_kernel_upper {E f : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) {w : ℂ} (hw : 0 < w.im) : heInner E f (deBrangesKernel E w) = f w := by
  sorry

/-- **Reproducing formula, `w ∈ ℂ₋`**: `integral_div_lower` for `f/E` and `cauchy_upper` (at `w̄`)
for `f^*/E`. -/
theorem heInner_kernel_lower {E f : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) {w : ℂ} (hw : w.im < 0) : heInner E f (deBrangesKernel E w) = f w := by
  sorry

/-- **Reproducing formula, real `w = x`**: decomposition `integrand_eq_real`, then
`cauchy_real` for `f/E` and `f^*/E` at `x` and `integral_two_I_div`. -/
theorem heInner_kernel_real {E f : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) (x : ℝ) : heInner E f (deBrangesKernel E x) = f x := by
  sorry

/-- **Theorem D, part 2**: `⟨f, K_w⟩_E = f(w)` for all `w ∈ ℂ`. -/
theorem heInner_kernel {E f : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) (w : ℂ) : heInner E f (deBrangesKernel E w) = f w := by
  sorry

end FF
