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
  set B := Metric.closedBall (0 : ℂ) ρ with hBdef
  have hBc : IsCompact B := isCompact_closedBall 0 ρ
  obtain ⟨M0, hM0⟩ := hBc.exists_bound_of_continuousOn hE.continuous.continuousOn
  have hdc : Continuous (deriv E) := hE.contDiff.continuous_deriv le_rfl
  obtain ⟨M1, hM1⟩ := hBc.exists_bound_of_continuousOn hdc.continuousOn
  have hconjB : ∀ u ∈ B, conj u ∈ B := fun u hu ↦ by
    simpa [hBdef, mem_closedBall_zero_iff] using hu
  refine ⟨‖I / (2 * (Real.pi : ℂ))‖ * (2 * (M1 * M0)), fun w z hw hz ↦ ?_⟩
  have hwB : w ∈ B := mem_closedBall_zero_iff.mpr hw
  have hzB : z ∈ B := mem_closedBall_zero_iff.mpr hz
  have hcwB : conj w ∈ B := hconjB w hwB
  have hNd : ∀ u, DifferentiableAt ℂ (kernelNum E w) u := fun u ↦
    ((hE u).mul_const _).sub (((Differentiable.fstar hE) u).mul_const _)
  have hderiv : ∀ u ∈ B, ‖deriv (kernelNum E w) u‖ ≤ 2 * (M1 * M0) := by
    intro u hu
    have e : deriv (kernelNum E w) u =
        deriv E u * conj (E w) - conj (deriv E (conj u)) * conj (fstar E w) := by
      show deriv (fun z ↦ E z * conj (E w) - fstar E z * conj (fstar E w)) u = _
      rw [deriv_fun_sub ((hE u).mul_const _) (((Differentiable.fstar hE) u).mul_const _),
        deriv_mul_const (hE u), deriv_mul_const ((Differentiable.fstar hE) u), deriv_fstar]
    rw [e]
    have h1 := hM1 u hu
    have h2 := hM1 (conj u) (hconjB u hu)
    have h3 := hM0 w hwB
    have h4 := hM0 (conj w) hcwB
    calc ‖deriv E u * conj (E w) - conj (deriv E (conj u)) * conj (fstar E w)‖
        ≤ ‖deriv E u * conj (E w)‖ + ‖conj (deriv E (conj u)) * conj (fstar E w)‖ :=
          norm_sub_le _ _
      _ = ‖deriv E u‖ * ‖E w‖ + ‖deriv E (conj u)‖ * ‖E (conj w)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, Complex.norm_conj,
            norm_fstar]
      _ ≤ M1 * M0 + M1 * M0 := by
          gcongr
          · exact (norm_nonneg _).trans h1
          · exact (norm_nonneg _).trans h2
      _ = 2 * (M1 * M0) := by ring
  rw [deBrangesKernel_eq_dslope hE w]
  simp only
  rw [norm_mul]
  gcongr
  by_cases hzw : z = conj w
  · rw [hzw, dslope_same]
    exact hderiv _ hcwB
  · rw [dslope_of_ne _ hzw, slope_def_field, norm_div,
      div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hzw))]
    exact (convex_closedBall 0 ρ).norm_image_sub_le_of_norm_deriv_le (fun u _ ↦ hNd u) hderiv
      hcwB hzB

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
  set a := c.re with ha
  set b : ℝ → ℝ := fun x ↦ (Icc (a - r) (a + r)).indicator (fun _ ↦ M ^ 2) x +
    2 * A ^ 2 * ((x - a) ^ 2 + r ^ 2)⁻¹ with hb
  have hbI : Integrable b :=
    ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc).add
      ((integrable_inv_sq_add_sq a hr.ne').const_mul _)
  have hb0 : ∀ x, 0 ≤ b x := fun x ↦
    add_nonneg (indicator_nonneg (fun _ _ ↦ sq_nonneg M) x) (by positivity)
  refine ⟨hG, (ENNReal.ofReal (∫ x, b x)).toNNReal, fun y hy ↦ ?_⟩
  rw [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top,
    ofReal_integral_eq_lintegral_ofReal hbI (Eventually.of_forall hb0)]
  refine lintegral_mono fun x ↦ ?_
  rw [enorm_sq_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  have hz : 0 < ((x : ℂ) + (y : ℂ) * I).im := by simpa using hy
  have hzre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  by_cases hnr : ‖(x : ℂ) + (y : ℂ) * I - c‖ < r
  · have hx : x ∈ Icc (a - r) (a + r) := by
      have h1 := Complex.abs_re_le_norm ((x : ℂ) + (y : ℂ) * I - c)
      rw [Complex.sub_re, hzre] at h1
      have := abs_le.mp (h1.trans hnr.le)
      constructor <;> linarith [this.1, this.2]
    have h1 := hnear _ hz hnr
    have h2 : ‖G ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    simp only [hb, indicator_of_mem hx]
    have : 0 ≤ 2 * A ^ 2 * ((x - a) ^ 2 + r ^ 2)⁻¹ := by positivity
    linarith
  · rw [not_lt] at hnr
    have hd : 0 < ‖(x : ℂ) + (y : ℂ) * I - c‖ := hr.trans_le hnr
    have h1 := hfar _ hz hnr
    have h2 : ‖G ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤ A ^ 2 * (‖(x : ℂ) + (y : ℂ) * I - c‖ ^ 2)⁻¹ := by
      calc ‖G ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤ (A / ‖(x : ℂ) + (y : ℂ) * I - c‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = _ := by rw [div_pow, div_eq_mul_inv]
    have h3 := inv_norm_sq_le_of_le hr hnr
    rw [hzre] at h3
    have h4 : A ^ 2 * (‖(x : ℂ) + (y : ℂ) * I - c‖ ^ 2)⁻¹ ≤
        2 * A ^ 2 * ((x - a) ^ 2 + r ^ 2)⁻¹ := by
      calc A ^ 2 * (‖(x : ℂ) + (y : ℂ) * I - c‖ ^ 2)⁻¹
          ≤ A ^ 2 * (2 * ((x - c.re) ^ 2 + r ^ 2)⁻¹) := by gcongr
        _ = _ := by ring
    have h5 : 0 ≤ (Icc (a - r) (a + r)).indicator (fun _ ↦ M ^ 2) x :=
      indicator_nonneg (fun _ _ ↦ sq_nonneg M) x
    simp only [hb]
    linarith

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
  set c := conj w with hcdef
  set A := (‖E w‖ + ‖fstar E w‖) / (2 * Real.pi) with hA
  have hK := differentiable_deBrangesKernel hE.1 w
  have hG : DifferentiableOn ℂ (fun z ↦ deBrangesKernel E w z / E z) {z : ℂ | 0 < z.im} :=
    fun z hz ↦ ((hK z).div (hE.1 z) (hE.2.1 z hz)).differentiableWithinAt
  have hnI : ‖(I / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, Complex.norm_I, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  have hfar : ∀ z : ℂ, 0 < z.im → z ≠ c → ‖deBrangesKernel E w z / E z‖ ≤ A / ‖z - c‖ := by
    intro z hz hzc
    have hEz := hE.2.1 z hz
    rw [kernel_div_E w z hEz hzc]
    have hΘ : ‖fstar E z / E z‖ ≤ 1 := by
      rw [norm_div, norm_fstar, div_le_one (norm_pos_iff.mpr hEz)]
      exact hE.2.2 z hz
    have h1 : ‖conj (E w) - fstar E z / E z * conj (fstar E w)‖ ≤ ‖E w‖ + ‖fstar E w‖ := by
      calc ‖conj (E w) - fstar E z / E z * conj (fstar E w)‖
          ≤ ‖conj (E w)‖ + ‖fstar E z / E z * conj (fstar E w)‖ := norm_sub_le _ _
        _ = ‖E w‖ + ‖fstar E z / E z‖ * ‖fstar E w‖ := by
            rw [Complex.norm_conj, norm_mul, Complex.norm_conj]
        _ ≤ ‖E w‖ + 1 * ‖fstar E w‖ := by gcongr
        _ = ‖E w‖ + ‖fstar E w‖ := by ring
    rw [norm_div, norm_mul, hnI, hA]
    gcongr
    calc 1 / (2 * Real.pi) * ‖conj (E w) - fstar E z / E z * conj (fstar E w)‖
        ≤ 1 / (2 * Real.pi) * (‖E w‖ + ‖fstar E w‖) := by gcongr
      _ = (‖E w‖ + ‖fstar E w‖) / (2 * Real.pi) := by ring
  rcases hw with hw | hw
  · refine isH2Upper_of_decay hG c A w.im 0 hw (fun z hz hzr ↦ hfar z hz ?_) ?_
    · rintro rfl
      simp at hzr
      linarith
    · intro z hz hzr
      exfalso
      have h1 := Complex.im_le_norm (z - c)
      simp only [Complex.sub_im, hcdef, Complex.conj_im] at h1
      linarith
  · have hEc : ∀ᶠ u in 𝓝 c, E u ≠ 0 := hE.1.continuous.continuousAt.eventually_ne hw
    obtain ⟨ε, hε, hεE⟩ := Metric.eventually_nhds_iff.mp hEc
    have hr : 0 < ε / 2 := by positivity
    have hsub : Metric.closedBall c (ε / 2) ⊆ {u | E u ≠ 0} := fun u hu ↦
      hεE (lt_of_le_of_lt (Metric.mem_closedBall.mp hu) (by linarith))
    have hcont : ContinuousOn (fun z ↦ deBrangesKernel E w z / E z) (Metric.closedBall c (ε / 2)) :=
      hK.continuous.continuousOn.div hE.1.continuous.continuousOn fun u hu ↦ hsub hu
    obtain ⟨M, hM⟩ := (isCompact_closedBall c (ε / 2)).exists_bound_of_continuousOn hcont
    refine isH2Upper_of_decay hG c A (ε / 2) M hr (fun z hz hzr ↦ hfar z hz ?_) ?_
    · rintro rfl
      simp at hzr
      linarith
    · intro z _ hzr
      exact hM z (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hzr.le))

/-- `K(w, ·) ∈ H(E)` for `E ∈ \overline{HB}` and `w` nonreal or `E(w) ≠ 0` (uses
`K_w^* = K_{w̄}`). -/
theorem memHE_deBrangesKernel_of_isHB {E : ℂ → ℂ} (hE : IsHB E) {w : ℂ}
    (hw : w.im ≠ 0 ∨ E w ≠ 0) : MemHE E (deBrangesKernel E w) := by
  refine ⟨differentiable_deBrangesKernel hE.1 w, isH2Upper_kernel_div hE ?_, ?_⟩
  · rcases lt_trichotomy w.im 0 with h' | h' | h'
    · right
      exact hE.2.1 (conj w) (by simpa using h')
    · right
      have hw' : conj w = w := Complex.conj_eq_iff_im.mpr h'
      rw [hw']
      rcases hw with h | h
      · exact absurd h' h
      · exact h
    · left
      exact h'
  · rw [fstar_deBrangesKernel E w]
    apply isH2Upper_kernel_div hE
    rw [Complex.conj_conj]
    rcases lt_trichotomy w.im 0 with h' | h' | h'
    · left
      simpa using h'
    · right
      rcases hw with h | h
      · exact absurd h' h
      · exact h
    · right
      exact hE.2.1 w h'

/-- **Theorem D, part 1**: `K(w, ·) ∈ H(E)` (`E ∈ \overline{HB}` without real zeros). -/
theorem memHE_deBrangesKernel {E : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (w : ℂ) :
    MemHE E (deBrangesKernel E w) := by
  apply memHE_deBrangesKernel_of_isHB hE
  by_cases h : w.im = 0
  · right
    have hw : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [h])
    rw [← hw]
    exact h0 _
  · left
    exact h

/-! ## 2.3 The reproducing formula -/

/-- `f ∈ H(E)` gives `f/E` and `f^*/E` in `IsH2Cont` (`E` without real zeros). -/
theorem isH2Cont_of_memHE {E f : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) : IsH2Cont (fun z ↦ f z / E z) ∧ IsH2Cont (fun z ↦ fstar f z / E z) := by
  refine ⟨⟨hf.2.1, fun t ↦ ?_⟩, ⟨hf.2.2, fun t ↦ ?_⟩⟩
  · exact (hf.1 t).continuousAt.div (hE t).continuousAt (h0 t)
  · exact ((Differentiable.fstar hf.1) t).continuousAt.div (hE t).continuousAt (h0 t)

/-- `t ↦ f(t)/E(t)` is in `L²(ℝ)` and `‖f‖²_E < ∞`. -/
theorem MemHE.heNormSq_lt_top {E f : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) : heNormSq E f < ⊤ := by
  exact (isH2Cont_of_memHE hE h0 hf).1.lintegral_real_lt_top

/-- For `f, g ∈ H(E)` the integrand of `heInner` is integrable (AM–GM). -/
theorem integrable_heInner {E f g : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) (hg : MemHE E g) :
    Integrable fun t : ℝ ↦ f t * conj (g t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) := by
  have hA := (isH2Cont_of_memHE hE h0 hf).1
  have hB := (isH2Cont_of_memHE hE h0 hg).1
  have hA2 : Integrable fun t : ℝ ↦ ‖f t / E t‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hA.memLp_real.aestronglyMeasurable).1 hA.memLp_real
  have hB2 : Integrable fun t : ℝ ↦ ‖g t / E t‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hB.memLp_real.aestronglyMeasurable).1 hB.memLp_real
  have hE' : ∀ t : ℝ, ((‖E t‖ ^ 2 : ℝ) : ℂ) ≠ 0 := fun t ↦ by
    have : 0 < ‖E t‖ := norm_pos_iff.mpr (h0 t)
    exact_mod_cast (by positivity : (0 : ℝ) < ‖E t‖ ^ 2).ne'
  have hcont : Continuous fun t : ℝ ↦ f t * conj (g t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : Continuous fun t : ℝ ↦ f t := hf.1.continuous.comp Complex.continuous_ofReal
    have h2 : Continuous fun t : ℝ ↦ g t := hg.1.continuous.comp Complex.continuous_ofReal
    have h3 : Continuous fun t : ℝ ↦ E t := hE.continuous.comp Complex.continuous_ofReal
    exact (h1.mul (Complex.continuous_conj.comp h2)).div
      (Complex.continuous_ofReal.comp (h3.norm.pow 2)) hE'
  refine ((hA2.add hB2).div_const 2).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t ↦ ?_)
  have hEt : 0 < ‖E t‖ := norm_pos_iff.mpr (h0 t)
  have e : ‖f t * conj (g t) / ((‖E t‖ ^ 2 : ℝ) : ℂ)‖ = ‖f t / E t‖ * ‖g t / E t‖ := by
    rw [norm_div, norm_mul, Complex.norm_conj, norm_div, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    field_simp
  show _ ≤ (‖f t / E t‖ ^ 2 + ‖g t / E t‖ ^ 2) / 2
  rw [e]
  nlinarith [sq_nonneg (‖f t / E t‖ - ‖g t / E t‖)]

theorem integrable_conj {g : ℝ → ℂ} (hg : Integrable g) : Integrable fun t ↦ conj (g t) := by
  have := (Complex.conjCLE.toContinuousLinearMap).integrable_comp hg
  simpa using this

/-- Decomposition of `⟨f, K_w⟩_E` for nonreal `w`, given `IsH2Cont` functions `A`, `B` equal a.e. on
`ℝ` to `f/E`, `f^*/E`:
`⟨f, K_w⟩ = (-i/2π) [E(w) ∫ A(t)/(t - w) - E^*(w) conj ∫ B(t)/(t - w̄)]`. -/
theorem heInner_kernel_eq_of_ae {E f A B : ℂ → ℂ} (hE0 : ∀ᵐ t : ℝ, E t ≠ 0) (hA : IsH2Cont A)
    (hB : IsH2Cont B) (hAr : ∀ᵐ t : ℝ, A t = f t / E t) (hBr : ∀ᵐ t : ℝ, B t = fstar f t / E t)
    {w : ℂ} (hw : w.im ≠ 0) :
    heInner E f (deBrangesKernel E w) = (-I / (2 * Real.pi)) *
      (E w * (∫ t : ℝ, A t / ((t : ℂ) - w)) -
        fstar E w * conj (∫ t : ℝ, B t / ((t : ℂ) - conj w))) := by
  have hcw : (conj w).im ≠ 0 := by simpa using hw
  have hiA := hA.integrable_div hw
  have hiBc := integrable_conj (hB.integrable_div hcw)
  have hae : (fun t : ℝ ↦ f t * conj (deBrangesKernel E w t) / ((‖E t‖ ^ 2 : ℝ) : ℂ)) =ᵐ[volume]
      fun t ↦ (-I / (2 * Real.pi)) * (E w * (A t / ((t : ℂ) - w)) -
        fstar E w * conj (B t / ((t : ℂ) - conj w))) := by
    filter_upwards [hE0, hAr, hBr] with t ht hA' hB'
    have htw : (t : ℂ) ≠ w := fun h ↦ hw (by rw [← h]; simp)
    have hc : conj (fstar f t / E t / ((t : ℂ) - conj w)) =
        conj (fstar f t / E t) / ((t : ℂ) - w) := by
      rw [map_div₀ _ (fstar f t / E t), map_sub, Complex.conj_ofReal, Complex.conj_conj]
    rw [integrand_eq w f ht htw, hA', hB', hc]
    ring
  unfold heInner
  rw [integral_congr_ae hae, integral_const_mul, integral_sub (hiA.const_mul _)
    (hiBc.const_mul _), integral_const_mul, integral_const_mul, integral_conj]

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
  have hEw : E w ≠ 0 := hE.2.1 w hw
  have hcw : (conj w).im < 0 := by simpa using hw
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [heInner_kernel_eq_of_ae hE0 hA hB hAr hBr hw.ne', hA.cauchy_upper hw,
    hB.integral_div_lower hcw, hAu w hw, map_zero, mul_zero, sub_zero]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Reproducing formula, `w ∈ ℂ₊`**: `cauchy_upper` for `f/E` and `integral_div_lower` (at `w̄`)
for `f^*/E` (the case `A = f/E`, `B = f^*/E` of the previous lemma). -/
theorem heInner_kernel_upper {E f : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) {w : ℂ} (hw : 0 < w.im) : heInner E f (deBrangesKernel E w) = f w := by
  obtain ⟨hA, hB⟩ := isH2Cont_of_memHE hE.1 h0 hf
  exact heInner_kernel_upper_of_isH2Cont hE (Eventually.of_forall h0) hA hB (fun z _ ↦ rfl)
    (Eventually.of_forall fun t ↦ rfl) (Eventually.of_forall fun t ↦ rfl) hw

/-- **Reproducing formula, `w ∈ ℂ₋`**: `integral_div_lower` for `f/E` and `cauchy_upper` (at `w̄`)
for `f^*/E`. -/
theorem heInner_kernel_lower {E f : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) {w : ℂ} (hw : w.im < 0) : heInner E f (deBrangesKernel E w) = f w := by
  obtain ⟨hA, hB⟩ := isH2Cont_of_memHE hE.1 h0 hf
  have hcw : 0 < (conj w).im := by simpa using hw
  have hEc : E (conj w) ≠ 0 := hE.2.1 _ hcw
  have hEs : fstar E w ≠ 0 := by
    simp only [fstar, ne_eq, map_eq_zero]
    exact hEc
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [heInner_kernel_eq_of_ae (Eventually.of_forall h0) hA hB (Eventually.of_forall fun t ↦ rfl)
    (Eventually.of_forall fun t ↦ rfl) hw.ne, hA.integral_div_lower hw, hB.cauchy_upper hcw]
  have e : conj (2 * Real.pi * I * (fstar f (conj w) / E (conj w))) =
      -(2 * Real.pi * I) * (f w / fstar E w) := by
    simp only [fstar, map_mul, map_div₀, Complex.conj_conj, Complex.conj_ofReal, Complex.conj_I,
      map_ofNat]
    ring
  rw [e]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Reproducing formula, real `w = x`**: decomposition `integrand_eq_real`, then
`cauchy_real` for `f/E` and `f^*/E` at `x` and `integral_two_I_div`. -/
theorem heInner_kernel_real {E f : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) (x : ℝ) : heInner E f (deBrangesKernel E x) = f x := by
  obtain ⟨hA, hB⟩ := isH2Cont_of_memHE hE.1 h0 hf
  have hdA : DifferentiableAt ℂ (fun z ↦ f z / E z) (x : ℂ) := (hf.1 _).div (hE.1 _) (h0 x)
  have hdB : DifferentiableAt ℂ (fun z ↦ fstar f z / E z) (x : ℂ) :=
    ((Differentiable.fstar hf.1) _).div (hE.1 _) (h0 x)
  have hP : Integrable fun t : ℝ ↦
      (f t / E t - f x / E x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x) :=
    hA.integrable_reg_real hdA
  have hQ : Integrable fun t : ℝ ↦
      (fstar f t / E t - fstar f x / E x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x) :=
    hB.integrable_reg_real hdB
  have hP0 : ∫ t : ℝ, (f t / E t - f x / E x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x) = 0 :=
    hA.cauchy_real hdA
  have hQ0 : ∫ t : ℝ,
      (fstar f t / E t - fstar f x / E x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x) = 0 :=
    hB.cauchy_real hdB
  have hR : Integrable fun t : ℝ ↦ 2 * I / ((((t - x) ^ 2 + 1 : ℝ)) : ℂ) := by
    have h : Integrable fun t : ℝ ↦ 2 * I * ((((t - x) ^ 2 + 1 ^ 2)⁻¹ : ℝ) : ℂ) :=
      ((integrable_inv_sq_add_sq x one_ne_zero).ofReal).const_mul (2 * I)
    refine h.congr (Eventually.of_forall fun t ↦ ?_)
    push_cast
    ring
  have hae : (fun t : ℝ ↦ f t * conj (deBrangesKernel E x t) / ((‖E t‖ ^ 2 : ℝ) : ℂ)) =ᵐ[volume]
      fun t ↦ (-I / (2 * Real.pi)) *
        (E x * ((f t / E t - f x / E x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x))
          - fstar E x *
            conj ((fstar f t / E t - fstar f x / E x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x))
          + f x * (2 * I / ((((t - x) ^ 2 + 1 : ℝ)) : ℂ))) := by
    filter_upwards [volume.ae_ne x] with t ht
    exact integrand_eq_real f (h0 x) (h0 t) ht
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hPQ : Integrable fun t : ℝ ↦
      E x * ((f t / E t - f x / E x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x))
        - fstar E x *
          conj ((fstar f t / E t - fstar f x / E x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x)) :=
    (hP.const_mul _).sub ((integrable_conj hQ).const_mul _)
  unfold heInner
  rw [integral_congr_ae hae, integral_const_mul, integral_add hPQ (hR.const_mul _),
    integral_sub (hP.const_mul _) ((integrable_conj hQ).const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, integral_conj, hP0, hQ0, integral_two_I_div,
    map_zero]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Theorem D, part 2**: `⟨f, K_w⟩_E = f(w)` for all `w ∈ ℂ`. -/
theorem heInner_kernel {E f : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) (w : ℂ) : heInner E f (deBrangesKernel E w) = f w := by
  rcases lt_trichotomy w.im 0 with h | h | h
  · exact heInner_kernel_lower hE h0 hf h
  · have hw : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [h])
    rw [← hw]
    exact heInner_kernel_real hE h0 hf w.re
  · exact heInner_kernel_upper hE h0 hf h

end FF
