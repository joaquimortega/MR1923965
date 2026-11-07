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
  sorry

/-! ## 2.1 Algebra of the kernel -/

theorem kernelNum_conj_self (E : ℂ → ℂ) (w : ℂ) : kernelNum E w (conj w) = 0 := by
  sorry

/-- Off the diagonal, `K(w, z) = (i/2) kernelNum / (π (z - w̄))` (unfolding the `if`). -/
theorem deBrangesKernel_of_ne (E : ℂ → ℂ) {w z : ℂ} (hz : z ≠ conj w) :
    deBrangesKernel E w z = (I / 2) * kernelNum E w z / (Real.pi * (z - conj w)) := by
  sorry

/-- `K(w, ·) = (i/2π) · dslope (kernelNum E w) w̄`. -/
theorem deBrangesKernel_eq_dslope {E : ℂ → ℂ} (hE : Differentiable ℂ E) (w : ℂ) :
    deBrangesKernel E w = fun z ↦ (I / (2 * Real.pi)) * dslope (kernelNum E w) (conj w) z := by
  sorry

theorem differentiable_deBrangesKernel {E : ℂ → ℂ} (hE : Differentiable ℂ E) (w : ℂ) :
    Differentiable ℂ (deBrangesKernel E w) := by
  sorry

/-- Multiplied form of the kernel: `K(w,z) · π (z - w̄) = (i/2) · kernelNum`, valid for all `z`. -/
theorem deBrangesKernel_mul (E : ℂ → ℂ) (w z : ℂ) :
    deBrangesKernel E w z * (Real.pi * (z - conj w)) = (I / 2) * kernelNum E w z := by
  sorry

/-- Hermitian symmetry `conj K(w, z) = K(z, w)`. -/
theorem conj_deBrangesKernel {E : ℂ → ℂ} (hE : Differentiable ℂ E) (w z : ℂ) :
    conj (deBrangesKernel E w z) = deBrangesKernel E z w := by
  sorry

/-- `K(w, ·)^* = K(w̄, ·)`. -/
theorem fstar_deBrangesKernel {E : ℂ → ℂ} (hE : Differentiable ℂ E) (w : ℂ) :
    fstar (deBrangesKernel E w) = deBrangesKernel E (conj w) := by
  sorry

/-- `K(w, w) = (|E(w)|² - |E(w̄)|²) / (4π Im w)` for nonreal `w`. -/
theorem deBrangesKernel_diag (E : ℂ → ℂ) {w : ℂ} (hw : w.im ≠ 0) :
    deBrangesKernel E w w =
      (((‖E w‖ ^ 2 - ‖E (conj w)‖ ^ 2) / (4 * Real.pi * w.im) : ℝ) : ℂ) := by
  sorry

/-- `K(x, x) = φ'(x) |E(x)|² / π` for real `x`. -/
theorem deBrangesKernel_diag_real (E : ℂ → ℂ) (x : ℝ) :
    deBrangesKernel E x x = ((phaseDeriv E x * ‖E x‖ ^ 2 / Real.pi : ℝ) : ℂ) := by
  sorry

/-- `K(w, w) ≥ 0` for `E ∈ \overline{HB}` (real, nonnegative). -/
theorem deBrangesKernel_diag_nonneg {E : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (w : ℂ) :
    (deBrangesKernel E w w).im = 0 ∧ 0 ≤ (deBrangesKernel E w w).re := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
