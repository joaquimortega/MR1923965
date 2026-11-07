import FourierFrames.Cited.DeBrangesDE.Cauchy
import FourierFrames.HB.Phase

/-!
# P3 — Theorem D: the reproducing kernel of `H(E)`

See `blueprint/P3_DeBrangesDE.md`, §2–§3.  The kernel `K(w, ·)` belongs to `H(E)` (an `H²` bound
for `(a + bΘ)/(z - c)` with `Θ = E^*/E`), and `⟨f, K(w, ·)⟩_E = f(w)` for nonreal `w` is the
Cauchy formula of `Cauchy.lean` applied to `f/E` and `conj (f^*/E)`; real `w` follows by an `L²`
limit (Fatou) from nonreal `w`.
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

/-! ## 2.1 Algebra of the kernel -/

theorem kernelNum_conj_self {E : ℂ → ℂ} (w : ℂ) : kernelNum E w (conj w) = 0 := by
  sorry

/-- `K(w, ·) = (i/2π) · dslope (kernelNum E w) w̄`. -/
theorem deBrangesKernel_eq_dslope {E : ℂ → ℂ} (hE : Differentiable ℂ E) (w : ℂ) :
    deBrangesKernel E w = fun z ↦ (I / (2 * Real.pi)) • dslope (kernelNum E w) (conj w) z := by
  sorry

theorem differentiable_deBrangesKernel {E : ℂ → ℂ} (hE : Differentiable ℂ E) (w : ℂ) :
    Differentiable ℂ (deBrangesKernel E w) := by
  sorry

/-- Joint continuity of the kernel (including across the diagonal `z = w̄`). -/
theorem continuous_deBrangesKernel {E : ℂ → ℂ} (hE : Differentiable ℂ E) :
    Continuous fun p : ℂ × ℂ ↦ deBrangesKernel E p.1 p.2 := by
  sorry

/-- Hermitian symmetry `conj K(w, z) = K(z, w)`. -/
theorem conj_deBrangesKernel {E : ℂ → ℂ} (hE : Differentiable ℂ E) (w z : ℂ) :
    conj (deBrangesKernel E w z) = deBrangesKernel E z w := by
  sorry

/-- Multiplied form of the kernel: `K(w,z) · π (z - w̄) = (i/2) · kernelNum`, valid for all `z`. -/
theorem deBrangesKernel_mul {E : ℂ → ℂ} (w z : ℂ) :
    deBrangesKernel E w z * (Real.pi * (z - conj w)) = (I / 2) * kernelNum E w z := by
  sorry

/-- `K(w, w) = (|E(w)|² - |E(w̄)|²) / (4π Im w)` for nonreal `w`. -/
theorem deBrangesKernel_diag {E : ℂ → ℂ} {w : ℂ} (hw : w.im ≠ 0) :
    deBrangesKernel E w w =
      (((‖E w‖ ^ 2 - ‖E (conj w)‖ ^ 2) / (4 * Real.pi * w.im) : ℝ) : ℂ) := by
  sorry

/-- `K(x, x) = φ'(x) |E(x)|² / π` for real `x` (`E` without real zeros). -/
theorem deBrangesKernel_diag_real {E : ℂ → ℂ} (hE : Differentiable ℂ E) (x : ℝ) :
    deBrangesKernel E x x = ((phaseDeriv E x * ‖E x‖ ^ 2 / Real.pi : ℝ) : ℂ) := by
  sorry

/-- `fstar (K(w, ·)) (z) · (z - w) = (-i/2π) (E^*(z) E(w) - E(z) E^*(w))`. -/
theorem fstar_deBrangesKernel_mul {E : ℂ → ℂ} (hE : Differentiable ℂ E) (w z : ℂ) :
    fstar (deBrangesKernel E w) z * (z - w) =
      (-I / (2 * Real.pi)) * (fstar E z * E w - E z * fstar E w) := by
  sorry

/-- The integrand of `⟨f, K(w, ·)⟩_E` on `ℝ` (`t ≠ w`):
`(-i/2π) [ (f/E)(t) E(w) - conj ((f^*/E)(t)) E^*(w) ] / (t - w)`. -/
theorem integrand_eq {E : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0) (w : ℂ)
    (f : ℂ → ℂ) (t : ℝ) (ht : (t : ℂ) ≠ w) :
    f t * conj (deBrangesKernel E w t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) =
      (-I / (2 * Real.pi)) *
        ((f t / E t * E w - conj (fstar f t / E t) * fstar E w) / ((t : ℂ) - w)) := by
  sorry

/-! ## 2.2 `K(w, ·) ∈ H(E)` -/

/-- `f ∈ H(E)` gives `f/E` and `f^*/E` in `IsH2Cont` (strict `E` without real zeros). -/
theorem isH2Cont_of_memHE {E f : ℂ → ℂ} (h0 : ∀ x : ℝ, E x ≠ 0) (hHB : IsHB E)
    (hf : MemHE E f) : IsH2Cont (fun z ↦ f z / E z) ∧ IsH2Cont (fun z ↦ fstar f z / E z) := by
  sorry

/-- Decay criterion for `H²(ℂ₊)`: `G` holomorphic on `ℂ₊`, bounded by `M` on `ℂ₊ ∩ B(c, r)` and by
`A / |z - c|` on `ℂ₊ \ B(c, r)` is in `H²`.  (On a line, `1/|z - c|² ≤ 2/((x - Re c)² + r²)` for
`|z - c| ≥ r`, whose integral is `2π/r`; the near part has measure `≤ 2r`.) -/
theorem isH2Upper_of_decay {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im}) (c : ℂ)
    (A r M : ℝ) (hr : 0 < r)
    (hfar : ∀ z : ℂ, 0 < z.im → r ≤ ‖z - c‖ → ‖G z‖ ≤ A / ‖z - c‖)
    (hnear : ∀ z : ℂ, 0 < z.im → ‖z - c‖ < r → ‖G z‖ ≤ M) : IsH2Upper G := by
  sorry

/-- `K(w, z) / E(z)` for `z ∈ ℂ₊`: `(i/2π)(conj E(w) - Θ(z) conj E^*(w))/(z - w̄)`, `Θ = E^*/E`
(so `‖K_w/E‖ ≤ (|E(w)| + |E^*(w)|)/(2π |z - w̄|)` on `ℂ₊` as `|Θ| ≤ 1`). -/
theorem kernel_div_E {E : ℂ → ℂ} (w z : ℂ) (hz : E z ≠ 0) (hne : z ≠ conj w) :
    deBrangesKernel E w z / E z =
      (I / (2 * Real.pi)) * (conj (E w) - (fstar E z / E z) * conj (fstar E w)) / (z - conj w) := by
  sorry

/-- `K_w^*(z) / E(z) = (-i/2π)(Θ(z) E(w) - E^*(w))/(z - w)` for `z ≠ w`. -/
theorem kernel_fstar_div_E {E : ℂ → ℂ} (hE : Differentiable ℂ E) (w z : ℂ) (hz : E z ≠ 0)
    (hne : z ≠ w) :
    fstar (deBrangesKernel E w) z / E z =
      (-I / (2 * Real.pi)) * ((fstar E z / E z) * E w - fstar E w) / (z - w) := by
  sorry

/-- **Theorem D, part 1**: `K(w, ·) ∈ H(E)`. -/
theorem memHE_deBrangesKernel {E : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (w : ℂ) : MemHE E (deBrangesKernel E w) := by
  sorry

/-! ## 2.3 The reproducing formula -/

/-- For `f ∈ H(E)` and `g ∈ H(E)` the integrand of `heInner` is integrable. -/
theorem integrable_heInner {E f g : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) (hg : MemHE E g) :
    Integrable fun t : ℝ ↦ f t * conj (g t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) := by
  sorry

/-- **Reproducing formula for nonreal `w`**: Cauchy formulas for `f/E` and `conj (f^*/E)`. -/
theorem heInner_kernel_nonreal {E f : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) {w : ℂ} (hw : w.im ≠ 0) : heInner E f (deBrangesKernel E w) = f w := by
  sorry

/-- `‖K_{w'} - K_{w''}‖² = K(w',w') - 2 Re K(w',w'') + K(w'',w'')` for nonreal `w', w''`. -/
theorem heNormSq_kernel_sub {E : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    {w w' : ℂ} (hw : w.im ≠ 0) (hw' : w'.im ≠ 0) :
    heNormSq E (fun z ↦ deBrangesKernel E w z - deBrangesKernel E w' z) =
      ENNReal.ofReal ((deBrangesKernel E w w).re + (deBrangesKernel E w' w').re
        - 2 * (deBrangesKernel E w w').re) := by
  sorry

/-- Real `w`: `K_{w + i/(n+1)} → K_w` in the norm of `H(E)` (Cauchy in norm by the previous
lemma and joint continuity; identification of the limit by Fatou). -/
theorem tendsto_heNormSq_kernel_real {E : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (x : ℝ) :
    Tendsto (fun n : ℕ ↦ heNormSq E (fun z ↦
      deBrangesKernel E ((x : ℂ) + (((1 : ℝ) / (n + 1) : ℝ) : ℂ) * I) z - deBrangesKernel E x z))
      atTop (𝓝 0) := by
  sorry

/-- **Reproducing formula for real `w`**. -/
theorem heInner_kernel_real {E f : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) (x : ℝ) : heInner E f (deBrangesKernel E x) = f x := by
  sorry

end FF
