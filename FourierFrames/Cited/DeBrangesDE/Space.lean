import FourierFrames.Cited.DeBrangesDE.Kernel

/-!
# P3 — `H(E)` as a Hilbert space of entire functions

See `blueprint/P3_DeBrangesDE.md`, §4.  For `E ∈ \overline{HB}` without real zeros: linear
structure, the sesquilinear form `heInner`, Cauchy–Schwarz, the evaluation bound
`|f(z)|² ≤ K(z,z) ‖f‖²_E` (from Theorem D), the bound of line integrals by the boundary norm, and
**completeness** (`memHE_of_cauchy`), proved with Fatou's lemma instead of any abstract `L²`
machinery.  We never build an `InnerProductSpace` instance: all statements are about functions
`ℂ → ℂ` and the integrals `heInner`, `heNormSq`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {E : ℂ → ℂ}

/-! ## 4.1 Linear structure (no hypothesis on `E`) -/

theorem MemHE.add {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    MemHE E (fun z ↦ f z + g z) := by
  sorry

theorem MemHE.const_mul {f : ℂ → ℂ} (hf : MemHE E f) (c : ℂ) : MemHE E (fun z ↦ c * f z) := by
  sorry

theorem MemHE.sub {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    MemHE E (fun z ↦ f z - g z) := by
  sorry

theorem memHE_zero : MemHE E (fun _ ↦ 0) := by
  sorry

theorem MemHE.finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, MemHE E (f i)) : MemHE E (fun z ↦ ∑ i ∈ s, f i z) := by
  sorry

/-- A nonzero constant multiple of a function not in `H(E)` is not in `H(E)`. -/
theorem MemHE.of_const_mul {f : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) (h : MemHE E (fun z ↦ c * f z)) :
    MemHE E f := by
  sorry

/-- `f ∈ H(E) ⇒ f^* ∈ H(E)` (the two defining conditions are swapped, `f^{**} = f`). -/
theorem memHE_fstar {f : ℂ → ℂ} (hf : MemHE E f) : MemHE E (fstar f) := by
  sorry

/-- `‖f^*‖_E = ‖f‖_E` (on `ℝ`, `|f^*(t)| = |f(t)|`). -/
theorem heNormSq_fstar (f : ℂ → ℂ) : heNormSq E (fstar f) = heNormSq E f := by
  sorry

/-! ## 4.2 The sesquilinear form -/

section Inner

variable (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)

include hE h0 in
/-- `heInner E f f = ‖f‖²_E` (as a real number; `E` continuous makes the integrand measurable). -/
theorem heInner_self {f : ℂ → ℂ} (hf : MemHE E f) :
    heInner E f f = (((heNormSq E f).toReal : ℝ) : ℂ) := by
  sorry

theorem heInner_conj_symm (f g : ℂ → ℂ) : conj (heInner E f g) = heInner E g f := by
  sorry

include hE h0 in
theorem heInner_add_left {f g k : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) (hk : MemHE E k) :
    heInner E (fun z ↦ f z + g z) k = heInner E f k + heInner E g k := by
  sorry

include hE h0 in
theorem heInner_sub_left {f g k : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) (hk : MemHE E k) :
    heInner E (fun z ↦ f z - g z) k = heInner E f k - heInner E g k := by
  sorry

theorem heInner_smul_left (f k : ℂ → ℂ) (c : ℂ) :
    heInner E (fun z ↦ c * f z) k = c * heInner E f k := by
  sorry

theorem heInner_smul_right (f k : ℂ → ℂ) (c : ℂ) :
    heInner E f (fun z ↦ c * k z) = conj c * heInner E f k := by
  sorry

include hE h0 in
theorem heInner_sum_left {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {k : ℂ → ℂ}
    (hf : ∀ i ∈ s, MemHE E (f i)) (hk : MemHE E k) :
    heInner E (fun z ↦ ∑ i ∈ s, f i z) k = ∑ i ∈ s, heInner E (f i) k := by
  sorry

include hE h0 in
theorem heInner_sum_right {ι : Type*} (s : Finset ι) {f : ℂ → ℂ} {k : ι → ℂ → ℂ}
    (hf : MemHE E f) (hk : ∀ i ∈ s, MemHE E (k i)) :
    heInner E f (fun z ↦ ∑ i ∈ s, k i z) = ∑ i ∈ s, heInner E f (k i) := by
  sorry

include hE h0 in
/-- `‖f - g‖² = ‖f‖² + ‖g‖² - 2 Re ⟨f, g⟩`. -/
theorem heNormSq_sub {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    (heNormSq E (fun z ↦ f z - g z)).toReal =
      (heNormSq E f).toReal + (heNormSq E g).toReal - 2 * (heInner E f g).re := by
  sorry

include hE h0 in
/-- Cauchy–Schwarz: `|⟨f, g⟩|² ≤ ‖f‖² ‖g‖²`. -/
theorem norm_heInner_sq_le {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    ‖heInner E f g‖ ^ 2 ≤ (heNormSq E f).toReal * (heNormSq E g).toReal := by
  sorry

include hE h0 in
/-- Continuity of `⟨f, ·⟩`: if `‖gₙ - g‖_E → 0` then `⟨f, gₙ⟩ → ⟨f, g⟩`. -/
theorem tendsto_heInner_right {f g : ℂ → ℂ} {gs : ℕ → ℂ → ℂ} (hf : MemHE E f)
    (hg : MemHE E g) (hgs : ∀ n, MemHE E (gs n))
    (hlim : Tendsto (fun n ↦ heNormSq E (fun z ↦ gs n z - g z)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ heInner E f (gs n)) atTop (𝓝 (heInner E f g)) := by
  sorry

/-! ## 4.3 Kernels and the evaluation bound -/

include hE h0 in
/-- `‖K_w‖² = K(w, w)`. -/
theorem heNormSq_kernel (w : ℂ) :
    (heNormSq E (deBrangesKernel E w)).toReal = (deBrangesKernel E w w).re := by
  sorry

include hE h0 in
/-- `⟨K_w, K_z⟩ = K(w, z)`. -/
theorem heInner_kernel_kernel (w z : ℂ) :
    heInner E (deBrangesKernel E w) (deBrangesKernel E z) = deBrangesKernel E w z := by
  sorry

include hE h0 in
/-- **Evaluation bound**: `|f(z)|² ≤ K(z,z) ‖f‖²_E`. -/
theorem norm_sq_le_kernel_mul {f : ℂ → ℂ} (hf : MemHE E f) (z : ℂ) :
    ‖f z‖ ^ 2 ≤ (deBrangesKernel E z z).re * (heNormSq E f).toReal := by
  sorry

include hE h0 in
/-- A function of `H(E)` with `‖f‖_E = 0` vanishes identically. -/
theorem eq_zero_of_heNormSq_eq_zero {f : ℂ → ℂ} (hf : MemHE E f) (h : heNormSq E f = 0) :
    ∀ z, f z = 0 := by
  sorry

/-! ## 4.4 Line integrals and completeness -/

include hE h0 in
/-- `∫ |f/E (x + iy)|² dx ≤ ‖f‖²_E` and the same for `f^*` (`IsH2Cont.lintegral_line_le`). -/
theorem MemHE.lintegral_line_le {f : ℂ → ℂ} (hf : MemHE E f) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ heNormSq E f ∧
    ∫⁻ x : ℝ, ‖fstar f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤
      heNormSq E f := by
  sorry

include hE h0 in
/-- **Completeness of `H(E)`**: a sequence in `H(E)` that is Cauchy for `‖·‖_E` converges in norm
and pointwise (even locally uniformly) to an element of `H(E)`. -/
theorem memHE_of_cauchy (f : ℕ → ℂ → ℂ) (hf : ∀ n, MemHE E (f n))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      heNormSq E (fun z ↦ f m z - f n z) ≤ ENNReal.ofReal ε) :
    ∃ g : ℂ → ℂ, MemHE E g ∧ (∀ z : ℂ, Tendsto (fun n ↦ f n z) atTop (𝓝 (g z))) ∧
      Tendsto (fun n ↦ heNormSq E (fun z ↦ f n z - g z)) atTop (𝓝 0) := by
  sorry

end Inner

end FF
