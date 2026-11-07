import FourierFrames.Cited.DeBrangesDE.Kernel

/-!
# P3 — `H(E)` as a Hilbert space of entire functions

See `blueprint/P3_DeBrangesDE.md`, §4.  For `E` strict without real zeros: linear structure,
inner product `heInner`, the evaluation bound `|f(z)|² ≤ K(z,z) ‖f‖²_E` (from Theorem D), the
bound of line integrals by the boundary norm, and **completeness** (`memHE_of_cauchy`), proved
with Fatou's lemma instead of any abstract `L²` machinery.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {E : ℂ → ℂ}

/-! ## 4.1 Linear structure -/

theorem MemHE.add {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    MemHE E (fun z ↦ f z + g z) := by
  sorry

theorem MemHE.sub {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    MemHE E (fun z ↦ f z - g z) := by
  sorry

theorem MemHE.const_mul {f : ℂ → ℂ} (hf : MemHE E f) (c : ℂ) : MemHE E (fun z ↦ c * f z) := by
  sorry

/-- A nonzero constant multiple of a function not in `H(E)` is not in `H(E)`. -/
theorem MemHE.of_const_mul {f : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) (h : MemHE E (fun z ↦ c * f z)) :
    MemHE E f := by
  sorry

/-! ## 4.2 Norm and inner product -/

variable (hE : IsStrictHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
include hE h0

theorem MemHE.heNormSq_lt_top {f : ℂ → ℂ} (hf : MemHE E f) : heNormSq E f < ⊤ := by
  sorry

/-- `heInner E f f = ‖f‖²_E` (as a real number). -/
theorem heInner_self {f : ℂ → ℂ} (hf : MemHE E f) :
    heInner E f f = (((heNormSq E f).toReal : ℝ) : ℂ) := by
  sorry

theorem heInner_conj_symm {f g : ℂ → ℂ} :
    conj (heInner E f g) = heInner E g f := by
  sorry

theorem heInner_add_left {f g k : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) (hk : MemHE E k) :
    heInner E (fun z ↦ f z + g z) k = heInner E f k + heInner E g k := by
  sorry

theorem heInner_sub_left {f g k : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) (hk : MemHE E k) :
    heInner E (fun z ↦ f z - g z) k = heInner E f k - heInner E g k := by
  sorry

theorem heInner_smul_left {f k : ℂ → ℂ} (hf : MemHE E f) (hk : MemHE E k) (c : ℂ) :
    heInner E (fun z ↦ c * f z) k = c * heInner E f k := by
  sorry

/-- Parallelogram-type identity `‖f - g‖² = ‖f‖² + ‖g‖² - 2 Re ⟨f, g⟩`. -/
theorem heNormSq_sub {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    (heNormSq E (fun z ↦ f z - g z)).toReal =
      (heNormSq E f).toReal + (heNormSq E g).toReal - 2 * (heInner E f g).re := by
  sorry

/-- Cauchy–Schwarz: `|⟨f, g⟩|² ≤ ‖f‖² ‖g‖²`. -/
theorem norm_heInner_sq_le {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    ‖heInner E f g‖ ^ 2 ≤ (heNormSq E f).toReal * (heNormSq E g).toReal := by
  sorry

/-! ## 4.3 Kernel as an element, evaluation bound -/

/-- Reproducing formula for all `w ∈ ℂ` (Theorem D, both cases). -/
theorem heInner_kernel {f : ℂ → ℂ} (hf : MemHE E f) (w : ℂ) :
    heInner E f (deBrangesKernel E w) = f w := by
  sorry

theorem kernel_diag_re_nonneg (w : ℂ) : 0 ≤ (deBrangesKernel E w w).re := by
  sorry

theorem kernel_diag_im (w : ℂ) : (deBrangesKernel E w w).im = 0 := by
  sorry

/-- `‖K_w‖² = K(w, w)`. -/
theorem heNormSq_kernel (w : ℂ) :
    (heNormSq E (deBrangesKernel E w)).toReal = (deBrangesKernel E w w).re := by
  sorry

/-- `⟨K_w, K_z⟩ = K(w, z)`. -/
theorem heInner_kernel_kernel (w z : ℂ) :
    heInner E (deBrangesKernel E w) (deBrangesKernel E z) = deBrangesKernel E w z := by
  sorry

/-- **Evaluation bound**: `|f(z)|² ≤ K(z,z) ‖f‖²_E`. -/
theorem norm_sq_le_kernel_mul {f : ℂ → ℂ} (hf : MemHE E f) (z : ℂ) :
    ‖f z‖ ^ 2 ≤ (deBrangesKernel E z z).re * (heNormSq E f).toReal := by
  sorry

/-! ## 4.4 Line integrals and completeness -/

/-- `∫ |f/E (x + iy)|² dx ≤ ‖f‖²_E` and the same for `f^*`. -/
theorem MemHE.lintegral_line_le {f : ℂ → ℂ} (hf : MemHE E f) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ heNormSq E f ∧
    ∫⁻ x : ℝ, ‖fstar f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤
      heNormSq E f := by
  sorry

/-- `heNormSq E (fstar f) = heNormSq E f` (symmetry `‖f^*‖ = ‖f‖`). -/
theorem heNormSq_fstar {f : ℂ → ℂ} (hf : MemHE E f) : heNormSq E (fstar f) = heNormSq E f := by
  sorry

/-- **Completeness of `H(E)`**: a sequence in `H(E)` that is Cauchy for `‖·‖_E` converges in norm
and locally uniformly to an element of `H(E)`. -/
theorem memHE_of_cauchy (f : ℕ → ℂ → ℂ) (hf : ∀ n, MemHE E (f n))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      heNormSq E (fun z ↦ f m z - f n z) ≤ ENNReal.ofReal ε) :
    ∃ g : ℂ → ℂ, MemHE E g ∧ (∀ z : ℂ, Tendsto (fun n ↦ f n z) atTop (𝓝 (g z))) ∧
      Tendsto (fun n ↦ heNormSq E (fun z ↦ f n z - g z)) atTop (𝓝 0) := by
  sorry

end FF
