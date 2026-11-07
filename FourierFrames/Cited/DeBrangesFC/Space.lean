import FourierFrames.Cited.DeBrangesFC.Analytic

/-!
# P4, Part C: `H(E)` for `E ∈ \overline{HB}` with real zeros

See `blueprint/P4_DeBrangesFC.md`, §1.3.  `h0`-free replacements of the P3 `Space.lean` lemmas
that P4 needs (P3 assumes `∀ x, E x ≠ 0`), through the extension `divExt E f` of `f/E`.  No inner
product space structure on `H(E)` and no completeness of `H(E)` are needed.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

section HE

variable {E : ℂ → ℂ}

theorem MemHE.heNormSq_lt_top_of_isHB (hE : IsHB E) {f : ℂ → ℂ} (hf : MemHE E f) :
    heNormSq E f < ⊤ := by
  rw [heNormSq_eq_lintegral_divExt hE hf.1]
  exact (isH2Cont_divExt hE hf.1 hf.2.1).lintegral_real_lt_top

theorem MemHE.memLp_div_of_isHB (hE : IsHB E) {f : ℂ → ℂ} (hf : MemHE E f) :
    MemLp (fun t : ℝ ↦ f t / E t) 2 :=
  (isH2Cont_divExt hE hf.1 hf.2.1).memLp_real.ae_eq (divExt_ae_eq hE hf.1)

/-- On a line `Im z = y > 0`, `divExt E f = f/E`. -/
theorem divExt_line {f : ℂ → ℂ} (hE : IsHB E) (hf : Differentiable ℂ f) {y : ℝ} (hy : 0 < y)
    (x : ℝ) : divExt E f ((x : ℂ) + (y : ℂ) * I) =
      f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I) := by
  have him : 0 < ((x : ℂ) + (y : ℂ) * I).im := by simpa using hy
  exact divExt_eq_of_ne hE.1 hf (hE.2.1 _ him)

/-- Line integrals are bounded by the norm: `∫ |f/E (x + iy)|² dx ≤ ‖f‖²_E`. -/
theorem MemHE.lintegral_line_le_of_isHB (hE : IsHB E) {f : ℂ → ℂ} (hf : MemHE E f) {y : ℝ}
    (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ heNormSq E f := by
  have h1 := (isH2Cont_divExt hE hf.1 hf.2.1).lintegral_line_le hy
  rw [← heNormSq_eq_lintegral_divExt hE hf.1] at h1
  refine le_trans (le_of_eq ?_) h1
  exact lintegral_congr fun x ↦ by rw [divExt_line hE hf.1 hy]

/-- The norm is bounded by any common bound of the line integrals (Fatou at the boundary). -/
theorem MemHE.heNormSq_le_of_lines_of_isHB (hE : IsHB E) {f : ℂ → ℂ} (hf : MemHE E f)
    {C : ℝ≥0∞} (hC : ∀ y : ℝ, 0 < y →
      ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ C) :
    heNormSq E f ≤ C := by
  rw [heNormSq_eq_lintegral_divExt hE hf.1]
  have hA := isH2Cont_divExt hE hf.1 hf.2.1
  refine lintegral_real_le_of_isH2 hA.1.1 hA.2 fun y hy ↦ ?_
  refine le_trans (le_of_eq ?_) (hC y hy)
  exact lintegral_congr fun x ↦ by rw [divExt_line hE hf.1 hy]

/-- The integrand of `heInner` is `(f/E) conj (g/E)` (also at the real zeros of `E`). -/
theorem heInner_integrand_eq (E f g : ℂ → ℂ) (t : ℝ) :
    f t * conj (g t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) = f t / E t * conj (g t / E t) := by
  by_cases h : E t = 0
  · simp [h]
  · have hc : conj (E t) ≠ 0 := (map_ne_zero _).mpr h
    have : ((‖E t‖ ^ 2 : ℝ) : ℂ) = E t * conj (E t) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this, map_div₀]
    field_simp

theorem integrable_heInner_of_isHB (hE : IsHB E) {f g : ℂ → ℂ} (hf : MemHE E f)
    (hg : MemHE E g) : Integrable fun t : ℝ ↦ f t * conj (g t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) := by
  simp_rw [heInner_integrand_eq E f g]
  exact (hf.memLp_div_of_isHB hE).integrable_mul (hg.memLp_div_of_isHB hE).star

theorem heInner_add_left_of_isHB (hE : IsHB E) {f g k : ℂ → ℂ} (hf : MemHE E f)
    (hg : MemHE E g) (hk : MemHE E k) :
    heInner E (fun z ↦ f z + g z) k = heInner E f k + heInner E g k := by
  unfold heInner
  rw [← integral_add (integrable_heInner_of_isHB hE hf hk) (integrable_heInner_of_isHB hE hg hk)]
  congr 1
  funext t
  ring

theorem heInner_add_right_of_isHB (hE : IsHB E) {f g k : ℂ → ℂ} (hf : MemHE E f)
    (hg : MemHE E g) (hk : MemHE E k) :
    heInner E f (fun z ↦ g z + k z) = heInner E f g + heInner E f k := by
  rw [← heInner_conj_symm, heInner_add_left_of_isHB hE hg hk hf, map_add, heInner_conj_symm,
    heInner_conj_symm]

theorem heInner_self_of_isHB (hE : IsHB E) {f : ℂ → ℂ} (hf : MemHE E f) :
    heInner E f f = (((heNormSq E f).toReal : ℝ) : ℂ) :=
  heInner_self hE hf

/-- Cauchy–Schwarz in `H(E)` (squared form; P3's `norm_heInner_sq_le` without `h0`). -/
theorem norm_heInner_sq_le_of_isHB (hE : IsHB E) {f g : ℂ → ℂ} (hf : MemHE E f)
    (hg : MemHE E g) :
    ‖heInner E f g‖ ^ 2 ≤ (heNormSq E f).toReal * (heNormSq E g).toReal := by
  have hmf := measurable_div_real hE hf.1
  have hmg := measurable_div_real hE hg.1
  have h1 : ‖heInner E f g‖ₑ ≤ ∫⁻ t : ℝ, ‖f t / E t‖ₑ * ‖g t / E t‖ₑ := by
    unfold heInner
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun t ↦ ?_
    rw [heInner_integrand_eq, enorm_mul, ← enorm_norm (conj _), Complex.norm_conj, enorm_norm]
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hmf.enorm.aemeasurable hmg.enorm.aemeasurable
  simp only [Pi.mul_apply] at h2
  have h3 : ‖heInner E f g‖ₑ ^ 2 ≤ heNormSq E f * heNormSq E g := by
    have := ENNReal.pow_le_pow_left (n := 2) (h1.trans h2)
    refine this.trans (le_of_eq ?_)
    rw [mul_pow]
    unfold heNormSq
    congr 1
    · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
  have hfin : heNormSq E f * heNormSq E g ≠ ⊤ :=
    ENNReal.mul_ne_top (hf.heNormSq_lt_top_of_isHB hE).ne (hg.heNormSq_lt_top_of_isHB hE).ne
  rw [enorm_sq_eq_ofReal, ENNReal.ofReal_le_iff_le_toReal hfin, ENNReal.toReal_mul] at h3
  exact h3

/-- Cauchy–Schwarz in `H(E)`. -/
theorem norm_heInner_le_of_isHB (hE : IsHB E) {f g : ℂ → ℂ} (hf : MemHE E f)
    (hg : MemHE E g) :
    ‖heInner E f g‖ ≤ Real.sqrt (heNormSq E f).toReal * Real.sqrt (heNormSq E g).toReal := by
  rw [← Real.sqrt_mul ENNReal.toReal_nonneg, ← Real.sqrt_sq (norm_nonneg (heInner E f g))]
  exact Real.sqrt_le_sqrt (norm_heInner_sq_le_of_isHB hE hf hg)

/-- **Reproducing formula at `w ∈ ℂ₊`** for `E ∈ \overline{HB}` with real zeros (P3
`heInner_kernel_upper_of_isH2Cont` with the extensions of `exists_isH2Cont_of_memHE`). -/
theorem heInner_kernel_upper_of_isHB (hE : IsHB E) {f : ℂ → ℂ} (hf : MemHE E f) {w : ℂ}
    (hw : 0 < w.im) : heInner E f (deBrangesKernel E w) = f w := by
  obtain ⟨A, B, hA, hB, hAu, -, hAB⟩ := exists_isH2Cont_of_memHE hE hf
  refine heInner_kernel_upper_of_isH2Cont hE hE.ae_ne_zero hA hB hAu ?_ ?_ hw
  · filter_upwards [hE.ae_ne_zero] with t ht using (hAB t ht).1
  · filter_upwards [hE.ae_ne_zero] with t ht using (hAB t ht).2

end HE

end FF
