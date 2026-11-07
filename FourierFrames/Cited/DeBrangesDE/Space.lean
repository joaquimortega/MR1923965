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
  refine ⟨hf.1.add hg.1, ?_, ?_⟩
  · exact (hf.2.1.add hg.2.1).congr fun z _ ↦ by simp [add_div]
  · rw [fstar_add]
    exact (hf.2.2.add hg.2.2).congr fun z _ ↦ by simp [add_div]

theorem MemHE.const_mul {f : ℂ → ℂ} (hf : MemHE E f) (c : ℂ) : MemHE E (fun z ↦ c * f z) := by
  refine ⟨hf.1.const_mul c, ?_, ?_⟩
  · exact (hf.2.1.const_mul c).congr fun z _ ↦ by simp [mul_div_assoc]
  · rw [fstar_const_mul]
    exact (hf.2.2.const_mul (conj c)).congr fun z _ ↦ by simp [mul_div_assoc]

theorem MemHE.sub {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    MemHE E (fun z ↦ f z - g z) := by
  refine ⟨hf.1.sub hg.1, ?_, ?_⟩
  · exact (hf.2.1.sub hg.2.1).congr fun z _ ↦ by simp [sub_div]
  · rw [fstar_sub]
    exact (hf.2.2.sub hg.2.2).congr fun z _ ↦ by simp [sub_div]

theorem memHE_zero : MemHE E (fun _ ↦ 0) := by
  have h0 : IsH2Upper (fun _ : ℂ ↦ (0 : ℂ)) :=
    ⟨differentiableOn_const 0, 0, fun y _ ↦ by simp⟩
  refine ⟨differentiable_const 0, h0.congr fun z _ ↦ by simp, h0.congr fun z _ ↦ by simp [fstar]⟩

theorem MemHE.finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, MemHE E (f i)) : MemHE E (fun z ↦ ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (memHE_zero (E := E))
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- A nonzero constant multiple of a function not in `H(E)` is not in `H(E)`. -/
theorem MemHE.of_const_mul {f : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) (h : MemHE E (fun z ↦ c * f z)) :
    MemHE E f := by
  have := h.const_mul c⁻¹
  simpa [inv_mul_cancel_left₀ hc] using this

/-- `f ∈ H(E) ⇒ f^* ∈ H(E)` (the two defining conditions are swapped, `f^{**} = f`). -/
theorem memHE_fstar {f : ℂ → ℂ} (hf : MemHE E f) : MemHE E (fstar f) :=
  ⟨Differentiable.fstar hf.1, hf.2.2, by rw [fstar_fstar]; exact hf.2.1⟩

/-- `‖f^*‖_E = ‖f‖_E` (on `ℝ`, `|f^*(t)| = |f(t)|`). -/
theorem heNormSq_fstar (f : ℂ → ℂ) : heNormSq E (fstar f) = heNormSq E f := by
  unfold heNormSq
  congr 1
  funext t
  have : ‖fstar f t / E t‖ = ‖f t / E t‖ := by
    rw [fstar_ofReal, norm_div, norm_div, Complex.norm_conj]
  rw [← enorm_norm, this, enorm_norm]

/-! ## 4.2 The sesquilinear form -/

section Inner

variable (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)

include hE in
/-- `t ↦ f(t)/E(t)` is measurable for entire `f` (no hypothesis on the real zeros of `E`). -/
theorem measurable_div_real {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Measurable fun t : ℝ ↦ f t / E t := by
  have h1 := hf.continuous
  have h2 := hE.1.continuous
  fun_prop

include hE in
/-- `heInner E f f = ‖f‖²_E` (as a real number; `E` continuous makes the integrand measurable).
(The hypothesis `h0` of the blueprint is not needed: if `‖f‖_E = ∞` both sides are `0`.) -/
theorem heInner_self {f : ℂ → ℂ} (hf : MemHE E f) :
    heInner E f f = (((heNormSq E f).toReal : ℝ) : ℂ) := by
  have hpt : ∀ t : ℝ, f t * conj (f t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) =
      ((‖f t / E t‖ ^ 2 : ℝ) : ℂ) := by
    intro t
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_div, div_pow, Complex.ofReal_div]
  unfold heInner
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_complex_ofReal]
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t ↦ by positivity)
    ((measurable_div_real hE hf.1).norm.pow_const 2).aestronglyMeasurable]
  unfold heNormSq
  congr 1
  refine lintegral_congr fun t ↦ ?_
  rw [enorm_sq_eq_ofReal]

theorem heInner_conj_symm (f g : ℂ → ℂ) : conj (heInner E f g) = heInner E g f := by
  unfold heInner
  rw [← integral_conj]
  congr 1
  funext t
  rw [map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

include hE h0 in
theorem heInner_add_left {f g k : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) (hk : MemHE E k) :
    heInner E (fun z ↦ f z + g z) k = heInner E f k + heInner E g k := by
  unfold heInner
  rw [← integral_add (integrable_heInner hE.1 h0 hf hk) (integrable_heInner hE.1 h0 hg hk)]
  congr 1
  funext t
  ring

include hE h0 in
theorem heInner_sub_left {f g k : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) (hk : MemHE E k) :
    heInner E (fun z ↦ f z - g z) k = heInner E f k - heInner E g k := by
  unfold heInner
  rw [← integral_sub (integrable_heInner hE.1 h0 hf hk) (integrable_heInner hE.1 h0 hg hk)]
  congr 1
  funext t
  ring

include hE h0 in
theorem heInner_sub_right {f g k : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) (hk : MemHE E k) :
    heInner E f (fun z ↦ g z - k z) = heInner E f g - heInner E f k := by
  rw [← heInner_conj_symm, heInner_sub_left hE h0 hg hk hf, map_sub, heInner_conj_symm,
    heInner_conj_symm]

theorem heInner_smul_left (f k : ℂ → ℂ) (c : ℂ) :
    heInner E (fun z ↦ c * f z) k = c * heInner E f k := by
  unfold heInner
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

theorem heInner_smul_right (f k : ℂ → ℂ) (c : ℂ) :
    heInner E f (fun z ↦ c * k z) = conj c * heInner E f k := by
  unfold heInner
  rw [← integral_const_mul]
  congr 1
  funext t
  rw [map_mul]
  ring

include hE h0 in
theorem heInner_sum_left {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {k : ℂ → ℂ}
    (hf : ∀ i ∈ s, MemHE E (f i)) (hk : MemHE E k) :
    heInner E (fun z ↦ ∑ i ∈ s, f i z) k = ∑ i ∈ s, heInner E (f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [heInner]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, MemHE E (f i) := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    simp_rw [Finset.sum_insert ha]
    rw [heInner_add_left hE h0 (hf a (Finset.mem_insert_self a s)) (MemHE.finset_sum s hs) hk,
      ih hs]

include hE h0 in
theorem heInner_sum_right {ι : Type*} (s : Finset ι) {f : ℂ → ℂ} {k : ι → ℂ → ℂ}
    (hf : MemHE E f) (hk : ∀ i ∈ s, MemHE E (k i)) :
    heInner E f (fun z ↦ ∑ i ∈ s, k i z) = ∑ i ∈ s, heInner E f (k i) := by
  rw [← heInner_conj_symm, heInner_sum_left hE h0 s hk hf, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ heInner_conj_symm _ _

include hE h0 in
/-- `‖f - g‖² = ‖f‖² + ‖g‖² - 2 Re ⟨f, g⟩`. -/
theorem heNormSq_sub {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    (heNormSq E (fun z ↦ f z - g z)).toReal =
      (heNormSq E f).toReal + (heNormSq E g).toReal - 2 * (heInner E f g).re := by
  have hfg := hf.sub hg
  have h1 := heInner_self hE hfg
  rw [heInner_sub_left hE h0 hf hg hfg, heInner_sub_right hE h0 hf hf hg,
    heInner_sub_right hE h0 hg hf hg, heInner_self hE hf, heInner_self hE hg,
    ← heInner_conj_symm f g] at h1
  have h2 := congrArg Complex.re h1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.conj_re] at h2
  linarith

include hE h0 in
/-- Cauchy–Schwarz: `|⟨f, g⟩|² ≤ ‖f‖² ‖g‖²`. -/
theorem norm_heInner_sq_le {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    ‖heInner E f g‖ ^ 2 ≤ (heNormSq E f).toReal * (heNormSq E g).toReal := by
  have hmf := measurable_div_real hE hf.1
  have hmg := measurable_div_real hE hg.1
  have h1 : ‖heInner E f g‖ₑ ≤ ∫⁻ t : ℝ, ‖f t / E t‖ₑ * ‖g t / E t‖ₑ := by
    unfold heInner
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun t ↦ ?_
    rw [← enorm_norm, ← enorm_mul, ← enorm_norm (f t / E t * (g t / E t))]
    congr 1
    rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), norm_mul, norm_div, norm_div]
    ring
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
    ENNReal.mul_ne_top (MemHE.heNormSq_lt_top hE.1 h0 hf).ne (MemHE.heNormSq_lt_top hE.1 h0 hg).ne
  rw [enorm_sq_eq_ofReal, ENNReal.ofReal_le_iff_le_toReal hfin, ENNReal.toReal_mul] at h3
  exact h3

include hE h0 in
/-- Continuity of `⟨f, ·⟩`: if `‖gₙ - g‖_E → 0` then `⟨f, gₙ⟩ → ⟨f, g⟩`. -/
theorem tendsto_heInner_right {f g : ℂ → ℂ} {gs : ℕ → ℂ → ℂ} (hf : MemHE E f)
    (hg : MemHE E g) (hgs : ∀ n, MemHE E (gs n))
    (hlim : Tendsto (fun n ↦ heNormSq E (fun z ↦ gs n z - g z)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ heInner E f (gs n)) atTop (𝓝 (heInner E f g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsub : ∀ n, heInner E f (gs n) - heInner E f g =
      heInner E f (fun z ↦ gs n z - g z) := fun n ↦ (heInner_sub_right hE h0 hf (hgs n) hg).symm
  simp_rw [hsub]
  have hbound : ∀ n, ‖heInner E f (fun z ↦ gs n z - g z)‖ ≤
      Real.sqrt ((heNormSq E f).toReal * (heNormSq E (fun z ↦ gs n z - g z)).toReal) :=
    fun n ↦ (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
      (norm_heInner_sq_le hE h0 hf ((hgs n).sub hg))
  have hlim2 : Tendsto (fun n ↦ Real.sqrt ((heNormSq E f).toReal *
      (heNormSq E (fun z ↦ gs n z - g z)).toReal)) atTop (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    have h2 := (h1.const_mul (heNormSq E f).toReal).sqrt
    simpa using h2
  exact squeeze_zero (fun n ↦ norm_nonneg _) hbound hlim2

/-! ## 4.3 Kernels and the evaluation bound -/

include hE h0 in
/-- `‖K_w‖² = K(w, w)`. -/
theorem heNormSq_kernel (w : ℂ) :
    (heNormSq E (deBrangesKernel E w)).toReal = (deBrangesKernel E w w).re := by
  have hK := memHE_deBrangesKernel hE h0 w
  have h1 := heInner_self hE hK
  rw [heInner_kernel hE h0 hK w] at h1
  rw [h1, Complex.ofReal_re]

include hE h0 in
/-- `⟨K_w, K_z⟩ = K(w, z)`. -/
theorem heInner_kernel_kernel (w z : ℂ) :
    heInner E (deBrangesKernel E w) (deBrangesKernel E z) = deBrangesKernel E w z :=
  heInner_kernel hE h0 (memHE_deBrangesKernel hE h0 w) z

include hE h0 in
/-- **Evaluation bound**: `|f(z)|² ≤ K(z,z) ‖f‖²_E`. -/
theorem norm_sq_le_kernel_mul {f : ℂ → ℂ} (hf : MemHE E f) (z : ℂ) :
    ‖f z‖ ^ 2 ≤ (deBrangesKernel E z z).re * (heNormSq E f).toReal := by
  have h1 := norm_heInner_sq_le hE h0 hf (memHE_deBrangesKernel hE h0 z)
  rw [heInner_kernel hE h0 hf z, heNormSq_kernel hE h0 z] at h1
  linarith

include hE h0 in
/-- A function of `H(E)` with `‖f‖_E = 0` vanishes identically. -/
theorem eq_zero_of_heNormSq_eq_zero {f : ℂ → ℂ} (hf : MemHE E f) (h : heNormSq E f = 0) :
    ∀ z, f z = 0 := by
  intro z
  have h1 := norm_sq_le_kernel_mul hE h0 hf z
  rw [h, ENNReal.toReal_zero, mul_zero] at h1
  have h2 : ‖f z‖ ^ 2 = 0 := le_antisymm h1 (by positivity)
  simpa using h2

/-! ## 4.4 Line integrals and completeness -/

include hE h0 in
/-- `∫ |f/E (x + iy)|² dx ≤ ‖f‖²_E` and the same for `f^*` (`IsH2Cont.lintegral_line_le`). -/
theorem MemHE.lintegral_line_le {f : ℂ → ℂ} (hf : MemHE E f) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ heNormSq E f ∧
    ∫⁻ x : ℝ, ‖fstar f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤
      heNormSq E f := by
  obtain ⟨h1, h2⟩ := isH2Cont_of_memHE hE.1 h0 hf
  refine ⟨h1.lintegral_line_le hy, ?_⟩
  rw [← heNormSq_fstar]
  exact h2.lintegral_line_le hy

/-- Fatou's lemma for `‖·‖ₑ²` along a pointwise convergent sequence: if `G_m → g` pointwise and
eventually `∫ ‖G_m‖² ≤ C`, then `∫ ‖g‖² ≤ C`. -/
theorem lintegral_enorm_sq_le_of_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : ℕ → α → ℂ} {g : α → ℂ} (hG : ∀ m, Measurable (G m))
    (hlim : ∀ x, Tendsto (fun m ↦ G m x) atTop (𝓝 (g x))) {C : ℝ≥0∞}
    (hC : ∀ᶠ m in atTop, ∫⁻ x, ‖G m x‖ₑ ^ 2 ∂μ ≤ C) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ≤ C := by
  have hpt : ∀ x, Filter.liminf (fun m ↦ ‖G m x‖ₑ ^ 2) atTop = ‖g x‖ₑ ^ 2 := fun x ↦
    (((ENNReal.continuous_pow 2).tendsto _).comp
      ((continuous_enorm.tendsto _).comp (hlim x))).liminf_eq
  calc ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ∫⁻ x, Filter.liminf (fun m ↦ ‖G m x‖ₑ ^ 2) atTop ∂μ := by
        simp_rw [hpt]
    _ ≤ Filter.liminf (fun m ↦ ∫⁻ x, ‖G m x‖ₑ ^ 2 ∂μ) atTop :=
        lintegral_liminf_le fun m ↦ ((hG m).enorm).pow_const 2
    _ ≤ C := Filter.liminf_le_of_frequently_le' hC.frequently

include hE h0 in
/-- A Cauchy sequence of `H(E)` is uniformly Cauchy on every closed ball (evaluation bound and
the local bound of the kernel). -/
theorem uniformCauchySeqOn_of_cauchy (f : ℕ → ℂ → ℂ) (hf : ∀ n, MemHE E (f n))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      heNormSq E (fun z ↦ f m z - f n z) ≤ ENNReal.ofReal ε) (ρ : ℝ) :
    UniformCauchySeqOn f atTop (Metric.closedBall 0 ρ) := by
  obtain ⟨M, hM⟩ := exists_bound_deBrangesKernel hE.1 ρ
  set M' : ℝ := max M 0 + 1 with hM'
  have hM'pos : 0 < M' := by positivity
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε ^ 2 / (2 * M')) (by positivity)
  refine ⟨N, fun m hm n hn z hz ↦ ?_⟩
  have hz' : ‖z‖ ≤ ρ := by simpa using hz
  have h1 := norm_sq_le_kernel_mul hE h0 ((hf m).sub (hf n)) z
  have h2 : (heNormSq E (fun z ↦ f m z - f n z)).toReal ≤ ε ^ 2 / (2 * M') :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hN m hm n hn)
  have h3 : (deBrangesKernel E z z).re ≤ M' :=
    (Complex.re_le_norm _).trans ((hM z z hz' hz').trans (by
      rw [hM']; have := le_max_left M 0; linarith))
  have h4 : ‖f m z - f n z‖ ^ 2 < ε ^ 2 := by
    calc ‖f m z - f n z‖ ^ 2
        ≤ (deBrangesKernel E z z).re * (heNormSq E (fun z ↦ f m z - f n z)).toReal := h1
      _ ≤ M' * (ε ^ 2 / (2 * M')) := mul_le_mul h3 h2 ENNReal.toReal_nonneg hM'pos.le
      _ < ε ^ 2 := by
        rw [mul_div_assoc', mul_comm 2 M', ← div_div, mul_div_cancel_left₀ _ hM'pos.ne']
        linarith [pow_pos hε 2]
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le h4

include hE h0 in
/-- A Cauchy sequence of `H(E)` converges pointwise to an entire function. -/
theorem exists_limit_of_cauchy (f : ℕ → ℂ → ℂ) (hf : ∀ n, MemHE E (f n))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      heNormSq E (fun z ↦ f m z - f n z) ≤ ENNReal.ofReal ε) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z : ℂ, Tendsto (fun n ↦ f n z) atTop (𝓝 (g z)) := by
  have hunif := uniformCauchySeqOn_of_cauchy hE h0 f hf hc
  have hlim : ∀ z : ℂ, Tendsto (fun n ↦ f n z) atTop
      (𝓝 (limUnder atTop (fun n ↦ f n z))) := by
    intro z
    have hz : z ∈ Metric.closedBall (0 : ℂ) ‖z‖ := by simp
    exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ((hunif ‖z‖).cauchySeq hz))
  refine ⟨fun z ↦ limUnder atTop (fun n ↦ f n z), ?_, hlim⟩
  have hloc : TendstoLocallyUniformlyOn f (fun z ↦ limUnder atTop (fun n ↦ f n z)) atTop
      univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall 0
    exact ((hunif ρ).tendstoUniformlyOn_of_tendsto fun z _ ↦ hlim z).mono hρ
  have hd := hloc.differentiableOn (Eventually.of_forall fun n ↦ (hf n).1.differentiableOn)
    isOpen_univ
  exact differentiableOn_univ.mp hd

include hE h0 in
/-- **Completeness of `H(E)`**: a sequence in `H(E)` that is Cauchy for `‖·‖_E` converges in norm
and pointwise (even locally uniformly) to an element of `H(E)`. -/
theorem memHE_of_cauchy (f : ℕ → ℂ → ℂ) (hf : ∀ n, MemHE E (f n))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      heNormSq E (fun z ↦ f m z - f n z) ≤ ENNReal.ofReal ε) :
    ∃ g : ℂ → ℂ, MemHE E g ∧ (∀ z : ℂ, Tendsto (fun n ↦ f n z) atTop (𝓝 (g z))) ∧
      Tendsto (fun n ↦ heNormSq E (fun z ↦ f n z - g z)) atTop (𝓝 0) := by
  obtain ⟨g, hgd, hlim⟩ := exists_limit_of_cauchy hE h0 f hf hc
  have hEc : Continuous E := hE.1.continuous
  -- norm convergence (Fatou)
  have hnorm : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      heNormSq E (fun z ↦ f n z - g z) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    apply lintegral_enorm_sq_le_of_tendsto (G := fun m (t : ℝ) ↦ (f n t - f m t) / E t)
    · intro m
      exact measurable_div_real hE (f := fun z ↦ f n z - f m z) ((hf n).1.sub (hf m).1)
    · intro t
      exact (tendsto_const_nhds.sub (hlim t)).div_const _
    · filter_upwards [eventually_ge_atTop N] with m hm using hN n hn m hm
  -- a uniform bound for the norms
  obtain ⟨N1, hN1⟩ := hc 1 one_pos
  set B : ℝ≥0∞ := 2 * heNormSq E (f N1) + 2 * ENNReal.ofReal 1 with hB_def
  have hB : B ≠ ⊤ := by
    have := (MemHE.heNormSq_lt_top hE.1 h0 (hf N1)).ne
    rw [hB_def]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) this,
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩
  have hbound : ∀ n ≥ N1, heNormSq E (f n) ≤ B := by
    intro n hn
    have hm1 := (measurable_div_real hE (hf N1).1).enorm.pow_const 2
    have hm2 : Measurable fun t : ℝ ↦ ‖(f n t - f N1 t) / E t‖ₑ ^ 2 :=
      (measurable_div_real hE (f := fun z ↦ f n z - f N1 z)
        ((hf n).1.sub (hf N1).1)).enorm.pow_const 2
    calc heNormSq E (f n)
        ≤ ∫⁻ t : ℝ, (2 * ‖f N1 t / E t‖ₑ ^ 2 + 2 * ‖(f n t - f N1 t) / E t‖ₑ ^ 2) := by
          refine lintegral_mono fun t ↦ ?_
          have := enorm_add_sq_le (f N1 t / E t) ((f n t - f N1 t) / E t)
          rwa [← add_div, add_sub_cancel] at this
      _ = 2 * heNormSq E (f N1) + 2 * heNormSq E (fun z ↦ f n z - f N1 z) := by
          rw [lintegral_add_left (hm1.const_mul 2), lintegral_const_mul _ hm1,
            lintegral_const_mul _ hm2]
          rfl
      _ ≤ B := add_le_add le_rfl (mul_le_mul_right (hN1 n hn N1 le_rfl) 2)
  -- the line integrals of `g/E` and `g^*/E`
  have hline : ∀ y : ℝ, 0 < y →
      ∫⁻ x : ℝ, ‖g ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ B := by
    intro y hy
    apply lintegral_enorm_sq_le_of_tendsto
      (G := fun m (x : ℝ) ↦ f m ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I))
    · intro m
      have := (hf m).1.continuous
      fun_prop
    · intro x
      exact (hlim _).div_const _
    · filter_upwards [eventually_ge_atTop N1] with m hm using
        (MemHE.lintegral_line_le hE h0 (hf m) hy).1.trans (hbound m hm)
  have hline' : ∀ y : ℝ, 0 < y →
      ∫⁻ x : ℝ, ‖fstar g ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ B := by
    intro y hy
    apply lintegral_enorm_sq_le_of_tendsto
      (G := fun m (x : ℝ) ↦ fstar (f m) ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I))
    · intro m
      have := (Differentiable.fstar (hf m).1).continuous
      fun_prop
    · intro x
      exact (((Complex.continuous_conj.tendsto _).comp (hlim _))).div_const _
    · filter_upwards [eventually_ge_atTop N1] with m hm using
        (MemHE.lintegral_line_le hE h0 (hf m) hy).2.trans (hbound m hm)
  have hdiv : ∀ k : ℂ → ℂ, Differentiable ℂ k →
      DifferentiableOn ℂ (fun z ↦ k z / E z) {z : ℂ | 0 < z.im} := fun k hk z hz ↦
    ((hk z).div (hE.1 z) (hE.2.1 z hz)).differentiableWithinAt
  refine ⟨g, ⟨hgd, ⟨hdiv g hgd, B.toNNReal, fun y hy ↦ ?_⟩,
    ⟨hdiv _ (Differentiable.fstar hgd), B.toNNReal, fun y hy ↦ ?_⟩⟩, hlim, ?_⟩
  · rw [ENNReal.coe_toNNReal hB]; exact hline y hy
  · rw [ENNReal.coe_toNNReal hB]; exact hline' y hy
  · rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    by_cases hεtop : ε = ⊤
    · exact ⟨0, fun n _ ↦ hεtop ▸ le_top⟩
    · obtain ⟨N, hN⟩ := hnorm ε.toReal (ENNReal.toReal_pos hε.ne' hεtop)
      refine ⟨N, fun n hn ↦ ?_⟩
      have := hN n hn
      rwa [ENNReal.ofReal_toReal hεtop] at this

end Inner

end FF
