import FourierFrames.Cited.DeBrangesFC.Kernel

/-!
# P4 — de Branges' Theorems C and F

See `blueprint/P4_DeBrangesFC.md`.  **Part C is proved**: `theoremC_holds` depends only on
`propext`, `Classical.choice`, `Quot.sound`.  Part F is deferred (statements only, `sorry`).

**Part C** (Theorem 23) goes through P3 (`Cited/DeBrangesDE`); the proofs are split over
`DeBrangesFC/Analytic.lean` (§1.1–1.2), `DeBrangesFC/Space.lean` (§1.3) and
`DeBrangesFC/Kernel.lean` (C.1–C.8); C.9–C.14 and the assembly are here.
* §C.1–C.4 the reproducing kernel `k` of `H` (Riesz, `K(ζ,ζ) > 0` by iterating (H1), symmetry,
  `K_w^* = K_{w̄}` from (H3));
* §C.5–C.8 the identity obtained from (H1), the explicit `E = √π (z+i) K(i,z)/√K(i,i)`, and
  `ι (k w) = K_E(w, ·)`, `E` strict;
* §RZ real zeros of `E` (they occur): order inequality, the `IsH2Cont` extension `divExt` of
  `f/E`, `h0`-free replacements of P3's `Space.lean` lemmas, and the reproducing formula in `H(E)`
  at `w ∈ ℂ₊`;
* §C.9–C.14 RKHS uniqueness without completeness of `H(E)`: the kernels at `ℂ₊` span a dense
  subspace of `H` on which `ι` is isometric into `H(E)`; Fatou on lines extends `ι` to a
  contraction `H → H(E)`, the reproducing formula upgrades it to an isometry, and Riesz in `H`
  (not a projection in `H(E)`) shows that it is onto.

**Part F** (Theorem 32) is deferred: statements only (with referee R7's correction of F.4).
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace FF

/-- The open upper half-plane. -/
def UHP : Set ℂ := {z : ℂ | 0 < z.im}

/-- `Θ = E^*/E`, the meromorphic inner function attached to `E`. -/
def thetaFn (E : ℂ → ℂ) (z : ℂ) : ℂ := fstar E z / E z

/-! §1.1–1.2 (general helpers, real zeros of `E`, `divExt`) are in `DeBrangesFC/Analytic.lean`. -/

/-! §1.3 (`H(E)` with real zeros, the `_of_isHB` lemmas) is in `DeBrangesFC/Space.lean`. -/

/-! ## Part C: Theorem 23 -/

section PartC

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The span of the kernel vectors at points of the upper half-plane. -/
def kernelSpan (k : ℂ → H) : Submodule ℂ H :=
  Submodule.span ℂ (k '' UHP)

variable {ι : H →ₗ[ℂ] (ℂ → ℂ)}

/-! `DBAxioms`, `IsKernelFamily`, `kernelE` and C.1–C.8 are in `DeBrangesFC/Kernel.lean`. -/

/-! ### C.9–C.14 `H = H(E)` isometrically (RKHS uniqueness) -/

/-- C.9 `K(w, ·) = ι (k w) ∈ H(E)` for nonreal `w` (P3 `memHE_deBrangesKernel_of_isHB`). -/
theorem memHE_kernel (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) {w : ℂ}
    (hw : w.im ≠ 0) : MemHE (kernelE ι k) (ι (k w)) := by
  rw [kernel_eq_deBrangesKernel hax hk hw]
  exact memHE_deBrangesKernel_of_isHB (isStrictHB_kernelE hax hk).1 (Or.inl hw)

/-- C.10 The span of the kernels at `ℂ₊` is mapped into `H(E)`. -/
theorem memHE_of_mem_kernelSpan (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k)
    {x : H} (hx : x ∈ kernelSpan k) : MemHE (kernelE ι k) (ι x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    have hw' : 0 < w.im := hw
    exact memHE_kernel hax hk hw'.ne'
  | zero =>
    rw [map_zero]
    exact memHE_zero
  | add x y _ _ hx hy =>
    rw [map_add]
    exact hx.add hy
  | smul c x _ hx =>
    rw [map_smul]
    exact hx.const_mul c

/-- C.10 If `ι h ∈ H(E)`, then `⟨ι h, ι x⟩_E = ⟪x, h⟫` for `x` in the span of the kernels
(reproducing formula in `H(E)` and in `H`; induction on the span in the second slot). -/
theorem heInner_iota_of_mem_kernelSpan (hax : DBAxioms ι) {k : ℂ → H}
    (hk : IsKernelFamily ι k) {h : H} (hh : MemHE (kernelE ι k) (ι h)) {x : H}
    (hx : x ∈ kernelSpan k) : heInner (kernelE ι k) (ι h) (ι x) = ⟪x, h⟫_ℂ := by
  have hE := (isStrictHB_kernelE hax hk).1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    have hw' : 0 < w.im := hw
    rw [kernel_eq_deBrangesKernel hax hk hw'.ne', heInner_kernel_upper_of_isHB hE hh hw',
      hk w hw'.ne']
  | zero =>
    rw [map_zero, inner_zero_left]
    simp [heInner]
  | add x y hx' hy' hx hy =>
    rw [map_add, inner_add_left, ← hx, ← hy]
    exact heInner_add_right_of_isHB hE hh (memHE_of_mem_kernelSpan hax hk hx')
      (memHE_of_mem_kernelSpan hax hk hy')
  | smul c x _ hx =>
    rw [map_smul, inner_smul_left, ← hx]
    exact heInner_smul_right _ _ c

/-- C.10 `ι` is isometric on the span. -/
theorem heNormSq_iota_of_mem_kernelSpan (hax : DBAxioms ι) {k : ℂ → H}
    (hk : IsKernelFamily ι k) {x : H} (hx : x ∈ kernelSpan k) :
    heNormSq (kernelE ι k) (ι x) = ENNReal.ofReal (‖x‖ ^ 2) := by
  have hE := (isStrictHB_kernelE hax hk).1
  have hx' := memHE_of_mem_kernelSpan hax hk hx
  have h1 := heInner_iota_of_mem_kernelSpan hax hk hx' hx
  rw [heInner_self_of_isHB hE hx'] at h1
  have h2 : (heNormSq (kernelE ι k) (ι x)).toReal = ‖x‖ ^ 2 := by
    have := congrArg Complex.re h1
    rw [Complex.ofReal_re] at this
    rw [this]
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [← h2, ENNReal.ofReal_toReal (hx'.heNormSq_lt_top_of_isHB hE).ne]

/-- C.11 The span of the kernels at `ℂ₊` is dense in `H` (its orthogonal complement is `0`). -/
theorem kernelSpan_topologicalClosure [CompleteSpace H] (hax : DBAxioms ι) {k : ℂ → H}
    (hk : IsKernelFamily ι k) : (kernelSpan k).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro h hh
  refine hax.eq_zero_of_upper fun z hz ↦ ?_
  rw [hk z hz.ne']
  exact (Submodule.mem_orthogonal _ _).mp hh (k z) (Submodule.subset_span ⟨z, hz, rfl⟩)

theorem exists_seq_kernelSpan [CompleteSpace H] (hax : DBAxioms ι) {k : ℂ → H}
    (hk : IsKernelFamily ι k) (h : H) :
    ∃ x : ℕ → H, (∀ n, x n ∈ kernelSpan k) ∧ Tendsto x atTop (𝓝 h) := by
  have hmem : h ∈ closure (kernelSpan k : Set H) := by
    rw [← Submodule.topologicalClosure_coe, kernelSpan_topologicalClosure hax hk]
    trivial
  exact mem_closure_iff_seq_limit.mp hmem

/-- C.12 `ι` maps `H` into `H(E)` contractively (Fatou on lines along a sequence of the span). -/
theorem memHE_iota [CompleteSpace H] (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k)
    (h : H) :
    MemHE (kernelE ι k) (ι h) ∧ heNormSq (kernelE ι k) (ι h) ≤ ENNReal.ofReal (‖h‖ ^ 2) := by
  set E := kernelE ι k with hEdef
  have hE := (isStrictHB_kernelE hax hk).1
  obtain ⟨x, hxS, hxlim⟩ := exists_seq_kernelSpan hax hk h
  have hxE : ∀ n, MemHE E (ι (x n)) := fun n ↦ memHE_of_mem_kernelSpan hax hk (hxS n)
  have hxn : ∀ n, heNormSq E (ι (x n)) = ENNReal.ofReal (‖x n‖ ^ 2) := fun n ↦
    heNormSq_iota_of_mem_kernelSpan hax hk (hxS n)
  have hpt : ∀ z : ℂ, z.im ≠ 0 → Tendsto (fun n ↦ ι (x n) z) atTop (𝓝 (ι h z)) :=
    fun z hz ↦ ((hax.h2 z hz).tendsto h).comp hxlim
  have hnorm : Tendsto (fun n ↦ ENNReal.ofReal (‖x n‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (‖h‖ ^ 2))) :=
    ENNReal.tendsto_ofReal (((continuous_norm.tendsto h).comp hxlim).pow 2)
  have hline : ∀ (F : ℕ → ℂ → ℂ) (G : ℂ → ℂ),
      (∀ n, DifferentiableOn ℂ (F n) {z : ℂ | 0 < z.im}) →
      (∀ z : ℂ, 0 < z.im → Tendsto (fun n ↦ F n z) atTop (𝓝 (G z))) →
      (∀ n (y : ℝ), 0 < y →
        ∫⁻ t : ℝ, ‖F n ((t : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ ENNReal.ofReal (‖x n‖ ^ 2)) →
      ∀ y : ℝ, 0 < y → ∫⁻ t : ℝ, ‖G ((t : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ ENNReal.ofReal (‖h‖ ^ 2) := by
    intro F G hF hFG hb y hy
    refine (lintegral_line_le_liminf hF hy fun t ↦ hFG _ (by simpa using hy)).trans ?_
    calc liminf (fun n ↦ ∫⁻ t : ℝ, ‖F n ((t : ℂ) + (y : ℂ) * I)‖ₑ ^ 2) atTop
        ≤ liminf (fun n ↦ ENNReal.ofReal (‖x n‖ ^ 2)) atTop :=
          liminf_le_liminf (Eventually.of_forall fun n ↦ hb n y hy)
      _ = ENNReal.ofReal (‖h‖ ^ 2) := hnorm.liminf_eq
  have hdiv : ∀ g : ℂ → ℂ, Differentiable ℂ g →
      DifferentiableOn ℂ (fun z ↦ g z / E z) {z : ℂ | 0 < z.im} := fun g hg ↦
    hg.differentiableOn.div hE.1.differentiableOn fun z hz ↦ hE.2.1 z hz
  have h1 := hline (fun n z ↦ ι (x n) z / E z) (fun z ↦ ι h z / E z)
    (fun n ↦ hdiv _ (hax.entire _)) (fun z hz ↦ (hpt z hz.ne').div_const (E z))
    (fun n y hy ↦ (hxn n) ▸ (hxE n).lintegral_line_le_of_isHB hE hy)
  have h2 := hline (fun n z ↦ fstar (ι (x n)) z / E z) (fun z ↦ fstar (ι h) z / E z)
    (fun n ↦ hdiv _ (Differentiable.fstar (hax.entire _)))
    (fun z hz ↦ ((Complex.continuous_conj.tendsto _).comp
      (hpt (conj z) (by simpa using hz.ne'))).div_const (E z))
    (fun n y hy ↦ by
      have := (memHE_fstar (hxE n)).lintegral_line_le_of_isHB hE hy
      rwa [heNormSq_fstar, hxn n] at this)
  have hmem : MemHE E (ι h) :=
    ⟨hax.entire h, ⟨hdiv _ (hax.entire h), Real.toNNReal (‖h‖ ^ 2), h1⟩,
      ⟨hdiv _ (Differentiable.fstar (hax.entire h)), Real.toNNReal (‖h‖ ^ 2), h2⟩⟩
  exact ⟨hmem, hmem.heNormSq_le_of_lines_of_isHB hE h1⟩

/-- C.13 `ι : H → H(E)` is isometric (`‖h‖² = lim ⟪x_n, h⟫ ≤ ‖ι h‖_E ‖h‖`). -/
theorem heNormSq_iota [CompleteSpace H] (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k)
    (h : H) :
    heNormSq (kernelE ι k) (ι h) = ENNReal.ofReal (‖h‖ ^ 2) := by
  have hE := (isStrictHB_kernelE hax hk).1
  obtain ⟨hmem, hle⟩ := memHE_iota hax hk h
  set a := (heNormSq (kernelE ι k) (ι h)).toReal with ha
  have hfin := hmem.heNormSq_lt_top_of_isHB hE
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have ha_le : a ≤ ‖h‖ ^ 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal (sq_nonneg _)] at this
  obtain ⟨x, hxS, hxlim⟩ := exists_seq_kernelSpan hax hk h
  have hbound : ∀ n, ‖⟪x n, h⟫_ℂ‖ ≤ Real.sqrt a * ‖x n‖ := by
    intro n
    rw [← heInner_iota_of_mem_kernelSpan hax hk hmem (hxS n)]
    refine (norm_heInner_le_of_isHB hE hmem (memHE_of_mem_kernelSpan hax hk (hxS n))).trans
      (le_of_eq ?_)
    rw [heNormSq_iota_of_mem_kernelSpan hax hk (hxS n), ENNReal.toReal_ofReal (sq_nonneg _),
      Real.sqrt_sq (norm_nonneg _)]
  have hlim1 : Tendsto (fun n ↦ ‖⟪x n, h⟫_ℂ‖) atTop (𝓝 ‖⟪h, h⟫_ℂ‖) :=
    (hxlim.inner tendsto_const_nhds).norm
  have hlim2 : Tendsto (fun n ↦ Real.sqrt a * ‖x n‖) atTop (𝓝 (Real.sqrt a * ‖h‖)) :=
    hxlim.norm.const_mul _
  have hineq : ‖h‖ ^ 2 ≤ Real.sqrt a * ‖h‖ := by
    have := le_of_tendsto_of_tendsto' hlim1 hlim2 hbound
    rwa [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at this
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0
  have heq : a = ‖h‖ ^ 2 := by
    rcases (norm_nonneg h).eq_or_lt with h0 | hpos
    · rw [← h0] at ha_le ⊢
      have : (0 : ℝ) ^ 2 = 0 := by norm_num
      linarith
    · have h3 : ‖h‖ ≤ Real.sqrt a := by
        by_contra hcon
        push Not at hcon
        nlinarith [Real.sqrt_nonneg a]
      nlinarith [Real.sqrt_nonneg a]
  rw [← heq, ha, ENNReal.ofReal_toReal hfin.ne]

/-- C.14 `ι` is onto `H(E)`: Riesz in `H` for `h ↦ ⟨ι h, f⟩_E`, then the reproducing formula
in `H(E)` and the identity theorem. -/
theorem mem_range_of_memHE [CompleteSpace H] (hax : DBAxioms ι) {k : ℂ → H}
    (hk : IsKernelFamily ι k) {f : ℂ → ℂ} (hf : MemHE (kernelE ι k) f) : f ∈ Set.range ι := by
  set E := kernelE ι k with hEdef
  have hE := (isStrictHB_kernelE hax hk).1
  have hmem : ∀ h, MemHE E (ι h) := fun h ↦ (memHE_iota hax hk h).1
  let Λ : H →ₗ[ℂ] ℂ :=
    { toFun := fun h ↦ heInner E (ι h) f
      map_add' := fun x y ↦ by
        simp only [map_add]
        exact heInner_add_left_of_isHB hE (hmem x) (hmem y) hf
      map_smul' := fun c x ↦ by
        simp only [map_smul, RingHom.id_apply, smul_eq_mul]
        exact heInner_smul_left _ _ c }
  have hΛ : ∀ h, ‖Λ h‖ ≤ Real.sqrt (heNormSq E f).toReal * ‖h‖ := fun h ↦ by
    refine (norm_heInner_le_of_isHB hE (hmem h) hf).trans (le_of_eq ?_)
    rw [heNormSq_iota hax hk h, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
      mul_comm]
  set u : H := (InnerProductSpace.toDual ℂ H).symm (Λ.mkContinuous _ hΛ) with hu
  refine ⟨u, eq_of_eqOn_upper (hax.entire u) hf.1 fun z hz ↦ ?_⟩
  rw [hk z hz.ne', ← inner_conj_symm, hu, InnerProductSpace.toDual_symm_apply,
    LinearMap.mkContinuous_apply]
  change conj (heInner E (ι (k z)) f) = f z
  rw [heInner_conj_symm, kernel_eq_deBrangesKernel hax hk hz.ne',
    heInner_kernel_upper_of_isHB hE hf hz]

end PartC

/-- **Theorem C** (de Branges, Theorem 23). -/
theorem theoremC_holds : TheoremC := by
  intro H _ _ _ ι hinj hent h1 h2 h3 hne
  have hax : DBAxioms ι := ⟨hinj, hent, h1, h2, h3, hne⟩
  obtain ⟨k, hk⟩ := exists_kernel hax
  refine ⟨kernelE ι k, (isStrictHB_kernelE hax hk).1, fun f ↦ ⟨fun hf ↦ ?_, ?_⟩,
    fun h ↦ (heNormSq_iota hax hk h).symm⟩
  · exact mem_range_of_memHE hax hk hf
  · rintro ⟨h, rfl⟩
    exact (memHE_iota hax hk h).1

/-! ## Part F: Theorem 32 (deferred; statements only)

The lemmas take `hD : TheoremD` explicitly (P3's `theoremD_holds` is imported and can be passed).
See `blueprint/P4_DeBrangesFC.md` §2 and §6 for the referee corrections (R7-10…R7-13). -/

section PartF

/-- `μ` embeds `H(E)` isometrically in `L²(μ/|E|²)`. -/
def IsIsometricMeasure (μ : Measure ℝ) (E : ℂ → ℂ) : Prop :=
  ∀ f : ℂ → ℂ, MemHE E f → ∫⁻ t, ‖f t / E t‖ₑ ^ 2 ∂μ = heNormSq E f

/-- The Herglotz transform of `μ`: `g(z) = (−i/π) ∫ (1/(t − z) − t/(1+t²)) dμ(t) + i c`;
`Re g` is the Poisson integral of `μ`. -/
def herglotzG (μ : Measure ℝ) (c : ℝ) (z : ℂ) : ℂ :=
  -(I / Real.pi) * ∫ t : ℝ, (((t : ℂ) - z)⁻¹ - ((t / (1 + t ^ 2) : ℝ) : ℂ)) ∂μ + I * c

variable {μ : Measure ℝ} {E : ℂ → ℂ}

/-- F.1 `∫ dμ/(1+t²) < ∞` (test the isometry on `K(i,·)`; uses `|E(i)| > |E^*(i)|`). -/
theorem isometric_moment (hD : TheoremD) (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0)
    (hμ : IsIsometricMeasure μ E) : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞ := by
  sorry

/-- F.2 Herglotz representation, constructive: `g` is holomorphic with `Re g = P[μ]`. -/
theorem herglotzG_spec (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞) (c : ℝ) :
    DifferentiableOn ℂ (herglotzG μ c) UHP ∧
      ∀ z ∈ UHP, poissonInt μ z ≠ ∞ ∧ (herglotzG μ c z).re = (poissonInt μ z).toReal := by
  sorry

/-- F.3 Pairing of two kernels at zeros of `E^*` in the upper half-plane (formula (67)):
`∫ dμ / ((t - v̄)(t - w)) = 2πi/(w - v̄)`. -/
theorem cauchy_pairing_zero (hD : TheoremD) (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0)
    (hμ : IsIsometricMeasure μ E) {w v : ℂ} (hw : 0 < w.im) (hv : 0 < v.im)
    (hw0 : fstar E w = 0) (hv0 : fstar E v = 0) :
    ∫ t : ℝ, (((t : ℂ) - conj v)⁻¹ * ((t : ℂ) - w)⁻¹) ∂μ = 2 * Real.pi * I / (w - conj v) := by
  sorry

/-- F.4 General pairing of the kernel at a zero `w₀` of `E^*` with `K(z,·)`, `z ∈ ℂ₊`:
`∫ dμ/((t - w̄₀)(t - z))` equals `2πi/(z - w̄₀)` up to an error `≤ ‖Θ(z)‖ · C(w₀)/√Im z`.
(R7-11: only where `‖Θ(z)‖ ≤ 1/2`, which F.5 needs for `P[μ](z) ≤ 3`; F.9 uses it only as
`Im z → ∞`, where `‖Θ(z)‖ ≤ e^{-a Im z}`.) -/
theorem cauchy_pairing_general (hD : TheoremD) (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0)
    (hμ : IsIsometricMeasure μ E) {w₀ : ℂ} (hw₀ : 0 < w₀.im) (hz0 : fstar E w₀ = 0) :
    ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im → ‖thetaFn E z‖ ≤ 1 / 2 →
      ‖∫ t : ℝ, (((t : ℂ) - conj w₀)⁻¹ * ((t : ℂ) - z)⁻¹) ∂μ - 2 * Real.pi * I / (z - conj w₀)‖ ≤
        C * ‖thetaFn E z‖ / Real.sqrt z.im := by
  sorry

/-- F.5 Diagonal estimate (isometry on `K(z,·)`): `|P[μ](z) − 1| ≤ 4 |Θ(z)|` when `|Θ(z)| ≤ 1/2`. -/
theorem poisson_diag_estimate (hD : TheoremD) (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : 0 < z.im) (hθ : ‖thetaFn E z‖ ≤ 1 / 2) :
    |(poissonInt μ z).toReal - 1| ≤ 4 * ‖thetaFn E z‖ := by
  sorry

/-- F.6 (Cauchy–Riemann argument) If `g` is holomorphic on `ℂ₊` and `|Re g − 1| ≤ C e^{−a y}` on
`y ≥ 1`, then there is `c ∈ ℝ` with `|g − 1 − i c| ≤ C' e^{−a' y}` on `y ≥ 2`, for every `a' < a`
(local uniformity in `x` is not needed, uniformity is assumed). -/
theorem exists_imag_limit {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g UHP) {C a : ℝ} (ha : 0 < a)
    (h : ∀ z : ℂ, 1 ≤ z.im → |(g z).re - 1| ≤ C * Real.exp (-(a * z.im))) {a' : ℝ} (ha' : a' < a) :
    ∃ c C' : ℝ, ∀ z : ℂ, 2 ≤ z.im → ‖g z - 1 - I * c‖ ≤ C' * Real.exp (-(a' * z.im)) := by
  sorry

/-- F.7 Factorization of the meromorphic inner function `Θ = E^*/E` (`E` strict, no real zeros):
`Θ = e^{i(az+θ)} B` with `a ≥ 0` and `B` a Blaschke product, together with the Blaschke division
property: a bounded holomorphic `Ψ` vanishing (with multiplicity) where `Θ` does satisfies
`|Ψ| ≤ ‖Ψ‖_∞ |B|`. -/
theorem inner_factorization (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0) :
    ∃ (a θ : ℝ) (B : ℂ → ℂ), 0 ≤ a ∧ DifferentiableOn ℂ B UHP ∧ (∀ z ∈ UHP, ‖B z‖ ≤ 1) ∧
      (∀ z ∈ UHP, thetaFn E z = Complex.exp (I * (a * z + θ)) * B z) ∧
      ∀ (Ψ : ℂ → ℂ) (M : ℝ), DifferentiableOn ℂ Ψ UHP → (∀ z ∈ UHP, ‖Ψ z‖ ≤ M) →
        (∀ z ∈ UHP, thetaFn E z = 0 → analyticOrderAt (thetaFn E) z ≤ analyticOrderAt Ψ z) →
        ∀ z ∈ UHP, ‖Ψ z‖ ≤ M * ‖B z‖ := by
  sorry

/-- F.8 Division lemma: if `Ξ` is holomorphic, `|Ξ| ≤ 1` on `ℂ₊`, vanishes where `Θ` does (with
multiplicity) and decays like `e^{−a' y}` for all `a' < a` (`a` from F.7), then `|Ξ| ≤ |Θ|`. -/
theorem division_lemma (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0) {a θ : ℝ} {B : ℂ → ℂ}
    (hfac : ∀ z ∈ UHP, thetaFn E z = Complex.exp (I * (a * z + θ)) * B z) {Ξ : ℂ → ℂ}
    (hΞ : DifferentiableOn ℂ Ξ UHP) (h1 : ∀ z ∈ UHP, ‖Ξ z‖ ≤ 1)
    (hz : ∀ z ∈ UHP, thetaFn E z = 0 → analyticOrderAt (thetaFn E) z ≤ analyticOrderAt Ξ z)
    (hdec : ∀ a' : ℝ, a' < a → ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im → ‖Ξ z‖ ≤ C * Real.exp (-(a' * z.im))) :
    ∀ z ∈ UHP, ‖Ξ z‖ ≤ ‖thetaFn E z‖ := by
  -- FALSE: see reviews/R10_TheoremC.md (needs 0 ≤ a, ‖B‖ ≤ 1 on ℂ₊ and the Blaschke-division
  -- clause as hypotheses); counterexample E = exp(-iz/2), Θ = e^{iz}, a = θ = 0, B = Θ, Ξ ≡ 1/2.
  sorry

end PartF

/-- **Theorem F** (de Branges, Theorem 32; with `p = 0`). -/
theorem theoremF_holds : TheoremF := by
  sorry

end FF
