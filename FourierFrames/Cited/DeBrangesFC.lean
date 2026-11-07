import FourierFrames.Cited.DeBrangesFC.Kernel

/-!
# P4 — de Branges' Theorems C and F

See `blueprint/P4_DeBrangesFC.md`.  Scaffold: lemma proofs are `sorry`, definitions are real, and
the assembly `theoremC_holds` is written from the lemmas.

**Part C** (Theorem 23) goes through P3 (`Cited/DeBrangesDE`):
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

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The span of the kernel vectors at points of the upper half-plane. -/
def kernelSpan (k : ℂ → H) : Submodule ℂ H :=
  Submodule.span ℂ (k '' UHP)

variable {ι : H →ₗ[ℂ] (ℂ → ℂ)}

/-! `DBAxioms`, `IsKernelFamily`, `kernelE` and C.1–C.8 are in `DeBrangesFC/Kernel.lean`. -/

/-! ### C.9–C.14 `H = H(E)` isometrically (RKHS uniqueness) -/

/-- C.9 `K(w, ·) = ι (k w) ∈ H(E)` for nonreal `w` (P3 `memHE_deBrangesKernel_of_isHB`). -/
theorem memHE_kernel (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) {w : ℂ}
    (hw : w.im ≠ 0) : MemHE (kernelE ι k) (ι (k w)) := by
  sorry

/-- C.10 The span of the kernels at `ℂ₊` is mapped into `H(E)`. -/
theorem memHE_of_mem_kernelSpan (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k)
    {x : H} (hx : x ∈ kernelSpan k) : MemHE (kernelE ι k) (ι x) := by
  sorry

/-- C.10 If `ι h ∈ H(E)`, then `⟨ι h, ι x⟩_E = ⟪x, h⟫` for `x` in the span of the kernels
(reproducing formula in `H(E)` and in `H`; induction on the span in the second slot). -/
theorem heInner_iota_of_mem_kernelSpan (hax : DBAxioms ι) {k : ℂ → H}
    (hk : IsKernelFamily ι k) {h : H} (hh : MemHE (kernelE ι k) (ι h)) {x : H}
    (hx : x ∈ kernelSpan k) : heInner (kernelE ι k) (ι h) (ι x) = ⟪x, h⟫_ℂ := by
  sorry

/-- C.10 `ι` is isometric on the span. -/
theorem heNormSq_iota_of_mem_kernelSpan (hax : DBAxioms ι) {k : ℂ → H}
    (hk : IsKernelFamily ι k) {x : H} (hx : x ∈ kernelSpan k) :
    heNormSq (kernelE ι k) (ι x) = ENNReal.ofReal (‖x‖ ^ 2) := by
  sorry

/-- C.11 The span of the kernels at `ℂ₊` is dense in `H` (its orthogonal complement is `0`). -/
theorem kernelSpan_topologicalClosure (hax : DBAxioms ι) {k : ℂ → H}
    (hk : IsKernelFamily ι k) : (kernelSpan k).topologicalClosure = ⊤ := by
  sorry

theorem exists_seq_kernelSpan (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k)
    (h : H) : ∃ x : ℕ → H, (∀ n, x n ∈ kernelSpan k) ∧ Tendsto x atTop (𝓝 h) := by
  sorry

/-- C.12 `ι` maps `H` into `H(E)` contractively (Fatou on lines along a sequence of the span). -/
theorem memHE_iota (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) (h : H) :
    MemHE (kernelE ι k) (ι h) ∧ heNormSq (kernelE ι k) (ι h) ≤ ENNReal.ofReal (‖h‖ ^ 2) := by
  sorry

/-- C.13 `ι : H → H(E)` is isometric (`‖h‖² = lim ⟪x_n, h⟫ ≤ ‖ι h‖_E ‖h‖`). -/
theorem heNormSq_iota (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) (h : H) :
    heNormSq (kernelE ι k) (ι h) = ENNReal.ofReal (‖h‖ ^ 2) := by
  sorry

/-- C.14 `ι` is onto `H(E)`: Riesz in `H` for `h ↦ ⟨ι h, f⟩_E`, then the reproducing formula
in `H(E)` and the identity theorem. -/
theorem mem_range_of_memHE (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k)
    {f : ℂ → ℂ} (hf : MemHE (kernelE ι k) f) : f ∈ Set.range ι := by
  sorry

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
