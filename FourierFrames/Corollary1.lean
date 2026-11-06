import FourierFrames.Defs

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF

/-!
# M04 — Corollary 1 and the remark of p. 797

See `blueprint/M04_Sufficiency.md`.
-/

/-! ## Upstream interface (temporary, replaced by imports at assembly) -/

/-! ### M01 (Paley–Wiener toolkit) -/

theorem pwNormSq_ne_top {f : ℂ → ℂ} (hf : MemPW f) : pwNormSq f ≠ ∞ := by
  sorry

theorem pw_norm_sq_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (z : ℂ) :
    ‖f z‖ ^ 2 ≤ Real.exp (2 * Real.pi * |z.im|) * (pwNormSq f).toReal := by
  sorry

theorem MemPW.sub {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) : MemPW (fun z ↦ f z - g z) := by
  sorry

theorem MemPW.comp_sub_ofReal {f : ℂ → ℂ} (hf : MemPW f) (a : ℝ) :
    MemPW (fun z ↦ f (z - a)) := by
  sorry

theorem pwNormSq_comp_sub_ofReal (f : ℂ → ℂ) (a : ℝ) :
    pwNormSq (fun z ↦ f (z - a)) = pwNormSq f := by
  sorry

theorem exists_memPW_eval_ne_zero : ∃ g : ℂ → ℂ, MemPW g ∧ g 0 = 1 := by
  sorry

theorem plancherelPolya (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ Λ : Set ℝ, (∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ |a - b|) →
      ∀ f : ℂ → ℂ, MemPW f → sampleSum Λ f ≤ C * pwNormSq f := by
  sorry

/-- Uniform tails: for `f ∈ PW` and `δ > 0` the tails of the sampling sums over `δ`-separated sets
are small, uniformly over all such sets. -/
theorem plancherelPolya_tail (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) {f : ℂ → ℂ}
    (hf : MemPW f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ Λ : Set ℝ, (∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ |a - b|) →
      sampleSum (Λ ∩ {x : ℝ | R ≤ |x|}) f ≤ ε := by
  sorry

theorem pw_deriv_bound (hPW : PaleyWienerThm) :
    ∃ C : ℝ, ∀ f : ℂ → ℂ, MemPW f → ∀ x : ℝ, ‖deriv f x‖ ^ 2 ≤ C * (pwNormSq f).toReal := by
  sorry

/-! ### M02 (Hermite–Biehler class, phases, `H(E)`) -/

theorem IsHB.mul {E F : ℂ → ℂ} (hE : IsHB E) (hF : IsHB F) : IsHB (fun z ↦ E z * F z) := by
  sorry

theorem IsStrictHB.mul_isHB {E F : ℂ → ℂ} (hE : IsStrictHB E) (hF : IsHB F) :
    IsStrictHB (fun z ↦ E z * F z) := by
  sorry

theorem IsHB.phaseDeriv_nonneg {E : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (x : ℝ) :
    0 ≤ phaseDeriv E x := by
  sorry

theorem IsStrictHB.phaseDeriv_pos {E : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (x : ℝ) : 0 < phaseDeriv E x := by
  sorry

theorem phaseDeriv_mul {E F : ℂ → ℂ} (hE : Differentiable ℂ E) (hF : Differentiable ℂ F)
    (hE0 : ∀ x : ℝ, E x ≠ 0) (hF0 : ∀ x : ℝ, F x ≠ 0) (x : ℝ) :
    phaseDeriv (fun z ↦ E z * F z) x = phaseDeriv E x + phaseDeriv F x := by
  sorry

theorem exists_isPhaseFunction {E : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0) :
    ∃ φ : ℝ → ℝ, IsPhaseFunction E φ ∧ ∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x := by
  sorry

/-- For `E` strict and `F ∈ \overline{HB}`, both without real zeros: the zeros of `EF + E^*F^*`
are the real points of the level set `{φ_E + φ_F ∈ π/2 + πℤ}`. -/
theorem zero_set_eq_phaseLevel {E F : ℂ → ℂ} (hE : IsStrictHB E) (hF : IsHB F)
    (hE0 : ∀ x : ℝ, E x ≠ 0) (hF0 : ∀ x : ℝ, F x ≠ 0) {φE φF : ℝ → ℝ}
    (hφE : IsPhaseFunction E φE) (hφF : IsPhaseFunction F φF) (z : ℂ) :
    E z * F z + fstar E z * fstar F z = 0 ↔
      ∃ x ∈ phaseLevel (fun t ↦ φE t + φF t) (Real.pi / 2), z = (x : ℂ) := by
  sorry

theorem MemHE.mul_isHB {E F f : ℂ → ℂ} (hE : IsHB E) (hF : IsHB F) (hF0 : ∀ x : ℝ, F x ≠ 0)
    (hf : MemHE E f) : MemHE (fun z ↦ E z * F z) (fun z ↦ F z * f z) := by
  sorry

theorem heNormSq_mul {E F : ℂ → ℂ} (f : ℂ → ℂ) (hF0 : ∀ x : ℝ, F x ≠ 0) :
    heNormSq (fun z ↦ E z * F z) (fun z ↦ F z * f z) = heNormSq E f := by
  sorry

theorem HEEqPW.isStrictHB (hPW : PaleyWienerThm) {E : ℂ → ℂ} (hE : IsHB E) (h : HEEqPW E) :
    IsStrictHB E := by
  sorry

theorem HEEqPW.ne_zero_ofReal (hPW : PaleyWienerThm) {E : ℂ → ℂ} (hE : IsHB E) (h : HEEqPW E)
    (x : ℝ) : E x ≠ 0 := by
  sorry

/-- `φ_E'(x) |E(x)|² ≥ c > 0` when `H(E) = PW` (the `≲` half of `φ_E'|E|² ≃ 1`). -/
theorem HEEqPW.phaseDeriv_mul_sq_ge (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (h : HEEqPW E) : ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, c ≤ phaseDeriv E x * ‖E x‖ ^ 2 := by
  sorry

/-- At most one `α` modulo `π` has `e^{iα}E - e^{-iα}E^* ∈ H(E)` (`E` strict). -/
theorem memHE_sAlpha_unique {E : ℂ → ℂ} (hE : IsStrictHB E) {α β : ℝ}
    (h1 : MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z))
    (h2 : MemHE E (fun z ↦ Complex.exp (I * β) * E z - Complex.exp (-(I * β)) * fstar E z)) :
    ∃ k : ℤ, β - α = k * Real.pi := by
  sorry

/-! ### M03 -/

/-- First half of the proof of Theorem 1 (necessity), exported by M03 under this (new) name: a
separated sampling sequence gives `E ∈ \overline{HB}` with `H(E) = PW` and
`‖f‖²_E = ∑_Λ |f(λ)|²` (Theorem C applied to the norm `(∑|f(λ)|²)^{1/2}` on `PW`). -/
theorem exists_HB_of_sampling (hPW : PaleyWienerThm) (hC : TheoremC) {Λ : Set ℝ}
    (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ E : ℂ → ℂ, IsHB E ∧ HEEqPW E ∧ ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Λ f := by
  sorry

/-- **Theorem 1** (p. 795), necessity. -/
theorem theorem1_necessity (hPW : PaleyWienerThm) (hC : TheoremC) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry

/-! ### M04, `Sufficiency.lean` -/

namespace Suff

def Exceptional (E : ℂ → ℂ) (α : ℝ) : Prop :=
  MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z)

theorem eventually_not_exceptional {E : ℂ → ℂ} (hE : IsStrictHB E) :
    ∀ᶠ n : ℕ in atTop, ¬ Exceptional E (Real.pi / 2 + Real.pi / (n + 2)) := by
  sorry

theorem isPhaseFunction_mul {E F : ℂ → ℂ} {φ ψ : ℝ → ℝ} (hφ : IsPhaseFunction E φ)
    (hψ : IsPhaseFunction F ψ) :
    IsPhaseFunction (fun z ↦ E z * F z) (fun x ↦ φ x + ψ x) := by
  sorry

theorem exists_noRealZero_hb {E F : ℂ → ℂ} {Λ : Set ℝ} (hEHB : IsHB E) (hFHB : IsHB F)
    (hzero : ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ)) :
    ∃ G : ℂ → ℂ, IsHB G ∧ (∀ x : ℝ, G x ≠ 0) ∧
      ∀ z : ℂ, E z * G z + fstar E z * fstar G z = 0 → ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry

end Suff

open Suff

theorem HEEqPW.levelSet_separated (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {α : ℝ}
    (hα : ¬ Exceptional E α) : IsSeparated (phaseLevel φ α) := by
  sorry

theorem HEEqPW.levelSet_cis (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {α : ℝ}
    (hα : ¬ Exceptional E α) : IsCompleteInterpolating (phaseLevel φ α) := by
  sorry

theorem HEEqPW.phase_tendsto (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ)
    (hφ' : ∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x) :
    Tendsto φ atTop atTop ∧ Tendsto φ atBot atBot := by
  sorry

/-! ## Enumerating a level set by `ℤ` -/

/-- A continuous increasing bijection `φ` of `ℝ` has level sets `{φ ∈ α + πℤ}` enumerated
increasingly by `ℤ`. -/
theorem exists_levelSet_enum {φ : ℝ → ℝ} (hm : StrictMono φ) (hs : Function.Surjective φ)
    (α : ℝ) : ∃ γ : ℤ → ℝ, StrictMono γ ∧ Set.range γ = phaseLevel φ α := by
  classical
  let e : ℝ ≃o ℝ := hm.orderIsoOfSurjective φ hs
  refine ⟨fun k ↦ e.symm (α + k * Real.pi), ?_, ?_⟩
  · intro j k hjk
    apply e.symm.strictMono
    have := Real.pi_pos
    have : (j : ℝ) < k := by exact_mod_cast hjk
    nlinarith
  · ext x
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      have : φ (e.symm (α + k * Real.pi)) = α + k * Real.pi := e.apply_symm_apply _
      exact this
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply e.injective
      rw [e.apply_symm_apply]
      exact hk.symm

/-- A half-open interval `[u, v)` with `v - u ≥ π` meets every coset `c + πℤ`. -/
theorem exists_mem_Ico_add_int_mul_pi (c u v : ℝ) (h : u + Real.pi ≤ v) :
    ∃ j : ℤ, u ≤ c + j * Real.pi ∧ c + j * Real.pi < v := by
  have hπ := Real.pi_pos
  refine ⟨⌈(u - c) / Real.pi⌉, ?_, ?_⟩
  · have := Int.le_ceil ((u - c) / Real.pi)
    rw [div_le_iff₀ hπ] at this
    linarith
  · have := Int.ceil_lt_add_one ((u - c) / Real.pi)
    have h2 : (⌈(u - c) / Real.pi⌉ : ℝ) * Real.pi < ((u - c) / Real.pi + 1) * Real.pi :=
      mul_lt_mul_of_pos_right this hπ
    have h3 : ((u - c) / Real.pi + 1) * Real.pi = u - c + Real.pi := by field_simp
    linarith

/-! ## Corollary 1 (p. 798) -/

/-- **Corollary 1**, strong form: the complete interpolating sequence `Γ` can be taken
separated (needed by Pavlov's theorem in the Claim). -/
theorem corollary1_strong (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE)
    (hF : TheoremF) {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ IsSeparated (Set.range γ) ∧
      IsCompleteInterpolating (Set.range γ) ∧ ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1) := by
  sorry

/-- **Corollary 1** (p. 798): a separated sampling sequence is "everywhere denser" than some
complete interpolating sequence `Γ = {γ_k}`: every `[γ_k, γ_{k+1})` contains a point of `Λ`. -/
theorem corollary1 (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ IsCompleteInterpolating (Set.range γ) ∧
      ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1) := by
  obtain ⟨γ, h1, -, h3, h4⟩ := corollary1_strong hPW hC hE hF hΛ hs
  exact ⟨γ, h1, h3, h4⟩

/-! ## The remark of p. 797 -/

/-- A complete interpolating sequence is a sampling sequence (bounded inverse of the sampling map
`PW → ℓ²(Λ)`, open mapping theorem). -/
theorem isSampling_of_isCompleteInterpolating (hPW : PaleyWienerThm) {Λ : Set ℝ}
    (hΛ : IsSeparated Λ) (hcis : IsCompleteInterpolating Λ) : IsSampling Λ := by
  sorry

theorem IsHB.rotate {E : ℂ → ℂ} (hE : IsHB E) (θ : ℝ) :
    IsHB (fun z ↦ Complex.exp (I * θ) * E z) := by
  sorry

theorem HEEqPW.rotate {E : ℂ → ℂ} (h : HEEqPW E) (θ : ℝ) :
    HEEqPW (fun z ↦ Complex.exp (I * θ) * E z) := by
  sorry

theorem IsPhaseFunction.rotate {E : ℂ → ℂ} {φ : ℝ → ℝ} (h : IsPhaseFunction E φ) (θ : ℝ) :
    IsPhaseFunction (fun z ↦ Complex.exp (I * θ) * E z) (fun x ↦ φ x - θ) := by
  sorry

/-- The zero set of `E + E^*` for `E` strict without real zeros. -/
theorem zero_set_single {E : ℂ → ℂ} (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0)
    {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) (z : ℂ) :
    E z + fstar E z = 0 ↔ ∃ x ∈ phaseLevel φ (Real.pi / 2), z = (x : ℂ) := by
  sorry

/-- Formula (1) of p. 793 on the real axis: `K_E(x, y) = |E(x)E(y)| sin(φ(y) - φ(x)) /
(π (y - x))` for real `x ≠ y`. -/
theorem deBrangesKernel_real {E : ℂ → ℂ} {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {x y : ℝ}
    (hxy : x ≠ y) :
    deBrangesKernel E x y =
      ((‖E x‖ * ‖E y‖ * Real.sin (φ y - φ x) / (Real.pi * (y - x)) : ℝ) : ℂ) := by
  sorry

/-- The kernels at the points of a complete interpolating sequence are orthogonal:
`K_E(a, b) = 0` for `a ≠ b` in `Λ` (Theorem D, Cauchy–Schwarz and the norm identity). -/
theorem kernel_orthogonal (hPW : PaleyWienerThm) (hD : TheoremD) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {Λ : Set ℝ} (hΛ : IsSeparated Λ)
    (hcis : IsCompleteInterpolating Λ)
    (hnorm : ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Λ f)
    {a b : ℝ} (ha : a ∈ Λ) (hb : b ∈ Λ) (hab : a ≠ b) : deBrangesKernel E a b = 0 := by
  sorry

/-- Completeness: a complete interpolating `Λ` is a full level set of the phase. -/
theorem levelSet_eq_of_cis (hPW : PaleyWienerThm) (hD : TheoremD) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {Λ : Set ℝ} (hΛ : IsSeparated Λ)
    (hcis : IsCompleteInterpolating Λ)
    (hnorm : ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Λ f)
    {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) : ∃ β : ℝ, Λ = phaseLevel φ β := by
  sorry

/-- **Remark** (p. 797): a separated complete interpolating sequence is the zero set of `E + E^*`
for some `E ∈ \overline{HB}` with `H(E) = PW`. -/
theorem completeInterpolating_zero_set (hPW : PaleyWienerThm) (hC : TheoremC) (hD : TheoremD)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hcis : IsCompleteInterpolating Λ) :
    ∃ E : ℂ → ℂ, IsHB E ∧ HEEqPW E ∧ ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry

end FF
