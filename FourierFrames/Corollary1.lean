import FourierFrames.Theorem1.Necessity
import FourierFrames.Theorem1.Sufficiency

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF

open Suff

/-!
# M04 — Corollary 1 and the remark of p. 797

See `blueprint/M04_Sufficiency.md`.
-/

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

theorem HEEqPW.rotate {E : ℂ → ℂ} (h : HEEqPW E) (θ : ℝ) :
    HEEqPW (fun z ↦ Complex.exp (I * θ) * E z) := by
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
