import FourierFrames.Defs

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF

/-!
# M05 — Landau's inequality from John–Nirenberg and Pavlov (p. 799)

See `blueprint/M05_Landau.md`.
-/

/-! ## Upstream interface (temporary, replaced by imports at assembly) -/

/-- Corollary 1, strong form (M04, `Corollary1.lean`): the complete interpolating sequence can be
taken separated. -/
theorem corollary1_strong (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE)
    (hF : TheoremF) {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ IsSeparated (Set.range γ) ∧
      IsCompleteInterpolating (Set.range γ) ∧ ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1) := by
  sorry

/-! ## Counting -/

/-- A separated set meets bounded intervals in finite sets. -/
theorem IsSeparated.finite_inter_Ioc {Γ : Set ℝ} (hΓ : IsSeparated Γ) (a b : ℝ) :
    (Γ ∩ Ioc a b).Finite := by
  sorry

/-- `n_Γ(b) - n_Γ(a) = #(Γ ∩ (a, b])` for `a ≤ b`, when `Γ ∩ (a, b]` is finite for all `a, b`. -/
theorem countFn_sub {Γ : Set ℝ} (hfin : ∀ a b : ℝ, (Γ ∩ Ioc a b).Finite) {a b : ℝ}
    (hab : a ≤ b) : countFn Γ b - countFn Γ a = ((Γ ∩ Ioc a b).ncard : ℝ) := by
  sorry

/-- A `q`-separated set has at most `(b - a)/q + 1` points in `(a, b]`. -/
theorem ncard_inter_Ioc_le {Γ : Set ℝ} {q : ℝ} (hq : 0 < q)
    (hΓ : ∀ x ∈ Γ, ∀ y ∈ Γ, x ≠ y → q ≤ |x - y|) {a b : ℝ} (hab : a ≤ b) :
    ((Γ ∩ Ioc a b).ncard : ℝ) ≤ (b - a) / q + 1 := by
  sorry

/-- `n_Λ(b) - n_Λ(a) ≥ n_Γ(b) - n_Γ(a) - 1` when every `[γ_k, γ_{k+1})` contains a point of `Λ`
(p. 799, first display). -/
theorem ncard_Ioc_ge {Λ : Set ℝ} {γ : ℤ → ℝ} (hγ : StrictMono γ)
    (hΛγ : ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1))
    (hfinΛ : ∀ a b : ℝ, (Λ ∩ Ioc a b).Finite) (hfinΓ : ∀ a b : ℝ, (Set.range γ ∩ Ioc a b).Finite)
    (a b : ℝ) :
    ((Set.range γ ∩ Ioc a b).ncard : ℝ) - 1 ≤ ((Λ ∩ Ioc a b).ncard : ℝ) := by
  sorry

/-! ## The oscillation bound from John–Nirenberg -/

/-- **Core of the Claim.** If `h ∈ BMO` has the local growth bound
`|h(b) - h(a)| ≤ K (b - a) + D` (`a ≤ b`), then `|h(b) - h(a)| ≤ A log⁺(b - a) + B`. -/
theorem osc_bound_of_JN (hJN : JohnNirenberg) {h : ℝ → ℝ} (hbmo : MemBMO h) {K D : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hloc : ∀ a b : ℝ, a ≤ b → |h b - h a| ≤ K * (b - a) + D) :
    ∃ A B : ℝ, ∀ a b : ℝ, a < b → |h b - h a| ≤ A * Real.posLog (b - a) + B := by
  sorry

/-- **Claim** (p. 798): Landau's inequality (Theorem B) follows from the John–Nirenberg theorem,
Pavlov's theorem (Theorem A) and Theorem 1: for a separated sampling sequence `Λ`,
`n_Λ(b) - n_Λ(a) ≥ b - a - A log⁺(b - a) - B`. -/
theorem landau_inequality (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE)
    (hF : TheoremF) (hA : PavlovBMO) (hJN : JohnNirenberg)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ A B : ℝ, ∀ a b : ℝ, a < b →
      ENNReal.ofReal (b - a - A * Real.posLog (b - a) - B) ≤ ((Λ ∩ Ioc a b).encard : ℝ≥0∞) := by
  sorry

end FF
