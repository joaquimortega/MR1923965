# P5: counting discrepancy from the conjugate Poisson limit

Implementation: `FourierFrames/Cited/Pavlov/CountingBMO.lean`.
Direct imports are `FourierFrames.Landau` and
`FourierFrames.Cited.Pavlov.PoissonBMO`; no `Unconditional` result is imported.
This module does not construct a generating function or assume Pavlov's theorem.
It is the final elementary adapter for the actual boundary convergence supplied
by the separate boundary-phase and dispersion arguments.

For a separated set, `FF.IsSeparated.finite_inter_Ioc` proves finiteness of every
bounded counting interval. The proved `FF.countFn_sub` then identifies
`countFn Γ b-countFn Γ a` with the nonnegative cardinality of `Γ ∩ (a,b]`.
Thus the counting function is monotone. Mathlib's local integrability theorem
for monotone real functions and subtraction of the identity give local
integrability of the counting discrepancy, before any use of a limit theorem.

Suppose positive-height conjugate Poisson transforms of BMO data converge a.e.
to `-π*(countFn Γ x-x)+c`. The existing uniform BMO estimate and pairwise Fatou
limit theorem give BMO for this affine normalization. Subtract the constant
`c` and multiply by `(-π)⁻¹`. Since `π≠0`, BMO algebra recovers the discrepancy.
No condition `y n → 0` is needed in the adapter: positivity and the stated a.e.
convergence suffice. The application will of course establish its convergence
along the desired heights.

The exact interfaces, with proofs omitted only in this Markdown listing, are:

```lean
open MeasureTheory Set Filter Topology
noncomputable section
namespace FF.Pavlov

theorem countFn_monotone {Γ : Set ℝ} (hΓ : IsSeparated Γ) :
    Monotone (countFn Γ) := by sorry

theorem locallyIntegrable_countFn {Γ : Set ℝ} (hΓ : IsSeparated Γ) :
    LocallyIntegrable (countFn Γ) := by sorry

theorem locallyIntegrable_countFn_sub_id {Γ : Set ℝ} (hΓ : IsSeparated Γ) :
    LocallyIntegrable (fun x ↦ countFn Γ x-x) := by sorry

theorem memBMO_countFn_sub_id_of_conjugatePoisson_limit {Γ : Set ℝ}
    (hΓ : IsSeparated Γ) {u : ℝ → ℝ} (hu : MemBMO u) (c : ℝ)
    {y : ℕ → ℝ} (hy : ∀ n, 0 < y n)
    (hlim : ∀ᵐ x : ℝ, Tendsto (fun n ↦ conjugatePoisson u (y n) x) atTop
      (𝓝 (-Real.pi*(countFn Γ x-x)+c))) :
    MemBMO (fun x ↦ countFn Γ x-x) := by sorry

end FF.Pavlov
```

Validation on 2026-11-07: `lake build FourierFrames.Cited.Pavlov.CountingBMO`
passes without warnings. Axiom checks for monotonicity, local integrability of
the discrepancy, and the final limit adapter list only `propext`,
`Classical.choice`, and `Quot.sound`.
