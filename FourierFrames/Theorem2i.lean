
import FourierFrames.Theorem2i.Estimates

/-!
# M08 — Theorem 2 (i)

See `blueprint/M08_Theorem2i.md`.  Construction of the canonical product `f` with zeros
`z_n = r_n e^{-i c d_n / r_n}` (one zero per cell `(t_{n-1}, t_n]` of `ψ`-mass `1`) such that
`|U_ψ - log|f|| ≲ 1` on `Im z ≥ 0`, and application of Corollary 2.

**Warning (see the blueprint, "Issues in the source", §A).**  The estimate of the cells at
distance `≲ d_n` from `z` needs the local density bound `ψ' ≲ 1/d_n` on `[t_{n-1}, t_n]`
(`DensBound`), which is *not* implied by the hypotheses of `theorem2_i`.  All lemmas below that
need it carry `hK : DensBound ψ t K`.  `theorem2_i_of_regular` is the provable statement;
`theorem2_i` (identical to `comparator/statements.lean`) has no honest proof from the paper's
argument unless `DensBound` can be derived or added to the hypotheses.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

/-! ## §6. Theorem 2 (i) -/

/-- The data of `IsLogRegularPartitionWithDensity`: a partition with `RegData` and `DensBound`. -/
theorem RegData.of_isLogRegularPartitionWithDensity {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ)
    (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0) (hreg : IsLogRegularPartitionWithDensity ψ) :
    ∃ (t : ℕ → ℝ) (C M K : ℝ), RegData ψ t C M ∧ DensBound ψ t K := by
  sorry

/-- The provable version of Theorem 2 (i), with the extra local regularity `DensBound`
(`RegData` is produced from the hypotheses of `theorem2_i` by `RegData.of_isLogRegularPartition`). -/
theorem theorem2_i_of_regular (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ} (h : RegData ψ t C M) (hK : DensBound ψ t K) :
    IsSampling (LambdaPsi ψ) := by
  sorry

/-- An eventually nonincreasing `ψ'` gives the local density bound: on `[t_{n-1}, t_n]`,
`ψ' ≤ ψ'(t_{n-1}) ≤ 1/d_{n-1} ≤ C/d_n` for the cells beyond `X` (the previous cell has mass `1`
and `ψ' ≥ ψ'(t_{n-1})` on it), and `ψ'` is bounded on the finitely many cells before `X`. -/
theorem RegData.densBound_of_antitoneOn (h : RegData ψ t C M)
    (hmono : ∃ X : ℝ, AntitoneOn (deriv ψ) (Set.Ici X)) : ∃ K : ℝ, DensBound ψ t K := by
  sorry

/-- **Theorem 2 (i)**, in the form its proof gives (p. 802): if `ψ = 0` on `(-∞, 0]` and `ψ` induces
a logarithmically regular partition on whose cells `ψ' ≲ 1/d_n`, then `Λ(ψ)` is sampling for `PW`.
The hypothesis `ψ'(x) = 1/O(x)` of the printed statement is not needed (NOTEBOOK N-22, N-26). -/
theorem theorem2_i_of_densityBound (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hreg : IsLogRegularPartitionWithDensity ψ) :
    IsSampling (LambdaPsi ψ) := by
  sorry

/-- **Theorem 2 (i)** (p. 801), identical to `comparator/statements.lean`.  The paper's argument
needs `DensBound`, which follows from `hmono` (NOTEBOOK N-22). -/
theorem theorem2_i (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x → c / x ≤ deriv ψ x)
    (hreg : IsLogRegularPartition ψ) (hmono : ∃ X : ℝ, AntitoneOn (deriv ψ) (Set.Ici X)) :
    IsSampling (LambdaPsi ψ) := by
  sorry

end FF
