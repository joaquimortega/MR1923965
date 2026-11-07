# P5 — logarithm of distance to a bounded-gap separated grid

Target: `FourierFrames/Cited/Pavlov/LogDistance.lean`.
Inputs: `FF.Pavlov.Grid Γ`; elementary BMO algebra in `BMO.lean`.
No further Pavlov assumption is used.

## Mathematical proof and constants

Write q = g.lower > 0 and D = g.upper >= q. Let d(x) = infDist x Γ.
On the closed Voronoi cell of γ_k, d(x)=|x-γ_k|; ties at cell
endpoints cause no ambiguity. Thus d <= D/2, d vanishes precisely on Γ,
and Γ is countable, hence null. The logarithm is measurable. At a node γ,
the nearest node remains γ on (γ-q/2,γ+q/2). Away from nodes d is
continuous positive. Consequently log d is locally integrable: use the
local equality with the translated logarithm near a node and continuity
at every other point. Mathlib's `intervalIntegrable_log'` provides
integrability of the translated logarithm across its single singularity.

For L=b-a >= q/8 take comparison constant 0. Each cell integral of
|log d| is bounded by
J = 2 integral_{0}^{D/2} |log t| dt < infinity.
Cells meeting [a,b] have centers in [a-D/2,b+D/2], so their number is at
most (L+D)/q+1. Summing over these finitely many cells gives
L^{-1} integral_[a,b] |log d| <= J (1/q+8D/q^2+8/q).
Closed cell overlaps are singletons and hence have measure zero.

For L<q/8 there are two cases. If no node lies within distance 2L of
[a,b], then d>=2L on the interval. Since d is 1-Lipschitz, its maximum
is at most 3/2 times its minimum. Comparing with log d(a) gives
mean oscillation <= 2 log(3/2).

Otherwise a node γ is within distance 2L of [a,b]. Every point of the
interval is at distance <=3L<q/2 from γ; separation forces γ to be its
nearest node. Compare log|x-γ| with log L. After x=a+Ls the integral is
L integral_0^1 |log|s-c|| ds, where c=(γ-a)/L belongs to [-2,3].
This is at most integral_{-3}^{3}|log|u||du, a finite absolute constant.
`meanOsc_le_twice_comparison` completes both cases.

## Planned Lean public signatures

```lean
namespace FF.Pavlov
variable {Γ : Set ℝ}
theorem Grid.infDist_eq_abs_sub (g : Grid Γ) {k : ℤ} {x : ℝ}
    (hx : x ∈ cell g k) : Metric.infDist x Γ = |x-g.point k|
theorem Grid.countable (g : Grid Γ) : Γ.Countable
theorem Grid.ae_not_mem (g : Grid Γ) : ∀ᵐ x : ℝ, x ∉ Γ
theorem Grid.locallyIntegrable_log_infDist (g : Grid Γ) :
    LocallyIntegrable (fun x ↦ Real.log (Metric.infDist x Γ))
theorem Grid.memBMO_log_infDist (g : Grid Γ) :
    FF.MemBMO (fun x ↦ Real.log (Metric.infDist x Γ))
```

## Boundary transfer

CellBounds supplies an epsilon>0 and C with, on each cell and away from
its central node,

|log‖G(x)‖ - log‖G(x+i epsilon)‖ - log|x-γ_k|| <= C.

The factor sqrt((x-γ_k)^2+epsilon^2) lies between epsilon and
sqrt(D^2/4+epsilon^2); these constants are absorbed in C. Replace the
cell distance by infDist using the first lemma and discard Γ using its
countability. Entirety ensures local integrability of log‖G‖ (Mathlib
`MeromorphicOn.intervalIntegrable_log_norm`). The difference with the
shifted logarithm and log distance is locally integrable and a.e bounded.
Then `memBMO_add_ae_bounded`, `memBMO_add`, and `memBMO_congr_ae` give

```lean
theorem memBMO_boundary_log_of_cell_comparison
    (g : Grid Γ) (G : ℂ → ℂ) (ε C : ℝ)
    (hboundary : LocallyIntegrable (fun x : ℝ ↦ Real.log ‖G x‖))
    (hshift : FF.MemBMO (fun x : ℝ ↦ Real.log ‖G ((x:ℂ)+(ε:ℂ)*I)‖))
    (hcmp : ∀ k x, x ∈ cell g k → x ≠ g.point k →
      |Real.log ‖G x‖ - Real.log ‖G ((x:ℂ)+(ε:ℂ)*I)‖ -
        Real.log |x-g.point k|| ≤ C) :
    FF.MemBMO (fun x : ℝ ↦ Real.log ‖G x‖)
```

The boundary transfer has a genuine dependence on the full log-distance
BMO theorem. Proving local integrability or an integral estimate with an
extra undischarged assumption does not finish this module.

## Implemented large-interval module

`LogDistanceLarge.lean` imports `LogDistanceCore` and `BMO`, and proves:

```lean
theorem Grid.exists_cell_cover (g : Grid Γ) {a b : ℝ} (hab : a < b) :
  ∃ m n : ℤ, m ≤ n ∧
    Set.Icc a b ⊆ ⋃ k ∈ Finset.Icc m n, cell g k ∧
    ((n-m+1 : ℤ) : ℝ) ≤ (b-a)/g.lower+2

theorem Grid.exists_large_interval_log_infDist_bound (g : Grid Γ) :
  ∃ K : ℝ, ∀ a b : ℝ, a < b → g.lower/8 ≤ b-a →
    (b-a)⁻¹ * (∫ x in a..b, |Real.log (Metric.infDist x Γ)|) ≤ K
```

The implementation improves the earlier center-count estimate: choose the cells of a and b. Their full
intermediate cells have length at least q, so the total number is at most `(b-a)/q+2`, independent of D.
Define `edge k=(γ_(k-1)+γ_k)/2`. The sequence `edge k-q*k` is monotone, which gives this count directly.
Consecutive cell integrals telescope using the natural-index interval integral sum theorem. Each cell
contributes at most `J=∫[-D/2,D/2]|log t|`, by translation and monotonicity of nonnegative integrals.
Thus `K=17J/q` works when `b-a≥q/8`. All integrability follows from the proved local-integrability theorem
in Core and the standard integrability of the logarithm. No disjointness assumption or totalized divergent
integral is used. `Grid.exists_cell_cover` also supplies the finite cover needed by the A2 transfer module.

Validation: `lake build FourierFrames.Cited.Pavlov.LogDistanceLarge` passes cleanly. Both public existence
results above have only `propext`, `Classical.choice`, and `Quot.sound` in their axiom reports.

## Implemented interfaces and review

The root independently reviewed and approved the two interval size cases and
explicit constants. The Cardinal/CellBounds implementer independently checked
and approved the Grid/cover interfaces and the nearest-node argument.

Implementation is split into:

* `LogDistanceCore.lean`: nearest-node formula, countable exceptional set,
  cell integrability, three-cell local integrability, far-interval estimate,
  and nearest-node reduction on short intervals.
* `LogSingularity.lean`: `log_singularity_comparison` with comparison constant
  `logSingularityBound = integral_[-4,4] |log |u||`; its local integrability
  lemma includes the singular point.
* `LogDistanceLarge.lean`: the large interval estimate with the sharper
  constant recorded above.
* `LogDistanceTransfer.lean`: BMO algebra transfer, plus local integrability
  of an entire function's boundary logarithmic modulus. The latter follows
  by restricting complex analyticity to the real axis and applying Mathlib's
  meromorphic logarithm integrability theorem.
* `LogDistance.lean`: `Grid.memBMO_log_infDist`,
  `memBMO_boundary_log_of_cell_comparison`, and
  `exists_boundary_log_BMO_transfer`.

The final distance BMO constant is
`max (2*K) (max (2*log 2) (2*logSingularityBound))`, where K is supplied by
`Grid.exists_large_interval_log_infDist_bound`. No positivity assumption
on K is needed: each applicable branch bounds its own mean oscillation.
The final cardinal transfer has no local-integrability assumption left:

```lean
theorem exists_boundary_log_BMO_transfer (g : Grid Γ) (d : CardinalData Γ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < g.lower/8 ∧
      (MemBMO (fun x : ℝ ↦ Real.log ‖d.G ((x:ℂ)+(ε:ℂ)*I)‖) →
        MemBMO (fun x : ℝ ↦ Real.log ‖d.G x‖))
```

Validation: `lake build FourierFrames.Cited.Pavlov.LogDistance` completed
successfully with 9126 jobs and no warnings. The axiom audit of
`Grid.memBMO_log_infDist` and `exists_boundary_log_BMO_transfer` reports only
`propext`, `Classical.choice`, and `Quot.sound`.
