# R14 — End-to-end audit of the Pavlov theorem assembly

Date: 2026-11-07. Reviewer: `sol_poisson`.

## Scope and verdict

Read-only audit of the current proof path ending in
`FourierFrames/Cited/Pavlov.lean`, especially `GeneratingDispersion`,
`CardinalLog`, `NoExponentialDefect`, `BoundaryPhase`, `CountingBMO`, and
its shifted-weight/BMO interfaces. Reviewed actual Lean proofs and their
public statements, rather than only the implementation blueprints.

**Verdict: approved. No critical, major, or minor mathematical defect was
found in the cross-module assembly.** The final target is precisely
`FF.PavlovBMO`, with the original separation and complete interpolation
hypotheses and the original `countFn Γ x-x` conclusion.

The reviewer authored the earlier `LogPoisson.lean` and generic
`Fatou.lean` proofs. Those components are not independently certified by
this review. Their use and hypothesis discharge in the new assembly
were audited independently. Root handles the complete build, kernel
axiom report, and comparator; this review does not substitute for those
checks.

## 1. Inputs are constructed, with no hidden strengthening

`pavlovBMO_holds` constructs both `CardinalData Γ` and `Grid Γ` from the
two original hypotheses, then applies the discrepancy theorem. The
cardinal data retain the exact sampling norm through the proved
unit-modulus phase rotation. Neither data package is an additional
assumption of the final theorem.

The grid's integer enumeration, lower gap, upper gap and exact range
are proved from the generating representation, separation and sampling
relative density. Thus midpoint/gap arguments and the nullness of Γ
are not vacuous enumeration assumptions. The central choice
`γ=g.point 0` has proved membership in Γ and a cardinal value exactly
one. No emptiness or nonemptiness premise is silently added.

No Pavlov theorem/hypothesis is called within the component proofs.
`CountingBMO` imports `Landau` for elementary `countFn_sub`; its use is
only the finite-interval counting identity. It does not invoke a Landau
result conditional on Pavlov, so this import does not introduce logical
circularity.

## 2. Shifted weight and boundary logarithm use aligned data

`boundary_log_bmo` obtains one tuple `(ε,c,C,...)` from
`generating_cell_bounds`. It passes those **same** ε,c,C and the
corresponding shifted bounds to `shifted_A2_of_bounds`. Its logarithmic
comparison then uses the real and shifted bounds from that same tuple.
There is no exchange of unrelated existential heights.

The discrete derivative-weight A₂ estimate is independent of this
particular selected height; the continuous transfer is parameterized by
any supplied valid cell bounds. Consequently its internal proof does
not require a second hidden height alignment.

The A₂ weight is `|G(x+iε)|²`, rather than the generally false
unregularized de Branges weight claim. Positive cell bounds establish
nonvanishing, continuity of its inverse and local integrability. The
half-log identity then yields BMO of the shifted log modulus. The
real/shifted cell comparison explicitly excludes a central node and
proves positivity of every logged factor there. The final boundary
transfer ignores only the proved null node set and supplies local
integrability of the boundary logarithm separately.

## 3. Cardinal logarithms handle real zeros correctly

`CardinalLog` uses the removable normalized quotient, including its
value one at the central node. Its real-entire symmetry includes the
realness of `G'(γ)`. Its upper nonvanishing comes from the exact complex
zero set, not from a totalized quotient computation.

`cardinalUpper=exp(iπz)*cardinal` is entire, zero-free on the open upper
half-plane and bounded there by the PW evaluation estimate. On the real
axis its exponential factor has unit modulus. These facts discharge
all inputs to the generic logarithmic defect theorem.

The real quotient logarithm identity is stated first outside Γ and then
almost everywhere. The exponential identity
`exp(2 cardinalLog)=|cardinal|²` is likewise asserted only a.e.; the proof
uses nonzero cardinal values off Γ. Thus `log 0=0` and `exp 0=1` at the
remaining nodes do not create a false pointwise equality. Square
integrability follows from the genuine PW cardinal norm, so the outer
comparison H² input is established, not assumed.

## 4. The exponential defect is eliminated without a type premise

`GeneratingDispersion` applies the slope theorem to the bounded
normalized cardinal and rewrites its boundary logarithm using exact
unit modulus. The outer comparison and its factorization are applied
to that same boundary datum. The resulting factorization has exactly
the sign and exponential normalization required by
`no_exponential_defect`.

The latter helper uses a real entire sine product with τ=a/2. Both
vertical decay rates a±τ are nonnegative, making the analytic
multiplier bounded. The canonical exponential HB comparison proves the
sine product lies in PW. All its Γ-values vanish; CIS uniqueness
identifies it with zero, while its central derivative is
`q(γ)τ≠0`. There is no assumed smaller exponential type, outer
factorization theorem, or stronger interpolation conclusion hidden in
this contradiction.

Adding back the removed real zero uses the exact logarithmic Poisson
identity and the derivative normalization constant. All upper factors
are proved nonzero. The resulting formula has the correct sign:

    log|G(x+iy)| = πy + P_y[log|G|](x).

For an arbitrary holomorphic logarithm L, zero real part of
`L-S[log|G|]+iπz` on the connected upper half-plane gives one imaginary
constant, yielding the stated complex dispersion formula.

## 5. Counting sign, boundary limits, and BMO conclusion

`BoundaryPhase` proves local limits using logarithms near one, extends
local constancy over connected whole gaps, and treats a simple zero
using its removable derivative quotient. The principal logarithm is
approached from the upper half-plane: its argument tends to π on the
left and zero on the right. Thus the continuous argument drops by π.
The integer midpoint recurrence matches `countFn` exactly, including
its convention at zero. No limit at a node is claimed.

The final assembly correctly computes

    Q_y u(x) = Im L(x+iy) + πx - c₁,

and therefore its boundary limit is
`-π(countFn Γ x-x)+(c₀-c₁)`. The sequence `1/(n+1)` is positive and tends
to zero through positive heights, and convergence is used only off the
proved null set Γ.

`CountingBMO` proves local integrability of the discrepancy directly
from monotonicity of the separated counting function. Uniform
conjugate-Poisson BMO and the center-free a.e.-limit theorem then give
BMO for the displayed affine normalization. Subtracting the constant
and multiplying by `(-π)⁻¹` recover exactly the unchanged discrepancy.
The proof does not assume convergence of interval means, principal-value
Hilbert transforms, or an unproved bounded difference between counting
and its Poisson smoothing.
