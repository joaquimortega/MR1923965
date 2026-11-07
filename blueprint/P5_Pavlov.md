# P5 — Pavlov's theorem, BMO necessity (`PavlovBMO`)

**Completed, 2026-11-07.** `FF.pavlovBMO_holds : FF.PavlovBMO` is proved in
`FourierFrames/Cited/Pavlov.lean`, with helpers in `FourierFrames/Cited/Pavlov/`.
The statement in `Defs.lean` is unchanged:

> A separated complete interpolating sequence Γ for PW has
> `x ↦ countFn Γ x - x` in `FF.MemBMO`.

This is the BMO necessity consequence of Theorem A used by the paper, not the
full Pavlov iff criterion or its Helson–Szegő decomposition. It discharges the
last cited hypothesis of `landau_inequality_unconditional`. The original
conditional statements and historical wrappers remain available.

The implementation contains 6761 lines in 37 project files, including the root
module. [`P5_Statements.md`](P5_Statements.md) indexes 339 public interfaces
across those modules. Its dependencies include the already proved Paley–Wiener and de Branges
C/D/E results, the project's John–Nirenberg theorem, Mathlib, and a pinned subset
of Tau Ceti. It does not depend on `Unconditional.lean` or assume `PavlovBMO`
in a helper.

## 1. Cardinal functions, a grid, and local comparisons

Retain the exact sampling norm identity in the de Branges representation of a
complete interpolating sequence. Rotating its Hermite–Biehler function produces
a real entire generator G with exactly the simple real zeros Γ. Its normalized
cardinals use the removable quotient `dslope G γ / deriv G γ`, belong to PW,
and satisfy uniform norm and finite synthesis bounds. Separation and sampling
provide a strictly increasing integer enumeration with lower and upper gap
bounds, and a partition into midpoint cells.

A rectangle Harnack estimate applies to zero-free cardinals on their cells.
It uses a fixed domain and a target-dependent complex affine map, so the
constant is uniform even when the actual interval length varies. This yields
uniform comparisons between the generating function at a small positive height
and its derivatives at the nodes, as well as the corresponding real-axis
comparison with the factor `|x-γ|`.

Files: `Cardinal`, `Harnack`, `CellBounds`. Details:
[`P5_Cardinal.md`](P5_Cardinal.md), [`P5_Harnack.md`](P5_Harnack.md).

## 2. Finite weighted tests and boundary BMO

Finite cardinal synthesis and shifted Plancherel–Pólya estimates bound a
weighted Cauchy matrix. Testing separated consecutive blocks in both directions
and applying finite Cauchy–Schwarz yields a discrete A₂ inequality for the
positive weights `|G'(γ)|²`. Cell comparisons transfer it to the positive
continuous weight `|G(x+iε)|²`, including intervals smaller than one cell.

Elementary logarithm inequalities imply BMO of the shifted logarithmic modulus.
The difference between the real and shifted logarithms is the cell log-distance
function plus a uniformly bounded error. The log-distance has a direct uniform
BMO estimate on short and long intervals. Thus `u(x)=log|G(x)|` belongs to BMO;
its values at the countable zero set do not affect this conclusion.

Files: `Weights`, `WeightTransfer`, `BoundaryWeight`, `BMO`, `LogDistance*`.
Details: [`P5_A2.md`](P5_A2.md), [`P5_BMO.md`](P5_BMO.md),
[`P5_LogDistance.md`](P5_LogDistance.md).

## 3. Weighted Schwarz integrals and exact dispersion

Dyadic interval growth of BMO means proves integrability of `u(t)/(1+t²)`.
The regularized Schwarz integral is holomorphic in the upper half-plane, with
real part the Poisson integral and imaginary part the normalized conjugate
Poisson integral. Its two kernel terms are kept together, avoiding subtraction
of divergent integrals.

For the bounded zero-free upper-half-plane function
`A(z)=exp(iπz)*cardinal G γ₀ z`, compact maximum-principle comparison proves
`log|A|≤P[log|A|]`. It compares squared holomorphic moduli and continuous
clipped boundary data, so real zeros cause no invalid finite-logarithm
continuity assumption. Finite-order analytic factorization and the exact
Poisson formula for `log|t-a|` cancel each boundary singularity, making the
nonnegative harmonic defect continuous and zero on the real axis.

Odd harmonic reflection, solved locally by the disk Dirichlet problem, and the
existing entire Pick-function classification identify the defect as `a Im z`,
`a≥0`. The associated outer comparison is in H² by Jensen and Tonelli. If
`a>0`, multiplying a cardinal by a small sine produces a nonzero PW function
vanishing on Γ, contradicting complete-interpolation uniqueness. Hence a=0.
This gives the exact upper-half-plane logarithmic dispersion identity for G;
no general Cartwright factorization theorem is assumed.

Files: `BMOIntervalGrowth`, `BMOLogIntegrable`, `Schwarz`, `SchwarzBoundary`,
`LogPoissonKernel`, `LogClipping`, `LogPoisson`, `LogPoissonBoundary`,
`HarmonicReflection`, `OuterComparison`, `CardinalLog`, `NoExponentialDefect`,
`GeneratingDispersion`. Details: [`P5_Dispersion.md`](P5_Dispersion.md) and its
specialized `P5_*` implementation notes.

## 4. Uniform conjugate-Poisson BMO and the boundary staircase

The conjugate-Poisson kernel is realized by an L² Fourier multiplier with norm
at most one. A localized decomposition, John–Nirenberg L² oscillation, and a
dyadic far-field estimate give BMO bounds independent of the positive height.
The project proves the kernel realization and extends the localized estimate
to arbitrary BMO data. Its direct near/far argument does not invoke the
Calderón–Zygmund endpoint theorem that is also present in the vendored subset.

An upper logarithm of G has boundary imaginary part
`-π countFn Γ x + constant` away from Γ. Exact dispersion consequently
identifies the conjugate-Poisson boundary limit as
`-π(countFn Γ x-x)+constant`. Pairwise mean oscillation and Fatou pass the
uniform BMO estimate to that limit without assuming convergence of interval
means. Separation independently supplies local integrability of the counting
discrepancy.

Files: `ConjugatePoisson`, `BMOSecondMoment`, `PoissonBMOKernel`,
`PoissonBMONear`, `PoissonBMOFar`, `PoissonBMO`, `BoundaryPhase`,
`BoundaryPhaseCount`, `Fatou`, `CountingBMO`, and the root `Pavlov.lean`.
Details: [`P5_HilbertL2.md`](P5_HilbertL2.md),
[`P5_PoissonBMO.md`](P5_PoissonBMO.md), [`P5_BoundaryPhase.md`](P5_BoundaryPhase.md),
[`P5_CountingBMO.md`](P5_CountingBMO.md).

## 5. Dependencies and verification

The selected Tau Ceti release is `v4.35.0`, commit
`1f9b4414105d86e487a4ac4c3d3397076a44d0d2`. Its 41 modules, 8882 lines,
are copied unchanged, with the Apache-2.0 license and full import-closure
inventory in [`TauCeti/VENDORED.md`](../TauCeti/VENDORED.md). The library uses
upstream's `autoImplicit` and `relaxedAutoImplicit` options, scoped to Tau Ceti;
project options are unchanged.

The modular blueprints were independently reviewed in
[`R13_Pavlov_Blueprint.md`](../reviews/R13_Pavlov_Blueprint.md). The end-to-end
assembly and logarithmic dispersion received separate code audits in
[`R14_Pavlov_Code.md`](../reviews/R14_Pavlov_Code.md) and
[`R15_Pavlov_Dispersion.md`](../reviews/R15_Pavlov_Dispersion.md). All reported
approval without mathematical defects. The full project and compatibility builds passed without warnings; the
46-theorem comparator was accepted on 2026-11-07 (`comparator/last_run.log`). Axiom audits of
`pavlovBMO_holds` and `landau_inequality_unconditional` report only `propext`,
`Classical.choice`, and `Quot.sound`.

## 6. Historical assessment and retained cautions

The initial phase-2 assessment deferred P5 because Mathlib lacked the necessary
weighted and BMO infrastructure. That assessment described the missing work;
it is superseded by this implementation, which develops the needed specialized
bridges and reuses the pinned Tau Ceti analytic tools.

Two cautions from referee R7 remain relevant. Equivalent norms on PW do not
imply pointwise comparability of weights. Also, summing per-zero argument errors
at a fixed positive height does not prove a bounded counting-function error;
its Hilbert-type tail can make that reasoning circular. The implemented route
uses finite weighted tests and exact boundary dispersion instead. The proof
establishes the unchanged BMO necessity statement, without replacing it by the
weaker Landau counting estimate or claiming the full Pavlov characterization.
