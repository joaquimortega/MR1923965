# R15 — Independent code audit of logarithmic dispersion

Reviewer: `sol_pavlov_poisson_bmo`, 2026-11-07.
Scope: `LogPoisson.lean`, `LogPoissonBoundary.lean`,
`OuterComparison.lean`, and `GeneratingDispersion.lean`. Read the supporting
interfaces in `CardinalLog.lean`, `NoExponentialDefect.lean`,
`LogClipping.lean`, `LogPoissonKernel.lean`, `HarmonicReflection.lean`,
and the final `Cited/Pavlov.lean` assembly to check their handoffs.
This is a mathematical statement/dependency audit; the root agent performs
the full build, theorem-axiom audit, and comparator run separately.

Verdict: **approved**. No statement mismatch, hidden analytic premise, or
incorrect exponential normalization was found. No proof edits requested.

## Boundary singularities and Poisson domination

`log_norm_le_poisson_boundary` assumes an entire function, no zeros in the
open upper half-plane, a positive uniform bound there, and weighted
integrability of its boundary logarithm. These are explicit inputs, not
conclusions smuggled into a helper. The cardinal constructor establishes
each of them from the actual normalized cardinal.

The compact comparison is applied to a squared holomorphic modulus.
Therefore it does not require a finite continuous logarithm at a boundary
zero. The continuous clipping floor in `logClip` preserves its diameter
modulus bound even at zeros. Passing to the logarithmic deficit uses
countability/nullity of the real zero set and domination only off that
set. In particular, totalized `Real.log 0 = 0` is not used as a genuine
logarithmic boundary value.

`LogPoissonBoundary.exists_local_factor` derives finite-order local
factorization from analyticity and nontriviality; nontriviality follows
from the upper-half-plane nonvanishing hypothesis. It does not assume
that a boundary zero is simple. The residual boundary logarithm is
updated at its single singular point, proved continuous there, and
identified with the original residual almost everywhere. Subtracting
`m log|t-a|` uses the exact proved logarithmic Poisson identity. Thus the
claimed defect continuity includes arbitrary finite-order boundary zeros;
it is not merely continuity at nonzeros or along vertical approaches.
The harmonic classification consumes the resulting continuous zero
boundary extension and explicit nonnegativity.

## Outer comparison and phase sign

The outer comparison proves its exponential majorant from the tangent
inequality for the exponential and the mass-one Poisson kernel. The
horizontal square-mass estimate uses an explicit Tonelli interchange and
Poisson normalization. `IsH2Upper` is concluded only after an integrable
boundary exponential has been supplied.

For the cardinal boundary function, `exp(2 cardinalLog)` equals the
squared cardinal modulus almost everywhere, using the grid's null zero
set. The assertion is deliberately not pointwise at zeros.

The defect convention is

    Re S[u](z) - log|A(z)| = a Im z,  a >= 0.

`factor_of_log_defect` accordingly concludes

    A(z) = exp(i(a z+b)) exp(S[u](z)).

The sign is correct: the first factor has modulus `exp(-a Im z)`.
The quotient used to identify the unimodular constant is holomorphic and
has modulus one; no assumed logarithm branch or boundary argument
convergence is needed at this step.

## Elimination of the defect and generator normalization

`cardinalUpper = exp(i pi z) * cardinal` has the required decaying
normalization. Its upper bound is established by PW evaluation and the
proved cardinal norm bound. Its boundary modulus equals that of the
cardinal at every real point. `CardinalLogInput` packages proved facts;
`cardinal_log_input` constructs it, so it is not an additional hypothesis
on the final Pavlov theorem.

`no_exponential_defect` does not assume the desired zero defect or a
smaller exponential type statement. A positive defect gives an entire
real function `q(z) sin(tau(z-gamma))`, with `tau=a/2`. The decaying
exponential times sine is bounded on the upper half-plane, so the proved
Hardy multiplier and PW/de Branges comparison give membership in PW.
The function vanishes on the interpolation set and is nonzero by its
derivative at the retained node. Interpolation uniqueness supplies the
contradiction. Both Hardy conditions use the proved real symmetry.

Adding back the removed real zero and the derivative normalization uses
almost-everywhere real logarithm identities and the exact Poisson formula
for `log|t-gamma|`; the derivative is nonzero by the proved simple-zero
property of the generator. The final identity is

    log|G(z)| = pi Im z + Re S[log|G|](z).

Consequently every holomorphic logarithm of G satisfies

    L(z) = S[log|G|](z) - i pi z + i c.

The real part of `-i pi z` is `+pi Im z`, and its imaginary part is
`-pi Re z`. These signs agree with the final assembly's
`conjugatePoisson = Im L + pi x - c` and therefore with the counting
boundary phase convention. The chosen node and derivative contribute
only the constants shown and cancel from the dispersion identity.

`GeneratingDispersion` explicitly takes `CardinalData`, a `Grid`,
separation, and complete interpolation. The final theorem obtains both
structures from separation/complete interpolation using proved
constructors. The auxiliary data therefore impose no hidden premise on
`FF.pavlovBMO_holds`.
