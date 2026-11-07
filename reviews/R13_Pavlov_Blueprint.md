# R13 — Independent review of the Pavlov implementation blueprints

Date: 2026-11-07. Reviewer: `sol_poisson`.

## 1. Cardinal functions and cell comparison

Reviewed `blueprint/P5_Cardinal.md` independently against the unchanged
`FF.PavlovBMO` statement and the existing de Branges reduction.

**Verdict: approved for implementation.**

- Retaining `sample_norm` while replaying the original construction is
  valid: the phase rotation multiplies E by a constant of modulus one,
  and therefore preserves `heNormSq` exactly. The representation supplied
  merely by `completeInterpolating_zero_set_unconditional` does not
  expose this identity, so replaying its construction is appropriate.
- The removable cardinal uses `dslope`; at its central zero its value is
  one by derivative nonvanishing. Real-zero simplicity follows from
  positive phase derivative and nonvanishing E on the real line.
- Finite synthesis is bounded directly by the sampling lower estimate;
  its sampling sum is the finite sum of squared coefficients. Proving PW
  membership and finite norm before taking `toReal` avoids totalization.
- The Voronoi geometry is correct. A cell has length between the lower
  and upper gap bounds; every other node is at distance at least half
  the lower gap from the closed cell. A horizontal enlargement smaller
  than one quarter of that gap preserves zero-freeness.
- The rectangle theorem is uniform in location and cell length: the
  smaller rectangle lies a fixed distance from its boundary, and a
  bounded number of disks joins the normalization point to each target.
  The harmonic function `log M-log‖f‖` is nonnegative (not necessarily
  strictly positive everywhere); Harnack for nonnegative functions is
  sufficient, since its value at the anchor is `log M>0`.
- The shifted and real generating estimates follow from the cardinal
  factorization. They remain valid at the node before logarithms are
  taken. The logarithmic estimate correctly excludes the node and has
  the required uniform bounded error.

No new hypothesis or circular Pavlov/Cartwright use was found. The
sampling-to-bounded-gaps helper and order enumeration are real proof
obligations, explicitly listed in the blueprint, rather than consequences
of separation alone.

## 2. Conjugate Poisson operator on L²

Reviewed `blueprint/P5_HilbertL2.md` independently.

**Verdict: approved for implementation.**

- With Fourier phase `exp(-2πitξ)`, the inverse transform of
  `-i sign ξ exp(-2πy|ξ|)` is exactly
  `x/(π(x²+y²))`. Splitting at zero gives the two fractions printed in
  the blueprint; both their sign and the factor `2π` are correct.
- The symbol is in L¹∩L²∩L∞ for y>0, with essential supremum at most
  one. The multiplier is consequently an L² contraction.
- Identifying its inverse L² transform with the explicit kernel before
  asserting the kernel is in L² is sound. The ordinary kernel is not
  L¹; the blueprint explicitly avoids this false assertion.
- For L¹∩L² inputs, Fubini is justified by the product
  `‖m_y‖₁‖f‖₁`. Boundedness of the ordinary Fourier transform makes the
  multiplied transform L¹, while the multiplier bound gives L².
- For general L² inputs, the translated/reflected kernel is in L².
  The pointwise pairing is continuous in the input L² norm; combining
  it with an a.e.-convergent subsequence of operator outputs correctly
  proves the stated a.e. realization. A countable union of exceptional
  sets suffices for the approximating sequence.
- The tail smoothness estimate is uniform in y: for s≠0,
  `|Q'_y(s)|≤1/(πs²)`. The segment from t to t-h stays beyond |t|/2,
  yielding the displayed constant. Its tail integral is uniformly
  bounded, including the trivial h=0 case.
- The endpoint theorem alone does not give BMO→BMO. The blueprint
  correctly retains the local John–Nirenberg L² estimate, annular tail
  control, and normalized integral as downstream work. Uniform-in-y
  BMO estimates followed by Fatou avoid an unnecessary PV boundary
  transform theorem.

No mathematical defect or scope weakening was found. This review
approves the proposed mathematical interfaces and proof route; it does
not certify yet-unwritten Lean code or the separate dispersion bridge.

## 3. Elementary BMO algebra, limits, and A₂ logarithms

Reviewed `blueprint/P5_BMO.md` independently.

**Verdict: approved for implementation, including the additional arbitrary
a.e.-limit Fatou interface below.**

- All linearity estimates retain the needed local integrability. The
  nonnegativity statement correctly needs none, since the integrand is
  nonnegative and a<b fixes interval orientation.
- The arbitrary-comparison factor two, scalar absolute-value factor,
  subadditivity, and bounded-perturbation factor two are correct.
  Boundedness alone is not used to infer measurability.
- A.e. invariance works for the means as well as centered integrands;
  interval restrictions preserve the a.e. equality.
- The local-L¹ oscillation difference estimate has the correct constant
  two. The Fatou-with-moving-centers statements explicitly require
  convergence of those centers, so do not presume convergence of means.
- The A₂ logarithm argument is valid with a.e. positivity, locally
  integrable w and its inverse. `|log s|≤s+s⁻¹` gives local log
  integrability; normalizing by A=average w gives comparison cost
  at most 1+C, and mean oscillation at most 2(1+C). No uniform positive
  lower bound on A or Jensen theorem is needed.

For the dispersion application, also approve the stronger statement:
locally integrable fn and g, a.e. convergence fn→g, and one common bound
`meanOsc fn I≤M` imply `meanOsc g I≤2M`, without convergence of centers.
Indeed `meanOsc g I` is at most its pairwise average
`average_(I×I)|g(s)-g(t)|`; each pairwise average for fn is at most 2M.
Fatou on the product interval measure gives the claim. All pairwise
integrals are finite for the prelimit and limit by local integrability;
the product a.e. convergence follows from the two coordinate exceptional
sets. This statement is sufficient for the regularized conjugate-Poisson
limit and avoids an unnecessary principal-value or mean-convergence
claim.

## 4. Schwarz integral API and dispersion normalization

Reviewed the proposed Schwarz calculus interfaces in `P5_Dispersion.md`
§1 and their shared definitions in `Pavlov/Basic.lean`; root will implement
the calculus independently of this review.

**Verdict: approved for implementation.**

The combined kernel is O((1+t²)⁻¹) for a fixed upper-half-plane pole,
so the stated `LogIntegrable` hypothesis gives absolute integrability.
Its locally uniform derivative bounds give holomorphy by dominated
differentiation. Multiplication by -i/π yields real part
`y/(π((x-t)²+y²))` and imaginary part
`((x-t)/((x-t)²+y²)+t/(1+t²))/π`, exactly the definitions printed.
The kernel at i makes the Schwarz integral real, fixing the imaginary
normalization. Regularization stays inside the integral; no separately
divergent summands are split. The log-distance Poisson identity and
weighted boundary convergence needed later are separate proof
obligations, not consequences of these calculus signatures alone.

The dispersion real part is consequently
`log|G(x+iy)|=πy+P_y[log|G|](x)` and its conjugate limit is
`-π(countFn Γ x-x)+constant`, consistent with the multiplier sign
approved in §2.

## 5. Odd harmonic reflection and zero-boundary classification

Reviewed `blueprint/P5_Reflection.md` independently.

**Verdict: approved for implementation.**

The odd reflection is continuous because the given boundary values are
zero. The disk Dirichlet solution and its reflected negative have equal
boundary values; compact uniqueness gives oddness, hence zero diameter
values. Uniqueness on the upper half-disk then identifies the solution
with r, and oddness identifies it on the whole disk. Balls centered at
zero exhaust the plane, proving harmonicity everywhere. An entire
analytic conjugate exists by the named Mathlib theorem. After
multiplication by i, averaging with fstar preserves the imaginary part
because the reflected harmonic function is odd. Thus the existing
entire-Pick affine theorem applies and yields exactly a≥0 and r=a Im z.
This argument never presumes boundary continuity of a harmonic conjugate
or an unproved half-plane representation theorem.

## 6. Uniform conjugate-Poisson BMO

Reviewed `blueprint/P5_PoissonBMO.md` independently.

**Verdict: route and interfaces approved; correct the printed numerical
sum before quoting its constant.**

The stated annular bound `(4/π)2⁻ᵏ(2k+3)M` sums to **40M/π**, not
28M/π. This has no effect on the existence of an absolute BMO constant.
All other quantitative steps check: the local layer-cake argument must
start with extended integrals; doubled interval means differ by at most
2M; the local L² contraction contributes `sqrt(2 C_JN)M`; the rational
kernel difference estimate has the correct uniform constant and sign.
Weighted integrability makes the combined normalization constants
finite. The transform of a constant is zero, but its proof must indeed
keep the combined kernel inside the integral. The near operator/kernel
identity only holds a.e., which is sufficient. The final arbitrary
comparison costs a factor two, and pairwise Fatou can add another factor
two. No principal-value operator or convergence of interval means is
needed.

## 7. Implemented elementary BMO and harmonic reflection

Inspected the completed proofs in `Pavlov/BMO.lean`, `Pavlov/Fatou.lean`,
and `Pavlov/HarmonicReflection.lean`. The BMO a.e.-limit theorem uses
product a.e. convergence, explicit integrability of pairwise differences,
and the proved nonnegative real Fatou helper; its factor two is sound.
The A₂ logarithm proof proves local integrability and positivity of the
normalizing average before any logarithm division/integral comparison.
An axiom audit of `integral_le_of_ae_tendsto_nonneg`,
`meanOsc_le_of_ae_tendsto`, and `memBMO_log_of_A2` reports only
`propext`, `Classical.choice`, and `Quot.sound`.

The implemented reflection proof follows §5 precisely. Its compact
frontier arguments retain both the semicircle and diameter cases, and
its final symmetrization preserves the odd-reflection imaginary part.
No omitted boundary regularity or representation premise was found.

## 8. Exact logarithmic Poisson kernel

Reviewed `blueprint/P5_LogPoissonKernel.md` independently.
**Verdict: approved for implementation.** The tangent substitution has
positive Jacobian and the printed 1/π cancellation. For w=c+iy,
`c cos θ+y sin θ=|w|cos(θ-arg w)` has the correct sign. The numerator
has exactly one zero on the tangent interval; discarding that singleton
makes all logarithm identities valid. The two log-absolute-cosine
integrals have equal length π and cancel by periodicity. Their absolute
integrability supplies the needed integrability transfer through the
Jacobian. No numerical evaluation of the log-cos integral or dispersion
uniqueness theorem is needed, so this dependency is noncircular.

## 9. Continuous compact logarithmic clipping

Reviewed `blueprint/P5_LogClipping.md` independently.
**Verdict: approved for implementation.** The positive exponential
floor makes the logarithm continuous even at zeros; both nonnegative
factors increase with n under the boundary bound. The cutoff support
radius n+1 is correct, including endpoints. The scalar exponential bound
uses the positive floor, so does not invoke exp(log 0). At a nonzero
point both clipping operations eventually disappear, giving actual
eventual equality. That convergence requires no boundary upper bound,
as reflected in the proposed signature. An offzero upper bound by the
unclipped deficit is also valid and useful for dominated convergence.

## 10. Elimination of the exponential defect

Reviewed `blueprint/P5_NoExponentialDefect.md` independently.
**Verdict: approved for implementation.** With τ=a/2, both vertical
rates a±τ are positive, so the two exponential terms in the multiplier
have norm at most one, and its half-sum has norm at most one. Reality of
q and the sine gives fstar f=f. The explicit canonical HB function has
exact exponential comparability, so the existing de Branges-to-PW
result gives the sine product in PW. CIS uniqueness and the nonzero
central derivative q(γ)τ contradict a>0. The signature contains no
smaller-type or phase/BMO hypothesis.

## 11. Boundary phase and counting staircase

Reviewed `blueprint/P5_BoundaryPhase.md` independently.
**Verdict: approved for implementation.** Local logarithms normalized
near one exist on genuine disks and are real on the real diameter.
Constancy of L minus the local logarithm follows from differentiating
its constant exponential. Connectedness of each entire gap makes the
local constants agree. At a simple zero the removed derivative quotient
is nonzero, and upper-half-plane principal arguments tend to π on the
left and zero on the right. Thus the jump is -π, with no false use of
principal-log continuity on the negative real axis. The half-open
midpoint interval contains exactly its single intervening node; the
integer recurrence then matches the fixed `countFn` normalization, also
when zero is a node. No dispersion or BMO premise is used.

The finite-order logarithmic defect cancellation route assigned to
`LogPoissonBoundary.lean` is also approved: factor locally by a power,
update the real residual at the one center to its nonsingular value,
apply weighted Poisson boundary convergence, and cancel the exact
log-distance Poisson identity. The singleton update must be kept in the
continuity proof and ignored only in a.e./integral identities.

## 12. Implemented uniform conjugate-Poisson BMO

Inspected the completed main decomposition and uniform estimate in
`Pavlov/PoissonBMO.lean`. The finite comparison constant subtracts the
near integral at the center from the normalized centered transform.
The exact near/far identity uses proven integrability before splitting,
and subtracting the constant datum uses the separately proved constant
transform identity. The near estimate is used only through its interval
integral; the far estimate has the corrected constant 40/π. The final
uniform witness enlarges a possibly zero/negative initial witness to
`max M 1`. No hidden principal-value or limiting-mean step was found.

## 13. Outer comparison and factorization from the harmonic defect

Reviewed `blueprint/P5_OuterComparison.md` independently.
**Verdict: approved for implementation.** Under the probability Poisson
measure, u is integrable by weighted integrability and exp(2u) is
integrable because its Lebesgue integral is finite and the kernel is
bounded at positive height. Jensen yields the advertised squared
modulus bound, and Tonelli plus kernel mass one gives a uniform H²
bound. The quotient `A exp(-Su-i a z)` has norm one with the printed
sign, since its logarithmic norm is `log|A|-Re Su+a Im z=0`.
Connected maximum modulus makes it constant; its unit norm supplies the
argument parametrization. Neither a sign assumption on a nor a
boundary value identification is needed for this generic helper.

## 14. Implemented logarithmic boundary cancellation

Inspected `Pavlov/LogPoissonBoundary.lean`. The local factor is obtained
from the analytic finite-order theorem after ruling out local
identical zero by the identity principle and one upper nonzero value.
The logarithmic residual is updated at the real center, proved
continuous there using the local factor, and changed only a.e. for its
weighted integrability and Schwarz identities. The exact log-distance
Poisson identity then cancels the singular term on the upper
neighborhood, giving the zero boundary limit. The final continuous
extension is zero below the axis and uses this boundary limit at every
real point. No boundedness assumption is needed in this separate
cancellation theorem; its combination with bounded-function domination
has precisely the hypotheses of the proposed dispersion bridge.
