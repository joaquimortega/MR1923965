# P5: uniform BMO for regularized conjugate Poisson integrals

Owner: `sol_pavlov_poisson_bmo`. Proof and interfaces, 2026-11-07.
The uniform BMO theorem is implemented in `PoissonBMO.lean`, using only proved
dependencies. This file records the argument and its analytic obligations;
no result below is a new hypothesis of `PavlovBMO`.

## Normalization

Write `Q_y(s)=s/(π(s²+y²))`. For real BMO data define

```
conjugatePoisson u y x = (1/π) ∫ t,
  ((x-t)/((x-t)^2+y^2) + t/(1+t^2)) * u t.
```

This agrees exactly with `P5_Dispersion.md`: it is the imaginary part of
the normalized Schwarz integral. The integral is of the combined kernel.
Neither of its two displayed summands is integrated separately.

The useful integrability statement is stronger than a.e. convergence:
`LogIntegrable u` implies absolute integrability of the displayed integrand
for every `y>0` and `x`. Indeed its kernel is continuous in t and has
`O((1+t²)⁻¹)` decay, with a constant depending on x and y. On compact
(x,y) sets inside the upper half-plane the constant is uniform. This also
proves continuity in x by dominated convergence and hence local integrability.

## Required interfaces in `FF.Pavlov`

The definitions of `conjugatePoisson` and `LogIntegrable` belong to the
shared `Basic.lean` module; every BMO module imports those definitions.

```lean
theorem bmo_local_square_bound :
  ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ), LocallyIntegrable u →
    ∀ M : ℝ, 0 < M →
    (∀ a b : ℝ, a < b → FF.meanOsc u a b ≤ M) →
    ∀ a b : ℝ, a < b →
      IntegrableOn (fun t ↦ (u t - FF.intervalMean u a b)^2)
        (Set.Icc a b) ∧
      (∫ t in a..b, (u t - FF.intervalMean u a b)^2) ≤
        C * M^2 * (b-a)

theorem memBMO_logIntegrable {u : ℝ → ℝ} (hu : FF.MemBMO u) :
  LogIntegrable u

theorem meanOsc_conjugatePoisson_le :
  ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ), LocallyIntegrable u →
    ∀ M : ℝ, 0 < M →
    (∀ a b : ℝ, a < b → FF.meanOsc u a b ≤ M) →
    ∀ y : ℝ, 0 < y → ∀ a b : ℝ, a < b →
      FF.meanOsc (conjugatePoisson u y) a b ≤ C * M
```

For the middle theorem a BMO witness may be enlarged to `max M 1`;
there is no need to treat a zero seminorm separately.

## Local square estimate

Use the proved `FF.johnNirenberg_holds`. Its constants can remain abstract:
if the tail is bounded by `C₀ exp(-c₀s/M)|I|`, layer cake gives

```
∫_I |u-u_I|²
 = ∫₀∞ 2s |{t∈I: |u(t)-u_I|>s}| ds
 ≤ 2 C₀ (M/c₀)² |I|.
```

The equality is initially an extended integral, so it establishes square
integrability as well as the numerical bound. Strict versus weak superlevel
sets is handled by inclusion. Endpoints of intervals are null. The integrand
is measurable from local integrability. Using a Bochner layer-cake equality
before proving integrability would be circular.

## Growth of means and weighted integrability

For centered intervals `I_k=(c-2^k r,c+2^k r]` and `M` bounding all mean
oscillations, restriction of the integral on `I_{k+1}` gives

```
|u_{I_k}-u_{I_{k+1}}| ≤ 2M,
average_{I_k}|u-u_{I_0}| ≤ (1+2k)M.
```

The first inequality uses the ratio `|I_{k+1}|/|I_k|=2`; the second is
the triangle inequality and telescoping of interval means. For c=0,r=1,
the annulus `2^k<|t|≤2^(k+1)` contributes at most
`4*2^(-k)*(|u_{I_0}|+(2k+3)M)` to `∫|u|/(1+t²)`. This is summable.
The initial compact interval is controlled by local integrability.

The same centered-interval estimate, with arbitrary c and r, supplies the
far-part estimate below. It should be proved once with those parameters.

## Near/far decomposition and quantitative constants

Fix `I=(c-r,c+r]`, `r>0`, and `J=(c-2r,c+2r]`. Set `v=u-u_J`,
`v₁=1_J v`, and `v₂=1_(ℝ\J) v`. For `x∈I` compare the regularized
integral at x with a suitable constant A. The exact difference is

```
conjugatePoisson u y x - A
  = T_y[v₁](x) + ∫_(ℝ\J) [Q_y(x-t)-Q_y(c-t)] v(t) dt,
```

where A absorbs the normalization, the center value of the far integral,
and the regularized transform of `u_J`. That last transform is constant
(in fact zero): integrating the combined regularized kernel against 1
gives zero. This needs a separate improper-integral calculation; it must
not be justified by splitting two divergent integrals. Alternatively,
define A by the convergent combined kernel integral and establish that
its x derivative is zero.

For the near part, the L² contraction and Cauchy–Schwarz give

```
average_I |T_y[v₁]| ≤ |I|^(-1/2) ‖v₁‖₂ ≤ sqrt(2 C_JN) M.
```

The equality with `T_y` is only a.e., which suffices for the interval
integral. The local square bound ensures that `v₁` defines an L² element.

For `|s|≥2|h|`, the uniform kernel estimate is

```
|Q_y(s+h)-Q_y(s)| ≤ (2/π) |h|/s².
```

One algebraic proof first bounds the difference by
`|h|/(π|s||s+h|)` and uses `|s+h|≥|s|/2`. This remains valid at
`|s|=2|h|`; `s=0` is excluded separately. An alternative derivative
proof uses `|Q'_y(s)|≤1/(πs²)` and gives the less sharp constant `4/π`.
Either is sufficient and independent of y.

Take far annuli `2^(k+1)r<|t-c|≤2^(k+2)r`, k≥0. Their contribution
is bounded by

```
(4/π) 2^(-k) (2k+3) M.
```

Here the enclosing centered interval has radius `2^(k+2)r`, and its
mean differs from `u_J` by at most `2(k+1)M`. The bound deliberately
rounds constants upward. Summation uses
`∑2^(-k)=2` and `∑k2^(-k)=2`, hence the displayed far bound sums to
`40M/π`. The arbitrary-comparison BMO lemma contributes the final factor
two. Any larger absolute constant is acceptable.

Absolute convergence of the far difference follows from this same bound.
All normalization constants are finite by weighted logarithmic
integrability, so the displayed near/far identity uses only valid
integral linearity. The implemented uniform bound is
`2*(C_near+40/π)*M`. No principal-value boundary operator is involved.

## Boundary handoff

The separate pairwise Fatou lemma passes a uniform mean-oscillation bound
to an a.e. limit, at cost at most two. It needs local integrability of
the limiting count discrepancy, which follows independently from
separation. No convergence of the means or choice of convergent additive
normalizations is required.


## Implemented modules and final interfaces

All names below are in namespace `FF.Pavlov`.

- `BMOIntervalGrowth.lean`: nested-interval length-ratio comparison,
  dyadic telescoping of means, and integral growth about a fixed mean.
- `BMOSecondMoment.lean`: extended layer cake, exponential-tail second
  moment integrability and numerical bound, and `bmo_local_square_bound`.
- `BMOLogIntegrable.lean`: `memBMO_logIntegrable`, proved by closed dyadic
  shell bounds and a summable countable-cover argument.
- `PoissonBMOKernel.lean`: rational kernel difference identity and the
  uniform `2|h|/(πs²)` estimate.
- `PoissonBMOFar.lean`: centered shells, exact cover of the far region,
  and `conjugatePoissonFarFraction_integrable_bound` with constant `40M`.
- `PoissonBMONear.lean` (owner `sol_kernel_integrals`): compact L² cutoff,
  its exact norm identity, the operator comparison, and the near estimate.
- `PoissonBMO.lean`: exact near/far splitting using differences of
  absolutely convergent normalized integrals, and
  `meanOsc_conjugatePoisson_le`. The latter has the precise quantitative
  interface displayed above.

The useful qualitative handoff is

```lean
theorem conjugatePoisson_uniform_bmo {u : ℝ → ℝ} (hu : FF.MemBMO u) :
  ∃ M : ℝ, 0 < M ∧ ∀ y : ℝ, 0 < y →
    LocallyIntegrable (conjugatePoisson u y) ∧
    ∀ a b : ℝ, a < b → FF.meanOsc (conjugatePoisson u y) a b ≤ M

theorem memBMO_conjugatePoisson {u : ℝ → ℝ} (hu : FF.MemBMO u)
    {y : ℝ} (hy : 0 < y) : FF.MemBMO (conjugatePoisson u y)
```

The actual comparison constant is
`conjugatePoisson (u-u_J) y c - nearConjugatePoisson u y c r c`.
Thus no separate far center integral needs to be introduced. The Schwarz
module proves that subtracting `u_J` leaves the normalized transform
unchanged, using its proved transform-of-constants identity. The two
integrable normalized kernels are subtracted first, then split into the
near and far sets. This is the concrete implementation of the convergence
precautions in the argument above.
