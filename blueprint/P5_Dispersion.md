# P5: special logarithmic dispersion without general factorization

Date: 2026-11-07. Owner: `sol_poisson`.
**Proposed interfaces and proof, awaiting independent review. No Lean implementation.**

This closes the analytic bridge proposed in `P5_RouteB.md`. Inputs are the
real generating function/cardinals of `P5_Cardinal.md`, boundary
`log|G| ∈ BMO` from the shifted A₂ route, and the uniform conjugate-Poisson
BMO estimate built on `P5_HilbertL2.md`. No claim here changes the target
`FF.PavlovBMO` or assumes it under another name.

## 1. Weighted logarithmic integrability and the Schwarz integral

Use the following definitions in namespace `FF.Pavlov`:

```lean
def LogIntegrable (u : ℝ → ℝ) : Prop :=
  Integrable (fun t ↦ u t / (1+t^2)) volume

def schwarzIntegral (u : ℝ → ℝ) (z : ℂ) : ℂ :=
  (-Complex.I / Real.pi) * ∫ t : ℝ,
    (((t : ℂ)-z)⁻¹ - ((t/(1+t^2) : ℝ) : ℂ)) * (u t : ℂ)

-- This is a normalized integral, not a difference of two possibly
-- divergent integrals.
def conjugatePoisson (u : ℝ → ℝ) (y x : ℝ) : ℝ :=
  (Real.pi)⁻¹ * ∫ t : ℝ,
    ((x-t)/((x-t)^2+y^2) + t/(1+t^2)) * u t
```

Planned lemmas:

```lean
theorem MemBMO.logIntegrable {u : ℝ → ℝ} (hu : FF.MemBMO u) :
  LogIntegrable u

theorem log_abs_sub_logIntegrable (a : ℝ) :
  LogIntegrable (fun t ↦ Real.log |t-a|)

theorem differentiableOn_schwarzIntegral {u : ℝ → ℝ}
    (hu : LogIntegrable u) :
  DifferentiableOn ℂ (schwarzIntegral u) FF.UHP

theorem schwarzIntegral_re {u : ℝ → ℝ} (hu : LogIntegrable u)
    {x y : ℝ} (hy : 0 < y) :
  (schwarzIntegral u ((x : ℂ)+(y : ℂ)*Complex.I)).re =
    ∫ t : ℝ, y/(Real.pi*((x-t)^2+y^2))*u t

theorem schwarzIntegral_im {u : ℝ → ℝ} (hu : LogIntegrable u)
    {x y : ℝ} (hy : 0 < y) :
  (schwarzIntegral u ((x : ℂ)+(y : ℂ)*Complex.I)).im =
    conjugatePoisson u y x
```

The complex-kernel domination/differentiation estimates already proved in
`DeBrangesF/Herglotz.lean` apply after multiplying by u and using
`LogIntegrable`; here the measure is signed through its integrand, not a
positive `withDensity` measure. All integrability must be proved before
rewriting real or imaginary parts of an integral.

For BMO logarithmic integrability, compare the means on `[-2^k,2^k]` and
`[-2^(k+1),2^(k+1)]`. Their difference is at most a fixed multiple of the
BMO seminorm. The mean of |u| on the kth interval is therefore O(k+1),
with a constant depending on the initial mean. The weighted annular
integral is O((k+1)2^-k), a summable series. This uses no
John–Nirenberg theorem. The elementary log|t-a| case follows by splitting
near its single logarithmic singularity and at infinity.

The normalization fixes the imaginary constant:
`(schwarzIntegral u I).im=0`, since its kernel at I is purely imaginary
before multiplication by -I/π.

## 2. Generic bounded zero-free boundary data

The special bounded analytic function will be

    q(z)=dslope G γ₀ z,       F(z)=exp(iπz) q(z),
    v(t)=log|q(t)|=log|F(t)| on ℝ.

Here γ₀∈Γ is fixed. q is real entire, belongs to PWπ, and has exactly the
simple real zeros Γ\{γ₀}. Therefore F is zero-free on C₊. Fourier PW
evaluation gives the **uniform upper-half-plane bound**

    |q(x+iy)| ≤ C exp(πy),  hence |F(x+iy)| ≤ C.

This extra fact avoids a general Hardy logarithmic domination theorem.
Also `v=log|G|-log|t-γ₀|` a.e., so §1 gives `LogIntegrable v`. The value
at the single removed node is immaterial.

For a reusable primitive, let A be holomorphic and zero-free on C₊,
bounded by M there. Suppose it extends analytically across every finite
real point, with only finite-order boundary zeros, and let
`v(t)=log‖A(t)‖`. Assume `LogIntegrable v`. Then:

```lean
-- Analytic continuation / finite-order zero hypotheses should be
-- packaged by an existing entire witness A, not by unproved predicates.
theorem log_norm_le_poisson_boundary
    {A : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hnz : ∀ z ∈ FF.UHP, A z ≠ 0)
    (hbd : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ FF.UHP, ‖A z‖ ≤ M)
    (hv : LogIntegrable (fun t : ℝ ↦ Real.log ‖A t‖)) :
  ∀ z ∈ FF.UHP,
    Real.log ‖A z‖ ≤
      (schwarzIntegral (fun t : ℝ ↦ Real.log ‖A t‖) z).re
```

An entire nonzero A has only finite-order real zeros automatically. The
zero-free-upper hypothesis ensures it is not identically zero.

### Proof of domination by positive harmonic comparison

Choose M strictly larger than the bound and put

    U(z)=log M-log|A(z)| ≥ 0.

This is positive harmonic on C₊. Its boundary value b is nonnegative;
at a real zero set b=+∞ for approximation purposes, since U tends to
+∞ there. For bounded continuous compactly supported g with 0≤g≤b,
compare U and P[g] on a large upper half-disk. On the diameter,
`liminf(U-P[g])≥0`; at boundary zeros this is automatic. On the
semicircle `P[g]≤C_g/R` uniformly, because g has fixed compact support
and the half-plane Poisson kernel is O(1/R) there. Since U≥0, the
minimum principle gives `U(z)≥P[g](z)-C_g/R`. Let R→∞.

Use increasing compact cutoffs times `min(b,N)`; the truncation extends
continuously at the real zeros, so these are legitimate g. Monotone
convergence gives `U≥P[b]`. Since the Poisson kernel has integral one,
this is exactly `log|A|≤P[v]`.

At a real zero, U itself is not continuous as a finite-valued function;
apply the compact minimum principle after deleting tiny half-disks
around the finitely many zeros in the large diameter, where U tends
uniformly to +∞. This is a finite geometric step, not an implicit
continuity assumption at a logarithmic singularity.

## 3. Defect reflection and classification

Let

    r(z)=Re schwarzIntegral[v](z)-log|A(z)|.

It is nonnegative harmonic on C₊. The needed boundary theorem is:

```lean
theorem poisson_log_defect_continuous_zero_boundary
    -- same hypotheses as §2
    ... :
  ContinuousOn (fun z ↦ if 0 < z.im then
    (schwarzIntegral (fun t : ℝ ↦ Real.log ‖A t‖) z).re -
      Real.log ‖A z‖ else 0) {z : ℂ | 0 ≤ z.im}
```

At a point a where A(a)≠0, split v into a smooth local part and a tail.
The approximate-identity estimate gives P[v](z)→v(a) as z→a within the
upper half-plane. Weighted tail domination makes the far part harmless.
At a zero of order m, write A(z)=(z-a)^m B(z), B(a)≠0 locally. Use

    P[log|t-a|](z)=log|z-a|,

subtract m times that exact identity, and apply the nonzero case to the
remaining boundary function. The remaining boundary function need only
be locally smooth near a and logarithmically integrable globally. This
proves cancellation and continuity of r, not continuity of the two
singular terms individually.

The separate harmonic primitive is:

```lean
theorem nonneg_harmonic_zero_boundary_eq_mul_im
    {r : ℂ → ℝ}
    (hr : InnerProductSpace.HarmonicOnNhd r FF.UHP)
    (hcont : ContinuousOn r {z : ℂ | 0 ≤ z.im})
    (hzero : ∀ x : ℝ, r x = 0)
    (hpos : ∀ z ∈ FF.UHP, 0 ≤ r z) :
  ∃ a : ℝ, 0 ≤ a ∧ ∀ z ∈ FF.UHP, r z = a*z.im
```

Prove odd harmonic reflection across ℝ. A narrow proof uses the disk
Dirichlet problem: prescribe the odd continuous boundary values on a
disk centered on ℝ; its harmonic extension is odd and zero on the
diameter; uniqueness on the upper half-disk identifies it with r.
Consequently the odd reflection is harmonic on all ℂ. Obtain an entire
holomorphic function with this real part from Mathlib's
`HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq`. Multiply by I and
normalize its imaginary constant. The oddness makes the result commute
with conjugation, and its imaginary part is nonnegative on C₊. Apply
existing `FF.entire_pick_linear` in
`FourierFrames/Cited/DeBrangesDE/EntireHerglotz.lean`. Its imaginary part
is exactly `a Im z`, with a≥0. No general half-plane harmonic
representation theorem is required.

## 4. Construct the outer comparison and kill a by uniqueness

A holomorphic branch ℓ of log F exists on the convex upper half-plane.
Once §3 gives `P[v]-log|F|=a Im z`, the analytic function
`schwarzIntegral v-ℓ+i a z` has zero real part and is a purely imaginary
constant. Thus

    F(z)=exp(i(a z+b)) O(z),    O(z)=exp(schwarzIntegral v(z)),

for a,b real and a≥0. (The name b absorbs the harmless sign of the
constant.) The outer comparison belongs to H² by Jensen:

    |O(x+iy)|² = exp(2P_y[v](x))
              ≤ P_y[exp(2v)](x) = P_y[|q|²](x).

Integrating in x and using Tonelli gives a bound by `||q||²₂`, uniform
in y. Differentiability follows from §1. Prove exp(2v)=|q|² only a.e.;
Lean's totalized real log gives the wrong equality at q(t)=0, a null
set here. The same a.e. precaution applies to real log identities.

Assume a>0, choose `0<τ<a`, and define the real entire function

    f(z)=q(z)sin(τ(z-γ₀)).

The factor `exp(iaz)sin(τ(z-γ₀))` is bounded analytic on C₊, since each
of its two exponential terms has nonnegative decaying vertical rate.
Hence `exp(iπz)f(z)∈H²`, by bounded analytic multiplication of O.
Because q and the sine are real entire, `f*=f`. Both Hardy conditions
of `MemHE (fun z ↦ exp(-iπz)) f` hold. Existing
`FF.memPW_of_memHE` (`HB/Comparable.lean`, with c=C=1) gives f∈PWπ.
It vanishes at every point of Γ: q vanishes at Γ\{γ₀}, and the sine
vanishes at γ₀. It is nonzero because neither entire factor is
identically zero. CIS uniqueness forces f=0, contradiction. Therefore

    a=0.

This argument uses the already proved de Branges/Paley–Wiener
identification, not an unformalized smaller-exponential-type assertion.

## 5. Exact dispersion and boundary staircase

By linearity of S and the exact log-distance Poisson identity,
`S[log|t-γ₀|]` differs from `log(z-γ₀)` by an imaginary constant.
The preceding factorization with a=0 therefore implies that a
holomorphic logarithm L of G on C₊ satisfies

    L(z)=schwarzIntegral[u](z)-iπz+i c,  u=log|G|.     (D)

Its real part is the exact dispersion identity

    log|G(x+iy)|=πy+P_y[log|G|](x).

The imaginary part, with the normalizations in §1, is

    Im L(x+iy)=conjugatePoisson u y x - πx+c.

At each x∉Γ, L has a local boundary logarithm, whose imaginary part is
constant modulo π on each zero-free real interval. Crossing a simple
real zero from left to right in C₊ decreases the continuous argument by
π (the local factor z-γ has argument decreasing from π to zero).
Therefore

    lim_(y↓0) Im L(x+iy) = -π countFn Γ x + c₀.

The additive constant accommodates the specified normalization
`countFn Γ 0=0`, also when 0∈Γ. Combining with (D),

    lim_(y↓0) conjugatePoisson u y x
      = -π(countFn Γ x-x)+constant                  (x∉Γ).   (Q)

There is no principal-value Hilbert transform in this statement.

## 6. Uniform BMO followed by Fatou

The separate BMO operator module proves a bound independent of y>0 for
`meanOsc (conjugatePoisson u y)`. Its ingredients are the L² operator
from `P5_HilbertL2.md`, John–Nirenberg L² oscillation on twice the target
interval, and the dyadic tail kernel estimate. The combined normalized
kernel is crucial for global convergence.

To pass to (Q), take y_n=1/(n+1). Avoid assuming convergence of interval
means. For any locally integrable g on I, its pairwise mean oscillation
satisfies

    meanOsc_I g ≤ average_(I×I)|g(s)-g(t)| ≤ 2 meanOsc_I g.

Fatou on I×I and a.e. convergence (Q) thus give the same BMO bound up
to a factor two for the staircase limit. Local integrability of
`countFn Γ x-x` follows directly from separation, independently of this
limit. Scaling by -1/π and adding constants preserve BMO. This proves
the unchanged `FF.PavlovBMO`.

## 7. Reusable inventory and real remaining proof obligations

Available now:

- Project: `FF.entire_pick_linear`, with no cited hypothesis;
  `FF.memPW_of_memHE` for exponential-comparable HB E;
  regularized Cauchy kernel estimates in `DeBrangesF/Herglotz.lean`;
  the PW Fourier evaluation bound and vertical L² estimate.
- Mathlib: disk harmonic Poisson formula;
  `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq`;
  continuous logarithms on simply connected domains in
  `Mathlib.Analysis.Complex.BranchLogRoot`.
- TauCeti v4.35.0:
  `Analysis/Complex/BranchLogRoot.lean` upgrades the continuous branch to
  `exists_differentiableOn_eqOn_exp_comp`;
  `Analysis/Complex/Conformal/Reflection/Principle.lean` proves ordinary
  holomorphic Schwarz reflection, but requires continuity of the whole
  complex boundary function, not just its real part;
  `Analysis/PDE/PoissonIntegral/Ball.lean` has
  `exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere`, useful
  for odd harmonic reflection;
  `Analysis/PDE/PoissonIntegral/HalfSpace.lean` has Poisson normalization,
  boundary convergence and harmonicity for bounded measurable data;
  `Analysis/InnerProductSpace/Laplacian/Comparison.lean` has
  `le_of_laplacian_le_of_le_frontier` for compact domains.

The bounded-data Poisson lemmas do not directly apply to logarithmic
boundary singularities: local/far splitting and weighted domination
remain necessary. Compilation/provenance checks for the additional Tau
closures are being performed separately before any proposed vendoring.
The principal new analytic proof obligations are §§2–3 and the weighted
Schwarz integral; no external theorem is being silently assumed.

## Implementation status

`Pavlov/LogPoisson.lean` now proves the full generic
`log_norm_le_poisson_boundary` and the derived
`poisson_log_defect_eq_mul_im`, with exactly the entire/zero-free/bounded/
weighted-log hypotheses above. The actual domination proof improves the
punctured-domain plan in §2: for each continuous compact logarithmic
cutoff g, compare the **continuous squared modulus**

    |A(z)|² exp(2 P[g](z)).

In the interior this is the squared norm of the holomorphic function
`A exp(S[g])`, whose Laplacian is nonnegative. Its diameter bound is
provided by the positive-floor logarithmic clipping lemma; its
semicircle bound is `M² exp(O(1/R))`. Compact comparison and R→∞ give
`P[g]≤log M-log|A|`. Dominated convergence removes the clipping, using
the countable boundary zero set. Thus no punctures or finite-valued
continuity of log|A| at its zeros are required in the maximum principle.

`Pavlov/LogPoissonBoundary.lean` separately proves finite-order local
cancellation, `Pavlov/HarmonicReflection.lean` proves the positive
zero-boundary classification, and the slope helper combines them.
`lake build FourierFrames.Cited.Pavlov.LogPoisson` succeeds without
warnings. An axiom audit of the domination theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`.
