# P5: boundary argument and the counting staircase

Target: `FourierFrames/Cited/Pavlov/BoundaryPhase.lean`. This proof and interface were independently reviewed and approved in R13. The
implementation is complete. It is independent of logarithmic
dispersion, Schwarz integrals, and BMO. The sign is a decrease by π on crossing a simple
real zero from left to right through the upper half-plane.

## Exact inputs and final interfaces

Use `GeneratingData Γ` from `Pavlov/Cardinal.lean`; `CardinalData Γ` extends it. Its
fields supply entire `G`, `fstar G=G`, and the exact complex zero set `Γ⊂ℝ`.
`GeneratingData.simple` already proves `deriv G γ≠0` at every node.
`Grid Γ` supplies an increasing integer enumeration of Γ with positive gaps.
The separation hypothesis supplies bounded-interval finiteness for `FF.countFn_sub`.

```lean
namespace FF.Pavlov

theorem GeneratingData.exists_upper_log {Γ : Set ℝ} (d : GeneratingData Γ) :
  ∃ L : ℂ → ℂ, DifferentiableOn ℂ L UHP ∧
    ∀ z ∈ UHP, Complex.exp (L z) = d.G z

theorem GeneratingData.boundary_phase {Γ : Set ℝ}
    (hΓ : IsSeparated Γ) (d : GeneratingData Γ) (g : Grid Γ)
    {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L UHP)
    (hexp : ∀ z ∈ UHP, Complex.exp (L z) = d.G z) :
  ∃ c : ℝ, ∀ x : ℝ, x ∉ Γ →
    Tendsto (fun y : ℝ ↦ (L ((x:ℂ)+(y:ℂ)*Complex.I)).im)
      (𝓝[>] 0) (𝓝 (-Real.pi * countFn Γ x + c))
```

The hypothesis `hΓ` is already present in `PavlovBMO`; it is used only for interval
finiteness and does not add an analytic assumption. A stronger theorem could derive
separation from the grid gap, but that is unnecessary bookkeeping here. The statement
is for every holomorphic logarithm L, so the subsequent factorization may choose its
preferred normalization.

## 1. Existence and comparison of logarithms

The upper half-plane is open, convex, nonempty, and hence simply connected. The zero-set
field of d excludes zeros there. Apply
`TauCeti.exists_differentiableOn_eqOn_exp_comp`, a 252-line standalone module with
Mathlib-only imports, vendored unchanged from the already selected TauCeti `v4.35.0`.
This upgrades Mathlib's continuous logarithm rather than assuming a branch theorem.

A reusable elementary comparison lemma is needed: on an open connected convex set V,
if M is holomorphic and `exp(M z)=C` for fixed C≠0, then M is constant. Differentiate
the equality: `exp(M z)*deriv M z=0`; exponential never vanishes, so `deriv M=0`.
Use `IsOpen.exists_is_const_of_deriv_eq_zero`. This avoids any unproved choice of an
integer-valued branch index.

## 2. Boundary limits away from zeros, and constancy on each gap

At real x with G(x)≠0, choose r>0 so that G(z)/G(x) lies in the complex slit plane on
the ball B(x,r), close to 1. Put `b(z)=Complex.log (G(z)/G(x))`. This is holomorphic
on that ball and continuous across its diameter, with b(x)=0. On the real diameter,
G(t)/G(x) is real and positive (shrink r using continuity), hence `Im b(t)=0`.

On the upper half-ball, `exp(L-b)=G(x)`. The comparison lemma gives L=b+C there.
Consequently `Im L(t+iy)→Im C` for every real t sufficiently close to x. This proves
existence of the vertical boundary limit β(x), and local constancy of β on ℝ\Γ.
Choose β by the proved existence, and use uniqueness of limits along the nontrivial
filter `𝓝[>]0` whenever two local descriptions overlap.

On every open gap `(g.point k,g.point(k+1))`, β is constant. Formally, local constancy
on this connected interval implies constancy. This step must use the entire gap and
connectedness; merely choosing unrelated local constants would not justify the result.
Let `m_k=(g.point k+g.point(k+1))/2`, and write β_k=β(m_k).

## 3. The π jump at a node

At γ=g.point k, define the entire removable quotient `B(z)=dslope G γ z`.
Then `G(z)=(z-γ)B(z)` everywhere and `B(γ)=G'(γ)≠0`.
Both G and B are real on ℝ. At γ this follows for the derivative from
`FF.deriv_fstar_ofReal` and `fstar G=G`; away from γ it is the real difference quotient.
Choose r so that `B(z)/B(γ)` lies near 1, and let `b=log(B/B(γ))` there.
Its imaginary part is zero on the real diameter.

On the upper half-ball, principal `log(z-γ)` is holomorphic. The comparison lemma,
applied to `L-log(z-γ)-b`, gives a constant C. Thus the left boundary value is
`Im C+π`, and the right value is `Im C`, since

```
lim_(y↓0) arg(s+iy) = π  (s<0),
lim_(y↓0) arg(s+iy) = 0  (s>0).
```

These are one-sided boundary limits of the principal argument; continuity of principal
log at a negative real number must **not** be assumed. The left limit is from the
upper half-plane. Use the existing one-sided argument-continuity APIs or prove the
limits via conjugation and continuity away from the negative axis.

Pick one real point from each adjacent gap inside this small diameter. Gap constancy
then gives `β_k=β_(k-1)-π`. No limit at the zero itself is claimed.

## 4. Match the prescribed counting function

`countFn Γ` is constant on each gap. Use `FF.countFn_sub` and the fact that the relevant
half-open interval contains no node, handling either ordering of x and m_k.
Between consecutive midpoints, `(m_k,m_(k+1)]` contains exactly g.point(k+1), so

```
countFn Γ m_(k+1) - countFn Γ m_k = 1.
```

The set equality follows from the strict integer enumeration and its exact range;
it does not require a general formula for the cardinality of every grid interval.
Together with the π jump this gives equality of

```
β_k + π countFn Γ m_k
```

at k and k+1. Integer induction shows this expression is one fixed constant c for all
k∈ℤ. For x∉Γ, `Grid.exists_between` puts x in a unique open gap: equality at its
left endpoint is excluded by x∉Γ. Combine gap constancy of β and countFn with the
constant c to obtain the final statement.

The constant absorbs the normalization at 0, including the case 0∈Γ. The proof does
not evaluate β at a node, does not change `Defs.countFn`, and does not need any phase
asymptotic at infinity.

## Implementation risk

The mathematics is elementary but the boundary-lift bookkeeping is substantial:
local logarithm comparison, connected gap constancy, one-sided principal-argument
limits, and integer recurrence are separate Lean interfaces. They should be compiled
and audited incrementally. No new analytic assumption may replace any of these steps.

## Implementation verification

`GeneratingData.exists_upper_log` and `GeneratingData.boundary_phase` are proved
with the signatures above. The integer-grid/counting layer is isolated in
`BoundaryPhaseCount.lean`; the analytic local branch and jump proofs are in
`BoundaryPhase.lean`. The negative-axis argument limit uses Mathlib's
`tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero`. No dispersion theorem,
principal-value transform, or extra branch-choice assumption enters the proof.
`lake build FourierFrames.Cited.Pavlov.BoundaryPhase` succeeds without warnings.
Axiom audits of both public theorems report only `propext`, `Classical.choice`, and
`Quot.sound`.
