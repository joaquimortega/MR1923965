# P5 route B: a real generating function, shifted weight, and logarithmic conjugacy

Investigation dated 2026-11-07. This is a proposed mathematical route, **not an
approved implementation blueprint**. No Lean proof should be started from its
unproved analytic bridge without independent review.

## 1. The exact target and the available reduction

The unchanged target is `FF.PavlovBMO`: for a separated complete interpolating
set Γ for `PWπ`, the real function `countFn Γ x - x` is in `FF.MemBMO`.

`completeInterpolating_zero_set_unconditional` already supplies an entire
Hermite–Biehler E with `HEEqPW E` whose real entire function

    G = E + E*

has exactly the zeros Γ, including no nonreal zeros. The phase and kernel
identities imply these real zeros are simple. At γ ∈ Γ the kernel formula
identifies the normalized cardinal function with

    Lγ(z) = G(z) / (G'(γ) (z-γ)),   Lγ(γ)=1.

Thus `Lγ ∈ PWπ`; the finite cardinal synthesis bound is

    || Σ aγ Lγ ||²_PW ≤ C Σ |aγ|².                     (S)

One may obtain (S) from the inverse bounded sampling map, or directly from
the equivalent de Branges norm and its orthogonal kernel expansion. The
latter requires checking that the selected level is nonexceptional;
complete interpolation already supplies completeness. In particular the
`Lγ` have uniformly bounded PW norms. Sampling also implies bounded gaps.
Write δ>0 for a separation bound and D<∞ for an upper gap bound.

This replaces construction of a generating canonical product. It does not
by itself prove the logarithmic conjugacy assertion in §5.

## 2. A correction to the older route B

Do **not** use the implication

    HEEqPW E  ⇒  |E(x)|² ∈ A₂(ℝ).

It fails for general equivalent de Branges representatives. The primary
source Lyubarskii–Seip, *Weighted Paley–Wiener spaces*, JAMS 15 (2002),
Theorem 4 and §7 Remark 3, gives examples with zeros approaching the real
axis. Its relevant Muckenhoupt weights are regularized expressions, not
bare |E|². In its example |E(x)| is comparable to
`(1+|x|)^(2δ) dist(x, zeros(E))`, with zero heights tending to zero. On
fixed small intervals around those zeros, the A₂ products of |E|² grow
without bound: after a scalar factor the local weight is comparable to
`s²+η²`, whose average reciprocal is of order 1/η.

Source: https://doi.org/10.1090/S0894-0347-02-00397-1 ; author-uploaded
full text: https://www.researchgate.net/publication/254351423_Weighted_Paley-Wiener_spaces

The existing bounds `phaseDeriv E x * ||E x||² ≍ 1` do not fix this issue.
They control kernel norms and allow arbitrarily narrow phase spikes.

## 3. Uniform local comparability by Harnack, without products

Let Vγ be the real Voronoi interval of γ. Its length is between δ and D
(up to harmless changes in those constants). All other zeros of G lie at
least δ/2 from Vγ. The removed quotient Lγ is therefore zero-free on a
fixed-width complex neighborhood of Vγ, of height η₀<δ/8. It is analytic
there, including across γ.

The uniform PW norm bound and the usual complex evaluation estimate give
`|Lγ(z)| ≤ M₀` throughout this neighborhood, with M₀ independent of γ.
Choose M>M₀. Then

    Uγ(z) = log(M / |Lγ(z)|)

is positive harmonic there and Uγ(γ)=log M. A chain of disks of radius
comparable to δ, with at most C(D/δ+1) disks, joins γ to every point of the
closed rectangle over Vγ of a slightly smaller height. Harnack's
inequality gives a uniform upper bound for Uγ. Consequently

    c ≤ |Lγ(x+iy)| ≤ C   (x ∈ Vγ, |y|≤ε),             (LC)

for one fixed ε>0. The positive harmonic function exists locally because
a zero-free holomorphic function has harmonic log modulus; no global
logarithm or factorization is needed for this step.

Put w(x)=|G(x+iε)|². From (LC) and δ≤gap≤D,

    w(x) ≍ |G'(γ)|²     (x ∈ Vγ).                    (W)

Indeed `|x+iε-γ|` is between ε and a fixed constant. Adjacent cell values
are comparable by applying (W) at their shared endpoint. Thus w is
uniformly comparable on every interval of any fixed bounded length.

A stronger boundary consequence will be useful:

    log|G(x)| = ½log w(x) + log dist(x,Γ) + O(1)     (a.e. x).   (B)

It follows by applying (LC) at x and x+iε on the same cell. This is a
uniform bounded error, including as x approaches a node after removing
the explicit logarithmic singularity.

## 4. Shifted A₂ necessity from finite synthesis only

The PW Fourier description implies the horizontal translation norm bound
`||f(·+iε)||₂ ≤ e^(πε)||f||PW`. Apply it to the finite sum in (S), written
as

    f(z)=G(z) Σγ cγ/(z-γ),   aγ=cγ G'(γ).

It gives

    ∫ w(x) |Σγ cγ/(x+iε-γ)|² dx
       ≤ C Σγ |cγ|² |G'(γ)|².                        (T)

There is no weighted continuous Hilbert transform in (T).

Choose a finite block A of nodes in an interval of length L and take
`cγ=|G'(γ)|⁻²` on A. Evaluate the left side on an interval J of comparable
length, separated from A by distance comparable to L, with L≥max(D,ε).
All real parts of the denominators have the same sign and magnitude
comparable to L. Hence

    (∫J w) (Σγ∈A |G'(γ)|⁻²) ≤ C L².                 (X)

By (W), sums over node blocks and integrals of w⁻¹ over their Voronoi
cells are comparable, with constants depending only on δ,D. The endpoint
cells are handled by enlarging the source and target intervals by at most
D. Apply (X) in both directions to comparable separated cell blocks I,J:

    WI VJ ≤ C L²,   WJ VI ≤ C L².

Cauchy–Schwarz gives `WJ VJ ≥ |J|² ≍ L²`; multiplying the two estimates
and dividing proves `WI VI ≤ C L²`. Outward cell covers extend this to
all sufficiently long real intervals. Short intervals follow from the
fixed-length local comparability of w. Therefore w ∈ A₂.

This is the necessity mechanism in Lyubarskii–Seip, *Complete
interpolating sequences for Paley–Wiener spaces and Muckenhoupt's (Ap)
condition*, Rev. Mat. Iberoam. 13 (1997), §3, specialized to real Γ and
with its product-based local comparison replaced by §3 above. The
finite-matrix argument avoids proving the full weighted Hilbert transform
theorem or the sufficiency direction of their characterization.

Source: https://arxiv.org/pdf/math/9511212 ;
https://doi.org/10.4171/RMI/224

## 5. The remaining logarithmic conjugacy bridge

The elementary inequality `|log s|≤s+s⁻¹` and the A₂ bound imply
`log w ∈ BMO`. More explicitly, on I put A=average_I w. The mean of
`|log(w/A)|` is at most `1+[w]A₂`; passing from the constant log A to its
actual mean costs a factor two.

For separated relatively dense Γ, `x↦log dist(x,Γ)` is in BMO. On short
intervals near a node this reduces to the scale-invariant BMO estimate
for log|x|; on other short intervals it has bounded oscillation. On long
intervals its absolute integral is bounded by a constant times the
length: integrate the logarithmic singularity cell by cell, using the
lower and upper cell lengths. Formula (B) now yields

    u(x)=log|G(x)| ∈ BMO.                            (LB)

The needed special Hardy/Schwarz theorem is the following exact bridge:

> If G is real entire, has only simple separated real zeros, one quotient
> G/(z-γ₀) is in PWπ, and Γ is a uniqueness set for PWπ, then the
> upper-half-plane logarithm of G has boundary imaginary part
> `-π countFn Γ + constant`, and
>
>     -π(countFn Γ x-x) = Hreg[log|G|](x)+constant
>
> almost everywhere, for the regularized Hilbert transform, with an
> immaterial convention-dependent sign.

The proof cannot simply declare the zero-free Hardy quotient outer.
For `F=e^(iπz)G(z)/(z-γ₀) ∈ H²`, possible inner factors must be excluded.
Analytic continuation across the real line, including finite-order real
zeros, excludes singular inner mass on finite boundary points. No
Blaschke factor occurs because there are no upper-half-plane zeros.
An exponential factor `e^(iaz)`, a≥0, may remain. If a>0, the real entire
cardinal quotient has exponential type at most π-a in both directions.
Then, for sufficiently small τ>0,

    [G(z)/(z-γ₀)] sin(τ(z-γ₀))

is a nonzero PWπ function vanishing on all Γ, contradicting uniqueness.
Thus a=0. The outer logarithm gives the regularized Schwarz/Hilbert
representation, and the boundary argument jumps identify countFn.

This is a **remaining substantial theorem to prove**, not an existing
Lean result. It can be isolated as a special zero-free Hardy logarithm
representation; general Hadamard or Cartwright products are unnecessary
for the proposed route. A rigorous formal proof still needs the relevant
Hardy factorization/Poisson uniqueness infrastructure (or a direct proof
of precisely this special theorem).

Finally, the Hilbert transform maps BMO to BMO. A minimal proof needs
only its unweighted L² bound, its kernel away from support, the kernel
smoothness estimate, and the L² mean-oscillation consequence of
John–Nirenberg. For I, split `(u-u₂I)` into its part on 2I and its tail.
The local term is bounded in mean by L² boundedness and John–Nirenberg;
the tail oscillation is bounded by the convergent annulus sum
`Σ 2⁻ᵏ(k+1)||u||BMO`. This avoids the full H¹–BMO duality theorem.
Applying this to (LB) and the displayed phase bridge proves the exact
`FF.PavlovBMO` after a.e. invariance and the elementary local integrability
of the counting function.

## 6. Minimal new formal components

1. Cardinal functions and finite synthesis from existing CIS/de Branges
   machinery; complex PW evaluation and horizontal-shift norm bounds;
   bounded gaps from sampling.
2. Local Harnack inequality and the uniform chain estimate for zero-free
   quotients; Voronoi cells and finite block bookkeeping.
3. A₂ definition and finite-synthesis necessity test (T)–(X); A₂→log-BMO;
   log-distance BMO, bounded perturbation and a.e. invariance.
4. The special zero-free Hardy logarithm/outer representation and
   elimination of the exponential by uniqueness, as detailed above.
5. L² Hilbert multiplier/kernel identification and the local/tail proof
   of BMO→BMO. TauCeti's compatible CZ endpoint infrastructure is useful,
   but its L∞→BMO theorem alone does not provide this last mapping.

The difficult analytic work is concentrated in items 2, 4, 5. The route
removes full canonical product construction, continuous weighted Hilbert
transform theory, A₂ sufficiency, and the potentially circular claim that
counting differs boundedly from its height-one Poisson smoothing.

## 7. A more focused alternative to abstract Hardy factorization

The assertion in §5 can be reduced further to three specific harmonic
lemmas, rather than importing the general inner/outer factorization
machine. Put `F(z)=e^(iπz)G(z)/(z-γ₀)` and
`v(t)=log|F(t)|=u(t)-log|t-γ₀|`. The boundary v has finite absolute
logarithmic integral; this also follows from (LB) and the same elementary
fact for log|t-γ₀|.

1. **Hardy logarithmic domination.** For zero-free F∈H²(C₊),
   `log|F(x+iy)| ≤ P_y[v](x)`. This is the Jensen/subharmonic inequality
   for the logarithm, including possible negative values; it needs a
   proof, not the false assertion that every zero-free Hardy function is
   outer.
2. **Local boundary cancellation.** The difference
   `r=P[v]-log|F|` is positive harmonic. Near a nonzero real boundary
   value of F, it tends continuously to zero. Near a finite-order real
   zero, subtract its multiple of `log|z-γ|` from both terms. The identity
   `P_y[log|t-γ|](x)=log|x+iy-γ|` reduces to the nonzero case, so r again
   extends continuously with zero boundary value.
3. **Positive harmonic zero-boundary classification.** A positive
   harmonic function on C₊ extending continuously as zero on all finite
   boundary points is `r(x+iy)=a*y`, a≥0.

The only possible defect from the Poisson logarithm is therefore linear
in y. The uniqueness argument in §5 eliminates a>0: the improved upper
Hardy mean type, its lower-half-plane reflection, and multiplication by a
sufficiently small real sine produce a nonzero PWπ function vanishing on
Γ. With a=0, the analytic logarithm and the regularized Schwarz integral
have equal real parts, so differ by an imaginary constant. Their boundary
imaginary parts give the required phase/Hilbert identity.

This formulation isolates exactly the residual analytic work and avoids
Hadamard products, Blaschke products, abstract singular-inner measures,
and a general factorization theorem. These three harmonic lemmas remain
unproved in the project; the classification in item 3 is a genuine
uniqueness theorem with positivity and must not be replaced by an
unrestricted zero-boundary Dirichlet uniqueness statement (which is
false on an unbounded domain).

For elimination of the defect there is an even cleaner version requiring
no smaller-bandwidth theorem. Construct

    O(z)=exp(Schwarz[v](z)).

Jensen's inequality for the probability Poisson kernel gives
`|O|²=exp(2P[v])≤P[exp(2v)]=P[|F_boundary|²]`; therefore O∈H². Equality of
real parts gives `F=e^(iaz+ib)O`. If a>0 choose `0<τ<a` and put
`f(z)=q(z)sin(τ(z-γ₀))`, where `q=G/(z-γ₀)` is real entire. The analytic
factor `e^(iaz)sin(τ(z-γ₀))` is bounded on C₊, so `e^(iπz)f∈H²`.
Since `f*=f`, both de Branges Hardy conditions hold for
`Eπ(z)=e^(-iπz)`. The already proved Paley–Wiener identification implies
f∈PWπ. It is nonzero and vanishes on all Γ, a contradiction. This only
uses bounded analytic multiplication in H², Schwarz/Poisson integrals,
Jensen, and the existing unweighted Paley–Wiener theorem.
