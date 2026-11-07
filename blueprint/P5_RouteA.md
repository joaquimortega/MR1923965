# P5 route investigation: discrete tests, shifted kernels, and BMO

Date: 2026-11-07. This is a proposed implementation route, not a proof certificate or a replacement hypothesis.
The target remains the unchanged `FF.PavlovBMO`. C/D/E/F and Paley–Wiener are now proved.
The old feasibility verdict in `P5_Pavlov.md` is not used as a stopping condition.

## 1. What can be avoided

The necessity proof of Lyubarskii–Seip, [1997 paper, §§2–3](https://arxiv.org/pdf/math/9511212), uses a discrete
Cauchy matrix and elementary positive block tests to obtain a discrete Muckenhoupt condition. Only this
necessity argument is needed; boundedness of the continuous weighted Hilbert transform and its full weighted
characterization are unnecessary. The source then compares its generating product locally with derivative
weights. The alternative below proposes using the norm of point evaluation instead of that product comparison.

A second primary reference is Semmler, [2007, Theorems 2 and 6](https://arxiv.org/pdf/0708.2787), which states the
continuous and discrete weight criteria and develops a conformal-mapping parameterization. That parameterization
would introduce substantially more infrastructure and is not proposed here.

The proposal uses existing de Branges results to construct the generating function algebraically. It does not
require constructing a canonical product to start the proof. A narrow logarithmic representation lemma remains
necessary later; it must not be silently inferred from exponential type alone.

## 2. Existing starting point and cardinal functions

`completeInterpolating_zero_set` in `Corollary1.lean` supplies `E` with `HEEqPW E` and
`G = E + E*` having precisely the real zero set Γ. In its construction the de Branges norm is exactly the sampling
norm (up to the harmless rotation). Keep that extra normalization when packaging a new helper rather than
throwing it away through the existing theorem's existential conclusion.

Kernel algebra at a phase-level point gives

```
L_k(z) = G(z)/(G'(γ_k)(z-γ_k)),
L_k(γ_j) = δ_kj.
```

The value at `γ_k` is the removable value. The kernels prove membership in PW, simplicity of every zero, and
that these are the unique cardinal functions. The sampling isomorphism gives, for finite coefficients,

```
A Σ|a_k|² ≤ ‖Σ a_k L_k‖²_PW ≤ B Σ|a_k|².
```

No Hadamard factorization is needed for these identities. Choosing one cardinal function also gives
`G(z) = G'(γ_k)(z-γ_k)L_k(z)`, hence exponential type at most π.

Missing elementary helpers:

1. Enumerate Γ increasingly by ℤ. Separation and relative density give two-sided unboundedness and
   `δ ≤ γ_(k+1)-γ_k ≤ Δ`. Relative density follows from the sampling lower bound by translating the existing
   PW bump into increasingly large holes, using its decaying real-axis bound.
2. Package the cardinal kernel identity including the removable value and derivative nonvanishing.
3. Package the sampling isomorphism as uniform synthesis bounds and the corresponding dual evaluation norm.

## 3. Discrete A2 without a weighted singular-integral theorem

Fix `0 < ε < δ/8`. The Harnack comparison of §4 gives
`|G(γ_j+iε)| ≍ ε|G'(γ_j)|` uniformly in j. Thus no auxiliary circle points are necessary.
The shifted real sequence is sampled using the usual real Plancherel–Pólya estimate applied to the PW function
`f(·+iε)`; its norm is controlled by the existing horizontal-line PW bound.
Applying this to finite cardinal sums proves

```
Σ_j w_j |Σ_k b_k/(γ_j+iε-γ_k)|² ≤ C Σ_k w_k |b_k|²,
w_j = |G'(γ_j)|².
```

Take equally large consecutive blocks I,J separated by one block. The real part of the Cauchy kernel has one
sign between them and has magnitude at least `c/N`, where N is their number of points. This uses both lower
and upper gap bounds. Test with `b_k=w_k⁻¹` supported on I, then reverse I,J. With
`W(I)=Σ_I w_k` and `V(I)=Σ_I w_k⁻¹`, the results are

```
W(J)V(I) ≤ CN²,       W(I)V(J) ≤ CN².
```

Cauchy–Schwarz gives `W(J)V(J) ≥ N²`. Multiplying the cross estimates and dividing by this positive lower
bound yields `W(I)V(I) ≤ C²N²`. This is discrete A2 for every finite consecutive block.
These are finite positive-sum estimates; no principal-value operator is constructed.
The classical source's necessity mechanism supplies the matrix-test idea; fixed shifted nodes replace its
variable circle points through the project-specific cardinal Harnack estimate.

Missing lemmas are the fixed-height Harnack comparison, shifted PW sampling bound, weighted matrix estimate,
and the positive-block A2 test. None assumes Pavlov or BMO.

## 4. Preferred local comparison: Harnack, not products

The independent `sol_poisson` investigation supplies a better replacement for the source's product-comparability
step. Fix a small `ε > 0` depending on separation. The cardinal functions `L_k` have uniformly bounded PW norms,
hence are uniformly bounded on a fixed strip by the PW evaluation bound, while `L_k(γ_k)=1`.
On a disc about γ_k containing no other zero, a fixed constant minus `log|L_k|` is positive harmonic.
Harnack therefore gives a uniform lower bound for `|L_k|` on a smaller disc. Continue the bound to
`x+iε` for x in γ_k's Voronoi cell along a uniformly bounded chain of discs that avoids the other real zeros.
Separation and the uniform upper gap bound control the chain. The upper bound was already supplied by PW.
Consequently

```
|G(x+iε)|² ≍ |G'(γ_k)|²
```

on each Voronoi cell: the additional factor `|x+iε-γ_k|²` is bounded above and below by fixed positive constants.
Cell lengths are also bounded above and below. This proves the local comparison without constructing products.
The Harnack chain and its uniform constants must be written explicitly; zero-freeness is used for the logarithm.

This comparison allows either the discrete-matrix proof of §3 followed by elementary transfer of discrete A2
to the cells, or an even more direct positive-block test. For the latter, take the finite cardinal sum
`G(z) Σ_(k∈I) c_k/(z-γ_k)` with `c_k=|G'(γ_k)|⁻²`. Its PW norm is controlled by `Σ_I c_k`.
Integrate its squared modulus on a separated neighboring block J at height ε. Positivity of the real part of
the Cauchy sum gives the lower bound by `L⁻²(Σ_I c_k)² ∫_J |G(x+iε)|² dx`.
Reverse I and J and use Cauchy–Schwarz together with the local comparison to obtain the diagonal A2 bound.
This version needs horizontal-line PW bounds and finite positive sums, rather than complex-strip sampling.

Thus the proposed missing machinery for this layer is narrow: Harnack applied to normalized cardinal functions,
a uniform geometric chain, finite positive-block tests, and bounded perturbation of intervals by cell endpoints.
Poisson-A2 stability and the full continuous weighted Hilbert transform are unnecessary for this layer.

## 5. The remaining analytic bridge: exact statements

The following independent modules suffice after shifted A2. They are genuine missing theorems, not consequences
already supplied by C/D/E/F.

1. **A2 logarithm.** If positive locally integrable w and w⁻¹ satisfy
   `(∫_I w)(∫_I w⁻¹) ≤ C|I|²`, then `log w ∈ FF.MemBMO`. Jensen and elementary logarithm bounds prove this.
   Local integrability of `log w` must be proved, using `|log w| ≤ w+w⁻¹`.
2. **Real boundary modulus from the shifted one.** The same Harnack estimate in §4 applies to real points
   inside the Voronoi cell after removing its central zero. Hence, off Γ,
   `log|G(x)| = log|G(x+iε)| + log dist(x,Γ) + O(1)`, with uniform error.
   The function `log dist(x,Γ)` is BMO when gaps have uniform positive lower and finite upper bounds:
   near one node it is a translate of `log|x|` up to bounded error, while intervals covering several cells
   have uniformly bounded mean absolute value. Prove its local integrability and this interval split explicitly.
   Therefore `log|G| ∈ BMO`. Values on Γ can be assigned arbitrarily, since Γ is countable and null.
3. **L² conjugation and BMO.** Define the Hilbert transform on L² by the Fourier multiplier
   `-i sgn ξ`. Prove its off-support Cauchy-kernel formula. The standard decomposition into twice an interval
   and its complement gives boundedness on BMO: use John–Nirenberg for local L² oscillation, the L² norm
   bound for the local piece, and dyadic telescoping of averages plus the kernel derivative bound for the tail.
   Constants require regularized transforms, since arbitrary BMO functions need not have ordinary integrable
   Hilbert transforms. A theorem about an ordinary totalized Bochner integral is insufficient.
4. **Narrow logarithmic dispersion.** For the real entire G constructed in §2, prove that an analytic logarithm
   of `G(z)` on the upper half-plane, after adding `iπz`, has boundary imaginary part equal up to a constant to
   the regularized conjugate of `log|G|`. This includes the exact mean-type coefficient π and absence of an
   additional singular term. It may be proved through a specialized Cartwright/outer lemma for
   `G/(z-γ_k) ∈ PW` with all its zeros real; it must not be assumed from the zero set alone.
   The upper boundary argument of G is constant on gaps and drops by π at each simple real zero.
   Consequently that boundary imaginary part is exactly `-π(countFn Γ x-x)+c` away from Γ.
   This direct real-boundary argument avoids Poisson smoothing of the counting function altogether.
5. **Finish in the project's definitions.** Separation makes `countFn Γ-id` locally bounded and measurable.
   Additive constants, bounded perturbations, scalar multiplication, and the estimates above yield the literal
   interval-mean `FF.MemBMO` definition. This packaging must retain local integrability.

This route avoids the full weighted Hilbert-transform characterization, Helson–Szegő theorem, canonical-product
construction, and counting-function deconvolution. It still needs unweighted L² singular-integral technology and
a precise logarithmic boundary theorem. External Lean libraries may discharge parts of those modules; inspect
actual exported statements and axioms before planning around them.

## 6. Decision points before large implementation

First formalize the cardinal and Harnack/local-comparison layer: it has the strongest reuse of the completed project and
has a direct source proof. In parallel with that work, locate a
proof/exportable formalization of the narrow logarithmic dispersion statement. If the latter cannot yet be
proved, report it as the remaining mathematical/formal dependency. Do not replace it by the desired phase-BMO
conclusion or assume the full Pavlov criterion.

The derivative comparison `φ'_E ≍ |E|⁻²` alone does not prove phase BMO (R7-17). Theorem F supplies an isometric
measure parameter but cannot be applied to an equivalent norm as though it were an exact isometry. Neither
shortcut is used here.
