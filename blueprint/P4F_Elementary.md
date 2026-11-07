# P4-F: isometric measures by two reproducing-kernel identities

**Implemented:** `FF.theoremF_holds : TheoremF`, proved in
`FourierFrames/Cited/DeBrangesF.lean` and 14 supporting files (2349 lines).
The module builds without warnings; its only axioms are `propext`, `Classical.choice`,
and `Quot.sound`. Exact Lean interfaces and imports are in [P4F_Statements.md](P4F_Statements.md).
Independent mathematical and code reviews: `reviews/R11_TheoremF.md` and
`reviews/R12_TheoremF_Code.md`.

This replaces the deferred factorization route in `P4_DeBrangesFC.md`, Part F. It proves the
unchanged `FF.TheoremF` with `p = 0`. It uses no Blaschke products, inner factorization,
Phragmén–Lindelöf division, or derivative kernels. The old false `division_lemma` is unnecessary.
The route was derived independently by the `theorem_f_route` and `theorem_f_review` agents on
2026-11-07; the latter reviews the final statement and calculations below.

Throughout, `E` is strict Hermite–Biehler, `E` has no real zeros, and `μ` satisfies the exact
isometry hypothesis of `TheoremF`. Put `K(w,z) = deBrangesKernel E w z`, with the project's
convention that `K(w,·)` represents evaluation at `w` and the integral inner product is linear
in its first argument. All complex integrals below are Bochner integrals; their integrability
is included in the modules, not inferred from a totalized integral identity.

## 1. Normalization, entirely inside the existing space

For `Im z ≥ 0` set

```
θ(z) = E*(z)/E(z),          a = θ(i),                 d = 1 - |a|² > 0,
D(z) = 1 - conjugate(a)θ(z),
φ(z) = (θ(z)-a)/D(z),       ξ(z) = (z-i)/(z+i),
h(z) = K(i,z),             κ = h(i) = |E(i)|² d/(4π) > 0.
```

`κ` is real; in Lean use `(K i i).re` as the real constant. On the closed upper half-plane,
`E`, `D`, and `h` do not vanish. On the real line, `|θ|=|φ|=|ξ|=1`; in the upper half-plane,
`|θ|<1`, `|φ|<1`, and `|ξ|<1`. Also `φ(i)=ξ(i)=0`. The formula for `h` is

```
h(z) = (i/(2π)) conjugate(E(i)) E(z) D(z)/(z+i).
```

The normalized measure is

```
dν(t) = |h(t)/E(t)|² dμ(t)/κ
      = |D(t)|² dμ(t)/(π d (1+t²)).
```

The isometry applied to `h`, together with `||h||²_E=κ`, gives `ν(ℝ)=1`. Thus `ν` is a
probability measure. The auxiliary finite measure

```
dνo(t) = dμ(t)/(π(1+t²))
```

exists by `isometric_moment`. Boundary algebra gives the inverse change of measure

```
dνo(t) = |1+conjugate(a)φ(t)|² dν(t)/d.
```

This is a change of measure only: no new entire function or equality of de Branges spaces
needs to be constructed.

For `f,g ∈ H(E)`, polarization of the assumed isometry gives

```
∫ (f/h)(t) conjugate((g/h)(t)) dν(t) = ⟨f,g⟩_E/κ.
```

In particular `∫(f/h)dν=f(i)/κ`, because `g=h`. The corresponding squared norm is
`∫|f/h|²dν=||f||²_E/κ`.

## 2. The two kernel identities

For `z` in the upper half-plane write `w=ξ(z)` and define the bounded boundary function

```
Cz(t) = 1/(1-w conjugate(ξ(t)))
      = (z+i)(t-i)/(2i(t-z)).
```

Define holomorphic transforms on the upper half-plane

```
F(z) = ∫ Cz(t) dν(t),
H(z) = ∫ conjugate(φ(t)) Cz(t) dν(t),
J(z) = ∫ φ(t) Cz(t) dν(t),
c    = ∫ φ(t) dν(t).
```

Their holomorphy follows by differentiating under a finite measure integral, locally in `z`.
On a compact neighbourhood of a given `z`, `|ξ(z)|≤r<1`, so the integrands and their
derivatives are bounded by constants. In particular, `F(i)=1`, `H(i)=conjugate(c)`, `J(i)=c`.

The normalized kernel ratio is

```
Rz(t) = κ K(z,t)/(h(t) conjugate(h(z)))
      = (1-φ(t) conjugate(φ(z)))/(1-ξ(t) conjugate(ξ(z))).
```

The corresponding entire function `h Rz` is a scalar multiple of `K(z,·)` and therefore
belongs to `H(E)`. Its value at `i`, divided by `h(i)`, is `1`. Pair it against `h`, take the
complex conjugate, and obtain the first identity

```
F(z) - φ(z) H(z) = 1.                                     (K1)
```

The second normalized kernel is

```
Qz(t) = (φ(t)-φ(z))/(ξ(t)-ξ(z)).
```

For real `t` all denominators are nonzero. `h Qz` is a scalar multiple of `K(conjugate(z),·)`.
One explicit scalar is

```
h(t) Qz(t) = [i d (z+i) conjugate(E(i))/(2 D(z) E(z))] K(conjugate(z),t).
```

This follows directly from the kernel formula. Alternatively, put `η=E(i)/conjugate(E(i))`;
then on `ℝ`, `h*/h=-η φ/ξ`, and apply `memHE_fstar` to `h Rz`.
Pairing this entire function against `h` gives, when `z ≠ i`,

```
∫ Qz(t)dν(t) = φ(z)/ξ(z).
```

Multiply by `ξ(z)`, use `ξ(t)/(ξ(t)-ξ(z))=Cz(t)`, and rearrange:

```
J(z) - c = φ(z) F(z).                                    (K2)
```

At `z=i`, (K2) follows immediately from `J(i)=c` and `φ(i)=0`; no limit is required. Thus
both identities hold everywhere in the upper half-plane. No division-closure theorem for
`H(E)` is required.

## 3. Cauchy–Schwarz yields the Schur bound

The pointwise circle identity

```
|Cz(t)|² = (Cz(t)+conjugate(Cz(t))-1)/(1-|ξ(z)|²)
```

gives

```
∫|Cz|²dν = (2 Re F(z)-1)/(1-|ξ(z)|²).
```

In particular `Re F(z)>0` (indeed `Re F(z)>1/2`), because `ν` is a probability measure,
`|ξ(z)|<1`, and `Cz` is nowhere zero. Thus `F(z)≠0`.

The normalized kernel norm, by the isometry and diagonal kernel formula, is

```
∫|Rz|²dν = (1-|φ(z)|²)/(1-|ξ(z)|²) =: N(z) > 0.
```

Use (K1), (K2), and the circle identity to calculate

```
∫ Rz(t) Cz(t)dν(t)
 = [F+conjugate(F)-1-conjugate(φ)(J+conjugate(H)-c)]/(1-|ξ|²)
 = F(z) N(z).
```

Cauchy–Schwarz, applied to `Rz` and `conjugate(Cz)`, now gives

```
|F|² N² ≤ N (2 Re F-1)/(1-|ξ|²),
|F|² (1-|φ|²) ≤ 2 Re F-1,
|F-1|² ≤ |φ|² |F|².
```

By (K1), `|φ|²|H|²≤|φ|²|F|²`. At points where `φ≠0` this gives `|H|≤|F|`.
The same inequality holds at every point by continuity and density of the nonzero set of
`φ`. To justify density: `φ` is analytic on the connected upper half-plane and not identically
zero; otherwise `θ≡a` there, and continuity to any real point would contradict `|a|<1` and
`|θ(t)|=1`. Thus the identity theorem excludes any open set of zeros. One can use analytic
order at a point instead of the global identity theorem. This continuation step is essential:
canceling `|φ|²` at its zeros would be invalid.

Define

```
B(z) = H(z)/F(z),                       |B(z)| ≤ 1,
A(z) = (conjugate(a)+B(z))/(1+a B(z))
     = (conjugate(a)F(z)+H(z))/(F(z)+a H(z)).
```

Since `|a|<1`, all denominators are nonzero. Hence `A` is holomorphic on the upper half-plane
and `|A|≤1`. The second formula is preferable in Lean because it avoids an extra quotient.
The elementary norm identity used is

```
|F+aH|² - |conjugate(a)F+H|² = d (|F|²-|H|²) ≥ 0.
```

## 4. Return to the original measure

Let `Fo(z)=∫Cz dνo` and `m=νo(ℝ)`. The inverse weight from §1 and `|φ(t)|=1` give

```
d Fo = (1+|a|²)F + conjugate(a)J + aH,
d m  = 1+|a|² + conjugate(a)c + a conjugate(c).
```

Since `conjugate(a)c-a conjugate(c)` is purely imaginary, (K2) implies

```
2 Re Fo - m = Re G,
G = [(1+|a|²)(2F-1) + 2 conjugate(a)φF + 2aH]/d.
```

Use (K1), `θ=(a+φ)/(1+conjugate(a)φ)`, and the definition of `A`. Elementary field algebra
gives

```
G = (1+θA)/(1-θA) = (E+E*A)/(E-E*A).
```

The denominator is nonzero because `|θ|<1` and `|A|≤1`. Finally, the half-plane/circle
Poisson identity is

```
2 Re Cz(t)-1 = Im(z)(1+t²)/|t-z|².
```

Integrating against `νo` gives

```
2 Re Fo(z)-m = (Im z/π) ∫ |t-z|⁻²dμ(t) = (poissonInt μ z).toReal.
```

Finiteness follows from `isometric_moment` (or the displayed integral identity). This is
exactly `TheoremF`, with `p=0`. No general Herglotz representation or imaginary normalization
constant is needed.

## 5. Implemented Lean modules and dependency boundaries

1. **`Isometry.lean` / `Moment.lean`**: the already reviewed isometry polarization, `MemLp`
   bookkeeping, and finite weighted moment. Imports proved de Branges D/E/C infrastructure,
   never the old `PartF` scaffold.
2. **`Kernel.lean` and `Normalization.lean`**: `a,d,D,φ,ξ,h,κ`, their nonvanishing/norm facts, normalized probability
   measure, and the inverse weight relation. Depends on (1). Isolate pure complex identities
   from measure calculations so that `ring`/`field_simp` do not see integrals.
3. **`Cauchy.lean` and `Transforms.lean`**: for any probability/finite measure on `ℝ`, bounded boundary
   weights, and the fixed Cayley kernel `Cz`, prove integrability, holomorphy, conjugation
   and the circle square identity. Independent of de Branges once definitions are shared.
4. **`KernelIdentities.lean`**: normalized kernel and conjugate kernel formulas, (K1), (K2),
   and the exact `Rz` norm; depends on (1), (2), (3).
5. **`Schur.lean`, `Analytic.lean`, `Algebra.lean`, `Contractive.lean`**: Cauchy–Schwarz calculation, extension through zeros, holomorphy and
   contractivity of `A`; depends on (3), (4). The purely algebraic final expression for `A`
   can be proved independently as a complex-number lemma.
6. **`Poisson.lean` and `DeBrangesF.lean`**: inverse measure transformation and §4 assembly; imports (1)–(5),
   proves `theoremF_holds : TheoremF` without any cited hypothesis.

`Basic.lean` contains the shared definitions. `Herglotz.lean` proves the regularized
Herglotz transform and its Poisson real-part identity; `Poisson.lean` uses this for finiteness.

The frozen main statements and `Defs.TheoremF` remain unchanged. The root library imports
`DeBrangesF`, `Unconditional.lean` supplies `theoremF_holds`, and comparator includes
the new unconditional results. The former `PartF.lean` is now an import-only compatibility
file; the abandoned false helper has been removed.
