# P5 cardinal functions and uniform local comparison: proposed Lean interfaces

Date: 2026-11-07. Owner: `sol_kernel`. **Review:** interfaces approved by root and independently in [R13](../reviews/R13_Pavlov_Blueprint.md).
This refines §§2–4 of [P5_RouteA.md](P5_RouteA.md). No new hypothesis is added to `FF.PavlovBMO`.
The signatures below record the reviewed design; implementation status and exact refinements are listed at the end.

## 1. Imports and ownership

`FourierFrames/Cited/Pavlov/Cardinal.lean` will import
`FourierFrames.Corollary1`, `FourierFrames.Cited.PaleyWiener`,
`FourierFrames.Cited.DeBrangesFC`, and `FourierFrames.Cited.DeBrangesDE`.
It will apply the existing parameterized theorems to `paleyWiener_holds`, `theoremC_holds`, and `theoremD_holds`.
It must not import `Unconditional` or the umbrella `FourierFrames` module, avoiding a future Pavlov import cycle.

`FourierFrames/Cited/Pavlov/Harnack.lean` will import `Cardinal` and the required Mathlib complex-analysis modules.
No changes to existing library files are planned. Shared namespace: `FF.Pavlov`.

## 2. Geometry interface

Use a ℤ enumeration because finite consecutive blocks are the next consumer. Keep the generating function and
geometry independent: the geometry result only needs separation and sampling, not a de Branges representation.

```lean
structure Grid (Γ : Set ℝ) where
  point : ℤ → ℝ
  strictMono : StrictMono point
  range_eq : Set.range point = Γ
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper
  gap_lower : ∀ k, lower ≤ point (k+1) - point k
  gap_upper : ∀ k, point (k+1) - point k ≤ upper

def cell {Γ : Set ℝ} (g : Grid Γ) (k : ℤ) : Set ℝ :=
  Set.Icc ((g.point (k-1) + g.point k)/2)
    ((g.point k + g.point (k+1))/2)

theorem exists_grid {Γ : Set ℝ} (hΓ : IsSeparated Γ)
    (hs : IsSampling Γ) : Nonempty (Grid Γ)
```

Supporting facts: cells cover ℝ; their interiors are disjoint; their lengths lie between `g.lower` and `g.upper`;
for `x ∈ cell g k`, `|x-g.point k| ≤ g.upper/2`; other nodes have distance at least `g.lower/2` from the cell.
The last distance statement concerns other nodes' distance to the whole cell, not their distance to the central node.

**Dependency proof:** obtain a uniform relative-density radius from the sampling lower bound and the existing
PW bump by a separated-tail estimate. Separation gives local finiteness. Relative density gives both unbounded
ends, an order enumeration, and the upper gap bound. Existing `exists_levelSet_enum` is another route when
constructing the grid together with the phase-level representation; the independent signature avoids forcing it.

## 3. Generating function and cardinal data

The removable quotient must be represented by `dslope`, not a raw quotient at its central zero.

```lean
def cardinal (G : ℂ → ℂ) (γ : ℝ) (z : ℂ) : ℂ :=
  dslope G (γ : ℂ) z / deriv G (γ : ℂ)

structure CardinalData (Γ : Set ℝ) where
  E : ℂ → ℂ
  strictHB : IsStrictHB E
  eqPW : HEEqPW E
  sample_norm : ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Γ f
  G : ℂ → ℂ
  G_eq : G = fun z ↦ E z + fstar E z
  entire : Differentiable ℂ G
  real : fstar G = G
  zeros : ∀ z : ℂ, G z = 0 ↔ ∃ x ∈ Γ, z = (x : ℂ)
  simple : ∀ γ ∈ Γ, deriv G (γ : ℂ) ≠ 0
  cardinal_mem : ∀ γ ∈ Γ, MemPW (cardinal G γ)
  cardinal_values : ∀ γ ∈ Γ, ∀ t ∈ Γ,
    cardinal G γ (t : ℂ) = if t = γ then 1 else 0
  normBound : ℝ
  normBound_pos : 0 < normBound
  cardinal_norm : ∀ γ ∈ Γ, (pwNormSq (cardinal G γ)).toReal ≤ normBound

theorem exists_cardinalData {Γ : Set ℝ} (hΓ : IsSeparated Γ)
    (hcis : IsCompleteInterpolating Γ) : Nonempty (CardinalData Γ)
```

Only the final packaged existence theorem has no `hPW/hC/hD` parameters. Intermediate helpers can retain them
for small proofs and explicit dependencies.

**Construction:** replay `exists_E` and the phase rotation inside `completeInterpolating_zero_set`, retaining
`sample_norm`. The rotation has modulus one, so preserves the exact norm identity. `G` is real entire by
`fstar_fstar` and the fstar addition identity. Its zeros are exactly Γ by `levelSet_eq_of_cis` and
`zero_set_single`. Derivative nonvanishing follows from the diagonal de Branges kernel formula and strict phase
positivity. The kernel at γ is a nonzero scalar multiple of `dslope G γ`, giving cardinal PW membership.
The interpolation values follow from its simple zero at γ and the zero set elsewhere. Thus its sampling sum is
1; the positive sampling lower bound gives the displayed uniform PW norm. There is no dependence on a generating
product or on Pavlov.

Useful consumers, derived rather than stored:

```lean
theorem cardinal_mul_sub (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ) (z : ℂ) :
  deriv d.G (γ : ℂ) * (z-(γ : ℂ)) * cardinal d.G γ z = d.G z

theorem cardinal_zero_iff (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ) (z : ℂ) :
  cardinal d.G γ z = 0 ↔ ∃ t ∈ Γ, t ≠ γ ∧ z = (t : ℂ)

theorem cardinal_synthesis_bound (d : CardinalData Γ) :
  ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset Γ) (a : Γ → ℂ),
    (pwNormSq (fun z ↦ ∑ γ ∈ s, a γ * cardinal d.G (γ : ℝ) z)).toReal ≤
      C * ∑ γ ∈ s, ‖a γ‖^2
```

The last estimate follows directly from sampling of a finite sum and the cardinal values. It requires no abstract
Riesz-basis formalization. Prove `MemPW` of that sum explicitly before converting its norm from `ENNReal`.

## 4. Uniform Harnack helper

The external TauCeti dependency provides compact-set Harnack, which now proves the narrow complex-analytic helper in `Pavlov/Harnack.lean`.
A proposed statement is below; `rect a b r` denotes the open rectangle
`a-r < z.re`, `z.re < b+r`, `|z.im| < r`.

```lean
def rect (a b r : ℝ) : Set ℂ :=
  {z | a-r < z.re ∧ z.re < b+r ∧ |z.im| < r}

theorem norm_lower_on_rectangle
    {r D M : ℝ} (hr : 0 < r) (hD : 0 < D) (hM : 1 < M) :
    ∃ c : ℝ, 0 < c ∧ ∀ (f : ℂ → ℂ) (a b t₀ : ℝ),
      a ≤ t₀ → t₀ ≤ b → b-a ≤ D →
      Differentiable ℂ f →
      (∀ z ∈ rect a b r, f z ≠ 0) →
      (∀ z ∈ rect a b r, ‖f z‖ ≤ M) →
      f (t₀ : ℂ) = 1 →
      ∀ x ∈ Set.Icc a b, ∀ y : ℝ, |y| ≤ r/2 →
        c ≤ ‖f ((x : ℂ) + (y : ℂ)*Complex.I)‖
```

Derive this from a disc Harnack inequality for the positive harmonic function `log M - log‖f‖`, using a finite
chain of overlapping discs of radius a fixed fraction of r. The number of links is bounded by a function of
`D/r`; the constant c can be existential, so integer ceiling formulas stay internal. Bounds are needed only at
`|y| ≤ r/2`, ensuring all chain discs remain a fixed distance from the rectangle boundary. Positivity follows
from `M>1`, `f(t₀)=1` and the norm bound; zero-freeness makes the logarithmic norm harmonic.

If the harmonic API proves cumbersome, the same disc estimate can be obtained from a local analytic logarithm
and the disk Schwarz lemma applied after mapping the right half-plane to the disk. This is a proof choice,
not a new hypothesis. The rectangle theorem should be reviewed separately before building the grid application.

## 5. Harnack application interfaces

For a grid g and data d on the same Γ, take `r < g.lower/4`. Each central cardinal is zero-free on the rectangle
over its closed cell by `cardinal_zero_iff`; PW evaluation bounds and `d.cardinal_norm` give a uniform strip
upper bound. The rectangle helper therefore yields:

```lean
theorem cardinal_cell_bounds (g : Grid Γ) (d : CardinalData Γ) :
  ∃ ε c C : ℝ, 0 < ε ∧ ε < g.lower/8 ∧ 0 < c ∧ 0 < C ∧
    ∀ k : ℤ, ∀ x ∈ cell g k, ∀ y : ℝ, |y| ≤ ε →
      c ≤ ‖cardinal d.G (g.point k) ((x : ℂ)+(y : ℂ)*Complex.I)‖ ∧
      ‖cardinal d.G (g.point k) ((x : ℂ)+(y : ℂ)*Complex.I)‖ ≤ C

theorem generating_cell_bounds (g : Grid Γ) (d : CardinalData Γ) :
  ∃ ε c C : ℝ, 0 < ε ∧ ε < g.lower/8 ∧ 0 < c ∧ 0 < C ∧
    ∀ k : ℤ, ∀ x ∈ cell g k,
      (c * ‖deriv d.G (g.point k : ℂ)‖ ≤ ‖d.G ((x : ℂ)+(ε : ℂ)*Complex.I)‖ ∧
       ‖d.G ((x : ℂ)+(ε : ℂ)*Complex.I)‖ ≤ C * ‖deriv d.G (g.point k : ℂ)‖) ∧
      (c * ‖deriv d.G (g.point k : ℂ)‖ * |x-g.point k| ≤ ‖d.G (x : ℂ)‖ ∧
       ‖d.G (x : ℂ)‖ ≤ C * ‖deriv d.G (g.point k : ℂ)‖ * |x-g.point k|)
```

The constants c,C may be enlarged between the cardinal and generating versions. The shift factor
`|(x-γ)+iε|` lies between ε and a fixed upper bound, and the real factor is exactly `|x-γ|`.
These inequalities remain true at the central zero without dividing by it.

```lean
theorem generating_log_cell_comparison (g : Grid Γ) (d : CardinalData Γ) :
  ∃ ε B : ℝ, 0 < ε ∧ ε < g.lower/8 ∧ 0 ≤ B ∧
    ∀ k : ℤ, ∀ x ∈ cell g k, x ≠ g.point k →
      |Real.log ‖d.G (x : ℂ)‖ -
        Real.log ‖d.G ((x : ℂ)+(ε : ℂ)*Complex.I)‖ -
        Real.log |x-g.point k|| ≤ B
```

This is the exact interface required for the subsequent BMO/log-distance bridge; it avoids selecting nearest
points or defining an infimum distance on an arbitrary set. The cell geometry later identifies `|x-γ_k|`
with distance to Γ if desired. All logarithm arguments in the displayed off-node result are proved positive.

## 6. Review request and implementation order

The reviewed checks were:
retain the sampling norm through rotation; use `dslope` at the central node; distinguish small-scale
zero-freeness from bounded-gap control of the Harnack chain; use squared PW norms consistently.

After review: implement geometry/cardinal identities first, the narrow disc/rectangle estimate second,
and the cell and logarithm comparisons last. Every delivered Lean file must compile without `sorry`, new axioms,
or linter suppression. The blueprint's planned signatures do not become declarations until their proofs exist.


## 7. Implemented interfaces

`Cardinal.lean` now proves all generator/cardinal and grid geometry results above, without `sorry` or new axioms.
`GeneratingData` stores the original E, exact sampling norm, real entire G and zero-set identity; derivative
simplicity, cardinal membership and interpolation values are proved methods. `CardinalData` extends this base
with `normBound`, `normBound_pos`, and `cardinal_norm`. Thus use `d.toGeneratingData.simple`,
`d.toGeneratingData.cardinal_mem`, etc. for the inherited proved methods.

`exists_grid` takes separation and complete interpolation: it uses the existing full phase-level enumeration.
The independent theorem `sampling_relatively_dense hΓ hs` establishes the sampling-only bounded-hole statement.
The uniform-gap bound is then `gap_le_of_relatively_dense`. This avoids duplicating general order enumeration
machinery. `Grid.exists_cell` proves covering, and the remaining public cell geometry has the reviewed names.

`CellBounds.lean` imports the completed generic `Harnack.lean` and proves `cardinal_ne_zero_rect`,
`cardinal_cell_bounds`, `generating_cell_bounds`, and `generating_log_cell_comparison` with the reviewed
conclusions. The logarithm expression writes its inner absolute value as `abs (x-g.point k)` to disambiguate
nested absolute-value notation. No other analytic hypotheses remain in these results.

The finite synthesis API is also proved: `cardinal_synthesis_mem`, `cardinal_synthesis_value`,
`sampleSum_cardinal_synthesis`, and `cardinal_synthesis_bound`, all methods on `GeneratingData`.
The generic rectangle helper is independently documented in [P5_Harnack.md](P5_Harnack.md).

Validation: clean `lake build FourierFrames.Cited.Pavlov.CellBounds` (including Cardinal), with no warnings.
Axiom checks for `exists_cardinalData`, `exists_grid`, `cardinal_cell_bounds`, and
`generating_log_cell_comparison` report only `propext`, `Classical.choice`, and `Quot.sound`.
