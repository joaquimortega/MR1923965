# Theorem F: the finite moment

Implemented in `FourierFrames/Cited/DeBrangesF/Moment.lean`.

- `momentWeight_le_kernel` proves the pointwise estimate
  `1/(1+t²) ≤ (2π/(|E(i)|-|E*(i)|))² |K_E(i,t)/E(t)|²`.
  The proof uses the reverse triangle inequality, `|E*(t)/E(t)|=1` on the
  real axis, and the explicit kernel formula. Strictness makes its constant finite.
- `isometric_moment` integrates this estimate and uses the isometry on the
  reproducing kernel at `i`.

The old scaffold's explicit `hD : TheoremD` parameter is unnecessary: the proved
`memHE_deBrangesKernel` and `MemHE.heNormSq_lt_top` suffice. The other hypotheses
and conclusion are unchanged.

Validation: `lake build FourierFrames.Cited.DeBrangesF.Moment` succeeds without
warnings or `sorry`. No additional axioms or suppressed linters.
