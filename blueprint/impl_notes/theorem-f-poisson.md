# Theorem F: return to the original measure

`FourierFrames/Cited/DeBrangesF/Poisson.lean` implements §4 of
`blueprint/P4F_Elementary.md`, approved in `reviews/R11_TheoremF.md`.

- `poissonWeightedMeasure μ` is `μ.withDensity (ofReal (1/(π(1+t²))))`.
  The finite moment implies this is a finite measure.
- `FMeasure.normalizedDensity_mul_inverse` proves the pointwise real density
  cancellation using `baseKernel_div_norm_sq`, `baseNorm_eq`, and
  `one_add_conj_anchor_mul_theta`. `poissonWeightedMeasure_eq` lifts it to
  the equality of measures with the inverse normalized circle weight.
- `originalCauchyF μ z` and `originalMass μ` are the original weighted
  transform and its real total mass. `originalCauchyF_expand` and
  `originalMass_expand` give the two complex linear identities in §4.
- `poissonInt_cayley_spec hm hz` proves finiteness and
  `(poissonInt μ z).toReal = 2*(originalCauchyF μ z).re-originalMass μ`.
  The proof integrates the explicit pointwise Cayley Poisson identity.
  The existing elementary regularized Herglotz integral supplies only the
  finite-moment integrability/finiteness facts; no representation theorem
  is invoked.

Validation: `lake build FourierFrames.Cited.DeBrangesF.Poisson` succeeds
without warnings. The module contains no `sorry`, axioms, or warning
suppression.
