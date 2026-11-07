# Theorem F: normalized transform identities

`FourierFrames/Cited/DeBrangesF/Transforms.lean` defines `cauchyF`,
`cauchyH`, `cauchyJ`, and `boundaryMean` in `FF.FMeasure`, using the
probability measure from `Normalization.lean` and the generic finite-measure
Cauchy transform from `Cauchy.lean`. It proves boundary measurability,
integrability, values at `I`, nonvanishing of `F`, and complex
differentiability on `UHP` for all three transforms.

`KernelIdentities.lean` proves the two reproduction identities:

- `cauchyF_sub_theta_mul_H`: `F - theta * H = 1`.
- `cauchyJ_sub_mean_eq_theta_mul_F`: `J - boundaryMean = theta * F`.

For the first, express `modelKernel` as a scalar multiple of `K(z,t)/h(t)`,
apply `integral_normalizedKernel`, and conjugate the resulting equality.

For the second, `normalized_conj_kernel` identifies `reflectedModelKernel`
with a scalar multiple of `K(conj z,t)/h(t)`. Its integrability is proved
before integration. Reproduction and evaluation of the same pointwise
identity at `I` give `cayley z * integral Q = theta z`. At `z=I` this is
immediate, so no division by zero or limiting argument is used.
`disk_reflected_identity` then integrates the elementary circle algebra.

`integrable_modelKernel_norm_sq` and `integral_modelKernel_norm_sq` establish
integrability and the exact norm

```
integral |modelKernel E z|^2 =
  (1 - |theta E z|^2) / (1 - |cayley z|^2).
```

The proof uses the normalized isometry for `K(z,.)` and evaluates
`normalized_kernel` on the diagonal. No factorization or division-closure
lemma is imported.

Validation: `lake build FourierFrames.Cited.DeBrangesF.KernelIdentities`
completed successfully without warnings on 2026-11-07. This builds
`Transforms` and all prerequisite modules as well. Neither module contains
`axiom`, `sorry`, or warning suppressions.
