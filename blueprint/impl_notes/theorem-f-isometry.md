# Theorem F: polarization of an isometric measure

Implemented in `FourierFrames/Cited/DeBrangesF/Isometry.lean`.

The defining equality of nonnegative integrals first gives `MemLp (f/E) 2 μ` for
every `f ∈ H(E)`, since its right-hand side is finite. Measurability follows from
entireness and the measurable division operation; real zeros of `E` cause no
problem, so only `IsHB E` is needed.

`measurePair μ E f g` denotes `∫ (f/E) conj(g/E) dμ`. Hölder gives integrability.
The isometry identifies its diagonal with `heInner E f f`. Expanding the two
diagonal identities for `f + g` and `f + i g` determines the real and imaginary
cross terms, proving the full polarized identity. This avoids constructing a
Hilbert-space type for `H(E)`.

Main interfaces:

- `IsIsometricMeasure.memLp`
- `IsIsometricMeasure.integrable_pair`
- `IsIsometricMeasure.integral_norm_sq`
- `IsIsometricMeasure.measurePair_eq`
- `IsIsometricMeasure.integral_pair`
- `IsIsometricMeasure.integral_kernel` (also assumes no real zeros, matching the
  existing all-points reproducing-kernel theorem)

No source corrections or changed statements are needed. The module has no
`sorry`, additional axioms, or suppressed linters.
