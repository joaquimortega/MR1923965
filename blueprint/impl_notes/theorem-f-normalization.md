# Theorem F: normalization of the isometric measure

Implemented `FourierFrames/Cited/DeBrangesF/Normalization.lean` after independent
approval of `blueprint/P4F_Normalization.md` by the route and review agents.

The density is represented exactly in `ℝ≥0∞` as
`‖K_E(i,t)/E(t)‖ₑ² / ENNReal.ofReal (K_E(i,i)).re`.
`normalizedKernelDensity_eq` gives its ordinary-real form. The resulting
`normalizedKernelMeasure μ E` is a probability measure by
`normalizedKernelMeasure_probability hE h0 hμ`.

For arbitrary `f : ℝ → ℂ`, `integral_normalizedKernelMeasure` and
`integrable_normalizedKernelMeasure_iff` give the standard weighted integral
and integrability formulas. For `f,g ∈ H(E)`, the specialized API is:

- `integrable_normalizedKernel_pair`, `integral_normalizedKernel_pair`;
- `integrable_normalizedKernel`, `integral_normalizedKernel`;
- `integrable_normalizedKernel_norm_sq`, `integral_normalizedKernel_norm_sq`;
- `memLp_normalizedKernel`.

All take `hE : IsStrictHB E`, `h0 : ∀ t : ℝ, E t ≠ 0`, and
`hμ : IsIsometricMeasure μ E`, followed by the `MemHE` hypotheses.
The pairing is `heInner E f g / κ`; the mean is `f(i)/κ`; the squared norm
is `(heNormSq E f).toReal / κ`.

`kernel_i_real_ne_zero` follows from the pointwise moment estimate. It permits
pointwise cancellation of the kernel in the density. `kernel_i_re_pos` and
`heNormSq_kernel_i` provide positivity and the precise norm normalization.

This module imports `Isometry.lean` for polarized isometry, and `Moment.lean`
for the kernel's real nonvanishing. It imports no unfinished scaffold and
changes no statement in `Defs.lean`.
