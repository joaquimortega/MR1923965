# Theorem F: finite-measure Cauchy transforms

Proposed helper interface, for independent review before implementation:

- `diskCauchyKernel (u : ℝ → ℂ) (w : ℂ) (t : ℝ) := (1 - w * conj (u t))⁻¹`.
- `diskCauchyTransform (ρ : Measure ℝ) (u b : ℝ → ℂ) (w : ℂ) := ∫ t, b t * diskCauchyKernel u w t ∂ρ`.
- For measurable `u` with `‖u t‖ = 1`, `‖w‖ < 1` implies the denominator is nonzero and the kernel norm is at most `(1 - ‖w‖)⁻¹`.
- If `ρ` is finite and `b` is measurable and bounded, `b * kernel` is integrable and its integral is complex differentiable on the open unit ball. Differentiate under the integral; on `‖w‖ < r < 1`, the derivative is bounded by `M / (1-r)^2`.
- For probability `ρ`, the unweighted transform `F` satisfies
  `2 * (F w).re - 1 = (1 - ‖w‖²) * ∫ t, ‖diskCauchyKernel u w t‖² ∂ρ`.
  The pointwise identity follows from `‖u t‖=1`; boundedness proves integrability. In particular `(F w).re ≥ 1/2` and `F w ≠ 0`.

The kernel-square identity is also provided with the integral alone on the left. All hypotheses are explicit and the measure is not changed by these helpers.

Implementation completed in `FourierFrames/Cited/DeBrangesF/Cauchy.lean`:
finite-measure bounded-weight integrability, dominated differentiation under the integral,
probability kernel-square identity, and `Re F ≥ 1/2` with nonvanishing all compile.

`FourierFrames/Cited/DeBrangesF/Schur.lean` implements the generic probability-measure
Cauchy–Schwarz argument from K1, K2 and the normalized model-kernel norm. Its main API is
`schur_bound_of_kernel_identities`, concluding `‖F - 1‖ ≤ ‖p * F‖`. It also supplies
`norm_integral_mul_conj_sq_le`, `diskModelKernel_memLp`, and the exact mixed integral
`diskModelKernel_integral_mul`. The latter equals `(1 - ‖p‖²) * F / (1 - ‖w‖²)`;
conjugation of F is unnecessary because its norm is unchanged. Extension through zeros
and assembly of the contractive parameter are handled by `Analytic.lean` and
`Contractive.lean`.

Validation: `lake build FourierFrames.Cited.DeBrangesF.Cauchy` and
`lake build FourierFrames.Cited.DeBrangesF.Schur` completed without warnings on 2026-11-07.
No custom axioms, sorry terms, warning suppression, or heartbeat overrides are present.
Axiom audit of the holomorphy theorem, complex Cauchy–Schwarz inequality, mixed integral,
and final generic Schur bound reports only `propext`, `Classical.choice`, and `Quot.sound`.
