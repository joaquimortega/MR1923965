# Theorem F: regularized Herglotz integral

Implemented `FourierFrames/Cited/DeBrangesF/Herglotz.lean` independently of the
isometry argument. Its only measure hypothesis is the finite moment
`∫⁻ t, ENNReal.ofReal (1 / (1 + t²)) ∂μ < ∞`.

The proof follows F.2 of the existing blueprint. Two algebraic identities make
all domination estimates uniform without splitting the integral into compact
and tail pieces:

- `1/(t-z) - t/(1+t²) = ((1+z²)/(t-z)+z)/(1+t²)`;
- `1/(t-z)² = ((1+z²)/(t-z)²+2z/(t-z)+1)/(1+t²)`.

On `Im z ≥ r > 0`, `|z| ≤ R`, the factors before `(1+t²)⁻¹` are bounded by
`(1+R²)/r+R` and `(1+R²)/r²+2R/r+1`, respectively. This proves integrability
and permits differentiation under the integral using
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the ball of radius
`min(1, Im z/2)`. The real-part identity follows by computing
`Re(-i kernel/π)` and commuting `Re` with an integrable Bochner integral.

Public result: `FF.herglotzG_spec`, with exactly the signature of F.2 in the
old scaffold. Supporting lemmas are in namespace `FF.Herglotz`; in particular,
`moment_integrable`, `kernel_integrable`, and `integral_differentiableAt`.
There is no dependence on `TheoremF`, no new axiom, and no warning suppression.
No change to the mathematical statement was needed.
