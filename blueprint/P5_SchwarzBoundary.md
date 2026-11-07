# P5 weighted Poisson boundary convergence

Implemented in `FourierFrames/Cited/Pavlov/SchwarzBoundary.lean`.
Root approved the mathematical statement; sol_poisson independently approved
the local/far majorant proof before its implementation. The main public theorem is
`tendsto_schwarzIntegral_re_boundary (hu : LogIntegrable u)
(hc : ContinuousAt u x)`, with unrestricted approach through `𝓝[FF.UHP] x`.
The continuous closed-half-plane extension is a second consumer.

Use the real Poisson kernel `P_z(t)=Im z/[π((t-Re z)²+(Im z)²)]`.
Its mass is one and its product with u is integrable by the existing Schwarz
kernel integrability. The constant function is LogIntegrable by
integrability of `(1+t²)⁻¹`; hence the weighted absolute error
`|u(t)-u(x)|/(1+t²)` has finite integral L.

For ε>0, continuity at x gives δ>0 so the error is at most ε/2 on
`|t-x|<δ`. Restrict z to `|z-x|≤min(1,δ/2)`. On the complementary t region,
`|t-Re z|≥δ/2`, while `|Re z|≤|x|+1=:R`. Put
`A=2+(1+2R²)/(δ²/4)` and `C=A/π`. Elementary quadratic inequalities give
`(1+t²)/((t-Re z)²+(Im z)²)≤A`, so
`P_z(t)≤C Im z/(1+t²)` there. Globally this yields the integrable majorant

`|P_z(t)*(u(t)-u(x))| ≤ (ε/2)*P_z(t) + C Im z*|u(t)-u(x)|/(1+t²)`.

After integration the error is at most `ε/2+C Im z L`. The second term
tends to zero at the real point, which proves the requested convergence.
No boundedness of u, nontangential restriction, or pointwise measurability
beyond the supplied weighted integrability is assumed.

For the closed-half-plane extension, use holomorphic continuity in the
interior and this boundary convergence together with continuity of u along
the axis. The value on/below the axis is `u(z.re)`.


Public API:

- `tendsto_schwarzIntegral_re_boundary`: weighted integrability plus continuity
  at the single boundary point; approach is unrestricted within UHP.
- `poissonExtension`: real Schwarz integral in UHP, `u(z.re)` elsewhere.
- `continuous_poissonExtension`: when u is continuous everywhere, this extension
  is continuous on all ℂ. Its lower-half-plane definition is deliberately
  constant in the vertical direction.
- `continuousOn_poissonExtension`: the requested closed-UHP consumer.

Only project Schwarz calculus and the existing mass-one Poisson kernel are
imported. No additional external library modules were needed. The proof uses
ordinary real integrals, proves all integrability before subtraction and
comparison, and requires only the AEStronglyMeasurable consequences of
LogIntegrable.

Validation: `lake build FourierFrames.Cited.Pavlov.SchwarzBoundary` succeeds
without warnings. Axiom audits of all three public convergence/continuity
theorems report only `propext`, `Classical.choice`, and `Quot.sound`.
