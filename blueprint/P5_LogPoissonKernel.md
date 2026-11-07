# P5: exact Poisson extension of a real logarithmic singularity

Target: `FourierFrames/Cited/Pavlov/LogPoissonKernel.lean`. This plan was independently reviewed and approved in R13, and the implementation
now builds cleanly. It uses a tangent substitution and periodic logarithmic
trigonometric integrals; no boundary uniqueness or log-defect theorem is used, so it
cannot create a cycle in the dispersion proof.

For `y>0`, `c=x-a`, put `w=c+iy`, `R=‖w‖>0`, and `α=arg w`. Substitute
`t=x+y tan θ`, `-π/2<θ<π/2`. The Jacobian cancels the Poisson kernel:

```
y / [π((t-x)²+y²)] dt = dθ/π.
c cosθ + y sinθ = R cos(θ-α),
log|c+y tanθ| = log R + log|cos(θ-α)| - log|cosθ|.
```

The last identity holds away from the single zero of the numerator; that singleton is
null. On this open interval `cosθ>0`. Both log-cos functions are interval integrable,
and `log|cosθ|` is π-periodic. Their integrals over any length-π interval coincide,
so their contributions cancel. Hence the transformed integral equals `log R`.
The same identity proves absolute integrability of the transformed logarithm, and the
Jacobian integrability equivalence transfers it to the real-line weighted logarithm.
In particular, `x=0,y=1` proves `LogIntegrable (log|·-a|)` without a separate tail estimate.

Planned public interface, namespace `FF.Pavlov`:

```lean
theorem logIntegrable_log_abs_sub (a : ℝ) :
  LogIntegrable (fun t ↦ Real.log |t-a|)

theorem poissonIntegral_log_abs_sub (a x : ℝ) {y : ℝ} (hy : 0 < y) :
  (∫ t : ℝ, y / (Real.pi * ((t-x)^2+y^2)) * Real.log |t-a|) =
    Real.log ‖((x-a : ℝ) : ℂ) + (y : ℂ)*Complex.I‖

theorem schwarzIntegral_re_log_abs_sub (a : ℝ) {z : ℂ} (hz : 0 < z.im) :
  (schwarzIntegral (fun t ↦ Real.log |t-a|) z).re = Real.log ‖z-(a:ℂ)‖
```

The last statement follows from the root's proved `schwarzIntegral_re`, with `x=z.re`,
`y=z.im`. An imaginary-part evaluation is optional and not needed for the real
log-defect cancellation.

Existing exact Mathlib APIs:

- `MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul` and
  `integral_image_eq_integral_abs_deriv_smul` in `Function/JacobianOneDim.lean`;
- `Real.image_tan_Ioo`, `Real.injOn_tan`, the derivative of tangent, and
  `Real.cos_pos_of_mem_Ioo` (or its equivalent endpoint inequalities);
- `Real.intervalIntegrable_log_cos`, including translated arguments, and `Real.log_abs`;
- `Function.Periodic.intervalIntegral_add_eq`: the integral over one period does not
  depend on the starting point (no exact numerical integral of log-cos is required);
- `Complex.cos_arg`, `Complex.sin_arg`, `Real.cos_sub`, and `Real.tan_eq_sin_div_cos`.

Implementation order: log-cos periodicity and translated-period integral;
pointwise logarithm identity with the explicit nonzero numerator; transformed
integrability (drop the unique zero); the tangent Jacobian formula and integrability
transfer; finally the Poisson and Schwarz statements. All Jacobian hypotheses
(injectivity, derivative, full image) are supplied explicitly. The proof does not
assume that `log 0` obeys the product rule at the omitted zero.

## Implementation verification

`lake build FourierFrames.Cited.Pavlov.LogPoissonKernel` succeeds without warnings.
The four public theorems are `integrable_poisson_log_abs_sub`,
`poissonIntegral_log_abs_sub`, `logIntegrable_log_abs_sub`, and
`schwarzIntegral_re_log_abs_sub`. The exact integral and weighted integrability are
proved together through the Jacobian equivalence; the final Schwarz theorem uses
`schwarzIntegral_re`. No boundary-uniqueness hypothesis, principal value, or numerical
evaluation of the log-cosine integral enters the proof.
Axiom audits of weighted log integrability, the exact Poisson integral, and the Schwarz
real-part identity report only `propext`, `Classical.choice`, and `Quot.sound`.
