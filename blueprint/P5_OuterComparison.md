# Outer comparison: generic interfaces

Owner: `sol_pavlov_weights`. Proposed exact interfaces; review requested before proof implementation.
File: `FourierFrames/Cited/Pavlov/OuterComparison.lean`; imports `Pavlov.Schwarz` and `HB.H2`,
whose existing import closures provide maximum modulus and complex argument. No `Unconditional` import.

```lean
theorem isH2Upper_exp_schwarzIntegral {u : ℝ → ℝ} (hu : LogIntegrable u)
    (he : Integrable (fun t : ℝ ↦ Real.exp (2*u t))) :
    IsH2Upper (fun z ↦ Complex.exp (schwarzIntegral u z))

theorem factor_of_log_defect {u : ℝ → ℝ} (hu : LogIntegrable u)
    {A : ℂ → ℂ} (hA : DifferentiableOn ℂ A UHP)
    (hnz : ∀ z ∈ UHP, A z ≠ 0) (a : ℝ)
    (hdefect : ∀ z ∈ UHP,
      (schwarzIntegral u z).re - Real.log ‖A z‖ = a*z.im) :
    ∃ b : ℝ, ∀ z ∈ UHP,
      A z = Complex.exp (Complex.I*((a : ℂ)*z+(b : ℂ))) *
        Complex.exp (schwarzIntegral u z)
```

The first theorem makes no boundary-value assumption. Holomorphy is the exponential of the proved Schwarz
integral. The Poisson kernel defines a probability measure for each upper point. Both `u` and `exp(2u)`
are integrable against it: the former from `poissonKernel_mul_integrable`, the latter from boundedness of
the kernel and the supplied L¹ assumption. Jensen for the convex exponential gives the pointwise bound
`‖exp(Su)‖² ≤ P[exp(2u)]`. Tonelli and Poisson normalization give the uniform horizontal L² bound.
All changes between real integrals and lintegrals require the nonnegative measurable integrands explicitly.

For the second theorem, B(z)=A(z)*exp(-Su(z)-i*a*z) is holomorphic and has norm one on UHP by hdefect.
The maximum-modulus theorem on the connected open upper half-plane makes it a constant c. Normalize at I;
`‖c‖=1`, hence `c=exp(i*arg c)`. Exp addition and cancellation yield the displayed factorization with
b=`arg c`. No positivity of a and no logarithm branch are needed.

## Implementation and review

Root and `sol_poisson` independently approved both interfaces; `sol_poisson` recorded approval in R13.
Both generic helpers are now implemented in `OuterComparison.lean` and pass Lean checking without warnings.
The proof uses no new axioms, `sorry`, or linter suppressions.

For Jensen, the implementation directly integrates the exponential tangent inequality
`exp(m)*(1+2u(t)-m) ≤ exp(2u(t))`, where `m=2 Re S[u](z)`, against the normalized positive Poisson kernel.
The integral of its left side is exactly exp(m), because the kernel has mass one and
`m=2∫P*u`. This is the scalar Jensen inequality without constructing a separate probability measure.
The local integrability inputs are explicitly proved before this integration.

Two quantitative public helpers accompany `isH2Upper_exp_schwarzIntegral`:

```lean
theorem norm_exp_schwarzIntegral_sq_le {u : ℝ → ℝ} (hu : LogIntegrable u)
    (he : Integrable (fun t : ℝ ↦ Real.exp (2*u t))) {z : ℂ} (hz : 0 < z.im) :
    ‖Complex.exp (schwarzIntegral u z)‖^2 ≤
      ∫ t : ℝ, z.im/(Real.pi*((t-z.re)^2+z.im^2))*Real.exp (2*u t)

theorem lintegral_exp_schwarzIntegral_sq_le {u : ℝ → ℝ} (hu : LogIntegrable u)
    (he : Integrable (fun t : ℝ ↦ Real.exp (2*u t))) {y : ℝ} (hy : 0 < y) :
    (∫⁻ x : ℝ, ‖Complex.exp (schwarzIntegral u ((x : ℂ)+(y : ℂ)*I))‖ₑ^2) ≤
      ENNReal.ofReal (∫ t : ℝ, Real.exp (2*u t))
```

The latter is a genuine Tonelli calculation, with joint ae measurability derived from the continuous Poisson
kernel and the supplied integrable exponential. The inner kernel mass in the horizontal variable is one by
reflection symmetry of the squared difference. Thus the Hardy constant is exactly the boundary exponential
mass, rather than an unspecified enlargement.
