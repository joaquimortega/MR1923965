# P4F: normalization by the kernel at i

This module is `FourierFrames/Cited/DeBrangesF/Normalization.lean`, importing
`Moment.lean`. It uses no part of Theorem F.

Let `h(z)=K_E(i,z)` and `κ=Re K_E(i,i)`. For strict Hermite–Biehler `E` with no
real zeros, `κ=(|E(i)|²−|E(-i)|²)/(4π)>0`. Since `h∈H(E)`, the kernel norm
identity gives `heNormSq E h = ENNReal.ofReal κ`.

For an isometric measure `μ`, define

```lean
def normalizedKernelMeasure (μ : Measure ℝ) (E : ℂ → ℂ) : Measure ℝ :=
  μ.withDensity (fun t ↦ ‖deBrangesKernel E I t / E t‖ₑ ^ 2 /
    ENNReal.ofReal (deBrangesKernel E I I).re)
```

Its mass is one: integrate the density, move out the finite positive constant
`κ⁻¹`, apply the isometry to `h`, and apply the kernel norm identity. Thus:

```lean
theorem normalizedKernelMeasure_probability {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) :
    IsProbabilityMeasure (normalizedKernelMeasure μ E)
```

The density is pointwise equal to
`ENNReal.ofReal (‖deBrangesKernel E I t / E t‖² / κ)`.
The standard `withDensity` integration formulas therefore transport integrals
against this probability measure to the original isometric measure. All
functions involved are measurable because `E` and the kernel are entire.

Dependencies: `deBrangesKernel_diag`, `memHE_deBrangesKernel`,
`heNormSq_kernel`, `MemHE.heNormSq_lt_top`, `IsIsometricMeasure`, and standard
measure-theoretic `withDensity` formulas. No Hardy boundary theorem, factorization,
or infinite product is needed.
