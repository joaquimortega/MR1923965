# Theorem F: exact Lean statements and dependencies

This appendix records the public interfaces of the elementary proof in
[`FourierFrames/Cited/DeBrangesF`](../FourierFrames/Cited/DeBrangesF) and its
[root assembly](../FourierFrames/Cited/DeBrangesF.lean). Read it with the detailed
mathematical proof in [P4F_Elementary.md](P4F_Elementary.md), the normalization
proof in [P4F_Normalization.md](P4F_Normalization.md), and the independent
review [R11_TheoremF.md](../reviews/R11_TheoremF.md).

Definitions below retain their source bodies. Theorem and lemma headers are
copied exactly from the source, with their proofs replaced by `by sorry`
**only in this Markdown appendix**. These are interface listings, not additional
Lean source files or assumptions of the formalization. Namespace and `variable`
commands are included, so implicit parameters remain explicit in context.
The open declarations used by the listings are:

```lean
open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace
noncomputable section
```

The modules are listed in an order compatible with their imports. Each section
states its direct imports; together these specify the dependency graph. The
common foundation `DeBrangesFC` supplies the established de Branges C/D/E
results, including reproducing kernels and their Hilbert-space identities.
`FourierFrames.Defs` supplies the unchanged predicates and theorem statements.
No factorization or division-closure lemma enters this dependency chain.

The mathematical and Lean dependency boundaries correspond as follows:

| Proof stage | Modules | Main exported results |
| --- | --- | --- |
| §1: isometry and finite moment | `Basic`, `Isometry`, `Moment` | `IsIsometricMeasure.integral_pair`, `isometric_moment` |
| §1: normalization | `Kernel`, `Normalization` | `normalized_kernel`, `normalizedKernelMeasure_probability`, `integral_normalizedKernel_pair` |
| §2: holomorphic transforms | `Cauchy`, `Transforms` | `diskCauchyTransform_differentiableOn`, `differentiableOn_cauchyF/H/J` |
| §2: two reproduction identities | `KernelIdentities` | `cauchyF_sub_theta_mul_H`, `cauchyJ_sub_mean_eq_theta_mul_F`, `integral_modelKernel_norm_sq` |
| §3: Cauchy–Schwarz and zeros | `Schur`, `Analytic`, `Contractive` | `schur_bound_of_kernel_identities`, `norm_le_on_upper_of_mul_norm_le`, `isometricSchur_spec` |
| §4: inverse weights and Poisson | `Herglotz`, `Poisson`, `Algebra` | `originalCauchyF_expand`, `originalMass_expand`, `poissonInt_cayley_spec`, `weighted_cauchy_cayley_re` |
| §4: final assembly | root `DeBrangesF` | `poissonInt_eq_isometricSchur`, `theoremF_holds` |

The unchanged target in `FourierFrames/Defs.lean` is:

```lean
namespace FF
def TheoremF : Prop :=
  ∀ (μ : Measure ℝ) (E : ℂ → ℂ), IsStrictHB E → (∀ x : ℝ, E x ≠ 0) →
    (∀ f : ℂ → ℂ, MemHE E f → ∫⁻ t, ‖f t / E t‖ₑ ^ 2 ∂μ = heNormSq E f) →
    ∃ A : ℂ → ℂ, DifferentiableOn ℂ A {z : ℂ | 0 < z.im} ∧ (∀ z : ℂ, 0 < z.im → ‖A z‖ ≤ 1) ∧
      ∃ p : ℝ, 0 ≤ p ∧ ∀ z : ℂ, 0 < z.im → poissonInt μ z ≠ ∞ ∧
        (poissonInt μ z).toReal + p * z.im =
          ((E z + fstar E z * A z) / (E z - fstar E z * A z)).re
end FF
```

The implementation proves this with `p = 0`.

## Basic.lean — Shared isometry hypothesis and the regularized transform.

Source: [Basic.lean](../FourierFrames/Cited/DeBrangesF/Basic.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesFC
```

The exact isometry hypothesis is named without strengthening it. The regularized transform is retained for the auxiliary Poisson estimates. Definitions have no proof obligations.

Public interface:

```lean
namespace FF

def IsIsometricMeasure (μ : Measure ℝ) (E : ℂ → ℂ) : Prop :=
  ∀ f : ℂ → ℂ, MemHE E f → ∫⁻ t, ‖f t / E t‖ₑ ^ 2 ∂μ = heNormSq E f

def herglotzG (μ : Measure ℝ) (c : ℝ) (z : ℂ) : ℂ :=
  -(I / Real.pi) * ∫ t : ℝ, (((t : ℂ) - z)⁻¹ - ((t / (1 + t ^ 2) : ℝ) : ℂ)) ∂μ + I * c

end FF
```

## Isometry.lean — Polarization and measure pairings.

Source: [Isometry.lean](../FourierFrames/Cited/DeBrangesF/Isometry.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesF.Basic
```

First turn the isometry into `MemLp` and integrability statements. Polarization of the diagonal quadratic form identifies the complex measure pairing with `heInner`; reproducing-kernel integration follows from `heInner_kernel`. See [the isometry notes](impl_notes/theorem-f-isometry.md) and §1 of the elementary proof.

Public interface:

```lean
namespace FF

variable {μ : Measure ℝ} {E : ℂ → ℂ}

theorem IsIsometricMeasure.memLp (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f : ℂ → ℂ} (hf : MemHE E f) : MemLp (fun t : ℝ ↦ f t / E t) 2 μ := by sorry

theorem IsIsometricMeasure.integrable_pair (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    Integrable (fun t : ℝ ↦ f t / E t * conj (g t / E t)) μ := by sorry

theorem IsIsometricMeasure.integral_norm_sq (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f : ℂ → ℂ} (hf : MemHE E f) :
    ∫ t : ℝ, ‖f t / E t‖ ^ 2 ∂μ = (heNormSq E f).toReal := by sorry

def measurePair (μ : Measure ℝ) (E f g : ℂ → ℂ) : ℂ :=
  ∫ t : ℝ, f t / E t * conj (g t / E t) ∂μ

theorem measurePair_smul_left (μ : Measure ℝ) (E f g : ℂ → ℂ) (c : ℂ) :
    measurePair μ E (fun z ↦ c * f z) g = c * measurePair μ E f g := by sorry

theorem measurePair_smul_right (μ : Measure ℝ) (E f g : ℂ → ℂ) (c : ℂ) :
    measurePair μ E f (fun z ↦ c * g z) = conj c * measurePair μ E f g := by sorry

theorem IsIsometricMeasure.measurePair_self (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f : ℂ → ℂ} (hf : MemHE E f) : measurePair μ E f f = heInner E f f := by sorry

theorem IsIsometricMeasure.measurePair_add_left (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f g k : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) (hk : MemHE E k) :
    measurePair μ E (fun z ↦ f z + g z) k =
      measurePair μ E f k + measurePair μ E g k := by sorry

theorem IsIsometricMeasure.measurePair_add_right (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f g k : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) (hk : MemHE E k) :
    measurePair μ E f (fun z ↦ g z + k z) =
      measurePair μ E f g + measurePair μ E f k := by sorry

theorem IsIsometricMeasure.measurePair_eq (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    measurePair μ E f g = heInner E f g := by sorry

theorem IsIsometricMeasure.integral_pair (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    ∫ t : ℝ, f t / E t * conj (g t / E t) ∂μ = heInner E f g := by sorry

theorem IsIsometricMeasure.integral_kernel (hμ : IsIsometricMeasure μ E) (hE : IsHB E)
    (h0 : ∀ x : ℝ, E x ≠ 0) {f : ℂ → ℂ} (hf : MemHE E f) (w : ℂ) :
    ∫ t : ℝ, f t / E t * conj (deBrangesKernel E w t / E t) ∂μ = f w := by sorry

end FF
```

## Moment.lean — Finite weighted moment.

Source: [Moment.lean](../FourierFrames/Cited/DeBrangesF/Moment.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesF.Basic
```

Compare the moment weight with the squared kernel at `I`, then integrate and apply the exact isometry. Strictness makes the comparison constant positive. See [the moment notes](impl_notes/theorem-f-moment.md).

Public interface:

```lean
namespace FF

theorem momentWeight_le_kernel {E : ℂ → ℂ} (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) (t : ℝ) :
    1 / (1 + t ^ 2) ≤
      (2 * Real.pi / (‖E I‖ - ‖fstar E I‖)) ^ 2 *
        ‖deBrangesKernel E I t / E t‖ ^ 2 := by sorry

theorem isometric_moment {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) :
    ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞ := by sorry

end FF
```

## Kernel.lean — Normalization coordinates and pure kernel algebra.

Source: [Kernel.lean](../FourierFrames/Cited/DeBrangesF/Kernel.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesF.Basic
```

The Cayley map and the disk automorphism have unit boundary modulus and strict interior modulus. The kernel at `I` has no zeros in the closed upper half-plane where `E` is nonzero. Substitute its explicit formula in the kernel quotient to obtain `normalized_kernel`; the reflected formula uses the kernel at `conj z`. All divisions carry explicit nonvanishing hypotheses. See §§1–2 of the elementary proof.

Public interface:

```lean
namespace FF.FMeasure

def cayley (z : ℂ) : ℂ := (z - I) / (z + I)

def anchor (E : ℂ → ℂ) : ℂ := thetaFn E I

def defect (E : ℂ → ℂ) : ℝ := 1 - ‖anchor E‖ ^ 2

def denom (E : ℂ → ℂ) (z : ℂ) : ℂ := 1 - conj (anchor E) * thetaFn E z

def theta (E : ℂ → ℂ) (z : ℂ) : ℂ := (thetaFn E z - anchor E) / denom E z

def baseKernel (E : ℂ → ℂ) : ℂ → ℂ := deBrangesKernel E I

def baseNorm (E : ℂ → ℂ) : ℝ := (deBrangesKernel E I I).re

theorem add_I_ne_zero {z : ℂ} (hz : 0 ≤ z.im) : z + I ≠ 0 := by sorry

theorem sub_conj_ne_zero {z w : ℂ} (hz : 0 < z.im) (hw : 0 ≤ w.im) : w - conj z ≠ 0 := by sorry

theorem cayley_norm_sq_diff (z : ℂ) : ‖z + I‖ ^ 2 - ‖z - I‖ ^ 2 = 4 * z.im := by sorry

theorem norm_cayley_lt_one {z : ℂ} (hz : 0 < z.im) : ‖cayley z‖ < 1 := by sorry

theorem norm_cayley_real (t : ℝ) : ‖cayley (t : ℂ)‖ = 1 := by sorry

@[simp] theorem cayley_I : cayley I = 0 := by sorry

theorem differentiableOn_cayley : DifferentiableOn ℂ cayley UHP := by sorry

theorem norm_thetaFn_lt_one {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ} (hz : z ∈ UHP) :
    ‖thetaFn E z‖ < 1 := by sorry

theorem norm_thetaFn_real {E : ℂ → ℂ} (h0 : ∀ t : ℝ, E t ≠ 0) (t : ℝ) :
    ‖thetaFn E t‖ = 1 := by sorry

theorem norm_anchor_lt_one {E : ℂ → ℂ} (hE : IsStrictHB E) : ‖anchor E‖ < 1 := by sorry

theorem defect_pos {E : ℂ → ℂ} (hE : IsStrictHB E) : 0 < defect E := by sorry

theorem one_sub_conj_mul_ne_zero {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) :
    1 - conj a * b ≠ 0 := by sorry

theorem denom_ne_zero {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ} (hz : z ∈ UHP) :
    denom E z ≠ 0 := by sorry

theorem denom_real_ne_zero {E : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (t : ℝ) : denom E t ≠ 0 := by sorry

theorem mobius_norm_sq_diff (a b : ℂ) :
    ‖1 - conj a * b‖ ^ 2 - ‖b - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by sorry

theorem norm_theta_lt_one {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ} (hz : z ∈ UHP) :
    ‖theta E z‖ < 1 := by sorry

theorem norm_theta_real {E : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (t : ℝ) : ‖theta E t‖ = 1 := by sorry

@[simp] theorem theta_I (E : ℂ → ℂ) : theta E I = 0 := by sorry

theorem differentiableOn_thetaFn {E : ℂ → ℂ} (hE : IsHB E) :
    DifferentiableOn ℂ (thetaFn E) UHP := by sorry

theorem differentiableOn_theta {E : ℂ → ℂ} (hE : IsStrictHB E) :
    DifferentiableOn ℂ (theta E) UHP := by sorry

theorem continuousAt_thetaFn_real {E : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (t : ℝ) : ContinuousAt (thetaFn E) (t : ℂ) := by sorry

theorem continuousAt_theta_real {E : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (t : ℝ) : ContinuousAt (theta E) (t : ℂ) := by sorry

theorem thetaFn_norm_le_one_closed {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ}
    (hz : 0 ≤ z.im) (he : E z ≠ 0) : ‖thetaFn E z‖ ≤ 1 := by sorry

theorem denom_closed_ne_zero {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ}
    (hz : 0 ≤ z.im) (he : E z ≠ 0) : denom E z ≠ 0 := by sorry

theorem baseKernel_eq {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ}
    (hz : 0 ≤ z.im) (he : E z ≠ 0) :
    baseKernel E z = (I / (2 * Real.pi)) * conj (E I) * E z * denom E z / (z + I) := by sorry

theorem baseKernel_ne_zero {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ}
    (hz : 0 ≤ z.im) (he : E z ≠ 0) : baseKernel E z ≠ 0 := by sorry

theorem baseNorm_eq {E : ℂ → ℂ} (hE : IsStrictHB E) :
    baseNorm E = ‖E I‖ ^ 2 * defect E / (4 * Real.pi) := by sorry

theorem baseNorm_pos {E : ℂ → ℂ} (hE : IsStrictHB E) : 0 < baseNorm E := by sorry

theorem baseKernel_I {E : ℂ → ℂ} : baseKernel E I = (baseNorm E : ℂ) := by sorry

theorem theta_ne_zero_of_numerator {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ}
    (hz : z ∈ UHP) (hn : fstar E z - anchor E * E z ≠ 0) : theta E z ≠ 0 := by sorry

theorem defect_complex (E : ℂ → ℂ) :
    (defect E : ℂ) = 1 - anchor E * conj (anchor E) := by sorry

theorem mobius_kernel (a u v : ℂ) (hu : 1 - conj a * u ≠ 0) (hv : 1 - conj a * v ≠ 0) :
    1 - ((u - a) / (1 - conj a * u)) * conj ((v - a) / (1 - conj a * v)) =
      (1 - a * conj a) * (1 - u * conj v) /
        ((1 - conj a * u) * conj (1 - conj a * v)) := by sorry

theorem theta_kernel {E : ℂ → ℂ} {z t : ℂ}
    (ht : denom E t ≠ 0) (hz : denom E z ≠ 0) :
    1 - theta E t * conj (theta E z) =
      (defect E : ℂ) * (1 - thetaFn E t * conj (thetaFn E z)) /
        (denom E t * conj (denom E z)) := by sorry

theorem cayley_kernel {z t : ℂ} (ht : t + I ≠ 0) (hz : z + I ≠ 0) :
    1 - cayley t * conj (cayley z) =
      -(2 * I) * (t - conj z) / ((t + I) * (conj z - I)) := by sorry

theorem kernel_eq_theta {E : ℂ → ℂ} {z t : ℂ} (hz : E z ≠ 0) (ht : E t ≠ 0)
    (hne : t ≠ conj z) :
    deBrangesKernel E z t = (I / (2 * Real.pi)) * E t * conj (E z) *
      (1 - thetaFn E t * conj (thetaFn E z)) / (t - conj z) := by sorry

theorem normalized_kernel {E : ℂ → ℂ} (hE : IsStrictHB E) {z t : ℂ}
    (hz : z ∈ UHP) (ht : 0 ≤ t.im) (hEt : E t ≠ 0) :
    (baseNorm E : ℂ) * deBrangesKernel E z t / (baseKernel E t * conj (baseKernel E z)) =
      (1 - theta E t * conj (theta E z)) / (1 - cayley t * conj (cayley z)) := by sorry

def conjKernelCoeff (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  I * (defect E : ℂ) / 2 * (z + I) * conj (E I) / (denom E z * E z)

theorem normalized_conj_kernel {E : ℂ → ℂ} (hE : IsStrictHB E) {z t : ℂ}
    (hz : z ∈ UHP) (ht : 0 ≤ t.im) (hEt : E t ≠ 0) (htz : t ≠ z) :
    baseKernel E t * ((theta E t - theta E z) / (cayley t - cayley z)) =
      conjKernelCoeff E z * deBrangesKernel E (conj z) t := by sorry

theorem one_add_conj_anchor_mul_theta {E : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ}
    (hz : 0 ≤ z.im) (he : E z ≠ 0) :
    1 + conj (anchor E) * theta E z = (defect E : ℂ) / denom E z := by sorry

theorem baseKernel_div_norm_sq {E : ℂ → ℂ} (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) (t : ℝ) :
    ‖baseKernel E t / E t‖ ^ 2 =
      ‖E I‖ ^ 2 * ‖denom E t‖ ^ 2 / (4 * Real.pi ^ 2 * (1+t^2)) := by sorry

end FF.FMeasure
```

## Normalization.lean — Probability measure and transfer of pairings.

Source: [Normalization.lean](../FourierFrames/Cited/DeBrangesF/Normalization.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesF.Moment
import FourierFrames.Cited.DeBrangesF.Isometry
```

Weight the original measure by `|K(I,t)/E(t)|²/κ`. The kernel norm and isometry give mass one. Pointwise cancellation of the density transfers pairings, means, and squared norms. Integrability is transferred explicitly through `withDensity`, before identities are integrated. See [the normalization notes](impl_notes/theorem-f-normalization.md).

Public interface:

```lean
namespace FF

theorem kernel_i_re_pos {E : ℂ → ℂ} (hE : IsStrictHB E) :
    0 < (deBrangesKernel E I I).re := by sorry

theorem heNormSq_kernel_i {E : ℂ → ℂ} (hE : IsHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) :
    heNormSq E (deBrangesKernel E I) = ENNReal.ofReal (deBrangesKernel E I I).re := by sorry

def normalizedKernelMeasure (μ : Measure ℝ) (E : ℂ → ℂ) : Measure ℝ :=
  μ.withDensity (fun t ↦ ‖deBrangesKernel E I t / E t‖ₑ ^ 2 /
    ENNReal.ofReal (deBrangesKernel E I I).re)

theorem normalizedKernelDensity_eq {E : ℂ → ℂ} (hE : IsStrictHB E) (t : ℝ) :
    ‖deBrangesKernel E I t / E t‖ₑ ^ 2 / ENNReal.ofReal (deBrangesKernel E I I).re =
      ENNReal.ofReal (‖deBrangesKernel E I t / E t‖ ^ 2 /
        (deBrangesKernel E I I).re) := by sorry

theorem measurable_normalizedKernelDensity {E : ℂ → ℂ} (hE : IsHB E) :
    Measurable (fun t : ℝ ↦ ‖deBrangesKernel E I t / E t‖ₑ ^ 2 /
      ENNReal.ofReal (deBrangesKernel E I I).re) := by sorry

theorem normalizedKernelMeasure_probability {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) :
    IsProbabilityMeasure (normalizedKernelMeasure μ E) := by sorry

theorem integral_normalizedKernelMeasure {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (f : ℝ → ℂ) :
    ∫ t, f t ∂normalizedKernelMeasure μ E =
      ∫ t, ((‖deBrangesKernel E I t / E t‖ ^ 2 /
        (deBrangesKernel E I I).re : ℝ) : ℂ) * f t ∂μ := by sorry

theorem kernel_i_real_ne_zero {E : ℂ → ℂ} (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) (t : ℝ) : deBrangesKernel E I t ≠ 0 := by sorry

theorem normalizedKernel_pair_density {E : ℂ → ℂ} (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) (f g : ℂ → ℂ) (t : ℝ) :
    ((‖deBrangesKernel E I t / E t‖ ^ 2 /
      (deBrangesKernel E I I).re : ℝ) : ℂ) *
        (f t / deBrangesKernel E I t * conj (g t / deBrangesKernel E I t)) =
      ((deBrangesKernel E I I).re : ℂ)⁻¹ * (f t / E t * conj (g t / E t)) := by sorry

theorem integrable_normalizedKernelMeasure_iff {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (f : ℝ → ℂ) :
    Integrable f (normalizedKernelMeasure μ E) ↔
      Integrable (fun t : ℝ ↦ ((‖deBrangesKernel E I t / E t‖ ^ 2 /
        (deBrangesKernel E I I).re : ℝ) : ℂ) * f t) μ := by sorry

theorem integrable_normalizedKernel_pair {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    Integrable (fun t : ℝ ↦ f t / deBrangesKernel E I t *
      conj (g t / deBrangesKernel E I t)) (normalizedKernelMeasure μ E) := by sorry

theorem integral_normalizedKernel_pair {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    ∫ t : ℝ, f t / deBrangesKernel E I t *
      conj (g t / deBrangesKernel E I t) ∂normalizedKernelMeasure μ E =
        heInner E f g / (deBrangesKernel E I I).re := by sorry

theorem integrable_normalizedKernel {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f : ℂ → ℂ} (hf : MemHE E f) :
    Integrable (fun t : ℝ ↦ f t / deBrangesKernel E I t) (normalizedKernelMeasure μ E) := by sorry

theorem integral_normalizedKernel {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f : ℂ → ℂ} (hf : MemHE E f) :
    ∫ t : ℝ, f t / deBrangesKernel E I t ∂normalizedKernelMeasure μ E =
      f I / (deBrangesKernel E I I).re := by sorry

theorem integrable_normalizedKernel_norm_sq {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f : ℂ → ℂ} (hf : MemHE E f) :
    Integrable (fun t : ℝ ↦ ‖f t / deBrangesKernel E I t‖ ^ 2)
      (normalizedKernelMeasure μ E) := by sorry

theorem integral_normalizedKernel_norm_sq {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f : ℂ → ℂ} (hf : MemHE E f) :
    ∫ t : ℝ, ‖f t / deBrangesKernel E I t‖ ^ 2 ∂normalizedKernelMeasure μ E =
      (heNormSq E f).toReal / (deBrangesKernel E I I).re := by sorry

theorem memLp_normalizedKernel {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {f : ℂ → ℂ} (hf : MemHE E f) :
    MemLp (fun t : ℝ ↦ f t / deBrangesKernel E I t) 2
      (normalizedKernelMeasure μ E) := by sorry

end FF
```

## Cauchy.lean — Finite-measure Cauchy transforms on the disk.

Source: [Cauchy.lean](../FourierFrames/Cited/DeBrangesF/Cauchy.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesF.Basic
```

Bound the kernel by `(1-|w|)⁻¹` and the derivative by `M(1-r)⁻²` on a smaller disk. Dominated differentiation gives holomorphy. The circle square identity gives the norm integral and `Re F ≥ 1/2`, hence nonvanishing. See [the Cauchy notes](impl_notes/theorem-f-cauchy.md) and §§2–3 of the elementary proof.

Public interface:

```lean
namespace FF

def diskCauchyKernel (u : ℝ → ℂ) (w : ℂ) (t : ℝ) : ℂ :=
  (1 - w * conj (u t))⁻¹

def diskCauchyTransform (ρ : Measure ℝ) (u b : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ t, b t * diskCauchyKernel u w t ∂ρ

lemma diskCauchyKernel_den_ne {u : ℝ → ℂ} (hu : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) (t : ℝ) : 1 - w * conj (u t) ≠ 0 := by sorry

lemma diskCauchyKernel_norm_le {u : ℝ → ℂ} (hu : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) (t : ℝ) :
    ‖diskCauchyKernel u w t‖ ≤ (1 - ‖w‖)⁻¹ := by sorry

lemma diskCauchyKernel_measurable {u : ℝ → ℂ} (hu : Measurable u) (w : ℂ) :
    Measurable (diskCauchyKernel u w) := by sorry

lemma diskCauchyTransform_integrable {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {u b : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    (hb : Measurable b) {M : ℝ} (hM : ∀ t, ‖b t‖ ≤ M)
    {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (fun t ↦ b t * diskCauchyKernel u w t) ρ := by sorry

lemma diskCauchyKernel_integrable {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {u : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) : Integrable (diskCauchyKernel u w) ρ := by sorry

lemma diskCauchyKernel_sq_integrable {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {u : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (fun t ↦ ‖diskCauchyKernel u w t‖ ^ 2) ρ := by sorry

lemma diskCauchyKernel_re_identity {u : ℝ → ℂ} (hu : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) (t : ℝ) :
    2 * (diskCauchyKernel u w t).re - 1 =
      (1 - ‖w‖ ^ 2) * ‖diskCauchyKernel u w t‖ ^ 2 := by sorry

lemma diskCauchyKernel_sq_integral {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {u : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    (∫ t, ‖diskCauchyKernel u w t‖ ^ 2 ∂ρ) =
      (2 * (diskCauchyTransform ρ u (fun _ ↦ 1) w).re - 1) / (1 - ‖w‖ ^ 2) := by sorry

lemma diskCauchyTransform_re_ge_half {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {u : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    1 / 2 ≤ (diskCauchyTransform ρ u (fun _ ↦ 1) w).re := by sorry

lemma diskCauchyTransform_ne_zero {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {u : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    diskCauchyTransform ρ u (fun _ ↦ 1) w ≠ 0 := by sorry

lemma diskCauchyKernel_hasDerivAt {u : ℝ → ℂ} (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) (t : ℝ) :
    HasDerivAt (fun v ↦ diskCauchyKernel u v t)
      (conj (u t) * diskCauchyKernel u w t ^ 2) w := by sorry

lemma diskCauchyTransform_hasDerivAt {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {u b : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    (hb : Measurable b) {M : ℝ} (hM : ∀ t, ‖b t‖ ≤ M)
    {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (diskCauchyTransform ρ u b)
      (∫ t, b t * conj (u t) * diskCauchyKernel u w t ^ 2 ∂ρ) w := by sorry

lemma diskCauchyTransform_differentiableOn {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {u b : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    (hb : Measurable b) {M : ℝ} (hM : ∀ t, ‖b t‖ ≤ M) :
    DifferentiableOn ℂ (diskCauchyTransform ρ u b) {w : ℂ | ‖w‖ < 1} := by sorry

end FF
```

## Transforms.lean — The three transforms of the normalized probability measure.

Source: [Transforms.lean](../FourierFrames/Cited/DeBrangesF/Transforms.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesF.Kernel
import FourierFrames.Cited.DeBrangesF.Normalization
import FourierFrames.Cited.DeBrangesF.Cauchy
```

Specialize the disk transform to the Cayley boundary parametrization and the weights `1`, `conj theta`, and `theta`. Their modulus bounds prove integrability. Compose generic holomorphy with the Cayley map. See [the kernel identity notes](impl_notes/theorem-f-kernel-identities.md).

Public interface:

```lean
namespace FF.FMeasure

def cauchyF (μ : Measure ℝ) (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  diskCauchyTransform (normalizedKernelMeasure μ E) (fun t ↦ cayley t)
    (fun _ ↦ 1) (cayley z)

def cauchyH (μ : Measure ℝ) (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  diskCauchyTransform (normalizedKernelMeasure μ E) (fun t ↦ cayley t)
    (fun t ↦ conj (theta E t)) (cayley z)

def cauchyJ (μ : Measure ℝ) (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  diskCauchyTransform (normalizedKernelMeasure μ E) (fun t ↦ cayley t)
    (fun t ↦ theta E t) (cayley z)

def boundaryMean (μ : Measure ℝ) (E : ℂ → ℂ) : ℂ :=
  ∫ t, theta E t ∂normalizedKernelMeasure μ E

theorem measurable_cayley_real : Measurable (fun t : ℝ ↦ cayley t) := by sorry

theorem measurable_theta_real {E : ℂ → ℂ} (hE : IsHB E) :
    Measurable (fun t : ℝ ↦ theta E t) := by sorry

variable {μ : Measure ℝ} {E : ℂ → ℂ}

theorem integrable_cauchyF (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    Integrable (diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z))
      (normalizedKernelMeasure μ E) := by sorry

theorem integrable_cauchyH (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    Integrable (fun t : ℝ ↦ conj (theta E t) *
      diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t)
      (normalizedKernelMeasure μ E) := by sorry

theorem integrable_cauchyJ (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    Integrable (fun t : ℝ ↦ theta E t *
      diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t)
      (normalizedKernelMeasure μ E) := by sorry

theorem integrable_boundaryMean (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) :
    Integrable (fun t : ℝ ↦ theta E t) (normalizedKernelMeasure μ E) := by sorry

theorem cauchyF_ne_zero (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) : cauchyF μ E z ≠ 0 := by sorry

@[simp] theorem cauchyF_I (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) : cauchyF μ E I = 1 := by sorry

@[simp] theorem cauchyJ_I : cauchyJ μ E I = boundaryMean μ E := by sorry

@[simp] theorem cauchyH_I : cauchyH μ E I = conj (boundaryMean μ E) := by sorry

theorem differentiableOn_cauchyF (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) : DifferentiableOn ℂ (cauchyF μ E) UHP := by sorry

theorem differentiableOn_cauchyH (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) : DifferentiableOn ℂ (cauchyH μ E) UHP := by sorry

theorem differentiableOn_cauchyJ (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) : DifferentiableOn ℂ (cauchyJ μ E) UHP := by sorry

end FF.FMeasure
```

## KernelIdentities.lean — The two reproduction identities and exact kernel norm.

Source: [KernelIdentities.lean](../FourierFrames/Cited/DeBrangesF/KernelIdentities.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesF.Transforms
```

Integrate the normalized kernel and conjugate to obtain K1. Integrate the reflected kernel and evaluate its normalization at `I` to obtain `cayley z * integral Q = theta z`; the case `z=I` is immediate. Integrate the circle algebra to obtain K2. The normalized isometry and diagonal kernel formula give the exact squared norm. See §2 of the elementary proof and [the kernel identity notes](impl_notes/theorem-f-kernel-identities.md).

Public interface:

```lean
namespace FF.FMeasure

def modelKernel (E : ℂ → ℂ) (z t : ℂ) : ℂ :=
  (1 - theta E t * conj (theta E z)) / (1 - cayley t * conj (cayley z))

def reflectedModelKernel (E : ℂ → ℂ) (z t : ℂ) : ℂ :=
  (theta E t - theta E z) / (cayley t - cayley z)

lemma disk_reflected_identity {u w : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ < 1)
    (v p : ℂ) :
    w * ((v-p)/(u-w)) = v * (1-w*conj u)⁻¹ - p * (1-w*conj u)⁻¹ - v + p := by sorry

variable {μ : Measure ℝ} {E : ℂ → ℂ}

theorem modelKernel_eq_normalized (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    {z : ℂ} (hz : z ∈ UHP) (t : ℝ) :
    modelKernel E z t = ((baseNorm E : ℂ) / conj (baseKernel E z)) *
      (deBrangesKernel E z t / deBrangesKernel E I t) := by sorry

theorem integral_modelKernel (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    ∫ t : ℝ, modelKernel E z t ∂normalizedKernelMeasure μ E = 1 := by sorry

theorem conj_modelKernel (E : ℂ → ℂ) (z : ℂ) (t : ℝ) :
    conj (modelKernel E z t) =
      diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t -
        theta E z * (conj (theta E t) *
          diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t) := by sorry

theorem cauchyF_sub_theta_mul_H (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    cauchyF μ E z - theta E z * cauchyH μ E z = 1 := by sorry

theorem reflectedModelKernel_eq_normalized (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) {z : ℂ} (hz : z ∈ UHP) (t : ℝ) :
    reflectedModelKernel E z t = conjKernelCoeff E z *
      (deBrangesKernel E (conj z) t / deBrangesKernel E I t) := by sorry

theorem integrable_reflectedModelKernel (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    Integrable (fun t : ℝ ↦ reflectedModelKernel E z t)
      (normalizedKernelMeasure μ E) := by sorry

theorem cayley_mul_integral_reflectedModelKernel (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) (hμ : IsIsometricMeasure μ E)
    {z : ℂ} (hz : z ∈ UHP) :
    cayley z * (∫ t : ℝ, reflectedModelKernel E z t ∂normalizedKernelMeasure μ E) =
      theta E z := by sorry

theorem cauchyJ_sub_mean_eq_theta_mul_F (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    cauchyJ μ E z - boundaryMean μ E = theta E z * cauchyF μ E z := by sorry

theorem integrable_modelKernel_norm_sq (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    Integrable (fun t : ℝ ↦ ‖modelKernel E z t‖ ^ 2)
      (normalizedKernelMeasure μ E) := by sorry

theorem integral_modelKernel_norm_sq (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : z ∈ UHP) :
    ∫ t : ℝ, ‖modelKernel E z t‖ ^ 2 ∂normalizedKernelMeasure μ E =
      (1 - ‖theta E z‖ ^ 2) / (1 - ‖cayley z‖ ^ 2) := by sorry

end FF.FMeasure
```

## Algebra.lean — Scalar disk automorphisms and the final Cayley expression.

Source: [Algebra.lean](../FourierFrames/Cited/DeBrangesF/Algebra.lean).

Direct imports:

```lean
import FourierFrames.Defs
```

Expand squared moduli to prove the disk defect identities and all denominator nonvanishing statements. Substitute K1 and K2 into the weighted transform expression and take real parts; the remaining discrepancy is purely imaginary. See §§3–4 of the elementary proof.

Public interface:

```lean
namespace FF

lemma schurBack_defect (a b : ℂ) :
    ‖1 + a * b‖ ^ 2 - ‖conj a + b‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by sorry

lemma schurBack_den_ne_zero {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) :
    1 + a * b ≠ 0 := by sorry

lemma norm_schurBack_le {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) :
    ‖(conj a + b) / (1 + a * b)‖ ≤ 1 := by sorry

lemma norm_schurBack_lt {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ‖(conj a + b) / (1 + a * b)‖ < 1 := by sorry

lemma schur_one_sub_mul_ne_zero {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) :
    1 - a * b ≠ 0 := by sorry

lemma norm_diskBack_lt {a φ : ℂ} (ha : ‖a‖ < 1) (hφ : ‖φ‖ < 1) :
    ‖(a + φ) / (1 + conj a * φ)‖ < 1 := by sorry

lemma schurBack_quotient (a F H : ℂ) (hF : F ≠ 0) :
    (conj a + H / F) / (1 + a * (H / F)) = (conj a * F + H) / (F + a * H) := by sorry

lemma schurBack_linear_den_ne_zero {a F H : ℂ} (ha : ‖a‖ < 1) (hF : F ≠ 0)
    (hH : ‖H‖ ≤ ‖F‖) : F + a * H ≠ 0 := by sorry

lemma norm_schurBack_linear_le {a F H : ℂ} (ha : ‖a‖ < 1) (hF : F ≠ 0)
    (hH : ‖H‖ ≤ ‖F‖) : ‖(conj a * F + H) / (F + a * H)‖ ≤ 1 := by sorry

lemma diskBack_den_ne_zero {a φ : ℂ} (ha : ‖a‖ < 1) (hφ : ‖φ‖ ≤ 1) :
    1 + conj a * φ ≠ 0 := by sorry

lemma disk_defect_ne_zero {a : ℂ} (ha : ‖a‖ < 1) :
    (1 : ℂ) - a * conj a ≠ 0 := by sorry

lemma cayley_schurBack_linear {a φ F H : ℂ} (ha : ‖a‖ < 1) (hφ : ‖φ‖ < 1)
    (hF0 : F ≠ 0) (hH : ‖H‖ ≤ ‖F‖) (hF : F - φ * H = 1) :
    ((1 + a * conj a) * (2 * F - 1) + 2 * conj a * φ * F + 2 * a * H) /
        (1 - a * conj a) =
      (1 + ((a + φ) / (1 + conj a * φ)) * ((conj a * F + H) / (F + a * H))) /
        (1 - ((a + φ) / (1 + conj a * φ)) * ((conj a * F + H) / (F + a * H))) := by sorry

lemma weighted_cauchy_re (a φ F H J c : ℂ) (d : ℝ) (hJ : J - c = φ * F) :
    (2 * (((1 + (‖a‖ ^ 2 : ℂ)) * F + conj a * J + a * H) / (d : ℂ)) -
      ((1 + (‖a‖ ^ 2 : ℂ)) + conj a * c + a * conj c) / (d : ℂ)).re =
    (((1 + (‖a‖ ^ 2 : ℂ)) * (2 * F - 1) + 2 * conj a * φ * F + 2 * a * H) /
      (d : ℂ)).re := by sorry

lemma weighted_cauchy_cayley_re {a φ F H J c : ℂ} (ha : ‖a‖ < 1) (hφ : ‖φ‖ < 1)
    (hF0 : F ≠ 0) (hH : ‖H‖ ≤ ‖F‖) (hF : F - φ * H = 1) (hJ : J - c = φ * F) :
    (2 * (((1 + (‖a‖ ^ 2 : ℂ)) * F + conj a * J + a * H) /
        ((1 - ‖a‖ ^ 2 : ℝ) : ℂ)) -
      ((1 + (‖a‖ ^ 2 : ℂ)) + conj a * c + a * conj c) /
        ((1 - ‖a‖ ^ 2 : ℝ) : ℂ)).re =
      ((1 + ((a + φ) / (1 + conj a * φ)) * ((conj a * F + H) / (F + a * H))) /
        (1 - ((a + φ) / (1 + conj a * φ)) * ((conj a * F + H) / (F + a * H)))).re := by sorry

end FF
```

## Analytic.lean — Extension across zeros and the holomorphic Schur parameter.

Source: [Analytic.lean](../FourierFrames/Cited/DeBrangesF/Analytic.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesF.Basic
import FourierFrames.Cited.DeBrangesF.Algebra
```

For a nonzero entire numerator, the analytic identity theorem excludes an open zero set. Continuity extends the inequality from punctured neighborhoods. This justifies cancellation of the normalized inner factor, including its zeros. The inverse disk automorphism then preserves holomorphy and contractivity. See §3 of the elementary proof.

Public interface:

```lean
namespace FF

theorem le_on_upper_of_le_off_entire_zeros {N : ℂ → ℂ} (hN : Differentiable ℂ N)
    (hne : ∃ z : ℂ, N z ≠ 0) {u v : ℂ → ℝ}
    (hu : ContinuousOn u UHP) (hv : ContinuousOn v UHP)
    (h : ∀ z ∈ UHP, N z ≠ 0 → u z ≤ v z) : ∀ z ∈ UHP, u z ≤ v z := by sorry

theorem norm_le_on_upper_of_mul_norm_le {N : ℂ → ℂ} (hN : Differentiable ℂ N)
    (hne : ∃ z : ℂ, N z ≠ 0) {φ f g : ℂ → ℂ}
    (hf : ContinuousOn f UHP) (hg : ContinuousOn g UHP)
    (hφ : ∀ z ∈ UHP, N z ≠ 0 → φ z ≠ 0)
    (h : ∀ z ∈ UHP, ‖φ z * f z‖ ≤ ‖φ z * g z‖) :
    ∀ z ∈ UHP, ‖f z‖ ≤ ‖g z‖ := by sorry

def schurParameter (a : ℂ) (F H : ℂ → ℂ) (z : ℂ) : ℂ :=
  (conj a * F z + H z) / (F z + a * H z)

theorem schurParameter_spec {a : ℂ} (ha : ‖a‖ < 1) {F H : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F UHP) (hH : DifferentiableOn ℂ H UHP)
    (hF0 : ∀ z ∈ UHP, F z ≠ 0) (hbound : ∀ z ∈ UHP, ‖H z‖ ≤ ‖F z‖) :
    DifferentiableOn ℂ (schurParameter a F H) UHP ∧
      ∀ z ∈ UHP, ‖schurParameter a F H z‖ ≤ 1 := by sorry

end FF
```

## Schur.lean — The finite-measure Cauchy–Schwarz argument.

Source: [Schur.lean](../FourierFrames/Cited/DeBrangesF/Schur.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesF.Isometry
import FourierFrames.Cited.DeBrangesF.Cauchy
```

Realize square-integrable functions in `L²`, use the Hilbert-space Cauchy–Schwarz inequality, and translate its norms back to integrals. The circle identity plus K1 and K2 determines the mixed kernel integral. Insert the exact kernel norm and simplify to `|F-1| ≤ |p F|`. See §3 of the elementary proof.

Public interface:

```lean
namespace FF

theorem norm_integral_mul_conj_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ t, f t * conj (g t) ∂μ‖ ^ 2 ≤
      (∫ t, ‖f t‖ ^ 2 ∂μ) * ∫ t, ‖g t‖ ^ 2 ∂μ := by sorry

theorem schur_bound_of_scalar_inequality {F p : ℂ} {d : ℝ} (hd : 0 < d) (hp : ‖p‖ < 1)
    (h : ‖((1 - ‖p‖ ^ 2 : ℝ) : ℂ) * conj F / (d : ℂ)‖ ^ 2 ≤
      ((2 * F.re - 1) / d) * ((1 - ‖p‖ ^ 2) / d)) :
    ‖F - 1‖ ≤ ‖p * F‖ := by sorry

def diskModelKernel (u v : ℝ → ℂ) (w p : ℂ) (t : ℝ) : ℂ :=
  (1 - v t * conj p) / (1 - u t * conj w)

theorem diskModelKernel_eq (u v : ℝ → ℂ) (w p : ℂ) (t : ℝ) :
    diskModelKernel u v w p t = (1 - conj p * v t) * conj (diskCauchyKernel u w t) := by sorry

theorem diskCauchyKernel_circle_identity {u : ℝ → ℂ} (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) (t : ℝ) :
    ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) *
        (conj (diskCauchyKernel u w t) * diskCauchyKernel u w t) =
      diskCauchyKernel u w t + conj (diskCauchyKernel u w t) - 1 := by sorry

theorem diskModelKernel_memLp {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {u v : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    (hv : Measurable v) (hvn : ∀ t, ‖v t‖ = 1) {w : ℂ} (hw : ‖w‖ < 1) (p : ℂ) :
    MemLp (diskModelKernel u v w p) 2 ρ := by sorry

theorem diskModelKernel_integral_mul {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {u v : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    (hv : Measurable v) (hvn : ∀ t, ‖v t‖ = 1) {w p : ℂ} (hw : ‖w‖ < 1)
    (h₁ : diskCauchyTransform ρ u (fun _ ↦ 1) w - 1 =
      p * diskCauchyTransform ρ u (fun t ↦ conj (v t)) w)
    (h₂ : diskCauchyTransform ρ u v w - ∫ t, v t ∂ρ =
      p * diskCauchyTransform ρ u (fun _ ↦ 1) w) :
    ∫ t, diskModelKernel u v w p t * diskCauchyKernel u w t ∂ρ =
      ((1 - ‖p‖ ^ 2 : ℝ) : ℂ) * diskCauchyTransform ρ u (fun _ ↦ 1) w /
        ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by sorry

theorem schur_bound_of_kernel_identities {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {u v : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    (hv : Measurable v) (hvn : ∀ t, ‖v t‖ = 1) {w p : ℂ} (hw : ‖w‖ < 1) (hp : ‖p‖ < 1)
    (h₁ : diskCauchyTransform ρ u (fun _ ↦ 1) w - 1 =
      p * diskCauchyTransform ρ u (fun t ↦ conj (v t)) w)
    (h₂ : diskCauchyTransform ρ u v w - ∫ t, v t ∂ρ =
      p * diskCauchyTransform ρ u (fun _ ↦ 1) w)
    (hn : ∫ t, ‖(1 - v t * conj p) / (1 - u t * conj w)‖ ^ 2 ∂ρ =
      (1 - ‖p‖ ^ 2) / (1 - ‖w‖ ^ 2)) :
    ‖diskCauchyTransform ρ u (fun _ ↦ 1) w - 1‖ ≤
      ‖p * diskCauchyTransform ρ u (fun _ ↦ 1) w‖ := by sorry

end FF
```

## Contractive.lean — The parameter associated with the isometric measure.

Source: [Contractive.lean](../FourierFrames/Cited/DeBrangesF/Contractive.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesF.Analytic
import FourierFrames.Cited.DeBrangesF.KernelIdentities
import FourierFrames.Cited.DeBrangesF.Schur
```

Apply the generic Schur bound to the normalized kernels. The entire numerator is nonzero already at the real point zero, using unimodular boundary values and strict interior modulus. Extend the bound through its zeros and apply `schurParameter_spec`. The remaining two statements undo the inner-function normalization. See §3 of the elementary proof.

Public interface:

```lean
namespace FF.FMeasure

variable {μ : Measure ℝ} {E : ℂ → ℂ}

theorem theta_numerator_ne_zero_at_zero (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) : fstar E 0 - anchor E * E 0 ≠ 0 := by sorry

theorem cauchyH_norm_le (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) : ∀ z ∈ UHP, ‖cauchyH μ E z‖ ≤ ‖cauchyF μ E z‖ := by sorry

def isometricSchur (μ : Measure ℝ) (E : ℂ → ℂ) : ℂ → ℂ :=
  schurParameter (anchor E) (cauchyF μ E) (cauchyH μ E)

theorem isometricSchur_spec (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) :
    DifferentiableOn ℂ (isometricSchur μ E) UHP ∧
      ∀ z ∈ UHP, ‖isometricSchur μ E z‖ ≤ 1 := by sorry

theorem thetaFn_eq_diskBack (hE : IsStrictHB E) {z : ℂ} (hz : z ∈ UHP) :
    thetaFn E z = (anchor E + theta E z) / (1 + conj (anchor E) * theta E z) := by sorry

theorem cayley_thetaFn_eq {E : ℂ → ℂ} {z A : ℂ} (hE : E z ≠ 0) :
    (1 + thetaFn E z * A) / (1 - thetaFn E z * A) =
      (E z + fstar E z * A) / (E z - fstar E z * A) := by sorry

end FF.FMeasure
```

## Herglotz.lean — Auxiliary regularized-kernel estimates.

Source: [Herglotz.lean](../FourierFrames/Cited/DeBrangesF/Herglotz.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesF.Basic
```

Rewrite the regularized kernel to obtain weighted-moment bounds for it and its derivative, then differentiate under the integral. Compute its real part as the Poisson kernel and establish finiteness. This module supplies estimates reused by `Poisson`; the final theorem is assembled from the two reproducing-kernel identities. See [the Herglotz notes](impl_notes/theorem-f-herglotz.md).

Public interface:

```lean
namespace FF

namespace Herglotz

def kernel (t : ℝ) (z : ℂ) : ℂ :=
  ((t : ℂ) - z)⁻¹ - ((t / (1 + t ^ 2) : ℝ) : ℂ)

lemma real_sub_ne_zero {z : ℂ} (hz : 0 < z.im) (t : ℝ) : (t : ℂ) - z ≠ 0 := by sorry

lemma norm_inv_sub_le {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : r ≤ z.im) (t : ℝ) :
    ‖((t : ℂ) - z)⁻¹‖ ≤ r⁻¹ := by sorry

lemma kernel_eq (t : ℝ) {z : ℂ} (hz : 0 < z.im) :
    kernel t z = (((1 + z ^ 2) * ((t : ℂ) - z)⁻¹ + z) : ℂ) /
      ((1 + t ^ 2 : ℝ) : ℂ) := by sorry

lemma inv_sq_eq (t : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (((t : ℂ) - z)⁻¹) ^ 2 =
      ((1 + z ^ 2) * (((t : ℂ) - z)⁻¹) ^ 2 + 2 * z * ((t : ℂ) - z)⁻¹ + 1) /
        ((1 + t ^ 2 : ℝ) : ℂ) := by sorry

lemma norm_kernel_le {z : ℂ} {r R : ℝ} (hr : 0 < r) (hz : r ≤ z.im)
    (hR : ‖z‖ ≤ R) (t : ℝ) :
    ‖kernel t z‖ ≤ ((1 + R ^ 2) * r⁻¹ + R) * (1 / (1 + t ^ 2)) := by sorry

lemma norm_inv_sq_le {z : ℂ} {r R : ℝ} (hr : 0 < r) (hz : r ≤ z.im)
    (hR : ‖z‖ ≤ R) (t : ℝ) :
    ‖(((t : ℂ) - z)⁻¹) ^ 2‖ ≤
      ((1 + R ^ 2) * (r⁻¹) ^ 2 + 2 * R * r⁻¹ + 1) * (1 / (1 + t ^ 2)) := by sorry

lemma moment_integrable {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞) :
    Integrable (fun t : ℝ ↦ 1 / (1 + t ^ 2)) μ := by sorry

lemma kernel_integrable {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞)
    {z : ℂ} (hz : 0 < z.im) : Integrable (fun t : ℝ ↦ kernel t z) μ := by sorry

lemma hasDerivAt_kernel (t : ℝ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (kernel t) (((t : ℂ) - z)⁻¹ ^ 2) z := by sorry

lemma integral_differentiableAt {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞)
    {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (fun w ↦ ∫ t : ℝ, kernel t w ∂μ) z := by sorry

lemma re_neg_I_mul_kernel (t : ℝ) (z : ℂ) :
    (-I * kernel t z).re = z.im / ((t - z.re) ^ 2 + z.im ^ 2) := by sorry

lemma re_scaled_kernel (t : ℝ) (z : ℂ) :
    ((-I / Real.pi) * kernel t z).re =
      z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2)) := by sorry

end Herglotz

theorem herglotzG_spec {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞) (c : ℝ) :
    DifferentiableOn ℂ (herglotzG μ c) UHP ∧
      ∀ z ∈ UHP, poissonInt μ z ≠ ∞ ∧ (poissonInt μ z).toReal = (herglotzG μ c z).re := by sorry

end FF
```

## Poisson.lean — Inverse change of measure and the original Poisson integral.

Source: [Poisson.lean](../FourierFrames/Cited/DeBrangesF/Poisson.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesF.Herglotz
import FourierFrames.Cited.DeBrangesF.Cauchy
import FourierFrames.Cited.DeBrangesF.Transforms
```

Form the finite measure `dμ/(π(1+t²))`. Identify it with the inverse disk-automorphism weight times the normalized measure. Expand that weight on the unit circle to obtain the original transform and mass formulas. Integrate the Cayley–Poisson identity, using the weighted moment for finiteness. See §4 of the elementary proof.

Public interface:

```lean
namespace FF

def poissonWeightedMeasure (μ : Measure ℝ) : Measure ℝ :=
  μ.withDensity (fun t ↦ ENNReal.ofReal (1 / (Real.pi * (1 + t ^ 2))))

lemma measurable_poissonWeight :
    Measurable (fun t : ℝ ↦ ENNReal.ofReal (1 / (Real.pi * (1 + t ^ 2)))) := by sorry

lemma poissonWeight_integrable {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞) :
    Integrable (fun t : ℝ ↦ 1 / (Real.pi * (1 + t ^ 2))) μ := by sorry

lemma poissonWeightedMeasure_finite {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞) :
    IsFiniteMeasure (poissonWeightedMeasure μ) := by sorry

lemma integral_poissonWeightedMeasure (μ : Measure ℝ) (f : ℝ → ℂ) :
    ∫ t, f t ∂poissonWeightedMeasure μ =
      ∫ t, ((1 / (Real.pi * (1 + t ^ 2)) : ℝ) : ℂ) * f t ∂μ := by sorry

lemma integral_poissonWeightedMeasure_real (μ : Measure ℝ) (f : ℝ → ℝ) :
    ∫ t, f t ∂poissonWeightedMeasure μ =
      ∫ t, (1 / (Real.pi * (1 + t ^ 2))) * f t ∂μ := by sorry

namespace FPoisson

lemma add_I_ne_zero {z : ℂ} (hz : 0 ≤ z.im) : z + I ≠ 0 := by sorry

lemma real_sub_I_ne_zero (t : ℝ) : (t : ℂ) - I ≠ 0 := by sorry

lemma cayley_kernel_eq {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    diskCauchyKernel (fun t : ℝ ↦ ((t : ℂ) - I) / ((t : ℂ) + I))
      ((z - I) / (z + I)) t = (z + I) * ((t : ℂ) - I) / (2 * I * ((t : ℂ) - z)) := by sorry

lemma cayley_poisson_identity {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    2 * (diskCauchyKernel (fun t : ℝ ↦ ((t : ℂ) - I) / ((t : ℂ) + I))
      ((z - I) / (z + I)) t).re - 1 =
        z.im * (1 + t ^ 2) / ((t - z.re) ^ 2 + z.im ^ 2) := by sorry

lemma circle_weight_expand (a p : ℂ) (hp : ‖p‖ = 1) :
    ((‖1 + conj a * p‖ ^ 2 : ℝ) : ℂ) =
      (1 + (‖a‖ ^ 2 : ℝ) : ℂ) + conj a * p + a * conj p := by sorry

lemma integral_circle_weight {ν : Measure ℝ} {p f : ℝ → ℂ} (hp : Measurable p)
    (hpn : ∀ t, ‖p t‖ = 1) (hf : Integrable f ν)
    (hpf : Integrable (fun t ↦ p t * f t) ν)
    (hpcf : Integrable (fun t ↦ conj (p t) * f t) ν)
    (a : ℂ) {d : ℝ} (hd : 0 < d) :
    (d : ℂ) * ∫ t, f t ∂ν.withDensity (fun t ↦ ENNReal.ofReal (‖1 + conj a * p t‖ ^ 2 / d)) =
      (1 + (‖a‖ ^ 2 : ℝ) : ℂ) * ∫ t, f t ∂ν +
        conj a * ∫ t, p t * f t ∂ν + a * ∫ t, conj (p t) * f t ∂ν := by sorry

end FPoisson

namespace FMeasure

def originalCauchyF (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t, diskCauchyKernel (fun t : ℝ ↦ cayley t) (cayley z) t
    ∂poissonWeightedMeasure μ

def originalMass (μ : Measure ℝ) : ℝ := (poissonWeightedMeasure μ Set.univ).toReal

lemma normalizedDensity_mul_inverse {E : ℂ → ℂ} (hE : IsStrictHB E)
    (h0 : ∀ t : ℝ, E t ≠ 0) (t : ℝ) :
    (‖baseKernel E t / E t‖ ^ 2 / baseNorm E) *
      (‖1 + conj (anchor E) * theta E t‖ ^ 2 / defect E) =
        1 / (Real.pi * (1 + t ^ 2)) := by sorry

theorem poissonWeightedMeasure_eq {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0) :
    poissonWeightedMeasure μ = (normalizedKernelMeasure μ E).withDensity
      (fun t ↦ ENNReal.ofReal (‖1 + conj (anchor E) * theta E t‖ ^ 2 / defect E)) := by sorry

theorem originalCauchyF_expand {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) {z : ℂ} (hz : 0 < z.im) :
    (defect E : ℂ) * originalCauchyF μ z =
      (1 + (‖anchor E‖ ^ 2 : ℝ) : ℂ) * cauchyF μ E z +
        conj (anchor E) * cauchyJ μ E z + anchor E * cauchyH μ E z := by sorry

theorem originalMass_expand {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0)
    (hμ : IsIsometricMeasure μ E) :
    (defect E : ℂ) * (originalMass μ : ℂ) =
      (1 + (‖anchor E‖ ^ 2 : ℝ) : ℂ) +
        conj (anchor E) * boundaryMean μ E + anchor E * conj (boundaryMean μ E) := by sorry

theorem poissonInt_cayley_spec {μ : Measure ℝ}
    (hm : ∫⁻ t, ENNReal.ofReal (1 / (1 + t ^ 2)) ∂μ < ∞)
    {z : ℂ} (hz : 0 < z.im) :
    poissonInt μ z ≠ ∞ ∧
      (poissonInt μ z).toReal = 2 * (originalCauchyF μ z).re - originalMass μ := by sorry

end FMeasure

end FF
```

## DeBrangesF.lean — Assembly of the unchanged Theorem F.

Source: [DeBrangesF.lean](../FourierFrames/Cited/DeBrangesF.lean).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesF.Contractive
import FourierFrames.Cited.DeBrangesF.Poisson
```

Combine the original Poisson formula, inverse-weight expansions, K1, K2, and the scalar Cayley identity. The denominator is nonzero by strictness and contractivity. Choose `isometricSchur μ E` and the real constant `p=0`; this proves the unchanged `TheoremF`. See §4 of the elementary proof.

Public interface:

```lean
namespace FF

namespace FMeasure

theorem poissonInt_eq_isometricSchur {μ : Measure ℝ} {E : ℂ → ℂ}
    (hE : IsStrictHB E) (h0 : ∀ t : ℝ, E t ≠ 0) (hμ : IsIsometricMeasure μ E)
    {z : ℂ} (hz : z ∈ UHP) :
    poissonInt μ z ≠ ∞ ∧ (poissonInt μ z).toReal =
      ((E z + fstar E z * isometricSchur μ E z) /
        (E z - fstar E z * isometricSchur μ E z)).re := by sorry

end FMeasure

theorem theoremF_holds : TheoremF := by sorry

end FF
```
