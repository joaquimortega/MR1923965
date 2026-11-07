# Pavlov's theorem: exact Lean statements and dependencies

This appendix records all public declarations of the completed
[`FourierFrames/Cited/Pavlov`](../FourierFrames/Cited/Pavlov) modules and the
[root assembly](../FourierFrames/Cited/Pavlov.lean). The source signatures are
extracted directly, including namespaces and shared `variable` contexts.
Definitions, abbreviations, and structure fields retain their actual source
bodies. Theorem and lemma proofs are replaced by `by sorry` **only in this
Markdown appendix**. Private implementation helpers are omitted. These
listings introduce no new Lean source, axioms, or assumptions.

Each section gives the exact direct imports and opening commands used by its
module, then links the detailed proof blueprint. Sections follow an order
compatible with the module import graph. The external foundations are the
project's already proved Paley–Wiener/de Branges/John–Nirenberg infrastructure,
Mathlib, and the vendored Tau Ceti harmonic-analysis helpers. No `Unconditional`
module enters this proof's dependency chain.

The master overview is [P5_Pavlov.md](P5_Pavlov.md). The focused blueprints
linked below and the present exact interfaces describe the implemented proof;
the earlier route A/B investigations retain historical exploration. Independent
reviews are recorded in [R13](../reviews/R13_Pavlov_Blueprint.md),
[R14](../reviews/R14_Pavlov_Code.md), and
[R15](../reviews/R15_Pavlov_Dispersion.md).

## Proof-stage and blueprint map

| Stage | Modules | Detailed proof |
| --- | --- | --- |
| Generating and cardinal data; separated bounded-gap grid | `Cardinal` | [P5_Cardinal](P5_Cardinal.md) |
| Discrete A₂, local comparison, continuous weight transfer | `Weights`, `Harnack`, `CellBounds`, `WeightTransfer` | [P5_A2](P5_A2.md), [P5_Harnack](P5_Harnack.md) |
| Elementary BMO algebra, logarithms, and Fatou | `Fatou`, `BMO` | [P5_BMO](P5_BMO.md) |
| Distance logarithm and boundary weight | `LogSingularity`, `LogDistanceCore`, `LogDistanceLarge`, `LogDistanceTransfer`, `LogDistance`, `BoundaryWeight` | [P5_LogDistance](P5_LogDistance.md) |
| BMO growth, square moments, and regularized conjugation | `BMOIntervalGrowth`, `BMOLogIntegrable`, `BMOSecondMoment`, `ConjugatePoisson`, `PoissonBMOKernel`, `PoissonBMONear`, `PoissonBMOFar`, `PoissonBMO` | [P5_PoissonBMO](P5_PoissonBMO.md), [P5_HilbertL2](P5_HilbertL2.md) |
| Normalized Schwarz integral and logarithmic cardinal input | `Basic`, `Schwarz`, `CardinalLog`, `LogPoissonKernel` | [P5_Dispersion](P5_Dispersion.md), [P5_CardinalLog](P5_CardinalLog.md), [P5_LogPoissonKernel](P5_LogPoissonKernel.md) |
| Clipping and boundary limits for logarithmic Poisson data | `LogClipping`, `SchwarzBoundary`, `LogPoissonBoundary` | [P5_LogClipping](P5_LogClipping.md), [P5_SchwarzBoundary](P5_SchwarzBoundary.md), [P5_LogPoissonBoundary](P5_LogPoissonBoundary.md) |
| Positive harmonic defect and its removal by CIS uniqueness | `HarmonicReflection`, `LogPoisson`, `OuterComparison`, `NoExponentialDefect`, `GeneratingDispersion` | [P5_Reflection](P5_Reflection.md), [P5_Dispersion](P5_Dispersion.md), [P5_OuterComparison](P5_OuterComparison.md), [P5_NoExponentialDefect](P5_NoExponentialDefect.md) |
| Phase jumps, counting normalization, and final limit | `BoundaryPhaseCount`, `BoundaryPhase`, `CountingBMO`, root `Pavlov` | [P5_BoundaryPhase](P5_BoundaryPhase.md), [P5_CountingBMO](P5_CountingBMO.md) |

The target remains exactly the definition in `FourierFrames/Defs.lean`:

```lean
namespace FF
def PavlovBMO : Prop :=
  ∀ Γ : Set ℝ, IsSeparated Γ → IsCompleteInterpolating Γ → MemBMO (fun t ↦ countFn Γ t - t)
end FF
```

All listed declarations are in a `noncomputable section`. Opening commands are
shown per module because Fourier, inner-product, and Laplacian notation have
different local requirements. A source's namespaced `variable` commands remain
in their original positions in its interface block.

## Fatou.lean

Source: [Fatou.lean](../FourierFrames/Cited/Pavlov/Fatou.lean).

Detailed proof: [P5_BMO](P5_BMO.md).

Direct imports:

```lean
import FourierFrames.Defs
```

Opening commands:

```lean
open MeasureTheory Filter Topology
```

Public interface:

```lean
namespace FF.Pavlov

theorem integral_le_of_ae_tendsto_nonneg {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ} {K : ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hfn : ∀ n, 0 ≤ᵐ[μ] f n) (hgn : 0 ≤ᵐ[μ] g)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    (hbound : ∀ n, ∫ x, f n x ∂μ ≤ K) :
    ∫ x, g x ∂μ ≤ K := by sorry

end FF.Pavlov
```

## BMO.lean

Source: [BMO.lean](../FourierFrames/Cited/Pavlov/BMO.lean).

Detailed proof: [P5_BMO](P5_BMO.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.Fatou
```

Opening commands:

```lean
open MeasureTheory Set Filter Topology
```

Public interface:

```lean
namespace FF.Pavlov

theorem intervalMean_sub_const_eq {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) (c : ℝ) :
    intervalMean h a b - c =
      (b - a)⁻¹ * ∫ t in a..b, (h t - c) := by sorry

theorem abs_intervalMean_sub_const_le {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) (c : ℝ) :
    |intervalMean h a b - c| ≤
      (b - a)⁻¹ * ∫ t in a..b, |h t - c| := by sorry

theorem meanOsc_le_twice_comparison {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) (c : ℝ) :
    meanOsc h a b ≤ 2 * ((b - a)⁻¹ * ∫ t in a..b, |h t - c|) := by sorry

theorem meanOsc_nonneg {h : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    0 ≤ meanOsc h a b := by sorry

theorem memBMO_of_comparison {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {M : ℝ} (hM : ∀ a b : ℝ, a < b →
      ∃ c : ℝ, (b - a)⁻¹ * ∫ t in a..b, |h t - c| ≤ M) :
    MemBMO h := by sorry

theorem meanOsc_const (c : ℝ) {a b : ℝ} (hab : a < b) :
    meanOsc (fun _ : ℝ ↦ c) a b = 0 := by sorry

theorem meanOsc_add_const {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    (c : ℝ) {a b : ℝ} (hab : a < b) :
    meanOsc (fun t ↦ h t + c) a b = meanOsc h a b := by sorry

theorem meanOsc_const_mul (h : ℝ → ℝ) (c a b : ℝ) :
    meanOsc (fun t ↦ c * h t) a b = |c| * meanOsc h a b := by sorry

theorem meanOsc_add_le {f g : ℝ → ℝ}
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    {a b : ℝ} (hab : a < b) :
    meanOsc (fun t ↦ f t + g t) a b ≤ meanOsc f a b + meanOsc g a b := by sorry

theorem meanOsc_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g)
    (a b : ℝ) : meanOsc f a b = meanOsc g a b := by sorry

theorem memBMO_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) :
    MemBMO f ↔ MemBMO g := by sorry

theorem memBMO_const (c : ℝ) : MemBMO (fun _ : ℝ ↦ c) := by sorry

theorem memBMO_const_mul {h : ℝ → ℝ} (hh : MemBMO h) (c : ℝ) :
    MemBMO (fun t ↦ c * h t) := by sorry

theorem memBMO_add {f g : ℝ → ℝ} (hf : MemBMO f) (hg : MemBMO g) :
    MemBMO (fun t ↦ f t + g t) := by sorry

theorem memBMO_neg {h : ℝ → ℝ} (hh : MemBMO h) :
    MemBMO (fun t ↦ -h t) := by sorry

theorem memBMO_sub {f g : ℝ → ℝ} (hf : MemBMO f) (hg : MemBMO g) :
    MemBMO (fun t ↦ f t - g t) := by sorry

theorem meanOsc_le_of_ae_abs_le {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {K : ℝ} (hK : ∀ᵐ t : ℝ, |h t| ≤ K) {a b : ℝ} (hab : a < b) :
    meanOsc h a b ≤ 2 * K := by sorry

theorem memBMO_of_ae_abs_le {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {K : ℝ} (hK : ∀ᵐ t : ℝ, |h t| ≤ K) : MemBMO h := by sorry

theorem memBMO_add_ae_bounded {f g : ℝ → ℝ} (hf : MemBMO f)
    (hg : LocallyIntegrable g) {K : ℝ} (hK : ∀ᵐ t : ℝ, |g t| ≤ K) :
    MemBMO (fun t ↦ f t + g t) := by sorry

theorem abs_meanOsc_sub_le {f g : ℝ → ℝ}
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    {a b : ℝ} (hab : a < b) :
    |meanOsc f a b - meanOsc g a b| ≤
      2 * ((b - a)⁻¹ * ∫ t in a..b, |f t - g t|) := by sorry

theorem meanOsc_le_of_tendsto_local_L1 {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M)
    (hlim : ∀ a b : ℝ, a < b →
      Tendsto (fun n ↦ ∫ t in a..b, |f n t - g t|) atTop (𝓝 0)) :
    ∀ a b : ℝ, a < b → meanOsc g a b ≤ M := by sorry

theorem memBMO_of_tendsto_local_L1 {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M)
    (hlim : ∀ a b : ℝ, a < b →
      Tendsto (fun n ↦ ∫ t in a..b, |f n t - g t|) atTop (𝓝 0)) :
    MemBMO g := by sorry

def intervalPairIntegral (h : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, |h p.1-h p.2|
    ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))

theorem integrable_intervalPair {h : ℝ → ℝ} (hh : LocallyIntegrable h) (a b : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ |h p.1-h p.2|)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by sorry

theorem meanOsc_le_pairIntegral {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) :
    meanOsc h a b ≤ (b-a)⁻¹ ^ 2 * intervalPairIntegral h a b := by sorry

theorem pairIntegral_le_twice_meanOsc {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) :
    intervalPairIntegral h a b ≤ 2 * (b-a)^2 * meanOsc h a b := by sorry

theorem meanOsc_le_of_ae_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M) :
    ∀ a b : ℝ, a < b → meanOsc g a b ≤ 2*M := by sorry

theorem memBMO_of_ae_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M) :
    MemBMO g := by sorry

theorem meanOsc_le_of_ae_tendsto_comparison
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ a b : ℝ, a < b →
      ∃ (c : ℕ → ℝ) (c₀ : ℝ), Tendsto c atTop (𝓝 c₀) ∧
        ∀ n, (b - a)⁻¹ * ∫ t in a..b, |f n t - c n| ≤ M) :
    ∀ a b : ℝ, a < b → meanOsc g a b ≤ 2*M := by sorry

theorem memBMO_of_ae_tendsto_comparison
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ a b : ℝ, a < b →
      ∃ (c : ℕ → ℝ) (c₀ : ℝ), Tendsto c atTop (𝓝 c₀) ∧
        ∀ n, (b - a)⁻¹ * ∫ t in a..b, |f n t - c n| ≤ M) :
    MemBMO g := by sorry

theorem memBMO_of_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M) :
    MemBMO g := by sorry

theorem abs_log_le_add_inv {s : ℝ} (hs : 0 < s) :
    |Real.log s| ≤ s + s⁻¹ := by sorry

theorem locallyIntegrable_log_of_pos_inv {w : ℝ → ℝ}
    (hw : LocallyIntegrable w)
    (hwi : LocallyIntegrable (fun t ↦ (w t)⁻¹))
    (hpos : ∀ᵐ t : ℝ, 0 < w t) :
    LocallyIntegrable (fun t ↦ Real.log (w t)) := by sorry

theorem intervalMean_pos_of_ae_pos {w : ℝ → ℝ}
    (hw : LocallyIntegrable w) (hpos : ∀ᵐ t : ℝ, 0 < w t)
    {a b : ℝ} (hab : a < b) : 0 < intervalMean w a b := by sorry

theorem log_comparison_le_of_A2 {w : ℝ → ℝ}
    (hw : LocallyIntegrable w)
    (hwi : LocallyIntegrable (fun t ↦ (w t)⁻¹))
    (hpos : ∀ᵐ t : ℝ, 0 < w t)
    {C a b : ℝ} (hab : a < b)
    (hA2 : intervalMean w a b * intervalMean (fun t ↦ (w t)⁻¹) a b ≤ C) :
    (b - a)⁻¹ * ∫ t in a..b,
      |Real.log (w t) - Real.log (intervalMean w a b)| ≤ 1 + C := by sorry

theorem meanOsc_log_le_of_A2 {w : ℝ → ℝ}
    (hw : LocallyIntegrable w)
    (hwi : LocallyIntegrable (fun t ↦ (w t)⁻¹))
    (hpos : ∀ᵐ t : ℝ, 0 < w t)
    {C a b : ℝ} (hab : a < b)
    (hA2 : intervalMean w a b * intervalMean (fun t ↦ (w t)⁻¹) a b ≤ C) :
    meanOsc (fun t ↦ Real.log (w t)) a b ≤ 2 * (1 + C) := by sorry

theorem memBMO_log_of_A2 {w : ℝ → ℝ}
    (hw : LocallyIntegrable w)
    (hwi : LocallyIntegrable (fun t ↦ (w t)⁻¹))
    (hpos : ∀ᵐ t : ℝ, 0 < w t)
    {C : ℝ} (hA2 : ∀ a b : ℝ, a < b →
      intervalMean w a b * intervalMean (fun t ↦ (w t)⁻¹) a b ≤ C) :
    MemBMO (fun t ↦ Real.log (w t)) := by sorry

end FF.Pavlov
```

## BMOIntervalGrowth.lean

Source: [BMOIntervalGrowth.lean](../FourierFrames/Cited/Pavlov/BMOIntervalGrowth.lean).

Detailed proof: [P5_PoissonBMO](P5_PoissonBMO.md).

Direct imports:

```lean
import FourierFrames.Cited.JohnNirenberg
```

Opening commands:

```lean
open MeasureTheory Set Filter
```

Public interface:

```lean
namespace FF.Pavlov

theorem abs_intervalMean_sub_le_length_ratio {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {M a b c d : ℝ}
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M)
    (hab : a < b) (hcd : c < d) (hca : c ≤ a) (hbd : b ≤ d) :
    |intervalMean u a b - intervalMean u c d| ≤ (b-a)⁻¹ * (M*(d-c)) := by sorry

theorem abs_intervalMean_center_double_sub_le {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {M c r : ℝ}
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M) (hr : 0 < r) :
    |intervalMean u (c-r) (c+r) - intervalMean u (c-2*r) (c+2*r)| ≤ 2*M := by sorry

theorem abs_intervalMean_center_pow_sub_le {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {M c r : ℝ}
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M) (hr : 0 < r) (k : ℕ) :
    |intervalMean u (c-(2:ℝ)^k*r) (c+(2:ℝ)^k*r) -
      intervalMean u (c-r) (c+r)| ≤ 2*(k:ℝ)*M := by sorry

theorem integral_abs_sub_center_mean_le {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {M c r : ℝ}
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M) (hr : 0 < r) (k : ℕ) :
    (∫ t in Ioc (c-(2:ℝ)^k*r) (c+(2:ℝ)^k*r),
      |u t - intervalMean u (c-r) (c+r)|) ≤
        (1+2*(k:ℝ))*M * (2*((2:ℝ)^k*r)) := by sorry

theorem integral_abs_center_pow_le {u : ℝ → ℝ} (hu : LocallyIntegrable u) {M : ℝ}
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M) (k : ℕ) :
    (∫ t in Icc (-(2:ℝ)^k) ((2:ℝ)^k), |u t|) ≤
      ((1+2*(k:ℝ))*M + |intervalMean u (-1) 1|) * (2*(2:ℝ)^k) := by sorry

end FF.Pavlov
```

## Basic.lean

Source: [Basic.lean](../FourierFrames/Cited/Pavlov/Basic.lean).

Detailed proof: [P5_Dispersion](P5_Dispersion.md).

Direct imports:

```lean
import FourierFrames.Defs
```

Opening commands:

```lean
open MeasureTheory Complex
```

Public interface:

```lean
namespace FF.Pavlov

def LogIntegrable (u : ℝ → ℝ) : Prop :=
  Integrable (fun t ↦ u t / (1 + t ^ 2)) volume

def schwarzIntegral (u : ℝ → ℝ) (z : ℂ) : ℂ :=
  (-I / Real.pi) * ∫ t : ℝ,
    (((t : ℂ) - z)⁻¹ - ((t / (1 + t ^ 2) : ℝ) : ℂ)) * (u t : ℂ)

def conjugatePoisson (u : ℝ → ℝ) (y x : ℝ) : ℝ :=
  Real.pi⁻¹ * ∫ t : ℝ,
    ((x - t) / ((x - t) ^ 2 + y ^ 2) + t / (1 + t ^ 2)) * u t

end FF.Pavlov
```

## BMOLogIntegrable.lean

Source: [BMOLogIntegrable.lean](../FourierFrames/Cited/Pavlov/BMOLogIntegrable.lean).

Detailed proof: [P5_PoissonBMO](P5_PoissonBMO.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.Basic
import FourierFrames.Cited.Pavlov.BMOIntervalGrowth
```

Opening commands:

```lean
open MeasureTheory Set Filter
```

Public interface:

```lean
namespace FF.Pavlov

def bmoDyadicShell (k : ℕ) : Set ℝ :=
  {t | (2:ℝ)^k ≤ |t| ∧ |t| ≤ (2:ℝ)^(k+1)}

lemma bmoDyadicShell_measurable (k : ℕ) : MeasurableSet (bmoDyadicShell k) := by sorry

lemma bmoDyadicShell_subset (k : ℕ) :
    bmoDyadicShell k ⊆ Icc (-(2:ℝ)^(k+1)) ((2:ℝ)^(k+1)) := by sorry

lemma bmo_weight_locallyIntegrable {u : ℝ → ℝ} (hu : LocallyIntegrable u) :
    LocallyIntegrable (fun t ↦ u t/(1+t^2)) := by sorry

lemma integral_bmo_weight_shell_le {u : ℝ → ℝ} (hu : LocallyIntegrable u) (k : ℕ) :
    (∫ t in bmoDyadicShell k, ‖u t/(1+t^2)‖) ≤
      ((2:ℝ)^k)^(-2:ℤ) *
        ∫ t in Icc (-(2:ℝ)^(k+1)) ((2:ℝ)^(k+1)), |u t| := by sorry

lemma integral_bmo_weight_shell_le_geometric {u : ℝ → ℝ} (hu : LocallyIntegrable u)
    {M : ℝ} (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M) (k : ℕ) :
    (∫ t in bmoDyadicShell k, ‖u t/(1+t^2)‖) ≤
      4 * ((1:ℝ)/2)^k * ((3+2*(k:ℝ))*M + |intervalMean u (-1) 1|) := by sorry

theorem memBMO_logIntegrable {u : ℝ → ℝ} (hu : FF.MemBMO u) : LogIntegrable u := by sorry

end FF.Pavlov
```

## BMOSecondMoment.lean

Source: [BMOSecondMoment.lean](../FourierFrames/Cited/Pavlov/BMOSecondMoment.lean).

Detailed proof: [P5_PoissonBMO](P5_PoissonBMO.md).

Direct imports:

```lean
import FourierFrames.Cited.JohnNirenberg
```

Opening commands:

```lean
open MeasureTheory Set Filter
open scoped ENNReal
```

Public interface:

```lean
namespace FF.Pavlov

theorem lintegral_sq_eq_tail {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ} (hf : AEMeasurable f μ) (hpos : 0 ≤ᵐ[μ] f) :
    (∫⁻ x, ENNReal.ofReal ((f x)^2) ∂μ) =
      ∫⁻ s in Ioi (0:ℝ), μ {x | s ≤ f x} * ENNReal.ofReal (2*s) := by sorry

theorem integrable_sq_of_exp_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hpos : 0 ≤ᵐ[μ] f) {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (htail : ∀ s : ℝ, 0 < s →
      μ {x | s ≤ f x} ≤ ENNReal.ofReal (A * Real.exp (-c*s))) :
    Integrable (fun x ↦ (f x)^2) μ := by sorry

theorem integral_linear_exp_neg {c : ℝ} (hc : 0 < c) :
    (∫ s : ℝ in Ioi 0, s*Real.exp (-c*s)) = c⁻¹^2 := by sorry

theorem integral_sq_le_of_exp_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hpos : 0 ≤ᵐ[μ] f) {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (htail : ∀ s : ℝ, 0 < s →
      μ {x | s ≤ f x} ≤ ENNReal.ofReal (A * Real.exp (-c*s))) :
    (∫ x, (f x)^2 ∂μ) ≤ 2*A*c⁻¹^2 := by sorry

theorem bmo_osc_integrableOn_sq {u : ℝ → ℝ} (hu : LocallyIntegrable u)
    {M : ℝ} (hM : 0 < M)
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M)
    {a b : ℝ} (hab : a < b) :
    IntegrableOn (fun t ↦ (u t-intervalMean u a b)^2) (Icc a b) := by sorry

theorem bmo_local_square_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ), LocallyIntegrable u →
      ∀ M : ℝ, 0 < M →
      (∀ a b : ℝ, a < b → meanOsc u a b ≤ M) →
      ∀ a b : ℝ, a < b →
        IntegrableOn (fun t ↦ (u t-intervalMean u a b)^2) (Icc a b) ∧
        (∫ t in a..b, (u t-intervalMean u a b)^2) ≤ C*M^2*(b-a) := by sorry

end FF.Pavlov
```

## Cardinal.lean

Source: [Cardinal.lean](../FourierFrames/Cited/Pavlov/Cardinal.lean).

Detailed proof: [P5_Cardinal](P5_Cardinal.md).

Direct imports:

```lean
import FourierFrames.Corollary1
import FourierFrames.Cited.PaleyWiener
import FourierFrames.Cited.DeBrangesFC
import FourierFrames.Cited.DeBrangesDE
```

Opening commands:

```lean
open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate
```

Public interface:

```lean
namespace FF.Pavlov

def cardinal (G : ℂ → ℂ) (γ : ℝ) (z : ℂ) : ℂ :=
  dslope G (γ : ℂ) z / deriv G (γ : ℂ)

structure GeneratingData (Γ : Set ℝ) where
  E : ℂ → ℂ
  strictHB : IsStrictHB E
  eqPW : HEEqPW E
  sample_norm : ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Γ f
  G : ℂ → ℂ
  G_eq : G = fun z ↦ E z + fstar E z
  entire : Differentiable ℂ G
  real : fstar G = G
  zeros : ∀ z : ℂ, G z = 0 ↔ ∃ x ∈ Γ, z = (x : ℂ)

theorem exists_generatingData {Γ : Set ℝ} (hΓ : IsSeparated Γ)
    (hcis : IsCompleteInterpolating Γ) : Nonempty (GeneratingData Γ) := by sorry

variable {Γ : Set ℝ}

def kernelCoeff (d : GeneratingData Γ) (γ : ℝ) : ℂ :=
  I / (2 * Real.pi) * conj (d.E γ)

theorem GeneratingData.zero (d : GeneratingData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    d.G (γ : ℂ) = 0 := by sorry

theorem GeneratingData.kernel_eq_dslope (d : GeneratingData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    deBrangesKernel d.E (γ : ℂ) =
      fun z ↦ kernelCoeff d γ * dslope d.G (γ : ℂ) z := by sorry

theorem GeneratingData.simple (d : GeneratingData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    deriv d.G (γ : ℂ) ≠ 0 := by sorry

theorem kernelCoeff_ne_zero (d : GeneratingData Γ) (γ : ℝ) : kernelCoeff d γ ≠ 0 := by sorry

theorem GeneratingData.cardinal_eq_kernel (d : GeneratingData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    cardinal d.G γ = fun z ↦ (kernelCoeff d γ)⁻¹ / deriv d.G (γ : ℂ) *
      deBrangesKernel d.E (γ : ℂ) z := by sorry

theorem GeneratingData.cardinal_mem (d : GeneratingData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    MemPW (cardinal d.G γ) := by sorry

theorem GeneratingData.cardinal_values (d : GeneratingData Γ) {γ t : ℝ}
    (hγ : γ ∈ Γ) (ht : t ∈ Γ) :
    cardinal d.G γ (t : ℂ) = if t = γ then 1 else 0 := by sorry

theorem GeneratingData.sampleSum_cardinal (d : GeneratingData Γ) {γ : ℝ}
    (hγ : γ ∈ Γ) : sampleSum Γ (cardinal d.G γ) = 1 := by sorry

theorem GeneratingData.uniform_cardinal_norm (d : GeneratingData Γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ ∈ Γ, (pwNormSq (cardinal d.G γ)).toReal ≤ C := by sorry

structure CardinalData (Γ : Set ℝ) extends GeneratingData Γ where
  normBound : ℝ
  normBound_pos : 0 < normBound
  cardinal_norm : ∀ γ ∈ Γ, (pwNormSq (cardinal G γ)).toReal ≤ normBound

theorem exists_cardinalData {Γ : Set ℝ} (hΓ : IsSeparated Γ)
    (hcis : IsCompleteInterpolating Γ) : Nonempty (CardinalData Γ) := by sorry

theorem GeneratingData.cardinal_mul_sub (d : GeneratingData Γ) {γ : ℝ}
    (hγ : γ ∈ Γ) (z : ℂ) :
    deriv d.G (γ : ℂ) * (z-(γ : ℂ)) * cardinal d.G γ z = d.G z := by sorry

theorem GeneratingData.cardinal_zero_iff (d : GeneratingData Γ) {γ : ℝ}
    (hγ : γ ∈ Γ) (z : ℂ) :
    cardinal d.G γ z = 0 ↔ ∃ t ∈ Γ, t ≠ γ ∧ z = (t : ℂ) := by sorry

theorem GeneratingData.cardinal_synthesis_mem (d : GeneratingData Γ)
    (s : Finset Γ) (a : Γ → ℂ) :
    MemPW (fun z ↦ ∑ γ ∈ s, a γ * cardinal d.G (γ : ℝ) z) := by sorry

theorem GeneratingData.cardinal_synthesis_value (d : GeneratingData Γ)
    (s : Finset Γ) (a : Γ → ℂ) (t : Γ) :
    (∑ γ ∈ s, a γ * cardinal d.G (γ : ℝ) (t : ℂ)) = if t ∈ s then a t else 0 := by sorry

theorem GeneratingData.sampleSum_cardinal_synthesis (d : GeneratingData Γ)
    (s : Finset Γ) (a : Γ → ℂ) :
    sampleSum Γ (fun z ↦ ∑ γ ∈ s, a γ * cardinal d.G (γ : ℝ) z) =
      ∑ γ ∈ s, ‖a γ‖ₑ ^ 2 := by sorry

theorem GeneratingData.cardinal_synthesis_bound (d : GeneratingData Γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset Γ) (a : Γ → ℂ),
      (pwNormSq (fun z ↦ ∑ γ ∈ s, a γ * cardinal d.G (γ : ℝ) z)).toReal ≤
        C * ∑ γ ∈ s, ‖a γ‖ ^ 2 := by sorry

theorem sampling_relatively_dense {Γ : Set ℝ} (hΓ : IsSeparated Γ) (hs : IsSampling Γ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, ∃ γ ∈ Γ, |γ-t| < R := by sorry

structure Grid (Γ : Set ℝ) where
  point : ℤ → ℝ
  strictMono : StrictMono point
  range_eq : Set.range point = Γ
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper
  gap_lower : ∀ k, lower ≤ point (k+1) - point k
  gap_upper : ∀ k, point (k+1) - point k ≤ upper

def cell {Γ : Set ℝ} (g : Grid Γ) (k : ℤ) : Set ℝ :=
  Icc ((g.point (k-1) + g.point k)/2) ((g.point k + g.point (k+1))/2)

theorem GeneratingData.exists_enum (d : GeneratingData Γ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ Set.range γ = Γ := by sorry

theorem gap_le_of_relatively_dense {γ : ℤ → ℝ} (hγ : StrictMono γ)
    {R : ℝ} (hR : ∀ t : ℝ, ∃ k : ℤ, |γ k-t| < R) (k : ℤ) :
    γ (k+1)-γ k ≤ 2*R := by sorry

theorem exists_grid {Γ : Set ℝ} (hΓ : IsSeparated Γ)
    (hcis : IsCompleteInterpolating Γ) : Nonempty (Grid Γ) := by sorry

theorem Grid.point_mem (g : Grid Γ) (k : ℤ) : g.point k ∈ Γ := by sorry

theorem Grid.upper_pos (g : Grid Γ) : 0 < g.upper := by sorry

theorem Grid.point_mem_cell (g : Grid Γ) (k : ℤ) : g.point k ∈ cell g k := by sorry

theorem Grid.cell_length_bounds (g : Grid Γ) (k : ℤ) :
    g.lower ≤ (g.point k + g.point (k+1))/2 - (g.point (k-1)+g.point k)/2 ∧
    (g.point k + g.point (k+1))/2 - (g.point (k-1)+g.point k)/2 ≤ g.upper := by sorry

theorem Grid.abs_sub_center_le (g : Grid Γ) {k : ℤ} {x : ℝ} (hx : x ∈ cell g k) :
    |x-g.point k| ≤ g.upper/2 := by sorry

theorem Grid.other_node_distance (g : Grid Γ) {k : ℤ} {x : ℝ}
    (hx : x ∈ cell g k) {j : ℤ} (hj : j ≠ k) : g.lower/2 ≤ |x-g.point j| := by sorry

theorem Grid.monotone_sub_lower (g : Grid Γ) :
    Monotone (fun k : ℤ ↦ g.point k-g.lower*(k : ℝ)) := by sorry

theorem Grid.exists_above (g : Grid Γ) (x : ℝ) : ∃ k : ℤ, x < g.point k := by sorry

theorem Grid.exists_below (g : Grid Γ) (x : ℝ) : ∃ k : ℤ, g.point k < x := by sorry

theorem Grid.exists_between (g : Grid Γ) (x : ℝ) :
    ∃ k : ℤ, g.point k ≤ x ∧ x < g.point (k+1) := by sorry

theorem Grid.exists_cell (g : Grid Γ) (x : ℝ) : ∃ k : ℤ, x ∈ cell g k := by sorry

end FF.Pavlov
```

## BoundaryPhaseCount.lean

Source: [BoundaryPhaseCount.lean](../FourierFrames/Cited/Pavlov/BoundaryPhaseCount.lean).

Detailed proof: [P5_BoundaryPhase](P5_BoundaryPhase.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.Cardinal
import FourierFrames.Landau
```

Opening commands:

```lean
open MeasureTheory Set Filter Topology
```

Public interface:

```lean
namespace FF.Pavlov

variable {Γ : Set ℝ}

def gapMid (g : Grid Γ) (k : ℤ) : ℝ := (g.point k+g.point (k+1))/2

theorem Grid.gapMid_mem (g : Grid Γ) (k : ℤ) :
    gapMid g k ∈ Ioo (g.point k) (g.point (k+1)) := by sorry

theorem Grid.not_mem_of_mem_gap (g : Grid Γ) {k : ℤ} {x : ℝ}
    (hx : x ∈ Ioo (g.point k) (g.point (k+1))) : x ∉ Γ := by sorry

theorem Grid.exists_open_gap (g : Grid Γ) {x : ℝ} (hx : x ∉ Γ) :
    ∃ k : ℤ, x ∈ Ioo (g.point k) (g.point (k+1)) := by sorry

theorem Grid.countFn_eq_on_gap (g : Grid Γ) (hΓ : IsSeparated Γ) {k : ℤ} {x y : ℝ}
    (hx : x ∈ Ioo (g.point k) (g.point (k+1)))
    (hy : y ∈ Ioo (g.point k) (g.point (k+1))) : countFn Γ x = countFn Γ y := by sorry

theorem Grid.countFn_eq_of_mem_gap (g : Grid Γ) (hΓ : IsSeparated Γ) {k : ℤ} {x : ℝ}
    (hx : x ∈ Ioo (g.point k) (g.point (k+1))) : countFn Γ x = countFn Γ (gapMid g k) := by sorry

theorem Grid.nodes_between_gapMids (g : Grid Γ) (k : ℤ) :
    Γ ∩ Ioc (gapMid g k) (gapMid g (k+1)) = {g.point (k+1)} := by sorry

theorem Grid.countFn_gapMid_succ_sub (g : Grid Γ) (hΓ : IsSeparated Γ) (k : ℤ) :
    countFn Γ (gapMid g (k+1))-countFn Γ (gapMid g k) = 1 := by sorry

theorem Grid.exists_countFn_constant_of_pi_jump (g : Grid Γ) (hΓ : IsSeparated Γ)
    (β : ℤ → ℝ) (hβ : ∀ k : ℤ, β (k+1) = β k-Real.pi) :
    ∃ c : ℝ, ∀ k : ℤ, β k = -Real.pi * countFn Γ (gapMid g k)+c := by sorry

end FF.Pavlov
```

## BoundaryPhase.lean

Source: [BoundaryPhase.lean](../FourierFrames/Cited/Pavlov/BoundaryPhase.lean).

Detailed proof: [P5_BoundaryPhase](P5_BoundaryPhase.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.BoundaryPhaseCount
import TauCeti.Analysis.Complex.BranchLogRoot
```

Opening commands:

```lean
open MeasureTheory Set Complex Filter Topology Metric
open scoped ENNReal NNReal ComplexConjugate
```

Public interface:

```lean
namespace FF.Pavlov

theorem GeneratingData.exists_upper_log {Γ : Set ℝ} (d : GeneratingData Γ) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L UHP ∧
      ∀ z ∈ UHP, Complex.exp (L z) = d.G z := by sorry

theorem GeneratingData.boundary_phase {Γ : Set ℝ}
    (hΓ : IsSeparated Γ) (d : GeneratingData Γ) (g : Grid Γ)
    {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L UHP)
    (hexp : ∀ z ∈ UHP, Complex.exp (L z) = d.G z) :
    ∃ c : ℝ, ∀ x : ℝ, x ∉ Γ →
      Tendsto (fun y : ℝ ↦ (L ((x:ℂ)+(y:ℂ)*I)).im)
        (𝓝[>] 0) (𝓝 (-Real.pi * countFn Γ x + c)) := by sorry

end FF.Pavlov
```

## Harnack.lean

Source: [Harnack.lean](../FourierFrames/Cited/Pavlov/Harnack.lean).

Detailed proof: [P5_Harnack](P5_Harnack.md).

Direct imports:

```lean
public import TauCeti.Analysis.PDE.Harnack.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.CauchyIntegral
```

Opening commands:

```lean
open Set Complex InnerProductSpace
```

Public interface:

```lean
namespace FF.Pavlov

def rect (a b r : ℝ) : Set ℂ :=
  {z | a-r < z.re ∧ z.re < b+r ∧ |z.im| < r}

theorem norm_lower_on_rectangle
    {r D M : ℝ} (hr : 0 < r) (hD : 0 < D) :
    ∃ c : ℝ, 0 < c ∧ ∀ (f : ℂ → ℂ) (a b t₀ : ℝ),
      a ≤ t₀ → t₀ ≤ b → b-a ≤ D →
      Differentiable ℂ f →
      (∀ z ∈ rect a b r, f z ≠ 0) →
      (∀ z ∈ rect a b r, ‖f z‖ ≤ M) →
      f (t₀ : ℂ) = 1 →
      ∀ x ∈ Set.Icc a b, ∀ y : ℝ, |y| ≤ r/2 →
        c ≤ ‖f ((x : ℂ) + (y : ℂ)*Complex.I)‖ := by sorry

end FF.Pavlov
```

## CellBounds.lean

Source: [CellBounds.lean](../FourierFrames/Cited/Pavlov/CellBounds.lean).

Detailed proof: [P5_A2](P5_A2.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.Cardinal
import FourierFrames.Cited.Pavlov.Harnack
```

Opening commands:

```lean
open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate
```

Public interface:

```lean
namespace FF.Pavlov

variable {Γ : Set ℝ}

theorem cardinal_ne_zero_rect (g : Grid Γ) (d : GeneratingData Γ) (k : ℤ)
    {r : ℝ} (hr : r < g.lower/2) :
    ∀ z ∈ rect ((g.point (k-1)+g.point k)/2) ((g.point k+g.point (k+1))/2) r,
      cardinal d.G (g.point k) z ≠ 0 := by sorry

theorem cardinal_cell_bounds (g : Grid Γ) (d : CardinalData Γ) :
    ∃ ε c C : ℝ, 0 < ε ∧ ε < g.lower/8 ∧ 0 < c ∧ 0 < C ∧
      ∀ k : ℤ, ∀ x ∈ cell g k, ∀ y : ℝ, |y| ≤ ε →
        c ≤ ‖cardinal d.G (g.point k) ((x : ℂ)+(y : ℂ)*I)‖ ∧
        ‖cardinal d.G (g.point k) ((x : ℂ)+(y : ℂ)*I)‖ ≤ C := by sorry

theorem GeneratingData.norm_generating_eq (d : GeneratingData Γ) {γ : ℝ}
    (hγ : γ ∈ Γ) (z : ℂ) :
    ‖d.G z‖ = ‖deriv d.G (γ : ℂ)‖ * ‖z-(γ : ℂ)‖ * ‖cardinal d.G γ z‖ := by sorry

theorem generating_cell_bounds (g : Grid Γ) (d : CardinalData Γ) :
    ∃ ε c C : ℝ, 0 < ε ∧ ε < g.lower/8 ∧ 0 < c ∧ 0 < C ∧
      ∀ k : ℤ, ∀ x ∈ cell g k,
        (c * ‖deriv d.G (g.point k : ℂ)‖ ≤ ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖ ∧
         ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖ ≤ C * ‖deriv d.G (g.point k : ℂ)‖) ∧
        (c * ‖deriv d.G (g.point k : ℂ)‖ * |x-g.point k| ≤ ‖d.G (x : ℂ)‖ ∧
         ‖d.G (x : ℂ)‖ ≤ C * ‖deriv d.G (g.point k : ℂ)‖ * |x-g.point k|) := by sorry

theorem generating_log_cell_comparison (g : Grid Γ) (d : CardinalData Γ) :
    ∃ ε B : ℝ, 0 < ε ∧ ε < g.lower/8 ∧ 0 ≤ B ∧
      ∀ k : ℤ, ∀ x ∈ cell g k, x ≠ g.point k →
        |Real.log ‖d.G (x : ℂ)‖ - Real.log ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖ -
          Real.log (abs (x-g.point k))| ≤ B := by sorry

end FF.Pavlov
```

## Weights.lean

Source: [Weights.lean](../FourierFrames/Cited/Pavlov/Weights.lean).

Detailed proof: [P5_A2](P5_A2.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.CellBounds
import FourierFrames.PW.PlancherelPolya
```

Opening commands:

```lean
open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal
```

Public interface:

```lean
namespace FF.Pavlov

theorem shifted_plancherelPolya {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    ∃ C : ℝ≥0, ∀ Λ : Set ℝ, IsSepBy δ Λ → ∀ f : ℂ → ℂ, MemPW f →
      sampleSum Λ (fun z ↦ f (z + (y : ℂ) * I)) ≤ C * pwNormSq f := by sorry

theorem shifted_finite_sampling {Γ : Set ℝ} (hΓ : IsSeparated Γ) (y : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : Finset Γ) (f : ℂ → ℂ), MemPW f →
      (∑ j ∈ t, ‖f ((j : ℂ) + (y : ℂ) * I)‖^2) ≤ C * (pwNormSq f).toReal := by sorry

theorem GeneratingData.cardinal_synthesis_cauchy {Γ : Set ℝ} (d : GeneratingData Γ)
    (s : Finset Γ) (b : Γ → ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    (∑ k ∈ s, (b k * deriv d.G (k : ℂ)) * cardinal d.G (k : ℝ) z) =
      d.G z * ∑ k ∈ s, b k / (z - (k : ℂ)) := by sorry

theorem GeneratingData.weighted_cauchy_bound {Γ : Set ℝ} (d : GeneratingData Γ)
    (hΓ : IsSeparated Γ) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hshift : ∀ j : Γ, c * ‖deriv d.G (j : ℂ)‖ ≤
      ‖d.G ((j : ℂ) + (ε : ℂ) * I)‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s t : Finset Γ) (b : Γ → ℂ),
      (∑ j ∈ t, ‖deriv d.G (j : ℂ)‖^2 *
        ‖∑ k ∈ s, b k / ((j : ℂ) + (ε : ℂ) * I - (k : ℂ))‖^2) ≤
      C * ∑ k ∈ s, ‖deriv d.G (k : ℂ)‖^2 * ‖b k‖^2 := by sorry

variable {ι : Type*}

def weightSum (s : Finset ι) (v : ι → ℝ) : ℝ := ∑ k ∈ s, v k

def invWeightSum (s : Finset ι) (v : ι → ℝ) : ℝ := ∑ k ∈ s, (v k)⁻¹

theorem card_sq_le_weightSum_mul_invWeightSum (s : Finset ι) (v : ι → ℝ)
    (hv : ∀ k ∈ s, 0 < v k) :
    (s.card : ℝ)^2 ≤ weightSum s v * invWeightSum s v := by sorry

theorem diagonal_of_cross_tests {WI VI WJ VJ K n : ℝ}
    (hWI : 0 ≤ WI) (hVI : 0 ≤ VI) (hWJ : 0 ≤ WJ) (hVJ : 0 ≤ VJ)
    (hn : 0 < n) (hlower : n^2 ≤ WJ * VJ)
    (hcross₁ : WJ * VI ≤ K) (hcross₂ : WI * VJ ≤ K) :
    WI * VI ≤ K^2 / n^2 := by sorry

theorem cross_test_of_positive_matrix [DecidableEq ι] (s t : Finset ι) (v : ι → ℝ)
    (T : ι → ι → ℝ) {κ C : ℝ} (hs : s.Nonempty)
    (hv : ∀ k ∈ s ∪ t, 0 < v k) (hκ : 0 < κ)
    (hT : ∀ j ∈ t, ∀ k ∈ s, κ ≤ T j k)
    (hbound : (∑ j ∈ t, v j * (∑ k ∈ s, T j k / v k)^2) ≤
      C * invWeightSum s v) :
    weightSum t v * invWeightSum s v ≤ C / κ^2 := by sorry

theorem cross_test_of_complex_matrix [DecidableEq ι] (s t : Finset ι) (v : ι → ℝ)
    (T : ι → ι → ℂ) {κ C : ℝ} (hs : s.Nonempty)
    (hv : ∀ k ∈ s ∪ t, 0 < v k) (hκ : 0 < κ)
    (hT : ∀ j ∈ t, ∀ k ∈ s, κ ≤ (T j k).re)
    (hbound : (∑ j ∈ t, v j * ‖∑ k ∈ s, ((v k)⁻¹ : ℂ) * T j k‖^2) ≤
      C * invWeightSum s v) :
    weightSum t v * invWeightSum s v ≤ C / κ^2 := by sorry

theorem cauchy_re_lower {r ε L U : ℝ} (hL : 0 < L) (hr : L ≤ r)
    (hU : r ≤ U) :
    L / (U^2 + ε^2) ≤ (((r : ℂ) + (ε : ℂ) * I)⁻¹).re := by sorry

theorem Grid.point_sub_bounds {Γ : Set ℝ} (g : Grid Γ) {k j : ℤ} (hkj : k ≤ j) :
    g.lower * ((j-k : ℤ) : ℝ) ≤ g.point j - g.point k ∧
      g.point j - g.point k ≤ g.upper * ((j-k : ℤ) : ℝ) := by sorry

theorem Grid.block_cauchy_re_lower {Γ : Set ℝ} (g : Grid Γ)
    {a N j k : ℤ} {ε : ℝ} (hN : 0 < N) (hε : 0 ≤ ε) (hεu : ε ≤ g.upper)
    (hk : k ∈ Finset.Ico a (a+N))
    (hj : j ∈ Finset.Ico (a+2*N) (a+3*N)) :
    (g.lower / (10 * g.upper^2)) / (N : ℝ) ≤
      (((g.point j : ℂ) + (ε : ℂ)*I - (g.point k : ℂ))⁻¹).re := by sorry

theorem cross_test_of_weighted_operator [DecidableEq ι] (s t : Finset ι)
    (v : ι → ℝ) (T : ι → ι → ℂ) {κ C : ℝ} (hs : s.Nonempty)
    (hv : ∀ k ∈ s ∪ t, 0 < v k) (hκ : 0 < κ)
    (hT : ∀ j ∈ t, ∀ k ∈ s, κ ≤ (T j k).re)
    (hbound : ∀ b : ι → ℂ,
      (∑ j ∈ t, v j * ‖∑ k ∈ s, b k * T j k‖^2) ≤
        C * ∑ k ∈ s, v k * ‖b k‖^2) :
    weightSum t v * invWeightSum s v ≤ C / κ^2 := by sorry

theorem GeneratingData.cauchy_cross_bound {Γ : Set ℝ} (d : GeneratingData Γ)
    (hΓ : IsSeparated Γ) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hshift : ∀ j : Γ, c * ‖deriv d.G (j : ℂ)‖ ≤
      ‖d.G ((j : ℂ) + (ε : ℂ) * I)‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s t : Finset Γ) (κ : ℝ), s.Nonempty → 0 < κ →
      (∀ j ∈ t, ∀ k ∈ s, κ ≤
        (((j : ℂ) + (ε : ℂ) * I - (k : ℂ))⁻¹).re) →
      weightSum t (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) *
        invWeightSum s (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) ≤ C / κ^2 := by sorry

theorem GeneratingData.cauchy_cross_bound_negative {Γ : Set ℝ} (d : GeneratingData Γ)
    (hΓ : IsSeparated Γ) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hshift : ∀ j : Γ, c * ‖deriv d.G (j : ℂ)‖ ≤
      ‖d.G ((j : ℂ) + (ε : ℂ) * I)‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s t : Finset Γ) (κ : ℝ), s.Nonempty → 0 < κ →
      (∀ j ∈ t, ∀ k ∈ s, κ ≤
        -(((j : ℂ) + (ε : ℂ) * I - (k : ℂ))⁻¹).re) →
      weightSum t (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) *
        invWeightSum s (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) ≤ C / κ^2 := by sorry

def Grid.nodeEmbedding {Γ : Set ℝ} (g : Grid Γ) : ℤ ↪ Γ where
  toFun k := ⟨g.point k, g.point_mem k⟩
  inj' := by intro a b h; exact g.strictMono.injective (congrArg Subtype.val h)

def Grid.block {Γ : Set ℝ} (g : Grid Γ) (a : ℤ) (N : ℕ) : Finset Γ :=
  (Finset.Ico a (a + N)).map g.nodeEmbedding

theorem Grid.block_card {Γ : Set ℝ} (g : Grid Γ) (a : ℤ) (N : ℕ) :
    (g.block a N).card = N := by sorry

theorem Grid.block_nonempty {Γ : Set ℝ} (g : Grid Γ) (a : ℤ) {N : ℕ}
    (hN : 0 < N) : (g.block a N).Nonempty := by sorry

theorem cauchy_re_reflect (x y ε : ℝ) :
    -(((x : ℂ) + (ε : ℂ)*I - (y : ℂ))⁻¹).re =
      (((y : ℂ) + (ε : ℂ)*I - (x : ℂ))⁻¹).re := by sorry

theorem GeneratingData.discrete_A2 {Γ : Set ℝ} (d : GeneratingData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) {ε c : ℝ}
    (hε : 0 < ε) (hεu : ε ≤ g.upper) (hc : 0 < c)
    (hshift : ∀ j : Γ, c * ‖deriv d.G (j : ℂ)‖ ≤
      ‖d.G ((j : ℂ) + (ε : ℂ) * I)‖) :
    ∃ A : ℝ, 0 < A ∧ ∀ (a : ℤ) (N : ℕ), 0 < N →
      weightSum (g.block a N) (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) *
        invWeightSum (g.block a N) (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) ≤ A * (N : ℝ)^2 := by sorry

theorem CardinalData.discrete_A2 {Γ : Set ℝ} (d : CardinalData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (a : ℤ) (N : ℕ), 0 < N →
      weightSum (g.block a N) (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) *
        invWeightSum (g.block a N) (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) ≤ A * (N : ℝ)^2 := by sorry

end FF.Pavlov
```

## LogDistanceCore.lean

Source: [LogDistanceCore.lean](../FourierFrames/Cited/Pavlov/LogDistanceCore.lean).

Detailed proof: [P5_LogDistance](P5_LogDistance.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.Cardinal
import FourierFrames.Cited.Pavlov.BMO
```

Opening commands:

```lean
open MeasureTheory Metric Set Filter Topology
```

Public interface:

```lean
namespace FF.Pavlov

variable {Γ : Set ℝ}

theorem Grid.abs_sub_center_le_node (g : Grid Γ) {k : ℤ} {x : ℝ}
    (hx : x ∈ cell g k) (j : ℤ) : |x-g.point k| ≤ |x-g.point j| := by sorry

theorem Grid.infDist_eq_abs_sub (g : Grid Γ) {k : ℤ} {x : ℝ}
    (hx : x ∈ cell g k) : Metric.infDist x Γ = |x-g.point k| := by sorry

theorem Grid.countable (g : Grid Γ) : Γ.Countable := by sorry

theorem Grid.ae_not_mem (g : Grid Γ) : ∀ᵐ x : ℝ, x ∉ Γ := by sorry

theorem Grid.infDist_le (g : Grid Γ) (x : ℝ) : Metric.infDist x Γ ≤ g.upper/2 := by sorry

theorem Grid.integrableOn_log_infDist_cell (g : Grid Γ) (k : ℤ) :
    IntegrableOn (fun x ↦ Real.log (Metric.infDist x Γ)) (cell g k) := by sorry

theorem Grid.locallyIntegrable_log_infDist (g : Grid Γ) :
    LocallyIntegrable (fun x ↦ Real.log (Metric.infDist x Γ)) := by sorry

theorem Grid.meanOsc_log_infDist_le_of_far (g : Grid Γ) {a b : ℝ} (hab : a < b)
    (hfar : 2*(b-a) ≤ Metric.infDist a Γ) :
    meanOsc (fun x ↦ Real.log (Metric.infDist x Γ)) a b ≤ 2*Real.log 2 := by sorry

theorem Grid.mem_cell_of_abs_sub_le (g : Grid Γ) {k : ℤ} {x : ℝ}
    (hx : |x-g.point k| ≤ g.lower/2) : x ∈ cell g k := by sorry

theorem Grid.exists_nearest_on_short_interval (g : Grid Γ) {a b : ℝ}
    (hab : a < b) (hsmall : b-a < g.lower/8)
    (hnear : Metric.infDist a Γ < 2*(b-a)) :
    ∃ k : ℤ, |g.point k-a| < 2*(b-a) ∧
      ∀ x ∈ Icc a b, Metric.infDist x Γ = |x-g.point k| := by sorry

theorem meanOsc_congr_on_Icc {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfg : EqOn f g (Icc a b)) : meanOsc f a b = meanOsc g a b := by sorry

end FF.Pavlov
```

## LogDistanceLarge.lean

Source: [LogDistanceLarge.lean](../FourierFrames/Cited/Pavlov/LogDistanceLarge.lean).

Detailed proof: [P5_LogDistance](P5_LogDistance.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.LogDistanceCore
import FourierFrames.Cited.Pavlov.BMO
```

Opening commands:

```lean
open MeasureTheory Metric Set Filter Topology
```

Public interface:

```lean
namespace FF.Pavlov

variable {Γ : Set ℝ}

def Grid.edge (g : Grid Γ) (k : ℤ) : ℝ := (g.point (k-1)+g.point k)/2

theorem Grid.cell_eq_Icc_edges (g : Grid Γ) (k : ℤ) :
    cell g k = Icc (g.edge k) (g.edge (k+1)) := by sorry

theorem Grid.edge_gap_lower (g : Grid Γ) (k : ℤ) :
    g.lower ≤ g.edge (k+1)-g.edge k := by sorry

theorem Grid.edge_strictMono (g : Grid Γ) : StrictMono g.edge := by sorry

theorem Grid.edge_mono_sub_lower (g : Grid Γ) :
    Monotone (fun k : ℤ ↦ g.edge k-g.lower*(k : ℝ)) := by sorry

theorem Grid.exists_cell_cover (g : Grid Γ) {a b : ℝ} (hab : a < b) :
    ∃ m n : ℤ, m ≤ n ∧
      Icc a b ⊆ ⋃ k ∈ Finset.Icc m n, cell g k ∧
      ((n-m+1 : ℤ) : ℝ) ≤ (b-a)/g.lower+2 := by sorry

theorem Grid.exists_cell_span (g : Grid Γ) {a b : ℝ} (hab : a < b) :
    ∃ m n : ℤ, m ≤ n ∧ g.edge m ≤ a ∧ b ≤ g.edge (n+1) ∧
      ((n-m+1 : ℤ) : ℝ) ≤ (b-a)/g.lower+2 := by sorry

theorem Grid.integral_abs_log_infDist_cell_le (g : Grid Γ) (k : ℤ) :
    (∫ x in g.edge k..g.edge (k+1), |Real.log (Metric.infDist x Γ)|) ≤
      ∫ x in (-g.upper/2)..(g.upper/2), |Real.log x| := by sorry

theorem Grid.integral_abs_log_infDist_span_le (g : Grid Γ) (m : ℤ) (N : ℕ) :
    (∫ x in g.edge m..g.edge (m+(N : ℤ)), |Real.log (Metric.infDist x Γ)|) ≤
      (N : ℝ) * ∫ x in (-g.upper/2)..(g.upper/2), |Real.log x| := by sorry

theorem Grid.exists_large_interval_log_infDist_bound (g : Grid Γ) :
    ∃ K : ℝ, ∀ a b : ℝ, a < b → g.lower/8 ≤ b-a →
      (b-a)⁻¹ * (∫ x in a..b, |Real.log (Metric.infDist x Γ)|) ≤ K := by sorry

end FF.Pavlov
```

## WeightTransfer.lean

Source: [WeightTransfer.lean](../FourierFrames/Cited/Pavlov/WeightTransfer.lean).

Detailed proof: [P5_A2](P5_A2.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.Weights
import FourierFrames.Cited.Pavlov.LogDistanceLarge
```

Opening commands:

```lean
open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal
```

Public interface:

```lean
namespace FF.Pavlov

theorem Grid.integral_le_cell_sum {Γ : Set ℝ} (g : Grid Γ)
    (s : Finset ℤ) (v : ℤ → ℝ) (hv : ∀ k ∈ s, 0 ≤ v k)
    {w : ℝ → ℝ} {a b : ℝ} (hw : IntegrableOn w (Icc a b))
    (hcover : ∀ x ∈ Icc a b, ∃ k ∈ s, x ∈ cell g k)
    (hbound : ∀ k ∈ s, ∀ x ∈ cell g k, w x ≤ v k) :
    (∫ x in Icc a b, w x) ≤ g.upper * ∑ k ∈ s, v k := by sorry

theorem Grid.integral_le_length_cell_sum {Γ : Set ℝ} (g : Grid Γ)
    (s : Finset ℤ) (v : ℤ → ℝ) (hv : ∀ k ∈ s, 0 ≤ v k)
    {w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hw : IntegrableOn w (Icc a b))
    (hcover : ∀ x ∈ Icc a b, ∃ k ∈ s, x ∈ cell g k)
    (hbound : ∀ k ∈ s, ∀ x ∈ cell g k, w x ≤ v k) :
    (∫ x in Icc a b, w x) ≤ (b-a) * ∑ k ∈ s, v k := by sorry

theorem Grid.integral_le_min_cell_sum {Γ : Set ℝ} (g : Grid Γ)
    (s : Finset ℤ) (v : ℤ → ℝ) (hv : ∀ k ∈ s, 0 ≤ v k)
    {w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hw : IntegrableOn w (Icc a b))
    (hcover : ∀ x ∈ Icc a b, ∃ k ∈ s, x ∈ cell g k)
    (hbound : ∀ k ∈ s, ∀ x ∈ cell g k, w x ≤ v k) :
    (∫ x in Icc a b, w x) ≤ min g.upper (b-a) * ∑ k ∈ s, v k := by sorry

theorem Grid.min_length_mul_card_le {Γ : Set ℝ} (g : Grid Γ) {L n : ℝ}
    (hL : 0 < L) (hn : 0 ≤ n) (hcard : n ≤ L/g.lower+2) :
    min g.upper L * n ≤ (3*g.upper/g.lower)*L := by sorry

theorem Grid.integral_A2_of_cells {Γ : Set ℝ} (g : Grid Γ)
    (v : ℤ → ℝ) (hv : ∀ k, 0 < v k) {w : ℝ → ℝ}
    (hw : LocallyIntegrable w) (hwi : LocallyIntegrable (fun x ↦ (w x)⁻¹))
    {c C A : ℝ} (hc : 0 < c) (hC : 0 < C) (hA : 0 < A)
    (hcell : ∀ k, ∀ x ∈ cell g k, c*v k ≤ w x ∧ w x ≤ C*v k)
    (hdiscrete : ∀ m n : ℤ, m ≤ n →
      (∑ k ∈ Finset.Icc m n, v k) * (∑ k ∈ Finset.Icc m n, (v k)⁻¹) ≤
        A * (((n-m+1 : ℤ) : ℝ))^2)
    (hcover : ∀ a b : ℝ, a < b → ∃ m n : ℤ, m ≤ n ∧
      (∀ x ∈ Icc a b, ∃ k ∈ Finset.Icc m n, x ∈ cell g k) ∧
      (((n-m+1 : ℤ) : ℝ)) ≤ (b-a)/g.lower+2) :
    ∀ a b : ℝ, a < b →
      (∫ x in Icc a b, w x) * (∫ x in Icc a b, (w x)⁻¹) ≤
        (C/c*A*(3*g.upper/g.lower)^2)*(b-a)^2 := by sorry

theorem CardinalData.discrete_A2_Icc {Γ : Set ℝ} (d : CardinalData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) :
    ∃ A : ℝ, 0 < A ∧ ∀ m n : ℤ, m ≤ n →
      (∑ k ∈ Finset.Icc m n, ‖deriv d.G (g.point k : ℂ)‖^2) *
        (∑ k ∈ Finset.Icc m n, (‖deriv d.G (g.point k : ℂ)‖^2)⁻¹) ≤
          A * (((n-m+1 : ℤ) : ℝ))^2 := by sorry

theorem CardinalData.shifted_A2_of_bounds {Γ : Set ℝ} (d : CardinalData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) (ε c C : ℝ)
    (hc : 0 < c) (hC : 0 < C)
    (hbounds : ∀ k : ℤ, ∀ x ∈ cell g k,
      c * ‖deriv d.G (g.point k : ℂ)‖ ≤ ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖ ∧
      ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖ ≤ C * ‖deriv d.G (g.point k : ℂ)‖) :
    ∃ K : ℝ, 0 < K ∧
      LocallyIntegrable (fun x : ℝ ↦ ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2) ∧
      LocallyIntegrable (fun x : ℝ ↦ (‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2)⁻¹) ∧
      (∀ x : ℝ, 0 < ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2) ∧
      ∀ a b : ℝ, a < b →
        intervalMean (fun x : ℝ ↦ ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2) a b *
          intervalMean (fun x : ℝ ↦ (‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2)⁻¹) a b ≤ K := by sorry

theorem CardinalData.shifted_A2 {Γ : Set ℝ} (d : CardinalData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) :
    ∃ ε K : ℝ, 0 < ε ∧ ε < g.lower/8 ∧ 0 < K ∧
      LocallyIntegrable (fun x : ℝ ↦ ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2) ∧
      LocallyIntegrable (fun x : ℝ ↦ (‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2)⁻¹) ∧
      (∀ x : ℝ, 0 < ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2) ∧
      ∀ a b : ℝ, a < b →
        intervalMean (fun x : ℝ ↦ ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2) a b *
          intervalMean (fun x : ℝ ↦ (‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2)⁻¹) a b ≤ K := by sorry

end FF.Pavlov
```

## LogSingularity.lean

Source: [LogSingularity.lean](../FourierFrames/Cited/Pavlov/LogSingularity.lean).

Detailed proof: [P5_LogDistance](P5_LogDistance.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.BMO
```

Opening commands:

```lean
open MeasureTheory Set Filter Topology
```

Public interface:

```lean
namespace FF.Pavlov

theorem intervalIntegrable_log_abs_sub (γ a b : ℝ) :
    IntervalIntegrable (fun x ↦ Real.log |x-γ|) volume a b := by sorry

theorem locallyIntegrable_log_abs_sub (γ : ℝ) :
    LocallyIntegrable (fun x ↦ Real.log |x-γ|) := by sorry

def logSingularityBound : ℝ := ∫ u in (-4 : ℝ)..4, |Real.log (|u|)|

theorem logSingularityBound_nonneg : 0 ≤ logSingularityBound := by sorry

theorem log_singularity_comparison {a b γ : ℝ} (hab : a < b)
    (hγ : |γ-a| ≤ 3*(b-a)) :
    (b-a)⁻¹ * ∫ x in a..b, |Real.log |x-γ| - Real.log (b-a)| ≤
      logSingularityBound := by sorry

theorem exists_log_singularity_comparison : ∃ C : ℝ, 0 ≤ C ∧
    ∀ a b γ : ℝ, a < b → |γ-a| ≤ 3*(b-a) →
      (b-a)⁻¹ * ∫ x in a..b, |Real.log |x-γ| - Real.log (b-a)| ≤ C := by sorry

end FF.Pavlov
```

## LogDistanceTransfer.lean

Source: [LogDistanceTransfer.lean](../FourierFrames/Cited/Pavlov/LogDistanceTransfer.lean).

Detailed proof: [P5_LogDistance](P5_LogDistance.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.LogDistanceCore
import FourierFrames.Cited.Pavlov.CellBounds
```

Opening commands:

```lean
open MeasureTheory Metric Set Filter Topology Complex
```

Public interface:

```lean
namespace FF.Pavlov

variable {Γ : Set ℝ}

theorem memBMO_boundary_log_of_distance
    (g : Grid Γ) (G : ℂ → ℂ) (ε C : ℝ)
    (hdistance : MemBMO (fun x ↦ Real.log (Metric.infDist x Γ)))
    (hboundary : LocallyIntegrable (fun x : ℝ ↦ Real.log ‖G x‖))
    (hshift : MemBMO (fun x : ℝ ↦ Real.log ‖G ((x:ℂ)+(ε:ℂ)*I)‖))
    (hcmp : ∀ k x, x ∈ cell g k → x ≠ g.point k →
      |Real.log ‖G x‖ - Real.log ‖G ((x:ℂ)+(ε:ℂ)*I)‖ -
        Real.log (abs (x-g.point k))| ≤ C) :
    MemBMO (fun x : ℝ ↦ Real.log ‖G x‖) := by sorry

theorem locallyIntegrable_boundary_log_of_entire {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) : LocallyIntegrable (fun x : ℝ ↦ Real.log ‖G x‖) := by sorry

end FF.Pavlov
```

## LogDistance.lean

Source: [LogDistance.lean](../FourierFrames/Cited/Pavlov/LogDistance.lean).

Detailed proof: [P5_LogDistance](P5_LogDistance.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.LogDistanceCore
import FourierFrames.Cited.Pavlov.LogSingularity
import FourierFrames.Cited.Pavlov.LogDistanceLarge
import FourierFrames.Cited.Pavlov.LogDistanceTransfer
```

Opening commands:

```lean
open MeasureTheory Metric Set Filter Topology Complex
```

Public interface:

```lean
namespace FF.Pavlov

variable {Γ : Set ℝ}

theorem Grid.meanOsc_log_infDist_le_of_near (g : Grid Γ) {a b : ℝ}
    (hab : a < b) (hsmall : b-a < g.lower/8)
    (hnear : Metric.infDist a Γ < 2*(b-a)) :
    meanOsc (fun x ↦ Real.log (Metric.infDist x Γ)) a b ≤ 2*logSingularityBound := by sorry

theorem Grid.memBMO_log_infDist (g : Grid Γ) :
    MemBMO (fun x ↦ Real.log (Metric.infDist x Γ)) := by sorry

theorem memBMO_boundary_log_of_cell_comparison
    (g : Grid Γ) (G : ℂ → ℂ) (ε C : ℝ)
    (hboundary : LocallyIntegrable (fun x : ℝ ↦ Real.log ‖G x‖))
    (hshift : MemBMO (fun x : ℝ ↦ Real.log ‖G ((x:ℂ)+(ε:ℂ)*I)‖))
    (hcmp : ∀ k x, x ∈ cell g k → x ≠ g.point k →
      |Real.log ‖G x‖ - Real.log ‖G ((x:ℂ)+(ε:ℂ)*I)‖ -
        Real.log (abs (x-g.point k))| ≤ C) :
    MemBMO (fun x : ℝ ↦ Real.log ‖G x‖) := by sorry

theorem exists_boundary_log_BMO_transfer (g : Grid Γ) (d : CardinalData Γ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < g.lower/8 ∧
      (MemBMO (fun x : ℝ ↦ Real.log ‖d.G ((x:ℂ)+(ε:ℂ)*I)‖) →
        MemBMO (fun x : ℝ ↦ Real.log ‖d.G x‖)) := by sorry

end FF.Pavlov
```

## BoundaryWeight.lean

Source: [BoundaryWeight.lean](../FourierFrames/Cited/Pavlov/BoundaryWeight.lean).

Detailed proof: [P5_A2](P5_A2.md), [P5_LogDistance](P5_LogDistance.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.WeightTransfer
import FourierFrames.Cited.Pavlov.LogDistance
```

Opening commands:

```lean
open MeasureTheory Metric Set Complex
```

Public interface:

```lean
namespace FF.Pavlov

theorem CardinalData.boundary_log_bmo {Γ : Set ℝ} (d : CardinalData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) :
    MemBMO (fun x : ℝ ↦ Real.log ‖d.G (x : ℂ)‖) := by sorry

end FF.Pavlov
```

## Schwarz.lean

Source: [Schwarz.lean](../FourierFrames/Cited/Pavlov/Schwarz.lean).

Detailed proof: [P5_Dispersion](P5_Dispersion.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.Basic
import FourierFrames.Cited.DeBrangesF.Herglotz
```

Opening commands:

```lean
open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate
```

Public interface:

```lean
namespace FF.Pavlov

theorem LogIntegrable.aestronglyMeasurable {u : ℝ → ℝ} (hu : LogIntegrable u) :
    AEStronglyMeasurable u volume := by sorry

theorem LogIntegrable.abs_weight {u : ℝ → ℝ} (hu : LogIntegrable u) :
    Integrable (fun t ↦ |u t| / (1 + t ^ 2)) volume := by sorry

theorem schwarzKernel_integrable {u : ℝ → ℝ} (hu : LogIntegrable u)
    {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ ↦ Herglotz.kernel t z * (u t : ℂ)) := by sorry

theorem schwarzIntegral_differentiableAt {u : ℝ → ℝ} (hu : LogIntegrable u)
    {z : ℂ} (hz : 0 < z.im) : DifferentiableAt ℂ (schwarzIntegral u) z := by sorry

theorem differentiableOn_schwarzIntegral {u : ℝ → ℝ} (hu : LogIntegrable u) :
    DifferentiableOn ℂ (schwarzIntegral u) UHP := by sorry

theorem schwarzIntegral_re {u : ℝ → ℝ} (hu : LogIntegrable u)
    {z : ℂ} (hz : 0 < z.im) :
    (schwarzIntegral u z).re =
      ∫ t : ℝ, z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2)) * u t := by sorry

theorem schwarzIntegral_im {u : ℝ → ℝ} (hu : LogIntegrable u)
    {x y : ℝ} (hy : 0 < y) :
    (schwarzIntegral u ((x : ℂ) + (y : ℂ) * I)).im = conjugatePoisson u y x := by sorry

theorem poissonKernel_mul_integrable {u : ℝ → ℝ} (hu : LogIntegrable u)
    {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ ↦ z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2)) * u t) := by sorry

theorem conjugatePoisson_integrand_eq_neg_re (u : ℝ → ℝ) (y x t : ℝ) :
    ((x - t) / ((x - t) ^ 2 + y ^ 2) + t / (1 + t ^ 2)) * u t =
      -(Herglotz.kernel t ((x : ℂ) + (y : ℂ) * I) * (u t : ℂ)).re := by sorry

theorem conjugatePoisson_integrand_integrable {u : ℝ → ℝ} (hu : LogIntegrable u)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Integrable (fun t : ℝ ↦
      ((x - t) / ((x - t) ^ 2 + y ^ 2) + t / (1 + t ^ 2)) * u t) := by sorry

theorem logIntegrable_const (c : ℝ) : LogIntegrable (fun _ ↦ c) := by sorry

theorem LogIntegrable.sub_const {u : ℝ → ℝ} (hu : LogIntegrable u) (c : ℝ) :
    LogIntegrable (fun t ↦ u t - c) := by sorry

theorem schwarzIntegral_im_I {u : ℝ → ℝ} (hu : LogIntegrable u) :
    (schwarzIntegral u I).im = 0 := by sorry

theorem schwarzIntegral_re_const (c : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (schwarzIntegral (fun _ ↦ c) z).re = c := by sorry

theorem schwarzIntegral_const (c : ℝ) {z : ℂ} (hz : 0 < z.im) :
    schwarzIntegral (fun _ ↦ c) z = (c : ℂ) := by sorry

theorem conjugatePoisson_const (c : ℝ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    conjugatePoisson (fun _ ↦ c) y x = 0 := by sorry

theorem LogIntegrable.sub {u v : ℝ → ℝ} (hu : LogIntegrable u) (hv : LogIntegrable v) :
    LogIntegrable (fun t ↦ u t - v t) := by sorry

theorem LogIntegrable.const_mul {u : ℝ → ℝ} (hu : LogIntegrable u) (c : ℝ) :
    LogIntegrable (fun t ↦ c * u t) := by sorry

theorem LogIntegrable.congr {u v : ℝ → ℝ} (hu : LogIntegrable u) (h : u =ᵐ[volume] v) :
    LogIntegrable v := by sorry

theorem schwarzIntegral_congr_ae {u v : ℝ → ℝ} (h : u =ᵐ[volume] v) (z : ℂ) :
    schwarzIntegral u z = schwarzIntegral v z := by sorry

theorem schwarzIntegral_sub {u v : ℝ → ℝ} (hu : LogIntegrable u) (hv : LogIntegrable v)
    {z : ℂ} (hz : 0 < z.im) :
    schwarzIntegral (fun t ↦ u t - v t) z = schwarzIntegral u z - schwarzIntegral v z := by sorry

theorem schwarzIntegral_const_mul (u : ℝ → ℝ) (c : ℝ) (z : ℂ) :
    schwarzIntegral (fun t ↦ c * u t) z = (c : ℂ) * schwarzIntegral u z := by sorry

theorem conjugatePoisson_sub_const {u : ℝ → ℝ} (hu : LogIntegrable u) (c : ℝ)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    conjugatePoisson (fun t ↦ u t - c) y x = conjugatePoisson u y x := by sorry

theorem continuous_conjugatePoisson {u : ℝ → ℝ} (hu : LogIntegrable u)
    {y : ℝ} (hy : 0 < y) : Continuous (conjugatePoisson u y) := by sorry

end FF.Pavlov
```

## LogPoissonKernel.lean

Source: [LogPoissonKernel.lean](../FourierFrames/Cited/Pavlov/LogPoissonKernel.lean).

Detailed proof: [P5_LogPoissonKernel](P5_LogPoissonKernel.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.Schwarz
```

Opening commands:

```lean
open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal
```

Public interface:

```lean
namespace FF.Pavlov

theorem integrable_poisson_log_abs_sub (a x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (fun t : ℝ ↦ y / (Real.pi * ((t-x)^2+y^2)) * Real.log |t-a|) := by sorry

theorem poissonIntegral_log_abs_sub (a x : ℝ) {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ, y / (Real.pi * ((t-x)^2+y^2)) * Real.log |t-a|) =
      Real.log ‖((x-a : ℝ) : ℂ) + (y : ℂ)*I‖ := by sorry

theorem logIntegrable_log_abs_sub (a : ℝ) :
    LogIntegrable (fun t ↦ Real.log |t-a|) := by sorry

theorem schwarzIntegral_re_log_abs_sub (a : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (schwarzIntegral (fun t ↦ Real.log |t-a|) z).re = Real.log ‖z-(a:ℂ)‖ := by sorry

end FF.Pavlov
```

## CardinalLog.lean

Source: [CardinalLog.lean](../FourierFrames/Cited/Pavlov/CardinalLog.lean).

Detailed proof: [P5_CardinalLog](P5_CardinalLog.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.BoundaryWeight
import FourierFrames.Cited.Pavlov.BMOLogIntegrable
import FourierFrames.Cited.Pavlov.LogPoissonKernel
```

Opening commands:

```lean
open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate
```

Public interface:

```lean
namespace FF.Pavlov

variable {Γ : Set ℝ}

def cardinalUpper (d : CardinalData Γ) (γ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (I*(Real.pi : ℂ)*z) * cardinal d.G γ z

def cardinalLog (d : CardinalData Γ) (γ : ℝ) (t : ℝ) : ℝ :=
  Real.log ‖cardinal d.G γ (t : ℂ)‖

theorem GeneratingData.deriv_real (d : GeneratingData Γ) (γ : ℝ) :
    conj (deriv d.G (γ : ℂ)) = deriv d.G (γ : ℂ) := by sorry

theorem GeneratingData.cardinal_real (d : GeneratingData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    fstar (cardinal d.G γ) = cardinal d.G γ := by sorry

theorem cardinalUpper_entire (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    Differentiable ℂ (cardinalUpper d γ) := by sorry

theorem cardinalUpper_ne_zero (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    ∀ z ∈ UHP, cardinalUpper d γ z ≠ 0 := by sorry

theorem cardinalUpper_bounded (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ UHP, ‖cardinalUpper d γ z‖ ≤ M := by sorry

theorem cardinal_ne_zero_upper (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ)
    {z : ℂ} (hz : z ∈ UHP) : cardinal d.G γ z ≠ 0 := by sorry

theorem log_generating_eq_cardinal_upper (d : CardinalData Γ) {γ : ℝ}
    (hγ : γ ∈ Γ) {z : ℂ} (hz : z ∈ UHP) :
    Real.log ‖d.G z‖ = Real.log ‖cardinal d.G γ z‖ + Real.log ‖z-(γ : ℂ)‖ +
      Real.log ‖deriv d.G (γ : ℂ)‖ := by sorry

theorem log_cardinalUpper_eq (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ)
    {z : ℂ} (hz : z ∈ UHP) :
    Real.log ‖cardinalUpper d γ z‖ = -Real.pi*z.im + Real.log ‖cardinal d.G γ z‖ := by sorry

theorem cardinalUpper_boundary_norm (d : CardinalData Γ) (γ t : ℝ) :
    ‖cardinalUpper d γ (t : ℂ)‖ = ‖cardinal d.G γ (t : ℂ)‖ := by sorry

theorem cardinalLog_eq_of_not_mem (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ)
    {t : ℝ} (ht : t ∉ Γ) :
    cardinalLog d γ t = Real.log ‖d.G (t : ℂ)‖ -
      Real.log |t-γ| - Real.log ‖deriv d.G (γ : ℂ)‖ := by sorry

theorem cardinalLog_eq_ae (d : CardinalData Γ) (g : Grid Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    cardinalLog d γ =ᵐ[volume] (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖ -
      Real.log |t-γ| - Real.log ‖deriv d.G (γ : ℂ)‖) := by sorry

theorem log_generating_eq_cardinalLog_of_not_mem (d : CardinalData Γ) {γ : ℝ}
    (hγ : γ ∈ Γ) {t : ℝ} (ht : t ∉ Γ) :
    Real.log ‖d.G (t : ℂ)‖ = cardinalLog d γ t + Real.log |t-γ| +
      Real.log ‖deriv d.G (γ : ℂ)‖ := by sorry

theorem log_generating_eq_cardinalLog_ae (d : CardinalData Γ) (g : Grid Γ)
    {γ : ℝ} (hγ : γ ∈ Γ) :
    (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖) =ᵐ[volume]
      (fun t ↦ cardinalLog d γ t + Real.log |t-γ| + Real.log ‖deriv d.G (γ : ℂ)‖) := by sorry

theorem cardinalLog_logIntegrable (d : CardinalData Γ) (g : Grid Γ) (hΓ : IsSeparated Γ)
    {γ : ℝ} (hγ : γ ∈ Γ) : LogIntegrable (cardinalLog d γ) := by sorry

theorem exp_two_cardinalLog_eq_ae (d : CardinalData Γ) (g : Grid Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    (fun t : ℝ ↦ Real.exp (2*cardinalLog d γ t)) =ᵐ[volume]
      (fun t : ℝ ↦ ‖cardinal d.G γ (t : ℂ)‖^2) := by sorry

theorem integrable_exp_two_cardinalLog (d : CardinalData Γ) (g : Grid Γ)
    {γ : ℝ} (hγ : γ ∈ Γ) : Integrable (fun t : ℝ ↦ Real.exp (2*cardinalLog d γ t)) := by sorry

theorem CardinalData.log_generating_logIntegrable (d : CardinalData Γ) (g : Grid Γ)
    (hΓ : IsSeparated Γ) : LogIntegrable (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖) := by sorry

theorem cardinalUpper_logIntegrable (d : CardinalData Γ) (g : Grid Γ)
    (hΓ : IsSeparated Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    LogIntegrable (fun t : ℝ ↦ Real.log ‖cardinalUpper d γ (t : ℂ)‖) := by sorry

structure CardinalLogInput (d : CardinalData Γ) (γ : ℝ) : Prop where
  memPW : MemPW (cardinal d.G γ)
  real : fstar (cardinal d.G γ) = cardinal d.G γ
  at_node : cardinal d.G γ (γ : ℂ) = 1
  zeros : ∀ z : ℂ, cardinal d.G γ z = 0 ↔ ∃ t ∈ Γ, t ≠ γ ∧ z = (t : ℂ)
  upper_entire : Differentiable ℂ (cardinalUpper d γ)
  upper_ne_zero : ∀ z ∈ UHP, cardinalUpper d γ z ≠ 0
  upper_bounded : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ UHP, ‖cardinalUpper d γ z‖ ≤ M
  boundary_norm : ∀ t : ℝ, ‖cardinalUpper d γ (t : ℂ)‖ = ‖cardinal d.G γ (t : ℂ)‖
  log_G_integrable : LogIntegrable (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖)
  log_q_integrable : LogIntegrable (cardinalLog d γ)
  log_upper_integrable : LogIntegrable (fun t : ℝ ↦ Real.log ‖cardinalUpper d γ (t : ℂ)‖)
  exp_sq_integrable : Integrable (fun t : ℝ ↦ Real.exp (2*cardinalLog d γ t))
  log_identity : (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖) =ᵐ[volume]
    (fun t ↦ cardinalLog d γ t + Real.log |t-γ| + Real.log ‖deriv d.G (γ : ℂ)‖)

theorem CardinalData.cardinal_log_input (d : CardinalData Γ) (g : Grid Γ)
    (hΓ : IsSeparated Γ) {γ : ℝ} (hγ : γ ∈ Γ) : CardinalLogInput d γ where
  memPW := by sorry

end FF.Pavlov
```

## ConjugatePoisson.lean

Source: [ConjugatePoisson.lean](../FourierFrames/Cited/Pavlov/ConjugatePoisson.lean).

Detailed proof: [P5_HilbertL2](P5_HilbertL2.md).

Direct imports:

```lean
import FourierFrames.Cited.PaleyWiener.L2Fourier
import TauCeti.Analysis.Fourier.L2Multiplier
```

Opening commands:

```lean
open MeasureTheory Set Complex Filter Topology FourierTransform ContinuousLinearMap
open scoped ENNReal NNReal FourierTransform ComplexConjugate SchwartzMap
```

Public interface:

```lean
namespace FF.Pavlov

abbrev C2 := Lp ℂ 2 (volume : Measure ℝ)

def conjugatePoissonKernel (y t : ℝ) : ℝ :=
  t / (Real.pi * (t ^ 2 + y ^ 2))

def conjugatePoissonSymbol (y ξ : ℝ) : ℂ :=
  if ξ < 0 then Complex.I * (Real.exp (-(2 * Real.pi * y * |ξ|)) : ℂ)
  else if 0 < ξ then -Complex.I * (Real.exp (-(2 * Real.pi * y * |ξ|)) : ℂ)
  else 0

lemma conjugatePoissonSymbol_eq (y ξ : ℝ) :
    conjugatePoissonSymbol y ξ = -I * (Real.sign ξ : ℂ) *
      (Real.exp (-(2 * Real.pi * y * |ξ|)) : ℂ) := by sorry

lemma conjugatePoissonSymbol_measurable (y : ℝ) :
    Measurable (conjugatePoissonSymbol y) := by sorry

lemma conjugatePoissonSymbol_norm_le_exp (y ξ : ℝ) :
    ‖conjugatePoissonSymbol y ξ‖ ≤ Real.exp (-(2 * Real.pi * y * |ξ|)) := by sorry

lemma conjugatePoissonSymbol_norm_le {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    ‖conjugatePoissonSymbol y ξ‖ ≤ 1 := by sorry

lemma conjugatePoissonSymbol_integrable {y : ℝ} (hy : 0 < y) :
    Integrable (conjugatePoissonSymbol y) := by sorry

lemma conjugatePoissonSymbol_memLp_two {y : ℝ} (hy : 0 < y) :
    MemLp (conjugatePoissonSymbol y) 2 volume := by sorry

lemma conjugatePoissonSymbol_memLp_top {y : ℝ} (hy : 0 < y) :
    MemLp (conjugatePoissonSymbol y) ∞ volume := by sorry

def conjugatePoissonOperator (y : ℝ) (hy : 0 < y) : C2 →L[ℂ] C2 :=
  MeasureTheory.Lp.fourierMultiplierCLM ℂ
    ((conjugatePoissonSymbol_memLp_top hy).toLp (conjugatePoissonSymbol y))

lemma norm_conjugatePoissonOperator_le {y : ℝ} (hy : 0 < y) :
    ‖conjugatePoissonOperator y hy‖ ≤ 1 := by sorry

lemma norm_conjugatePoissonOperator_apply_le {y : ℝ} (hy : 0 < y) (f : C2) :
    ‖conjugatePoissonOperator y hy f‖ ≤ ‖f‖ := by sorry

lemma fourierInv_conjugatePoissonSymbol {y : ℝ} (hy : 0 < y) (x : ℝ) :
    𝓕⁻ (conjugatePoissonSymbol y) x = (conjugatePoissonKernel y x : ℂ) := by sorry

lemma conjugatePoissonKernel_memLp_two {y : ℝ} (hy : 0 < y) :
    MemLp (fun t ↦ (conjugatePoissonKernel y t : ℂ)) 2 volume := by sorry

lemma conjugatePoissonKernel_mul_integrable {y : ℝ} (hy : 0 < y)
    (f : C2) (x : ℝ) :
    Integrable (fun t ↦ (conjugatePoissonKernel y (x-t) : ℂ) * f t) := by sorry

lemma conjugatePoissonOperator_eq_integral_of_integrable {y : ℝ} (hy : 0 < y)
    (f : C2) (hf : Integrable (f : ℝ → ℂ)) :
    (conjugatePoissonOperator y hy f : ℝ → ℂ) =ᵐ[volume]
      fun x ↦ ∫ t, (conjugatePoissonKernel y (x-t) : ℂ) * f t := by sorry

lemma conjugatePoissonOperator_eq_integral {y : ℝ} (hy : 0 < y) (f : C2) :
    (conjugatePoissonOperator y hy f : ℝ → ℂ) =ᵐ[volume]
      fun x ↦ ∫ t, (conjugatePoissonKernel y (x-t) : ℂ) * f t := by sorry

end FF.Pavlov
```

## PoissonBMOKernel.lean

Source: [PoissonBMOKernel.lean](../FourierFrames/Cited/Pavlov/PoissonBMOKernel.lean).

Detailed proof: [P5_PoissonBMO](P5_PoissonBMO.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.Basic
```

Opening commands:

```lean

```

Public interface:

```lean
namespace FF.Pavlov

theorem poisson_square_denominator_pos {y t : ℝ} (hy : 0 < y) :
    0 < t ^ 2 + y ^ 2 := by sorry

theorem conjugatePoissonFraction_sub {y a b : ℝ} (hy : 0 < y) :
    a / (a ^ 2 + y ^ 2) - b / (b ^ 2 + y ^ 2) =
      (a-b) * (y ^ 2-a*b) / ((a ^ 2+y ^ 2)*(b ^ 2+y ^ 2)) := by sorry

theorem abs_conjugatePoissonFraction_sub_le {y a b : ℝ}
    (hy : 0 < y) (ha : a ≠ 0) (hb : b ≠ 0) :
    |a / (a ^ 2 + y ^ 2) - b / (b ^ 2 + y ^ 2)| ≤
      |a-b| / (|a| *|b|) := by sorry

theorem abs_conjugatePoissonFraction_shift_sub_le {y s h : ℝ}
    (hy : 0 < y) (hs : s ≠ 0) (hsep : 2 * |h| ≤ |s|) :
    |(s+h) / ((s+h)^2+y^2) - s / (s^2+y^2)| ≤ 2 * |h| / s^2 := by sorry

theorem abs_conjugatePoissonKernel_shift_sub_le {y s h : ℝ}
    (hy : 0 < y) (hs : s ≠ 0) (hsep : 2 * |h| ≤ |s|) :
    |(s+h) / (Real.pi * ((s+h)^2+y^2)) - s / (Real.pi * (s^2+y^2))| ≤
      2 * |h| / (Real.pi * s^2) := by sorry

end FF.Pavlov
```

## PoissonBMOFar.lean

Source: [PoissonBMOFar.lean](../FourierFrames/Cited/Pavlov/PoissonBMOFar.lean).

Detailed proof: [P5_PoissonBMO](P5_PoissonBMO.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.BMOIntervalGrowth
import FourierFrames.Cited.Pavlov.PoissonBMOKernel
```

Opening commands:

```lean
open MeasureTheory Set Filter
```

Public interface:

```lean
namespace FF.Pavlov

def bmoCenteredShell (c r : ℝ) (k : ℕ) : Set ℝ :=
  {t | (2:ℝ)^(k+1)*r ≤ |t-c| ∧ |t-c| ≤ (2:ℝ)^(k+2)*r}

lemma bmoCenteredShell_measurable (c r : ℝ) (k : ℕ) :
    MeasurableSet (bmoCenteredShell c r k) := by sorry

lemma bmoCenteredShell_subset (c r : ℝ) (k : ℕ) :
    bmoCenteredShell c r k ⊆ Icc (c-(2:ℝ)^(k+2)*r) (c+(2:ℝ)^(k+2)*r) := by sorry

def conjugatePoissonFarFraction (y x c t : ℝ) : ℝ :=
  (x-t)/((x-t)^2+y^2) - (c-t)/((c-t)^2+y^2)

lemma continuous_conjugatePoissonFarFraction {y : ℝ} (hy : 0 < y) (x c : ℝ) :
    Continuous (conjugatePoissonFarFraction y x c) := by sorry

lemma abs_conjugatePoissonFarFraction_shell_le {y x c r : ℝ}
    (hy : 0 < y) (hr : 0 < r) (hx : |x-c| ≤ r) {k : ℕ} {t : ℝ}
    (ht : t ∈ bmoCenteredShell c r k) :
    |conjugatePoissonFarFraction y x c t| ≤
      2*r / (((2:ℝ)^(k+1)*r)^2) := by sorry

theorem integral_conjugatePoissonFarFraction_shell_le {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {M y x c r : ℝ}
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M)
    (hy : 0 < y) (hr : 0 < r) (hx : |x-c| ≤ r) (k : ℕ) :
    (∫ t in bmoCenteredShell c r k,
      |conjugatePoissonFarFraction y x c t *
        (u t-intervalMean u (c-2*r) (c+2*r))|) ≤
      4*((1:ℝ)/2)^k*(3+2*(k:ℝ))*M := by sorry

lemma hasSum_bmoFarBound (M : ℝ) :
    HasSum (fun k : ℕ ↦ 4*((1:ℝ)/2)^k*(3+2*(k:ℝ))*M) (40*M) := by sorry

theorem integrableOn_and_integral_abs_le_of_cover {f : ℝ → ℝ} {s : ℕ → Set ℝ}
    {A : Set ℝ} {B : ℕ → ℝ} (hi : ∀ k, IntegrableOn f (s k))
    (hB : ∀ k, 0 ≤ B k) (hsum : Summable B)
    (hbound : ∀ k, (∫ t in s k, |f t|) ≤ B k) (hcover : A ⊆ ⋃ k, s k) :
    IntegrableOn f A ∧ (∫ t in A, |f t|) ≤ ∑' k, B k := by sorry

lemma bmoCenteredShell_cover {c r : ℝ} (hr : 0 < r) :
    (Icc (c-2*r) (c+2*r))ᶜ ⊆ ⋃ k, bmoCenteredShell c r k := by sorry

theorem conjugatePoissonFarFraction_integrable_bound {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {M y x c r : ℝ} (hM : 0 ≤ M)
    (hosc : ∀ a b : ℝ, a < b → meanOsc u a b ≤ M)
    (hy : 0 < y) (hr : 0 < r) (hx : |x-c| ≤ r) :
    IntegrableOn (fun t ↦ conjugatePoissonFarFraction y x c t *
      (u t-intervalMean u (c-2*r) (c+2*r))) (Icc (c-2*r) (c+2*r))ᶜ ∧
    (∫ t in (Icc (c-2*r) (c+2*r))ᶜ,
      |conjugatePoissonFarFraction y x c t *
        (u t-intervalMean u (c-2*r) (c+2*r))|) ≤ 40*M := by sorry

end FF.Pavlov
```

## PoissonBMONear.lean

Source: [PoissonBMONear.lean](../FourierFrames/Cited/Pavlov/PoissonBMONear.lean).

Detailed proof: [P5_PoissonBMO](P5_PoissonBMO.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.BMOSecondMoment
import FourierFrames.Cited.Pavlov.ConjugatePoisson
```

Opening commands:

```lean
open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace
```

Public interface:

```lean
namespace FF.Pavlov

def centeredCutoff (u : ℝ → ℝ) (a b : ℝ) : ℝ → ℂ :=
  (Icc a b).indicator (fun t ↦ ((u t-intervalMean u a b : ℝ) : ℂ))

theorem centeredCutoff_memLp_two {u : ℝ → ℝ} (hu : LocallyIntegrable u)
    {a b : ℝ} (hs : IntegrableOn (fun t ↦ (u t-intervalMean u a b)^2) (Icc a b)) :
    MemLp (centeredCutoff u a b) 2 volume := by sorry

theorem c2_norm_sq_eq_integral (f : C2) : ‖f‖^2 = ∫ t : ℝ, ‖f t‖^2 := by sorry

theorem exists_centeredCutoff_L2 {u : ℝ → ℝ} (hu : LocallyIntegrable u)
    {a b : ℝ} (hab : a < b)
    (hs : IntegrableOn (fun t ↦ (u t-intervalMean u a b)^2) (Icc a b)) :
    ∃ f : C2, (f : ℝ → ℂ) =ᵐ[volume] centeredCutoff u a b ∧
      ‖f‖^2 = ∫ t in a..b, (u t-intervalMean u a b)^2 := by sorry

theorem integral_norm_C2_le (f : C2) {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, ‖f t‖) ≤ Real.sqrt (b-a) * ‖f‖ := by sorry

def nearConjugatePoisson (u : ℝ → ℝ) (y c r x : ℝ) : ℝ :=
  ∫ t in Icc (c-2*r) (c+2*r),
    conjugatePoissonKernel y (x-t) * (u t-intervalMean u (c-2*r) (c+2*r))

theorem nearConjugatePoisson_fraction_integrable {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) {y : ℝ} (hy : 0 < y) (c r x : ℝ) :
    IntegrableOn (fun t ↦ ((x-t)/((x-t)^2+y^2)) *
      (u t-intervalMean u (c-2*r) (c+2*r))) (Icc (c-2*r) (c+2*r)) := by sorry

theorem nearConjugatePoisson_eq_fraction (u : ℝ → ℝ) (y c r x : ℝ) :
    nearConjugatePoisson u y c r x = Real.pi⁻¹ *
      ∫ t in Icc (c-2*r) (c+2*r), ((x-t)/((x-t)^2+y^2)) *
        (u t-intervalMean u (c-2*r) (c+2*r)) := by sorry

theorem conjugatePoisson_centeredCutoff_eq {u : ℝ → ℝ} {c r y : ℝ}
    (hy : 0 < y) (f : C2)
    (hf : (f : ℝ → ℂ) =ᵐ[volume] centeredCutoff u (c-2*r) (c+2*r)) :
    (conjugatePoissonOperator y hy f : ℝ → ℂ) =ᵐ[volume]
      (fun x ↦ (nearConjugatePoisson u y c r x : ℂ)) := by sorry

theorem nearConjugatePoisson_bound {u : ℝ → ℝ} (hu : LocallyIntegrable u)
    {C M c r y : ℝ} (hC : 0 < C) (hM : 0 < M) (hr : 0 < r) (hy : 0 < y)
    (hs : IntegrableOn
      (fun t ↦ (u t-intervalMean u (c-2*r) (c+2*r))^2)
      (Icc (c-2*r) (c+2*r)))
    (hb : (∫ t in (c-2*r)..(c+2*r),
      (u t-intervalMean u (c-2*r) (c+2*r))^2) ≤ C*M^2*(4*r)) :
    IntegrableOn (nearConjugatePoisson u y c r) (Icc (c-r) (c+r)) ∧
      (2*r)⁻¹ * ∫ x in (c-r)..(c+r), |nearConjugatePoisson u y c r x| ≤
        Real.sqrt (2*C)*M := by sorry

theorem bmo_near_conjugatePoisson_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ), LocallyIntegrable u →
      ∀ M : ℝ, 0 < M →
      (∀ a b : ℝ, a < b → meanOsc u a b ≤ M) →
      ∀ y : ℝ, 0 < y → ∀ c r : ℝ, 0 < r →
        IntegrableOn (nearConjugatePoisson u y c r) (Icc (c-r) (c+r)) ∧
        (2*r)⁻¹ * ∫ x in (c-r)..(c+r), |nearConjugatePoisson u y c r x| ≤ C*M := by sorry

end FF.Pavlov
```

## PoissonBMO.lean

Source: [PoissonBMO.lean](../FourierFrames/Cited/Pavlov/PoissonBMO.lean).

Detailed proof: [P5_PoissonBMO](P5_PoissonBMO.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.BMO
import FourierFrames.Cited.Pavlov.BMOLogIntegrable
import FourierFrames.Cited.Pavlov.PoissonBMOFar
import FourierFrames.Cited.Pavlov.Schwarz
import FourierFrames.Cited.Pavlov.PoissonBMONear
```

Opening commands:

```lean
open MeasureTheory Set Filter Topology
```

Public interface:

```lean
namespace FF.Pavlov

theorem conjugatePoisson_difference_integrable {u : ℝ → ℝ} {y x c : ℝ}
    (hx : Integrable (fun t ↦ ((x-t)/((x-t)^2+y^2)+t/(1+t^2))*u t))
    (hc : Integrable (fun t ↦ ((c-t)/((c-t)^2+y^2)+t/(1+t^2))*u t)) :
    Integrable (fun t ↦ conjugatePoissonFarFraction y x c t*u t) := by sorry

theorem conjugatePoisson_sub_eq_integral {u : ℝ → ℝ} {y x c : ℝ}
    (hx : Integrable (fun t ↦ ((x-t)/((x-t)^2+y^2)+t/(1+t^2))*u t))
    (hc : Integrable (fun t ↦ ((c-t)/((c-t)^2+y^2)+t/(1+t^2))*u t)) :
    conjugatePoisson u y x-conjugatePoisson u y c =
      Real.pi⁻¹ * ∫ t, conjugatePoissonFarFraction y x c t*u t := by sorry

theorem conjugatePoisson_sub_eq_near_add_far {u : ℝ → ℝ} {y x c : ℝ} {J : Set ℝ}
    (hJ : MeasurableSet J)
    (hx : Integrable (fun t ↦ ((x-t)/((x-t)^2+y^2)+t/(1+t^2))*u t))
    (hc : Integrable (fun t ↦ ((c-t)/((c-t)^2+y^2)+t/(1+t^2))*u t)) :
    conjugatePoisson u y x-conjugatePoisson u y c =
      Real.pi⁻¹ * (∫ t in J, conjugatePoissonFarFraction y x c t*u t) +
      Real.pi⁻¹ * (∫ t in Jᶜ, conjugatePoissonFarFraction y x c t*u t) := by sorry

theorem meanOsc_le_of_near_and_bounded {f n : ℝ → ℝ}
    (hf : LocallyIntegrable f) {a b : ℝ} (hn : IntervalIntegrable n volume a b)
    (hab : a < b) {c A B : ℝ}
    (hcmp : ∀ x ∈ Icc a b, |f x-c| ≤ |n x|+B)
    (hnear : (∫ x in a..b, |n x|) ≤ A*(b-a)) :
    meanOsc f a b ≤ 2*(A+B) := by sorry

theorem conjugatePoisson_eq_near_add_far {u : ℝ → ℝ}
    (hu : LocallyIntegrable u) (hlog : LogIntegrable u) {y : ℝ} (hy : 0 < y)
    (c r x : ℝ) :
    conjugatePoisson u y x -
      (conjugatePoisson (fun t ↦ u t-intervalMean u (c-2*r) (c+2*r)) y c -
        nearConjugatePoisson u y c r c) =
      nearConjugatePoisson u y c r x + Real.pi⁻¹ *
        ∫ t in (Icc (c-2*r) (c+2*r))ᶜ, conjugatePoissonFarFraction y x c t *
          (u t-intervalMean u (c-2*r) (c+2*r)) := by sorry

theorem meanOsc_conjugatePoisson_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ), LocallyIntegrable u →
      ∀ M : ℝ, 0 < M →
      (∀ a b : ℝ, a < b → meanOsc u a b ≤ M) →
      ∀ y : ℝ, 0 < y → ∀ a b : ℝ, a < b →
        meanOsc (conjugatePoisson u y) a b ≤ C*M := by sorry

theorem conjugatePoisson_uniform_bmo {u : ℝ → ℝ} (hu : FF.MemBMO u) :
    ∃ M : ℝ, 0 < M ∧ ∀ y : ℝ, 0 < y →
      LocallyIntegrable (conjugatePoisson u y) ∧
      ∀ a b : ℝ, a < b → meanOsc (conjugatePoisson u y) a b ≤ M := by sorry

theorem memBMO_conjugatePoisson {u : ℝ → ℝ} (hu : FF.MemBMO u)
    {y : ℝ} (hy : 0 < y) : FF.MemBMO (conjugatePoisson u y) := by sorry

theorem memBMO_of_conjugatePoisson_ae_limit {u g : ℝ → ℝ} (hu : FF.MemBMO u)
    (hg : LocallyIntegrable g) {y : ℕ → ℝ} (hy : ∀ n, 0 < y n)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ conjugatePoisson u (y n) t) atTop (𝓝 (g t))) :
    FF.MemBMO g := by sorry

end FF.Pavlov
```

## CountingBMO.lean

Source: [CountingBMO.lean](../FourierFrames/Cited/Pavlov/CountingBMO.lean).

Detailed proof: [P5_CountingBMO](P5_CountingBMO.md).

Direct imports:

```lean
import FourierFrames.Landau
import FourierFrames.Cited.Pavlov.PoissonBMO
```

Opening commands:

```lean
open MeasureTheory Set Filter Topology
```

Public interface:

```lean
namespace FF.Pavlov

theorem countFn_monotone {Γ : Set ℝ} (hΓ : IsSeparated Γ) : Monotone (countFn Γ) := by sorry

theorem locallyIntegrable_countFn {Γ : Set ℝ} (hΓ : IsSeparated Γ) :
    LocallyIntegrable (countFn Γ) := by sorry

theorem locallyIntegrable_countFn_sub_id {Γ : Set ℝ} (hΓ : IsSeparated Γ) :
    LocallyIntegrable (fun x ↦ countFn Γ x-x) := by sorry

theorem memBMO_countFn_sub_id_of_conjugatePoisson_limit {Γ : Set ℝ}
    (hΓ : IsSeparated Γ) {u : ℝ → ℝ} (hu : MemBMO u) (c : ℝ)
    {y : ℕ → ℝ} (hy : ∀ n, 0 < y n)
    (hlim : ∀ᵐ x : ℝ, Tendsto (fun n ↦ conjugatePoisson u (y n) x) atTop
      (𝓝 (-Real.pi*(countFn Γ x-x)+c))) :
    MemBMO (fun x ↦ countFn Γ x-x) := by sorry

end FF.Pavlov
```

## SchwarzBoundary.lean

Source: [SchwarzBoundary.lean](../FourierFrames/Cited/Pavlov/SchwarzBoundary.lean).

Detailed proof: [P5_SchwarzBoundary](P5_SchwarzBoundary.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.Schwarz
import FourierFrames.Cited.DeBrangesDE.Cauchy
```

Opening commands:

```lean
open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate
```

Public interface:

```lean
namespace FF.Pavlov

theorem tendsto_schwarzIntegral_re_boundary {u : ℝ → ℝ} (hu : LogIntegrable u)
    {x : ℝ} (hc : ContinuousAt u x) :
    Tendsto (fun z ↦ (schwarzIntegral u z).re) (𝓝[FF.UHP] (x : ℂ)) (𝓝 (u x)) := by sorry

def poissonExtension (u : ℝ → ℝ) (z : ℂ) : ℝ :=
  if 0 < z.im then (schwarzIntegral u z).re else u z.re

theorem continuous_poissonExtension {u : ℝ → ℝ} (hu : LogIntegrable u)
    (hc : Continuous u) : Continuous (poissonExtension u) := by sorry

theorem continuousOn_poissonExtension {u : ℝ → ℝ} (hu : LogIntegrable u)
    (hc : Continuous u) : ContinuousOn (poissonExtension u) {z : ℂ | 0 ≤ z.im} := by sorry

end FF.Pavlov
```

## LogClipping.lean

Source: [LogClipping.lean](../FourierFrames/Cited/Pavlov/LogClipping.lean).

Detailed proof: [P5_LogClipping](P5_LogClipping.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.Basic
```

Opening commands:

```lean
open MeasureTheory Set Filter Topology Complex
```

Public interface:

```lean
namespace FF.Pavlov

def logClipCutoff (n : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 ((n:ℝ)+1-|t|))

def logClip (M : ℝ) (A : ℂ → ℂ) (n : ℕ) (t : ℝ) : ℝ :=
  logClipCutoff n t *
    (Real.log M-Real.log (max ‖A t‖ (M*Real.exp (-(n:ℝ)))))

theorem logClipCutoff_nonneg (n : ℕ) (t : ℝ) : 0 ≤ logClipCutoff n t := by sorry

theorem logClipCutoff_le_one (n : ℕ) (t : ℝ) : logClipCutoff n t ≤ 1 := by sorry

theorem logClipCutoff_monotone (t : ℝ) : Monotone (fun n : ℕ ↦ logClipCutoff n t) := by sorry

theorem logClipCutoff_eq_one {n : ℕ} {t : ℝ} (h : |t| ≤ (n:ℝ)) :
    logClipCutoff n t = 1 := by sorry

theorem logClipCutoff_eq_zero {n : ℕ} {t : ℝ} (h : (n:ℝ)+1 ≤ |t|) :
    logClipCutoff n t = 0 := by sorry

theorem continuous_logClipCutoff (n : ℕ) : Continuous (logClipCutoff n) := by sorry

theorem logClip_nonneg {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hbd : ∀ t : ℝ, ‖A t‖ ≤ M) (n : ℕ) (t : ℝ) : 0 ≤ logClip M A n t := by sorry

theorem logClip_monotone {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hbd : ∀ t : ℝ, ‖A t‖ ≤ M) (t : ℝ) :
    Monotone (fun n : ℕ ↦ logClip M A n t) := by sorry

theorem continuous_logClip {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hA : Continuous (fun t : ℝ ↦ A t)) (n : ℕ) : Continuous (logClip M A n) := by sorry

theorem logClip_eq_zero_of_abs_ge {M : ℝ} {A : ℂ → ℂ} {n : ℕ} {t : ℝ}
    (h : (n:ℝ)+1 ≤ |t|) : logClip M A n t = 0 := by sorry

theorem hasCompactSupport_logClip (M : ℝ) (A : ℂ → ℂ) (n : ℕ) :
    HasCompactSupport (logClip M A n) := by sorry

theorem integrable_logClip {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hA : Continuous (fun t : ℝ ↦ A t)) (n : ℕ) : Integrable (logClip M A n) := by sorry

theorem logIntegrable_logClip {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hA : Continuous (fun t : ℝ ↦ A t)) (n : ℕ) : LogIntegrable (logClip M A n) := by sorry

theorem logClip_le_nat {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hbd : ∀ t : ℝ, ‖A t‖ ≤ M) (n : ℕ) (t : ℝ) : logClip M A n t ≤ n := by sorry

theorem logClip_le_deficit {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hbd : ∀ t : ℝ, ‖A t‖ ≤ M) (n : ℕ) {t : ℝ} (ht : A t ≠ 0) :
    logClip M A n t ≤ Real.log M-Real.log ‖A t‖ := by sorry

theorem logClip_boundary_bound {M : ℝ} {A : ℂ → ℂ} (hM : 0 < M)
    (hbd : ∀ t : ℝ, ‖A t‖ ≤ M) (n : ℕ) (t : ℝ) :
    ‖A t‖^2 * Real.exp (2*logClip M A n t) ≤ M^2 := by sorry

theorem eventually_logClip_eq {M : ℝ} {A : ℂ → ℂ}
    {t : ℝ} (ht : A t ≠ 0) :
    ∀ᶠ n : ℕ in atTop, logClip M A n t = Real.log M-Real.log ‖A t‖ := by sorry

theorem tendsto_logClip {M : ℝ} {A : ℂ → ℂ}
    {t : ℝ} (ht : A t ≠ 0) :
    Tendsto (fun n : ℕ ↦ logClip M A n t) atTop (𝓝 (Real.log M-Real.log ‖A t‖)) := by sorry

end FF.Pavlov
```

## LogPoissonBoundary.lean

Source: [LogPoissonBoundary.lean](../FourierFrames/Cited/Pavlov/LogPoissonBoundary.lean).

Detailed proof: [P5_LogPoissonBoundary](P5_LogPoissonBoundary.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.SchwarzBoundary
import FourierFrames.Cited.Pavlov.LogPoissonKernel
```

Opening commands:

```lean
open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate
```

Public interface:

```lean
namespace FF.Pavlov

theorem tendsto_poisson_log_defect_boundary {A : ℂ → ℂ}
    (hA : Differentiable ℂ A) (hnz : ∀ z ∈ FF.UHP, A z ≠ 0)
    (hv : LogIntegrable (fun t : ℝ ↦ Real.log ‖A t‖)) (a : ℝ) :
    Tendsto (fun z ↦ (schwarzIntegral (fun t : ℝ ↦ Real.log ‖A t‖) z).re -
      Real.log ‖A z‖) (𝓝[FF.UHP] (a : ℂ)) (𝓝 0) := by sorry

def poissonLogDefect (A : ℂ → ℂ) (z : ℂ) : ℝ :=
  if 0 < z.im then (schwarzIntegral (fun t : ℝ ↦ Real.log ‖A t‖) z).re -
    Real.log ‖A z‖ else 0

theorem continuous_poissonLogDefect {A : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hnz : ∀ z ∈ FF.UHP, A z ≠ 0)
    (hv : LogIntegrable (fun t : ℝ ↦ Real.log ‖A t‖)) : Continuous (poissonLogDefect A) := by sorry

theorem poisson_log_defect_continuous_zero_boundary {A : ℂ → ℂ}
    (hA : Differentiable ℂ A) (hnz : ∀ z ∈ FF.UHP, A z ≠ 0)
    (hv : LogIntegrable (fun t : ℝ ↦ Real.log ‖A t‖)) :
    ContinuousOn (poissonLogDefect A) {z : ℂ | 0 ≤ z.im} := by sorry

end FF.Pavlov
```

## HarmonicReflection.lean

Source: [HarmonicReflection.lean](../FourierFrames/Cited/Pavlov/HarmonicReflection.lean).

Detailed proof: [P5_Reflection](P5_Reflection.md).

Direct imports:

```lean
import FourierFrames.Cited.DeBrangesDE.EntireHerglotz
import FourierFrames.Cited.DeBrangesFC
import TauCeti.Analysis.PDE.PoissonIntegral.Ball
import TauCeti.Analysis.InnerProductSpace.Laplacian.Comparison
```

Opening commands:

```lean
open Set Complex InnerProductSpace Metric Topology
open scoped ComplexConjugate
```

Public interface:

```lean
namespace FF.Pavlov

def oddReflection (r : ℂ → ℝ) (z : ℂ) : ℝ :=
  if 0 ≤ z.im then r z else -r (conj z)

theorem harmonicOnNhd_oddReflection {r : ℂ → ℝ}
    (hr : HarmonicOnNhd r FF.UHP)
    (hcont : ContinuousOn r {z : ℂ | 0 ≤ z.im})
    (hzero : ∀ x : ℝ, r x = 0) : HarmonicOnNhd (oddReflection r) univ := by sorry

theorem nonneg_harmonic_zero_boundary_eq_mul_im
    {r : ℂ → ℝ}
    (hr : HarmonicOnNhd r FF.UHP)
    (hcont : ContinuousOn r {z : ℂ | 0 ≤ z.im})
    (hzero : ∀ x : ℝ, r x = 0)
    (hpos : ∀ z ∈ FF.UHP, 0 ≤ r z) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ z ∈ FF.UHP, r z = a*z.im := by sorry

end FF.Pavlov
```

## LogPoisson.lean

Source: [LogPoisson.lean](../FourierFrames/Cited/Pavlov/LogPoisson.lean).

Detailed proof: [P5_Dispersion](P5_Dispersion.md), [P5_LogClipping](P5_LogClipping.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.SchwarzBoundary
import FourierFrames.Cited.Pavlov.LogClipping
import FourierFrames.Cited.Pavlov.LogPoissonBoundary
import FourierFrames.Cited.Pavlov.HarmonicReflection
import FourierFrames.HB.DeBranges
import FourierFrames.Cited.DeBrangesFC
import TauCeti.Analysis.InnerProductSpace.Laplacian.Comparison
```

Opening commands:

```lean
open MeasureTheory Complex Set Filter Topology InnerProductSpace Laplacian Metric
```

Public interface:

```lean
namespace FF.Pavlov

lemma laplacian_norm_sq_nonneg {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    0 ≤ Δ (fun w ↦ ‖f w‖ ^ 2) z := by sorry

lemma le_of_locally_holomorphic_norm_sq {K : Set ℂ} (hK : IsCompact K)
    {T : ℂ → ℝ} {C : ℝ} (hT : ContinuousOn T K)
    (hloc : ∀ z ∈ interior K, ∃ f : ℂ → ℂ, AnalyticAt ℂ f z ∧
      T =ᶠ[𝓝 z] (fun w ↦ ‖f w‖ ^ 2))
    (hbd : ∀ z ∈ frontier K, T z ≤ C) : ∀ z ∈ K, T z ≤ C := by sorry

lemma compact_poisson_modulus_comparison
    {A S : ℂ → ℂ} {p : ℂ → ℝ} {R C : ℝ}
    (hA : Differentiable ℂ A)
    (hS : AnalyticOnNhd ℂ S UHP)
    (hp : ContinuousOn p {z : ℂ | 0 ≤ z.im})
    (hpre : ∀ z ∈ UHP, p z = (S z).re)
    (hbd : ∀ z ∈ frontier (Metric.closedBall (0 : ℂ) R ∩ {z : ℂ | 0 ≤ z.im}),
      ‖A z‖ ^ 2 * Real.exp (2 * p z) ≤ C) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R ∩ {z : ℂ | 0 ≤ z.im},
      ‖A z‖ ^ 2 * Real.exp (2 * p z) ≤ C := by sorry

lemma mem_frontier_upper_halfdisk {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ frontier (Metric.closedBall (0 : ℂ) R ∩ {w : ℂ | 0 ≤ w.im})) :
    (‖z‖ = R ∧ 0 ≤ z.im) ∨ (‖z‖ ≤ R ∧ z.im = 0) := by sorry

lemma poisson_modulus_le_on_halfdisk
    {A S : ℂ → ℂ} {p : ℂ → ℝ} {R M e : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hA : Differentiable ℂ A) (hS : AnalyticOnNhd ℂ S UHP)
    (hp : ContinuousOn p {z : ℂ | 0 ≤ z.im})
    (hpre : ∀ z ∈ UHP, p z = (S z).re)
    (hAn : ∀ z : ℂ, 0 ≤ z.im → ‖A z‖ ≤ M)
    (hdiam : ∀ x : ℝ, ‖A x‖ ^ 2 * Real.exp (2*p x) ≤ M^2)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → 0 ≤ z.im → p z ≤ e) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R ∩ {w : ℂ | 0 ≤ w.im},
      ‖A z‖ ^ 2 * Real.exp (2*p z) ≤ M^2*Real.exp (2*e) := by sorry

lemma norm_le_on_closed_upper {A : ℂ → ℂ} (hA : Continuous A) {M : ℝ}
    (hbd : ∀ z ∈ UHP, ‖A z‖ ≤ M) :
    ∀ z : ℂ, 0 ≤ z.im → ‖A z‖ ≤ M := by sorry

lemma poisson_kernel_le_on_semicircle {R B : ℝ} (hR : 0 < R) (hBR : B ≤ R/2)
    {z : ℂ} (hzn : ‖z‖ = R) {t : ℝ} (ht : |t| ≤ B) :
    z.im / (Real.pi*((t-z.re)^2+z.im^2)) ≤ 4/(Real.pi*R) := by sorry

lemma schwarzIntegral_re_le_on_semicircle {g : ℝ → ℝ}
    (hg : LogIntegrable g) (hgi : Integrable g) (hgn : ∀ t, 0 ≤ g t)
    {R B : ℝ} (hR : 0 < R) (hBR : B ≤ R/2)
    (hgs : ∀ t : ℝ, B < |t| → g t = 0)
    {z : ℂ} (hzn : ‖z‖ = R) (hz : 0 < z.im) :
    (schwarzIntegral g z).re ≤ (4/(Real.pi*R)) * ∫ t : ℝ, g t := by sorry

lemma schwarzIntegral_re_le_log_deficit_of_compact
    {A : ℂ → ℂ} (hA : Differentiable ℂ A) {M : ℝ} (hM : 0 < M)
    (hAb : ∀ z ∈ UHP, ‖A z‖ ≤ M)
    {g : ℝ → ℝ} (hg : LogIntegrable g) (hgi : Integrable g)
    (hgc : Continuous g) (hgn : ∀ t, 0 ≤ g t)
    {B : ℝ} (hgs : ∀ t : ℝ, B < |t| → g t = 0)
    (hdiam : ∀ t : ℝ, ‖A t‖^2 * Real.exp (2*g t) ≤ M^2)
    {z : ℂ} (hz : z ∈ UHP) (hAz : A z ≠ 0) :
    (schwarzIntegral g z).re ≤ Real.log M - Real.log ‖A z‖ := by sorry

theorem log_norm_le_poisson_boundary
    {A : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hnz : ∀ z ∈ UHP, A z ≠ 0)
    (hbd : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ UHP, ‖A z‖ ≤ M)
    (hv : LogIntegrable (fun t : ℝ ↦ Real.log ‖A t‖)) :
    ∀ z ∈ UHP, Real.log ‖A z‖ ≤
      (schwarzIntegral (fun t : ℝ ↦ Real.log ‖A t‖) z).re := by sorry

theorem poisson_log_defect_eq_mul_im
    {A : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hnz : ∀ z ∈ UHP, A z ≠ 0)
    (hbd : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ UHP, ‖A z‖ ≤ M)
    (hv : LogIntegrable (fun t : ℝ ↦ Real.log ‖A t‖)) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ z ∈ UHP,
      (schwarzIntegral (fun t : ℝ ↦ Real.log ‖A t‖) z).re -
        Real.log ‖A z‖ = a*z.im := by sorry

end FF.Pavlov
```

## OuterComparison.lean

Source: [OuterComparison.lean](../FourierFrames/Cited/Pavlov/OuterComparison.lean).

Detailed proof: [P5_OuterComparison](P5_OuterComparison.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.Schwarz
import FourierFrames.HB.H2
```

Opening commands:

```lean
open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate
```

Public interface:

```lean
namespace FF.Pavlov

theorem norm_exp_schwarzIntegral_sq_le {u : ℝ → ℝ} (hu : LogIntegrable u)
    (he : Integrable (fun t : ℝ ↦ Real.exp (2*u t))) {z : ℂ} (hz : 0 < z.im) :
    ‖Complex.exp (schwarzIntegral u z)‖^2 ≤
      ∫ t : ℝ, z.im/(Real.pi*((t-z.re)^2+z.im^2))*Real.exp (2*u t) := by sorry

theorem lintegral_exp_schwarzIntegral_sq_le {u : ℝ → ℝ} (hu : LogIntegrable u)
    (he : Integrable (fun t : ℝ ↦ Real.exp (2*u t))) {y : ℝ} (hy : 0 < y) :
    (∫⁻ x : ℝ, ‖Complex.exp (schwarzIntegral u ((x : ℂ)+(y : ℂ)*I))‖ₑ^2) ≤
      ENNReal.ofReal (∫ t : ℝ, Real.exp (2*u t)) := by sorry

theorem isH2Upper_exp_schwarzIntegral {u : ℝ → ℝ} (hu : LogIntegrable u)
    (he : Integrable (fun t : ℝ ↦ Real.exp (2*u t))) :
    IsH2Upper (fun z ↦ Complex.exp (schwarzIntegral u z)) := by sorry

theorem factor_of_log_defect {u : ℝ → ℝ} (hu : LogIntegrable u)
    {A : ℂ → ℂ} (hA : DifferentiableOn ℂ A UHP)
    (hnz : ∀ z ∈ UHP, A z ≠ 0) (a : ℝ)
    (hdefect : ∀ z ∈ UHP,
      (schwarzIntegral u z).re - Real.log ‖A z‖ = a*z.im) :
    ∃ b : ℝ, ∀ z ∈ UHP,
      A z = Complex.exp (I*((a : ℂ)*z+(b : ℂ))) *
        Complex.exp (schwarzIntegral u z) := by sorry

end FF.Pavlov
```

## NoExponentialDefect.lean

Source: [NoExponentialDefect.lean](../FourierFrames/Cited/Pavlov/NoExponentialDefect.lean).

Detailed proof: [P5_NoExponentialDefect](P5_NoExponentialDefect.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.Cardinal
import FourierFrames.HB.Comparable
import FourierFrames.HB.H2
```

Opening commands:

```lean
open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate
```

Public interface:

```lean
namespace FF.Pavlov

theorem no_exponential_defect {Γ : Set ℝ} (hcis : IsCompleteInterpolating Γ)
    {q O : ℂ → ℂ} (hq : Differentiable ℂ q) (hqreal : fstar q = q)
    (hO : IsH2Upper O) {γ a b : ℝ} (hqγ : q (γ : ℂ) ≠ 0)
    (hzeros : ∀ x ∈ Γ, x ≠ γ → q (x : ℂ) = 0)
    (ha : 0 ≤ a)
    (hfactor : ∀ z : ℂ, 0 < z.im →
      Complex.exp (I * Real.pi * z) * q z =
        Complex.exp (I * ((a : ℂ)*z+(b : ℂ))) * O z) : a = 0 := by sorry

end FF.Pavlov
```

## GeneratingDispersion.lean

Source: [GeneratingDispersion.lean](../FourierFrames/Cited/Pavlov/GeneratingDispersion.lean).

Detailed proof: [P5_Dispersion](P5_Dispersion.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.CardinalLog
import FourierFrames.Cited.Pavlov.LogPoisson
import FourierFrames.Cited.Pavlov.OuterComparison
import FourierFrames.Cited.Pavlov.NoExponentialDefect
```

Opening commands:

```lean
open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate
```

Public interface:

```lean
namespace FF.Pavlov

variable {Γ : Set ℝ}

theorem CardinalData.log_norm_eq_poisson (d : CardinalData Γ) (g : Grid Γ)
    (hΓ : IsSeparated Γ) (hcis : IsCompleteInterpolating Γ) :
    ∀ z ∈ UHP, Real.log ‖d.G z‖ = Real.pi * z.im +
      (schwarzIntegral (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖) z).re := by sorry

theorem CardinalData.upper_log_dispersion (d : CardinalData Γ) (g : Grid Γ)
    (hΓ : IsSeparated Γ) (hcis : IsCompleteInterpolating Γ)
    {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L UHP)
    (hexp : ∀ z ∈ UHP, Complex.exp (L z) = d.G z) :
    ∃ c : ℝ, ∀ z ∈ UHP,
      L z = schwarzIntegral (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖) z -
        I * Real.pi * z + (c : ℂ) * I := by sorry

end FF.Pavlov
```

## Pavlov.lean

Source: [Pavlov.lean](../FourierFrames/Cited/Pavlov.lean).

Detailed proof: [P5_Dispersion](P5_Dispersion.md), [P5_BoundaryPhase](P5_BoundaryPhase.md), [P5_CountingBMO](P5_CountingBMO.md).

Direct imports:

```lean
import FourierFrames.Cited.Pavlov.GeneratingDispersion
import FourierFrames.Cited.Pavlov.BoundaryPhase
import FourierFrames.Cited.Pavlov.CountingBMO
```

Opening commands:

```lean
open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate
```

Public interface:

```lean
namespace FF

namespace Pavlov

theorem CardinalData.counting_discrepancy_bmo {Γ : Set ℝ} (d : CardinalData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) (hcis : IsCompleteInterpolating Γ) :
    MemBMO (fun x ↦ countFn Γ x - x) := by sorry

end Pavlov

theorem pavlovBMO_holds : PavlovBMO := by sorry

end FF
```

Interface inventory: 339 public declarations in 37 modules.
