import FourierFrames.PW.Bounds

/-!
# M01 — The Plancherel–Pólya inequality and its uniform tail version

See `blueprint/M01_PW.md`, §3.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- **Sub-mean-value property** of `|f|²` for entire `f`:
`|f(c)|² ≤ (π r²)⁻¹ ∫_{D(c,r)} |f|² dA`. -/
theorem enorm_sq_le_lintegral_ball {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) {r : ℝ}
    (hr : 0 < r) :
    ‖f c‖ₑ ^ 2 ≤ ENNReal.ofReal (1 / (Real.pi * r ^ 2)) * ∫⁻ z in ball c r, ‖f z‖ₑ ^ 2 := by
  sorry

/-- `∫∫_{|y| < r} |f(x+iy)|² dx dy ≤ (e^{2πr} - 1)/π · ‖f‖²`. -/
theorem lintegral_strip_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) {r : ℝ} (hr : 0 < r) :
    ∫⁻ z in {z : ℂ | |z.im| < r}, ‖f z‖ₑ ^ 2 ≤
      ENNReal.ofReal ((Real.exp (2 * Real.pi * r) - 1) / Real.pi) * pwNormSq f := by
  sorry

/-- The Plancherel–Pólya constant `C(δ) = 4 (e^{πδ} - 1) / (π² δ²)`; it depends only on `δ`. -/
def ppConst (δ : ℝ) : ℝ := 4 * (Real.exp (Real.pi * δ) - 1) / (Real.pi ^ 2 * δ ^ 2)

/-- Subadditivity of the sampling sum (used for `Λ_α = Λ' ∪ Λ''`, p. 796). -/
theorem sampleSum_union_le (Λ₁ Λ₂ : Set ℝ) (f : ℂ → ℂ) :
    sampleSum (Λ₁ ∪ Λ₂) f ≤ sampleSum Λ₁ f + sampleSum Λ₂ f := by
  sorry

/-- **Plancherel–Pólya**, explicit constant. -/
theorem plancherelPolya_explicit (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) {Λ : Set ℝ}
    (hΛ : IsSepBy δ Λ) {f : ℂ → ℂ} (hf : MemPW f) :
    sampleSum Λ f ≤ ENNReal.ofReal (ppConst δ) * pwNormSq f := by
  sorry

/-- **Plancherel–Pólya** (interface form): the constant depends only on `δ`. -/
theorem plancherelPolya (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ Λ : Set ℝ, IsSepBy δ Λ → ∀ f : ℂ → ℂ, MemPW f → sampleSum Λ f ≤ C * pwNormSq f := by
  sorry

/-- The strip-tail integral `∫∫_{|y|<r, |x| ≥ R} |f|²` tends to `0` as `R → ∞`. -/
theorem tendsto_strip_tail (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R : ℝ ↦ ∫⁻ z in {z : ℂ | |z.im| < r ∧ R ≤ |z.re|}, ‖f z‖ₑ ^ 2)
      atTop (nhds 0) := by
  sorry

/-- **Uniform tail version**: for fixed `δ` and `f ∈ PW`, `∑_{λ ∈ Λ, |λ| ≥ R} |f(λ)|² → 0` as
`R → ∞`, uniformly over all `δ`-separated `Λ`. Explicitly,
`sampleSum (Λ ∩ {|x| ≥ R}) f ≤ (π (δ/2)²)⁻¹ ∫∫_{|y|<δ/2, |x| ≥ R - δ/2} |f|²`. -/
theorem plancherelPolya_tail (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) {f : ℂ → ℂ}
    (hf : MemPW f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ R : ℝ, ∀ Λ : Set ℝ, IsSepBy δ Λ → sampleSum (Λ ∩ {x : ℝ | R ≤ |x|}) f ≤ ε := by
  sorry

end FF
