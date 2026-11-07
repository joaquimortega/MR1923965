import Mathlib

/-!
# P3 — an entire Pick function is linear

See `blueprint/P3_DeBrangesDE.md`, §6.  This file does not depend on any project file.

**Lemma L.**  If `h` is entire, real on `ℝ` (`h(z̄) = conj h(z)`) and `Im h ≥ 0` on `ℂ₊`, then
`h(z) = p z + q` with `p ≥ 0`, `q ∈ ℝ`.  Proof: Poisson formula on the circle `|ζ| = R` for the
odd harmonic function `v = Im h`, with positive weights `Im ζ · v(ζ) ≥ 0`, and `R → ∞`.
-/

open Complex Metric Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace FF

/-- `v = Im h` is harmonic on a neighbourhood of every closed disc. -/
theorem entire_im_harmonicOnNhd {h : ℂ → ℂ} (hd : Differentiable ℂ h) (c : ℂ) (R : ℝ) :
    InnerProductSpace.HarmonicOnNhd (fun z ↦ (h z).im) (closedBall c R) := by
  sorry

/-- Poisson formula for the odd function `Im h`: for `|w| < R`,
`2 Im h(w) = ⨍_{|ζ|=R} (P(w,ζ) - P(w̄,ζ)) Im h(ζ)`, because `Im h(w̄) = - Im h(w)`. -/
theorem two_mul_im_eq_circleAverage {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ z, h (conj z) = conj (h z)) {R : ℝ} {w : ℂ} (hw : ‖w‖ < R) :
    2 * (h w).im = Real.circleAverage
      (fun ζ ↦ (poissonKernel 0 w ζ - poissonKernel 0 (conj w) ζ) * (h ζ).im) 0 R := by
  sorry

/-- The difference kernel on `|ζ| = R`:
`P(w,ζ) - P(w̄,ζ) = 4 (R² - |w|²) Im w Im ζ / (|ζ - w|² |ζ - w̄|²)`. -/
theorem poissonKernel_sub_conj {R : ℝ} {w ζ : ℂ} (hζ : ‖ζ‖ = R) (hwR : ‖w‖ < R) :
    poissonKernel 0 w ζ - poissonKernel 0 (conj w) ζ =
      4 * (R ^ 2 - ‖w‖ ^ 2) * w.im * ζ.im / (‖ζ - w‖ ^ 2 * ‖ζ - conj w‖ ^ 2) := by
  sorry

/-- The weights `Im ζ · Im h(ζ)` are `≥ 0` (positivity on `ℂ₊`, oddness below). -/
theorem im_mul_im_nonneg {h : ℂ → ℂ} (hreal : ∀ z, h (conj z) = conj (h z))
    (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im) (ζ : ℂ) : 0 ≤ ζ.im * (h ζ).im := by
  sorry

/-- Comparison of the kernels: for `‖w‖, ‖w'‖ ≤ r < R` and `‖ζ‖ = R`,
`k_w(ζ) ≤ κ(r,R) k_{w'}(ζ)` with `κ(r,R) = (R+r)^4 / ((R-r)^4 (1 - r²/R²)) → 1` as `R → ∞`;
here `k_w(ζ) = (R² - |w|²) / (|ζ-w|² |ζ-w̄|²)`. -/
theorem kernel_ratio_le {R r : ℝ} {w w' ζ : ℂ} (hr : 0 < r) (hrR : r < R) (hw : ‖w‖ ≤ r)
    (hw' : ‖w'‖ ≤ r) (hζ : ‖ζ‖ = R) :
    (R ^ 2 - ‖w‖ ^ 2) / (‖ζ - w‖ ^ 2 * ‖ζ - conj w‖ ^ 2) ≤
      ((R + r) ^ 4 / ((R - r) ^ 4 * (1 - r ^ 2 / R ^ 2))) *
        ((R ^ 2 - ‖w'‖ ^ 2) / (‖ζ - w'‖ ^ 2 * ‖ζ - conj w'‖ ^ 2)) := by
  sorry

/-- `Im h(w) / Im w` does not depend on `w` (nonreal). -/
theorem im_div_im_eq {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ z, h (conj z) = conj (h z)) (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im)
    {w w' : ℂ} (hw : w.im ≠ 0) (hw' : w'.im ≠ 0) :
    (h w).im / w.im = (h w').im / w'.im := by
  sorry

/-- An entire function with values in `ℝ` (zero imaginary part) is constant. -/
theorem entire_im_eq_zero_const {g : ℂ → ℂ} (hd : Differentiable ℂ g) (him : ∀ z, (g z).im = 0) :
    ∀ z, g z = g 0 := by
  sorry

/-- **Lemma L.**  An entire Pick function that is real on `ℝ` is `p z + q`, `p ≥ 0`. -/
theorem entire_pick_linear {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ z, h (conj z) = conj (h z)) (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im) :
    ∃ p q : ℝ, 0 ≤ p ∧ ∀ z, h z = p * z + q := by
  sorry

end FF
