import FourierFrames.Defs

/-!
# M02 — Hardy space toolkit (`H²` of the upper half-plane) and area mean-value bounds

See `blueprint/M02_HB.md`, §1.  Mathlib has no Hardy space theory; everything needed by M02
(and possibly by M03/M04) is proved here from first principles: closure properties of
`IsH2Upper`, the area mean-value inequality `|G(c)|² ≤ (π r²)⁻¹ ∫_{B(c,r)} |G|²`, and its
consequences (pointwise bound for `H²` functions, bounded on strips, Liouville for `L²` on lines).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Closure properties of `IsH2Upper` -/

theorem IsH2Upper.congr {g h : ℂ → ℂ} (hg : IsH2Upper g)
    (heq : ∀ z : ℂ, 0 < z.im → g z = h z) : IsH2Upper h := by
  obtain ⟨hd, C, hC⟩ := hg
  refine ⟨hd.congr fun z hz ↦ (heq z hz).symm, C, fun y hy ↦ ?_⟩
  have : ∀ x : ℝ, h ((x : ℂ) + (y : ℂ) * I) = g ((x : ℂ) + (y : ℂ) * I) := fun x ↦ by
    rw [heq]; simpa using hy
  simpa only [this] using hC y hy

/-- Elementary inequality `‖a + b‖ₑ² ≤ 2 ‖a‖ₑ² + 2 ‖b‖ₑ²`. -/
theorem enorm_add_sq_le (a b : ℂ) :
    ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  sorry

theorem IsH2Upper.add {g h : ℂ → ℂ} (hg : IsH2Upper g) (hh : IsH2Upper h) :
    IsH2Upper (fun z ↦ g z + h z) := by
  sorry

theorem IsH2Upper.sub {g h : ℂ → ℂ} (hg : IsH2Upper g) (hh : IsH2Upper h) :
    IsH2Upper (fun z ↦ g z - h z) := by
  sorry

theorem IsH2Upper.const_mul {g : ℂ → ℂ} (hg : IsH2Upper g) (c : ℂ) :
    IsH2Upper (fun z ↦ c * g z) := by
  sorry

/-- A bounded holomorphic multiplier (`|B| ≤ 1`) preserves `H²`. -/
theorem IsH2Upper.mul_bounded {g B : ℂ → ℂ} (hg : IsH2Upper g)
    (hB : DifferentiableOn ℂ B {z : ℂ | 0 < z.im}) (hB1 : ∀ z : ℂ, 0 < z.im → ‖B z‖ ≤ 1) :
    IsH2Upper (fun z ↦ B z * g z) := by
  sorry

/-- A constant function is in `H²(ℂ₊)` only if it is `0` (its line integrals are `∞`). -/
theorem IsH2Upper.const_eq_zero {c : ℂ} (h : IsH2Upper (fun _ ↦ c)) : c = 0 := by
  sorry

/-! ## Area mean-value inequality -/

/-- **Area mean-value inequality.**  If `G` is holomorphic on a neighbourhood of the closed disc
`B̄(c, r)`, `r > 0`, then `|G(c)|² ≤ (π r²)⁻¹ ∫_{B(c,r)} |G|² dA`. -/
theorem enorm_sq_le_setLIntegral_ball {G : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (closedBall c r)) :
    ‖G c‖ₑ ^ 2 ≤ (ENNReal.ofReal (Real.pi * r ^ 2))⁻¹ * ∫⁻ z in ball c r, ‖G z‖ₑ ^ 2 := by
  sorry

/-- Pointwise bound from a bound on the horizontal line integrals in the strip
`|Im w - Im c| < r`: if `G` is holomorphic near `B̄(c, r)` and
`∫ |G(x + is)|² dx ≤ K` for almost every `s ∈ (Im c - r, Im c + r)`, then
`|G(c)|² ≤ (2 / (π r)) K`. -/
theorem enorm_sq_le_of_lines {G : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (closedBall c r)) {K : ℝ≥0∞}
    (hK : ∀ᵐ s : ℝ, s ∈ Ioo (c.im - r) (c.im + r) →
      ∫⁻ x : ℝ, ‖G ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2 ≤ K) :
    ‖G c‖ₑ ^ 2 ≤ ENNReal.ofReal (2 / (Real.pi * r)) * K := by
  sorry

/-- **Pointwise bound in `H²`.**  If `g` is holomorphic on `Im z > 0` and
`∫ |g(x + iy)|² dx ≤ C` for all `y > 0`, then `|g(z)|² ≤ (4 / (π Im z)) C`. -/
theorem IsH2Upper.enorm_sq_le {g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, 0 < y → ∫⁻ x : ℝ, ‖g ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ C)
    {z : ℂ} (hz : 0 < z.im) :
    ‖g z‖ₑ ^ 2 ≤ ENNReal.ofReal (4 / (Real.pi * z.im)) * C := by
  sorry

/-- **Liouville for `L²` on lines.**  An entire function whose line integrals
`∫ |G(x + is)|² dx` are bounded by a constant `K < ∞` for all (almost all) `s` is `0`. -/
theorem eq_zero_of_lines_le {G : ℂ → ℂ} (hG : Differentiable ℂ G) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hline : ∀ s : ℝ, s ≠ 0 → ∫⁻ x : ℝ, ‖G ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2 ≤ K) :
    ∀ z, G z = 0 := by
  sorry

/-- **Blow-up at a real zero.**  If `E` is entire without zeros in `Im z > 0` and has a zero at
the real point `x₀`, and `f` is entire with `f(x₀) ≠ 0`, then `f/E` is *not* in `H²(ℂ₊)`:
`∫ |f/E (x + iy)|² dx ≥ c / y` for small `y`. -/
theorem not_isH2Upper_div_of_zero {E f : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hf : Differentiable ℂ f) (hE0 : ∀ z : ℂ, 0 < z.im → E z ≠ 0) {x₀ : ℝ} (hx₀ : E x₀ = 0)
    (hfx : f x₀ ≠ 0) : ¬ IsH2Upper (fun z ↦ f z / E z) := by
  sorry

end FF
