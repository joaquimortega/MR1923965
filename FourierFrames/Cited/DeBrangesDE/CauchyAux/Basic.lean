import FourierFrames.HB.MeanValue

/-!
# P3 — auxiliary lemmas for `Cauchy.lean`

Elementary pieces of the half-plane Cauchy–Goursat theorem that do not involve `IsH2Cont`:
Tonelli on a strip, existence of good abscissae for the vertical sides, the rectangle identity on
`[-R, R] × [0, Y]`, and the pointwise AM–GM form of the domination hypothesis.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate Interval

noncomputable section

namespace FF

/-- Tonelli on a strip for a measurable integrand. -/
theorem lintegral_lintegral_strip_le {g : ℂ → ℝ≥0∞} (hg : Measurable g) {Y : ℝ} {C : ℝ≥0∞}
    (hC : ∀ y ∈ Ioc (0 : ℝ) Y, ∫⁻ x : ℝ, g ((x : ℂ) + (y : ℂ) * I) ≤ C) :
    ∫⁻ x : ℝ, ∫⁻ y in Ioc (0 : ℝ) Y, g ((x : ℂ) + (y : ℂ) * I) ≤ C * ENNReal.ofReal Y := by
  have hm : Measurable fun p : ℝ × ℝ ↦ g ((p.1 : ℂ) + (p.2 : ℂ) * I) :=
    hg.comp (by fun_prop)
  rw [lintegral_lintegral_swap (f := fun (x y : ℝ) ↦ g ((x : ℂ) + (y : ℂ) * I))
    (μ := volume) (ν := volume.restrict (Ioc (0 : ℝ) Y)) (by exact hm.aemeasurable)]
  calc ∫⁻ y in Ioc (0 : ℝ) Y, ∫⁻ x : ℝ, g ((x : ℂ) + (y : ℂ) * I)
      ≤ ∫⁻ _ in Ioc (0 : ℝ) Y, C := setLIntegral_mono' measurableSet_Ioc hC
    _ = C * ENNReal.ofReal Y := by rw [setLIntegral_const, Real.volume_Ioc, sub_zero]

/-- Measurability of `x ↦ ∫⁻_{(0,Y]} g(x + iy) dy`. -/
theorem measurable_lintegral_strip {g : ℂ → ℝ≥0∞} (hg : Measurable g) (Y : ℝ) :
    Measurable fun x : ℝ ↦ ∫⁻ y in Ioc (0 : ℝ) Y, g ((x : ℂ) + (y : ℂ) * I) := by
  have hm : Measurable fun p : ℝ × ℝ ↦ g ((p.1 : ℂ) + (p.2 : ℂ) * I) :=
    hg.comp (by fun_prop)
  exact hm.lintegral_prod_right'

/-- Good abscissae: if `∫⁻ H < ∞`, then `H(x) + H(-x) ≤ 1` for arbitrarily large `x`. -/
theorem exists_ge_add_neg_le_one {H : ℝ → ℝ≥0∞} (hH : Measurable H) (hfin : ∫⁻ x, H x ≠ ⊤)
    (a : ℝ) : ∃ x, a ≤ x ∧ H x + H (-x) ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have h1 : ∫⁻ x in Ici a, (1 : ℝ≥0∞) ≤ ∫⁻ x in Ici a, (H x + H (-x)) :=
    setLIntegral_mono' measurableSet_Ici fun x hx ↦ (hcon x hx).le
  have h2 : ∫⁻ x in Ici a, (H x + H (-x)) ≤ ∫⁻ x, (H x + H (-x)) :=
    setLIntegral_le_lintegral _ _
  have h3 : ∫⁻ x, (H x + H (-x)) = 2 * ∫⁻ x, H x := by
    rw [lintegral_add_left hH, lintegral_neg_eq_self, two_mul]
  rw [setLIntegral_const, Real.volume_Ici, one_mul] at h1
  have := h1.trans (h2.trans h3.le)
  rw [top_le_iff] at this
  exact ENNReal.mul_ne_top (by norm_num) hfin this

/-- `‖∫_0^Y f‖ₑ ≤ ∫⁻_{(0,Y]} ‖f‖ₑ`. -/
theorem enorm_intervalIntegral_le {f : ℝ → ℂ} {Y : ℝ} (hY : 0 ≤ Y) :
    ‖∫ y in (0 : ℝ)..Y, f y‖ₑ ≤ ∫⁻ y in Ioc (0 : ℝ) Y, ‖f y‖ₑ := by
  rw [intervalIntegral.integral_of_le hY]
  exact enorm_integral_le_lintegral_enorm _

/-- The rectangle identity on `[-R, R] × [0, Y]`. -/
theorem rect_identity {G : ℂ → ℂ} {Y : ℝ} (hY : 0 < Y)
    (hc : ContinuousOn G {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Y})
    (hd : ∀ z : ℂ, 0 < z.im → z.im < Y → DifferentiableAt ℂ G z) (R : ℝ) :
    (∫ x in -R..R, G (x : ℂ)) - (∫ x in -R..R, G ((x : ℂ) + (Y : ℂ) * I)) +
      I • (∫ y in (0 : ℝ)..Y, G ((R : ℂ) + (y : ℂ) * I)) -
      I • (∫ y in (0 : ℝ)..Y, G (((-R : ℝ) : ℂ) + (y : ℂ) * I)) = 0 := by
  have hwre : ((R : ℂ) + (Y : ℂ) * I).re = R := by simp
  have hwim : ((R : ℂ) + (Y : ℂ) * I).im = Y := by simp
  have Hc : ContinuousOn G ([[(((-R : ℝ) : ℂ)).re, ((R : ℂ) + (Y : ℂ) * I).re]] ×ℂ
      [[(((-R : ℝ) : ℂ)).im, ((R : ℂ) + (Y : ℂ) * I).im]]) := by
    refine hc.mono fun p hp ↦ ?_
    have h2 := hp.2
    simp only [mem_preimage, Complex.ofReal_im, hwim, uIcc_of_le hY.le, mem_Icc] at h2
    exact h2
  have Hd : DifferentiableOn ℂ G
      (Ioo (min (((-R : ℝ) : ℂ)).re ((R : ℂ) + (Y : ℂ) * I).re)
          (max (((-R : ℝ) : ℂ)).re ((R : ℂ) + (Y : ℂ) * I).re) ×ℂ
        Ioo (min (((-R : ℝ) : ℂ)).im ((R : ℂ) + (Y : ℂ) * I).im)
          (max (((-R : ℝ) : ℂ)).im ((R : ℂ) + (Y : ℂ) * I).im)) := by
    intro p hp
    have h2 := hp.2
    simp only [mem_preimage, Complex.ofReal_im, hwim, min_eq_left hY.le, max_eq_right hY.le,
      mem_Ioo] at h2
    exact (hd p h2.1 h2.2).differentiableWithinAt
  have := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn G _ _ Hc Hd
  rw [hwre, hwim, Complex.ofReal_re, Complex.ofReal_im] at this
  simpa only [Complex.ofReal_zero, zero_mul, add_zero] using this

/-- AM–GM form of the domination bound: `g ≤ f/d + A/d²`, `d ≥ 1` give
`g ≤ (ε/2) f² + (1/(2ε) + |A|) d⁻²`. -/
theorem le_of_dom {g f d A ε : ℝ} (hd : 1 ≤ d) (hε : 0 < ε) (h : g ≤ f / d + A / d ^ 2) :
    g ≤ ε / 2 * f ^ 2 + (1 / (2 * ε) + |A|) * (d ^ 2)⁻¹ := by
  have hd0 : 0 < d := by linarith
  have h1 : f / d ≤ ε / 2 * f ^ 2 + 1 / (2 * ε) * (d ^ 2)⁻¹ := by
    rw [div_eq_mul_inv, ← inv_pow]
    have key : 0 ≤ (ε * f - d⁻¹) ^ 2 := sq_nonneg _
    have e : (ε / 2 * f ^ 2 + 1 / (2 * ε) * d⁻¹ ^ 2) * (2 * ε) = ε ^ 2 * f ^ 2 + d⁻¹ ^ 2 := by
      field_simp
    refine le_of_mul_le_mul_right ?_ (by positivity : 0 < 2 * ε)
    rw [e]
    nlinarith
  have h2 : A / d ^ 2 ≤ |A| * (d ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
  nlinarith

section Dominated

variable {F G : ℂ → ℂ} {w₀ : ℂ} {A : ℝ}

/-- Pointwise bound on the vertical sides: for `‖z - w₀‖ ≥ ρ ≥ 1`,
`‖G z‖ₑ ≤ (ρ⁻¹/2) ‖F z‖ₑ² + (ρ⁻¹/2 + |A| ρ⁻²)`. -/
theorem enorm_le_of_dom_side
    (hdom : ∀ z : ℂ, 0 ≤ z.im → 1 ≤ ‖z - w₀‖ → ‖G z‖ ≤ ‖F z‖ / ‖z - w₀‖ + A / ‖z - w₀‖ ^ 2)
    {z : ℂ} (hz : 0 ≤ z.im) {ρ : ℝ} (hρ : 1 ≤ ρ) (hzρ : ρ ≤ ‖z - w₀‖) :
    ‖G z‖ₑ ≤ ENNReal.ofReal (ρ⁻¹ / 2) * ‖F z‖ₑ ^ 2 +
      ENNReal.ofReal (ρ⁻¹ / 2 + |A| * ρ⁻¹ ^ 2) := by
  have hρ0 : 0 < ρ := by linarith
  have hd : 1 ≤ ‖z - w₀‖ := hρ.trans hzρ
  have h1 := le_of_dom hd (inv_pos.mpr hρ0) (hdom z hz hd)
  have h2 : (‖z - w₀‖ ^ 2)⁻¹ ≤ ρ⁻¹ ^ 2 := by
    rw [inv_pow]
    gcongr
  have h3 : ‖G z‖ ≤ ρ⁻¹ / 2 * ‖F z‖ ^ 2 + (ρ⁻¹ / 2 + |A| * ρ⁻¹ ^ 2) := by
    have e : (1 / (2 * ρ⁻¹) + |A|) * ρ⁻¹ ^ 2 = ρ⁻¹ / 2 + |A| * ρ⁻¹ ^ 2 := by
      field_simp
    calc ‖G z‖ ≤ _ := h1
      _ ≤ ρ⁻¹ / 2 * ‖F z‖ ^ 2 + (1 / (2 * ρ⁻¹) + |A|) * ρ⁻¹ ^ 2 := by gcongr
      _ = _ := by rw [e]
  rw [← ofReal_norm, enorm_sq_eq_ofReal, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal h3

end Dominated

end FF
