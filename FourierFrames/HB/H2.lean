import FourierFrames.Defs
import FourierFrames.HB.MeanValue

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

/-- The line `x ↦ g (x + y i)` is continuous for `g` differentiable on the upper half-plane. -/
theorem continuous_line {g : ℂ → ℂ} (hd : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) {y : ℝ}
    (hy : 0 < y) : Continuous fun x : ℝ ↦ g ((x : ℂ) + (y : ℂ) * I) := by
  have hc : Continuous fun x : ℝ ↦ (x : ℂ) + (y : ℂ) * I := by fun_prop
  refine hd.continuousOn.comp_continuous hc fun x ↦ ?_
  simpa using hy

theorem measurable_line_sq {g : ℂ → ℂ} (hd : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) {y : ℝ}
    (hy : 0 < y) : Measurable fun x : ℝ ↦ ‖g ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 :=
  ((continuous_line hd hy).measurable.enorm).pow_const 2

/-- Elementary inequality `‖a + b‖ₑ² ≤ 2 ‖a‖ₑ² + 2 ‖b‖ₑ²`. -/
theorem enorm_add_sq_le (a b : ℂ) :
    ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  have h1 : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have := norm_add_le a b
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]
  have h2 := ENNReal.ofReal_le_ofReal h1
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (norm_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)] at h2
  simpa [ofReal_norm] using h2

theorem IsH2Upper.add {g h : ℂ → ℂ} (hg : IsH2Upper g) (hh : IsH2Upper h) :
    IsH2Upper (fun z ↦ g z + h z) := by
  obtain ⟨hd1, C1, h1⟩ := hg
  obtain ⟨hd2, C2, h2⟩ := hh
  refine ⟨hd1.add hd2, 2 * C1 + 2 * C2, fun y hy ↦ ?_⟩
  calc ∫⁻ x : ℝ, ‖(g ((x : ℂ) + (y : ℂ) * I) + h ((x : ℂ) + (y : ℂ) * I))‖ₑ ^ 2
      ≤ ∫⁻ x : ℝ, (2 * ‖g ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 + 2 * ‖h ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2) :=
        lintegral_mono fun x ↦ enorm_add_sq_le _ _
    _ = 2 * (∫⁻ x : ℝ, ‖g ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2) + 2 * (∫⁻ x : ℝ, ‖h ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2) := by
        rw [lintegral_add_left ((measurable_line_sq hd1 hy).const_mul 2), lintegral_const_mul _
          (measurable_line_sq hd1 hy), lintegral_const_mul _ (measurable_line_sq hd2 hy)]
    _ ≤ _ := by
        push_cast
        exact add_le_add (mul_le_mul_right (h1 y hy) 2) (mul_le_mul_right (h2 y hy) 2)

theorem IsH2Upper.const_mul {g : ℂ → ℂ} (hg : IsH2Upper g) (c : ℂ) :
    IsH2Upper (fun z ↦ c * g z) := by
  obtain ⟨hd, C, h1⟩ := hg
  refine ⟨hd.const_mul c, ‖c‖₊ ^ 2 * C, fun y hy ↦ ?_⟩
  calc ∫⁻ x : ℝ, ‖c * g ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2
      = ∫⁻ x : ℝ, ‖c‖ₑ ^ 2 * ‖g ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 := by
        congr 1; funext x; rw [enorm_mul, mul_pow]
    _ = ‖c‖ₑ ^ 2 * ∫⁻ x : ℝ, ‖g ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 :=
        lintegral_const_mul _ (measurable_line_sq hd hy)
    _ ≤ _ := by
        push_cast
        gcongr
        · rfl
        · exact h1 y hy

theorem IsH2Upper.sub {g h : ℂ → ℂ} (hg : IsH2Upper g) (hh : IsH2Upper h) :
    IsH2Upper (fun z ↦ g z - h z) := by
  have := hg.add (hh.const_mul (-1))
  refine this.congr fun z _ ↦ ?_
  ring

/-- A bounded holomorphic multiplier (`|B| ≤ 1`) preserves `H²`. -/
theorem IsH2Upper.mul_bounded {g B : ℂ → ℂ} (hg : IsH2Upper g)
    (hB : DifferentiableOn ℂ B {z : ℂ | 0 < z.im}) (hB1 : ∀ z : ℂ, 0 < z.im → ‖B z‖ ≤ 1) :
    IsH2Upper (fun z ↦ B z * g z) := by
  obtain ⟨hd, C, h1⟩ := hg
  refine ⟨hB.mul hd, C, fun y hy ↦ le_trans (lintegral_mono fun x ↦ ?_) (h1 y hy)⟩
  have hB' := hB1 ((x : ℂ) + (y : ℂ) * I) (by simpa using hy)
  rw [enorm_mul]
  have : ‖B ((x : ℂ) + (y : ℂ) * I)‖ₑ ≤ 1 := by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_one.mpr hB'
  calc (‖B ((x : ℂ) + (y : ℂ) * I)‖ₑ * ‖g ((x : ℂ) + (y : ℂ) * I)‖ₑ) ^ 2
      ≤ (1 * ‖g ((x : ℂ) + (y : ℂ) * I)‖ₑ) ^ 2 := by gcongr
    _ = _ := by rw [one_mul]

/-- A constant function is in `H²(ℂ₊)` only if it is `0` (its line integrals are `∞`). -/
theorem IsH2Upper.const_eq_zero {c : ℂ} (h : IsH2Upper (fun _ ↦ c)) : c = 0 := by
  by_contra hc
  obtain ⟨-, C, h1⟩ := h
  have := h1 1 one_pos
  simp only [lintegral_const, Real.volume_univ] at this
  have hne : ‖c‖ₑ ^ 2 ≠ 0 := by simp [hc]
  rw [ENNReal.mul_top hne] at this
  exact absurd this (by simp)

/-! ## Area mean-value inequality -/

/-- **Area mean-value inequality.**  If `G` is holomorphic on a neighbourhood of the closed disc
`B̄(c, r)`, `r > 0`, then `|G(c)|² ≤ (π r²)⁻¹ ∫_{B(c,r)} |G|² dA`. -/
theorem enorm_sq_le_setLIntegral_ball {G : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (closedBall c r)) :
    ‖G c‖ₑ ^ 2 ≤ (ENNReal.ofReal (Real.pi * r ^ 2))⁻¹ * ∫⁻ z in ball c r, ‖G z‖ₑ ^ 2 := by
  have h := area_ge hr hG
  have hpos : ENNReal.ofReal (Real.pi * r ^ 2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  calc ‖G c‖ₑ ^ 2 = (ENNReal.ofReal (Real.pi * r ^ 2))⁻¹ * (ENNReal.ofReal (Real.pi * r ^ 2) * ‖G c‖ₑ ^ 2) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hpos ENNReal.ofReal_ne_top, one_mul]
    _ ≤ _ := by gcongr

/-- Pointwise bound from a bound on the horizontal line integrals in the strip
`|Im w - Im c| < r`: if `G` is holomorphic near `B̄(c, r)` and
`∫ |G(x + is)|² dx ≤ K` for almost every `s ∈ (Im c - r, Im c + r)`, then
`|G(c)|² ≤ (2 / (π r)) K`. -/
theorem enorm_sq_le_of_lines {G : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (closedBall c r)) {K : ℝ≥0∞}
    (hK : ∀ᵐ s : ℝ, s ∈ Ioo (c.im - r) (c.im + r) →
      ∫⁻ x : ℝ, ‖G ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2 ≤ K) :
    ‖G c‖ₑ ^ 2 ≤ ENNReal.ofReal (2 / (Real.pi * r)) * K := by
  classical
  set G' : ℂ → ℂ := (closedBall c r).piecewise G 0 with hG'
  have hm : Measurable G' :=
    hG.continuousOn.measurable_piecewise continuousOn_const isClosed_closedBall.measurableSet
  have hG'le : ∀ z, ‖G' z‖ₑ ^ 2 ≤ ‖G z‖ₑ ^ 2 := by
    intro z
    by_cases hz : z ∈ closedBall c r
    · rw [hG', Set.piecewise_eq_of_mem _ _ _ hz]
    · rw [hG', Set.piecewise_eq_of_notMem _ _ _ hz]
      simp
  have hball : ∫⁻ z in ball c r, ‖G z‖ₑ ^ 2 = ∫⁻ z in ball c r, ‖G' z‖ₑ ^ 2 :=
    setLIntegral_congr_fun measurableSet_ball fun z hz ↦ by
      simp only [hG', Set.piecewise_eq_of_mem _ _ _ (ball_subset_closedBall hz)]
  have hsub : ball c r ⊆ {z : ℂ | z.im ∈ Ioo (c.im - r) (c.im + r)} := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : |(z - c).im| ≤ ‖z - c‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_im] at h1
    have := abs_lt.mp (lt_of_le_of_lt h1 hz)
    show c.im - r < z.im ∧ z.im < c.im + r
    constructor <;> linarith [this.1, this.2]
  have hFm : Measurable fun z ↦ ‖G' z‖ₑ ^ 2 := (hm.enorm).pow_const 2
  have h1 : ∫⁻ z in ball c r, ‖G' z‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * r) * K := by
    calc ∫⁻ z in ball c r, ‖G' z‖ₑ ^ 2
        ≤ ∫⁻ z in {z : ℂ | z.im ∈ Ioo (c.im - r) (c.im + r)}, ‖G' z‖ₑ ^ 2 :=
          lintegral_mono_set hsub
      _ = ∫⁻ s in Ioo (c.im - r) (c.im + r), ∫⁻ x : ℝ, ‖G' ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2 :=
          lintegral_strip hFm measurableSet_Ioo
      _ ≤ ∫⁻ s in Ioo (c.im - r) (c.im + r), K := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).mpr ?_)
          filter_upwards [hK] with s hs hsI
          exact le_trans (lintegral_mono fun x ↦ hG'le _) (hs hsI)
      _ = ENNReal.ofReal (2 * r) * K := by
          rw [setLIntegral_const, Real.volume_Ioo, mul_comm]
          congr 2; ring
  have h2 := area_ge hr hG
  rw [hball] at h2
  have h3 := h2.trans h1
  have hpos : ENNReal.ofReal (Real.pi * r ^ 2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  calc ‖G c‖ₑ ^ 2 = (ENNReal.ofReal (Real.pi * r ^ 2))⁻¹ *
        (ENNReal.ofReal (Real.pi * r ^ 2) * ‖G c‖ₑ ^ 2) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hpos ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal (Real.pi * r ^ 2))⁻¹ * (ENNReal.ofReal (2 * r) * K) := by gcongr
    _ = ENNReal.ofReal (2 / (Real.pi * r)) * K := by
        rw [← mul_assoc, ← ENNReal.ofReal_inv_of_pos (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

/-- **Pointwise bound in `H²`.**  If `g` is holomorphic on `Im z > 0` and
`∫ |g(x + iy)|² dx ≤ C` for all `y > 0`, then `|g(z)|² ≤ (4 / (π Im z)) C`. -/
theorem IsH2Upper.enorm_sq_le {g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, 0 < y → ∫⁻ x : ℝ, ‖g ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ C)
    {z : ℂ} (hz : 0 < z.im) :
    ‖g z‖ₑ ^ 2 ≤ ENNReal.ofReal (4 / (Real.pi * z.im)) * C := by
  have hr : 0 < z.im / 2 := by linarith
  have hsub : closedBall z (z.im / 2) ⊆ {z : ℂ | 0 < z.im} := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_im] at h1
    have := abs_le.mp (h1.trans hw)
    show 0 < w.im
    linarith [this.1]
  have := enorm_sq_le_of_lines hr (hd.mono hsub) (K := C) (by
    refine Filter.Eventually.of_forall fun s hs ↦ hC s ?_
    have := hs.1
    linarith)
  convert this using 3
  field_simp
  ring

/-- **Liouville for `L²` on lines.**  An entire function whose line integrals
`∫ |G(x + is)|² dx` are bounded by a constant `K < ∞` for all (almost all) `s` is `0`. -/
theorem eq_zero_of_lines_le {G : ℂ → ℂ} (hG : Differentiable ℂ G) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hline : ∀ s : ℝ, s ≠ 0 → ∫⁻ x : ℝ, ‖G ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2 ≤ K) :
    ∀ z, G z = 0 := by
  intro z
  have hae : ∀ᵐ s : ℝ, s ≠ 0 := by rw [ae_iff]; simp
  have hle : ∀ r : ℝ, 0 < r → ‖G z‖ₑ ^ 2 ≤ ENNReal.ofReal (2 / (Real.pi * r)) * K := fun r hr ↦
    enorm_sq_le_of_lines hr hG.differentiableOn (by
      filter_upwards [hae] with s hs _ using hline s hs)
  have htend : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (2 / (Real.pi * r)) * K) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ ↦ 2 / (Real.pi * r)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := (2 / Real.pi : ℝ))).div_atTop tendsto_id
      refine this.congr fun r ↦ ?_
      simp only [id]; field_simp
    have h2 : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (2 / (Real.pi * r))) atTop (𝓝 0) := by
      simpa using (ENNReal.tendsto_ofReal h1)
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inr hK)
  have h0 : ‖G z‖ₑ ^ 2 ≤ 0 :=
    ge_of_tendsto htend ((eventually_gt_atTop 0).mono fun r hr ↦ hle r hr)
  have : ‖G z‖ₑ ^ 2 = 0 := le_antisymm h0 bot_le
  simpa using this

/-- **Blow-up at a real zero.**  If `E` is entire without zeros in `Im z > 0` and has a zero at
the real point `x₀`, and `f` is entire with `f(x₀) ≠ 0`, then `f/E` is *not* in `H²(ℂ₊)`:
`∫ |f/E (x + iy)|² dx ≥ c / y` for small `y`. -/
theorem not_isH2Upper_div_of_zero {E f : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hf : Differentiable ℂ f) (hE0 : ∀ z : ℂ, 0 < z.im → E z ≠ 0) {x₀ : ℝ} (hx₀ : E x₀ = 0)
    (hfx : f x₀ ≠ 0) : ¬ IsH2Upper (fun z ↦ f z / E z) := by
  sorry

end FF
