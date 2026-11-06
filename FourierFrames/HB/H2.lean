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
  intro ⟨hd, C, hC⟩
  set a : ℝ := ‖f x₀‖ with ha
  have hapos : 0 < a := norm_pos_iff.mpr hfx
  -- Lipschitz bound for `E` near `x₀`
  obtain ⟨L, hLpos, hL⟩ : ∃ L : ℝ, 0 < L ∧ ∀ w : ℂ, ‖w - x₀‖ ≤ 1 → ‖E w‖ ≤ L * ‖w - x₀‖ := by
    obtain ⟨L₀, hL₀⟩ := (isCompact_closedBall (x₀ : ℂ) 1).exists_bound_of_continuousOn
      (hE.contDiff.continuous_deriv le_rfl).continuousOn
    refine ⟨max L₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun w hw ↦ ?_⟩
    have hw' : w ∈ closedBall (x₀ : ℂ) 1 := by rwa [mem_closedBall, dist_eq_norm]
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := E) (s := closedBall (x₀ : ℂ) 1) (C := max L₀ 1)
      (fun x _ ↦ hE.differentiableAt) (fun x hx ↦ (hL₀ x hx).trans (le_max_left L₀ 1))
      (convex_closedBall _ _) (mem_closedBall_self zero_le_one) hw'
    rwa [hx₀, sub_zero] at this
  -- lower bound for `f` near `x₀`
  obtain ⟨δ₂, hδ₂, hf⟩ : ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ w : ℂ, ‖w - x₀‖ < δ₂ → a / 2 ≤ ‖f w‖ := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hf.continuous.continuousAt (a / 2) (by linarith)
    refine ⟨δ, hδ, fun w hw ↦ ?_⟩
    have := h (by rwa [dist_eq_norm])
    rw [dist_eq_norm] at this
    have h2 := norm_sub_norm_le (f x₀) (f w)
    rw [norm_sub_rev] at h2
    linarith
  set δ : ℝ := min 1 δ₂ / 4 with hδ
  have hδpos : 0 < δ := by positivity
  set y : ℝ := min δ (a ^ 2 / (8 * L ^ 2 * (C + 1))) with hy
  have hypos : 0 < y := lt_min hδpos (by positivity)
  have hyδ : y ≤ δ := min_le_left _ _
  have hCy := hC y hypos
  -- pointwise lower bound on the segment
  have hpt : ∀ x ∈ Icc ((x₀ : ℝ) - y) (x₀ + y),
      ENNReal.ofReal ((a / (4 * L * y)) ^ 2) ≤ ‖f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 := by
    intro x hx
    set w : ℂ := (x : ℂ) + (y : ℂ) * I with hw
    have hwx : ‖w - x₀‖ ≤ 2 * y := by
      have h1 : w - x₀ = ((x - x₀ : ℝ) : ℂ) + (y : ℂ) * I := by rw [hw]; push_cast; ring
      rw [h1]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
        zero_add]
      have : |x - x₀| ≤ y := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [abs_of_pos hypos]
      linarith
    have hmin1 : min 1 δ₂ ≤ 1 := min_le_left _ _
    have hmin2 : min 1 δ₂ ≤ δ₂ := min_le_right _ _
    have hwle : 2 * y ≤ min 1 δ₂ / 2 := by rw [hδ] at hyδ; linarith
    have hEw : ‖E w‖ ≤ L * (2 * y) :=
      (hL w (by linarith)).trans (mul_le_mul_of_nonneg_left hwx hLpos.le)
    have hfw : a / 2 ≤ ‖f w‖ := hf w (by
      have : 0 < δ₂ := hδ₂
      have : 0 < min 1 δ₂ := lt_min one_pos hδ₂
      linarith)
    have hEne : E w ≠ 0 := hE0 w (by simp [hw, hypos])
    have hEpos : 0 < ‖E w‖ := norm_pos_iff.mpr hEne
    have h1 : a / (4 * L * y) ≤ ‖f w / E w‖ := by
      rw [norm_div, div_le_div_iff₀ (by positivity) hEpos]
      calc a * ‖E w‖ ≤ a * (L * (2 * y)) := by gcongr
        _ = 2 * a * (L * y) := by ring
        _ ≤ ‖f w‖ * (4 * L * y) := by nlinarith [mul_pos hLpos hypos]
    rw [enorm_sq_eq_ofReal]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) h1 2)
  have hint : ENNReal.ofReal (2 * y) * ENNReal.ofReal ((a / (4 * L * y)) ^ 2) ≤ C := by
    calc ENNReal.ofReal (2 * y) * ENNReal.ofReal ((a / (4 * L * y)) ^ 2)
        = ∫⁻ x in Icc ((x₀ : ℝ) - y) (x₀ + y), ENNReal.ofReal ((a / (4 * L * y)) ^ 2) := by
          rw [setLIntegral_const, Real.volume_Icc, mul_comm]
          congr 2; ring
      _ ≤ ∫⁻ x in Icc ((x₀ : ℝ) - y) (x₀ + y),
          ‖f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 :=
          setLIntegral_mono (measurable_line_sq hd hypos) hpt
      _ ≤ ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 :=
          setLIntegral_le_lintegral _ _
      _ ≤ C := hCy
  rw [← ENNReal.ofReal_mul (by positivity)] at hint
  have h1 : (2 * y * (a / (4 * L * y)) ^ 2) ≤ C := by
    have := (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).mp hint
    simpa using this
  have h2 : 2 * y * (a / (4 * L * y)) ^ 2 = a ^ 2 / (8 * L ^ 2 * y) := by
    field_simp; ring
  rw [h2] at h1
  have hy2 : y ≤ a ^ 2 / (8 * L ^ 2 * (C + 1)) := min_le_right _ _
  have hC0 : (0:ℝ) ≤ C := C.coe_nonneg
  have h3 : (C + 1) * y ≤ a ^ 2 / (8 * L ^ 2) := by
    have : y * (8 * L ^ 2 * (C + 1)) ≤ a ^ 2 := by
      rwa [le_div_iff₀ (by positivity)] at hy2
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [div_le_iff₀ (by positivity)] at h1
  have : (C + 1) * y ≤ C * y := by
    calc (C + 1) * y ≤ a ^ 2 / (8 * L ^ 2) := h3
      _ ≤ C * y := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
  nlinarith


end FF
