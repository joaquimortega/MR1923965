import FourierFrames.Defs

/-!
# M07 -- helper lemmas for `Corollary2.lean`: Schwarz reflection (Morera)
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate Interval

noncomputable section

namespace FF


/-- The reflected function. -/
def schwarzExt (H : ℂ → ℂ) (c : ℝ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then H z else conj (H (conj z)) + 2 * Complex.I * c

/-- The rectangle expression. -/
def rectInt (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (((∫ x : ℝ in a..b, f (x + c * Complex.I)) - ∫ x : ℝ in a..b, f (x + d * Complex.I)) +
    Complex.I • ∫ y : ℝ in c..d, f (b + y * Complex.I)) -
      Complex.I • ∫ y : ℝ in c..d, f (a + y * Complex.I)

theorem rectInt_split {f : ℂ → ℂ} (hf : Continuous f) (a b c m d : ℝ) :
    rectInt f a b c d = rectInt f a b c m + rectInt f a b m d := by
  unfold rectInt
  have h1 : ∀ u v : ℝ, ∀ r : ℝ, IntervalIntegrable (fun y : ℝ ↦ f (r + y * Complex.I)) volume u v :=
    fun u v r ↦ (hf.comp (by fun_prop)).intervalIntegrable u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (h1 c m b) (h1 m d b),
    ← intervalIntegral.integral_add_adjacent_intervals (h1 c m a) (h1 m d a)]
  simp only [smul_add]
  abel

theorem schwarzExt_eq_of_im_nonneg (H : ℂ → ℂ) (c : ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    schwarzExt H c z = H z := by
  simp [schwarzExt, hz]

theorem schwarzExt_eq_of_im_neg (H : ℂ → ℂ) (c : ℝ) {z : ℂ} (hz : z.im < 0) :
    schwarzExt H c z = conj (H (conj z)) + 2 * Complex.I * c := by
  simp [schwarzExt, not_le.mpr hz]


theorem rectInt_eq_zero {f : ℂ → ℂ} (a b c d : ℝ)
    (hc : ContinuousOn f ([[a, b]] ×ℂ [[c, d]]))
    (hd : ∀ x ∈ Ioo (min a b) (max a b) ×ℂ Ioo (min c d) (max c d), DifferentiableAt ℂ f x) :
    rectInt f a b c d = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f (⟨a, c⟩ : ℂ) ⟨b, d⟩ ∅
    countable_empty hc (fun x hx ↦ hd x hx.1)

theorem exists_entire_reflection_aux {H : ℂ → ℂ} (hc : ContinuousOn H {z : ℂ | 0 ≤ z.im})
    (hd : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) {c : ℝ} (him : ∀ x : ℝ, (H x).im = c) :
    ∃ Ĥ : ℂ → ℂ, Differentiable ℂ Ĥ ∧ (∀ z : ℂ, 0 ≤ z.im → Ĥ z = H z) ∧
      ∀ z : ℂ, Ĥ (conj z) = conj (Ĥ z) + 2 * Complex.I * c := by
  set Ĥ : ℂ → ℂ := schwarzExt H c with hĤ
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  -- the lower piece
  set H' : ℂ → ℂ := fun z ↦ conj (H (conj z)) + 2 * Complex.I * c with hH'
  have hcl : ContinuousOn H' {z : ℂ | z.im ≤ 0} := by
    have h1 : ContinuousOn (fun z : ℂ ↦ H (conj z)) {z : ℂ | z.im ≤ 0} :=
      hc.comp (by fun_prop) (fun z hz ↦ by simpa using hz)
    exact (Complex.continuous_conj.comp_continuousOn h1).add continuousOn_const
  have hdl : DifferentiableOn ℂ H' {z : ℂ | z.im < 0} := by
    intro z hz
    have : DifferentiableAt ℂ H (conj z) :=
      (hd.differentiableAt (hopen.mem_nhds (by simpa using hz)))
    have h2 := this.conj_conj
    simp only [Complex.conj_conj] at h2
    exact (h2.add_const _).differentiableWithinAt
  -- reality on the axis
  have hreal : ∀ z : ℂ, z.im = 0 → H' z = H z := by
    intro z hz
    have hzc : conj z = z := by
      apply Complex.ext <;> simp [hz]
    have hH : (H z).im = c := by
      have := him z.re
      rwa [show ((z.re : ℝ) : ℂ) = z from Complex.ext (by simp) (by simp [hz])] at this
    simp only [hH', hzc]
    apply Complex.ext
    · simp
    · simp [hH]; ring
  -- continuity
  have hcu : ContinuousOn Ĥ {z : ℂ | 0 ≤ z.im} :=
    hc.congr fun z hz ↦ schwarzExt_eq_of_im_nonneg H c hz
  have hcl' : ContinuousOn Ĥ {z : ℂ | z.im ≤ 0} := by
    refine hcl.congr fun z hz ↦ ?_
    rcases lt_or_eq_of_le (show z.im ≤ 0 from hz) with h | h
    · exact schwarzExt_eq_of_im_neg H c h
    · show schwarzExt H c z = H' z
      rw [schwarzExt_eq_of_im_nonneg H c h.ge, hreal z h]
  have hcont : Continuous Ĥ := by
    rw [← continuousOn_univ]
    have : (univ : Set ℂ) = {z : ℂ | 0 ≤ z.im} ∪ {z : ℂ | z.im ≤ 0} := by
      ext z; simp only [mem_univ, mem_union, mem_ofPred_eq, true_iff]; exact le_total _ _
    rw [this]
    exact hcu.union_of_isClosed hcl' (isClosed_le continuous_const Complex.continuous_im)
      (isClosed_le Complex.continuous_im continuous_const)
  -- same-side rectangles
  have hside : ∀ a b c₁ d : ℝ, ((0 ≤ c₁ ∧ 0 ≤ d) ∨ (c₁ ≤ 0 ∧ d ≤ 0)) → rectInt Ĥ a b c₁ d = 0 := by
    intro a b c₁ d hcd
    rcases hcd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine rectInt_eq_zero a b c₁ d (hcu.mono ?_) ?_
      · intro w hw
        rw [Complex.mem_reProdIm] at hw
        have hw2 := hw.2
        rw [mem_uIcc] at hw2
        show 0 ≤ w.im
        rcases hw2 with h | h <;> linarith [h.1]
      · intro w hw
        rw [Complex.mem_reProdIm] at hw
        have hpos : 0 < w.im := by
          have := hw.2.1
          rcases le_total c₁ d with h | h
          · rw [min_eq_left h] at this; linarith
          · rw [min_eq_right h] at this; linarith
        have hev : Ĥ =ᶠ[𝓝 w] H := by
          filter_upwards [hopen.mem_nhds hpos] with u hu
          exact schwarzExt_eq_of_im_nonneg H c (le_of_lt hu)
        exact ((hd.differentiableAt (hopen.mem_nhds hpos)).congr_of_eventuallyEq hev)
    · refine rectInt_eq_zero a b c₁ d (hcl'.mono ?_) ?_
      · intro w hw
        rw [Complex.mem_reProdIm] at hw
        have hw2 := hw.2
        rw [mem_uIcc] at hw2
        show w.im ≤ 0
        rcases hw2 with h | h <;> linarith [h.2]
      · intro w hw
        rw [Complex.mem_reProdIm] at hw
        have hneg : w.im < 0 := by
          have := hw.2.2
          rcases le_total c₁ d with h | h
          · rw [max_eq_right h] at this; linarith
          · rw [max_eq_left h] at this; linarith
        have hev : Ĥ =ᶠ[𝓝 w] H' := by
          have : {z : ℂ | z.im < 0} ∈ 𝓝 w := (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg
          filter_upwards [this] with u hu
          exact schwarzExt_eq_of_im_neg H c hu
        exact ((hdl.differentiableAt ((isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg)).congr_of_eventuallyEq hev)
  have hall : ∀ a b c₁ d : ℝ, rectInt Ĥ a b c₁ d = 0 := by
    intro a b c₁ d
    rw [rectInt_split hcont a b c₁ 0 d]
    rcases le_total c₁ 0 with h1 | h1 <;> rcases le_total 0 d with h2 | h2
    · rw [hside a b c₁ 0 (Or.inr ⟨h1, le_rfl⟩), hside a b 0 d (Or.inl ⟨le_rfl, h2⟩)]; simp
    · rw [hside a b c₁ 0 (Or.inr ⟨h1, le_rfl⟩), hside a b 0 d (Or.inr ⟨le_rfl, h2⟩)]; simp
    · rw [hside a b c₁ 0 (Or.inl ⟨h1, le_rfl⟩), hside a b 0 d (Or.inl ⟨le_rfl, h2⟩)]; simp
    · rw [hside a b c₁ 0 (Or.inl ⟨h1, le_rfl⟩), hside a b 0 d (Or.inr ⟨le_rfl, h2⟩)]; simp
  have hcons : IsConservativeOn Ĥ univ := by
    intro z w _
    rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
    exact hall z.re w.re z.im w.im
  have hdiff : DifferentiableOn ℂ Ĥ univ :=
    (isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ).mp
      ⟨hcons, hcont.continuousOn⟩
  refine ⟨Ĥ, differentiableOn_univ.mp hdiff, fun z hz ↦ schwarzExt_eq_of_im_nonneg H c hz, ?_⟩
  intro z
  show schwarzExt H c (conj z) = conj (schwarzExt H c z) + 2 * Complex.I * c
  rcases lt_trichotomy z.im 0 with h | h | h
  · have h1 : 0 ≤ (conj z).im := by simp; linarith
    rw [schwarzExt_eq_of_im_nonneg H c h1, schwarzExt_eq_of_im_neg H c h]
    simp only [Complex.conj_conj, map_add, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    ring
  · have hzc : conj z = z := by apply Complex.ext <;> simp [h]
    rw [hzc, schwarzExt_eq_of_im_nonneg H c h.ge]
    have hH : (H z).im = c := by
      have := him z.re
      rwa [show ((z.re : ℝ) : ℂ) = z from Complex.ext (by simp) (by simp [h])] at this
    apply Complex.ext
    · simp
    · simp [hH]; ring
  · have h1 : (conj z).im < 0 := by simp; linarith
    rw [schwarzExt_eq_of_im_neg H c h1, schwarzExt_eq_of_im_nonneg H c h.le]
    simp only [Complex.conj_conj]


end FF
