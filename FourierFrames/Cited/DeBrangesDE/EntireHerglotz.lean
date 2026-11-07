import FourierFrames.Defs

/-!
# P3 — an entire Pick function is linear

See `blueprint/P3_DeBrangesDE.md`, §6.  This file uses no project lemma (it imports `Defs` only for
Mathlib).

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
    InnerProductSpace.HarmonicOnNhd (fun z ↦ (h z).im) (closedBall c R) :=
  fun z _ ↦ (hd.analyticAt z).harmonicAt_im

/-- The Poisson kernel `poissonKernel 0 u` is continuous on the circle `|ζ| = R` when `|u| < R`. -/
theorem continuousOn_poissonKernel_sphere {u : ℂ} {R : ℝ} (hu : ‖u‖ < R) :
    ContinuousOn (poissonKernel 0 u) (sphere 0 |R|) := by
  intro ζ hζ
  have hR : 0 < R := (norm_nonneg u).trans_lt hu
  rw [mem_sphere_zero_iff_norm, abs_of_pos hR] at hζ
  have hne : ζ ≠ u := by rintro rfl; linarith
  apply ContinuousAt.continuousWithinAt
  have h1 : ‖(ζ - 0) - (u - 0)‖ ^ 2 ≠ 0 := by
    simpa [sub_eq_zero] using hne
  show ContinuousAt (fun z ↦ (‖z - 0‖ ^ 2 - ‖u - 0‖ ^ 2) / ‖(z - 0) - (u - 0)‖ ^ 2) ζ
  exact ContinuousAt.div (by fun_prop) (by fun_prop) h1

/-- Poisson formula for the odd function `Im h`: for `|w| < R`,
`2 Im h(w) = ⨍_{|ζ|=R} (P(w,ζ) - P(w̄,ζ)) Im h(ζ)`, because `Im h(w̄) = - Im h(w)`. -/
theorem two_mul_im_eq_circleAverage {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ z, h (conj z) = conj (h z)) {R : ℝ} {w : ℂ} (hw : ‖w‖ < R) :
    2 * (h w).im = Real.circleAverage
      (fun ζ ↦ (poissonKernel 0 w ζ - poissonKernel 0 (conj w) ζ) * (h ζ).im) 0 R := by
  set v : ℂ → ℝ := fun z ↦ (h z).im with hv
  have hw' : ‖conj w‖ < R := by rwa [Complex.norm_conj]
  have hvc : Continuous v := Complex.continuous_im.comp hd.continuous
  have hint : ∀ u : ℂ, ‖u‖ < R → CircleIntegrable (poissonKernel 0 u • v) 0 R := fun u hu ↦
    ((continuousOn_poissonKernel_sphere hu).smul hvc.continuousOn).circleIntegrable'
  have hP : ∀ u : ℂ, ‖u‖ < R → Real.circleAverage (poissonKernel 0 u • v) 0 R = v u :=
    fun u hu ↦ (entire_im_harmonicOnNhd hd 0 R).circleAverage_poissonKernel_smul
      (by simpa using hu)
  have hsub := Real.circleAverage_sub (hint w hw) (hint (conj w) hw')
  rw [hP w hw, hP (conj w) hw'] at hsub
  have hvconj : v (conj w) = -v w := by simp [hv, hreal]
  have heq : (poissonKernel 0 w • v - poissonKernel 0 (conj w) • v) =
      fun ζ ↦ (poissonKernel 0 w ζ - poissonKernel 0 (conj w) ζ) * (h ζ).im := by
    funext ζ; simp [hv, sub_mul]
  rw [← heq, hsub, hvconj]
  ring

/-- The difference kernel on `|ζ| = R`:
`P(w,ζ) - P(w̄,ζ) = 4 (R² - |w|²) Im w Im ζ / (|ζ - w|² |ζ - w̄|²)`. -/
theorem poissonKernel_sub_conj {R : ℝ} {w ζ : ℂ} (hζ : ‖ζ‖ = R) (hwR : ‖w‖ < R) :
    poissonKernel 0 w ζ - poissonKernel 0 (conj w) ζ =
      4 * (R ^ 2 - ‖w‖ ^ 2) * w.im * ζ.im / (‖ζ - w‖ ^ 2 * ‖ζ - conj w‖ ^ 2) := by
  have hne : ζ ≠ w := by rintro rfl; linarith
  have hne' : ζ ≠ conj w := by rintro rfl; rw [Complex.norm_conj] at hζ; linarith
  have ha : ‖ζ - w‖ ^ 2 = (ζ.re - w.re) ^ 2 + (ζ.im - w.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hb : ‖ζ - conj w‖ ^ 2 = (ζ.re - w.re) ^ 2 + (ζ.im + w.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have ha0 : ‖ζ - w‖ ^ 2 ≠ 0 := by simpa [sub_eq_zero] using hne
  have hb0 : ‖ζ - conj w‖ ^ 2 ≠ 0 := by simpa [sub_eq_zero] using hne'
  simp only [poissonKernel, sub_zero, Complex.norm_conj, hζ]
  rw [div_sub_div _ _ ha0 hb0, hb, ha]
  congr 1
  ring

/-- The weights `Im ζ · Im h(ζ)` are `≥ 0` (positivity on `ℂ₊`, oddness below). -/
theorem im_mul_im_nonneg {h : ℂ → ℂ} (hreal : ∀ z, h (conj z) = conj (h z))
    (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im) (ζ : ℂ) : 0 ≤ ζ.im * (h ζ).im := by
  rcases lt_trichotomy ζ.im 0 with hlt | heq | hgt
  · have h1 : 0 < (conj ζ).im := by simpa using hlt
    have h2 := hpos _ h1
    rw [hreal, Complex.conj_im] at h2
    nlinarith
  · simp [heq]
  · exact mul_nonneg hgt.le (hpos ζ hgt)

/-- Comparison of the kernels: for `‖w‖, ‖w'‖ ≤ r < R` and `‖ζ‖ = R`,
`k_w(ζ) ≤ κ(r,R) k_{w'}(ζ)` with `κ(r,R) = (R+r)^4 / ((R-r)^4 (1 - r²/R²)) → 1` as `R → ∞`;
here `k_w(ζ) = (R² - |w|²) / (|ζ-w|² |ζ-w̄|²)`. -/
theorem kernel_ratio_le {R r : ℝ} {w w' ζ : ℂ} (hr : 0 < r) (hrR : r < R) (hw : ‖w‖ ≤ r)
    (hw' : ‖w'‖ ≤ r) (hζ : ‖ζ‖ = R) :
    (R ^ 2 - ‖w‖ ^ 2) / (‖ζ - w‖ ^ 2 * ‖ζ - conj w‖ ^ 2) ≤
      ((R + r) ^ 4 / ((R - r) ^ 4 * (1 - r ^ 2 / R ^ 2))) *
        ((R ^ 2 - ‖w'‖ ^ 2) / (‖ζ - w'‖ ^ 2 * ‖ζ - conj w'‖ ^ 2)) := by
  have hR : 0 < R := hr.trans hrR
  have hRr : 0 < R - r := by linarith
  have ha : R - r ≤ ‖ζ - w‖ := by have := norm_sub_norm_le ζ w; linarith
  have hb : R - r ≤ ‖ζ - conj w‖ := by
    have := norm_sub_norm_le ζ (conj w); rw [Complex.norm_conj] at this; linarith
  have ha'0 : R - r ≤ ‖ζ - w'‖ := by have := norm_sub_norm_le ζ w'; linarith
  have hb'0 : R - r ≤ ‖ζ - conj w'‖ := by
    have := norm_sub_norm_le ζ (conj w'); rw [Complex.norm_conj] at this; linarith
  have ha' : ‖ζ - w'‖ ≤ R + r := (norm_sub_le _ _).trans (by linarith)
  have hb' : ‖ζ - conj w'‖ ≤ R + r :=
    (norm_sub_le _ _).trans (by rw [Complex.norm_conj]; linarith)
  have hwn := norm_nonneg w
  have hw'n := norm_nonneg w'
  have h1 : (R ^ 2 - ‖w‖ ^ 2) / (‖ζ - w‖ ^ 2 * ‖ζ - conj w‖ ^ 2) ≤ R ^ 2 / (R - r) ^ 4 := by
    apply div_le_div₀ (by positivity) (by nlinarith) (by positivity)
    calc (R - r) ^ 4 = (R - r) ^ 2 * (R - r) ^ 2 := by ring
      _ ≤ ‖ζ - w‖ ^ 2 * ‖ζ - conj w‖ ^ 2 := by gcongr
  have hrR2 : r ^ 2 < R ^ 2 := by nlinarith
  have hκ : 0 < 1 - r ^ 2 / R ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]; exact hrR2
  have h2 : R ^ 2 / (R - r) ^ 4 =
      ((R + r) ^ 4 / ((R - r) ^ 4 * (1 - r ^ 2 / R ^ 2))) * ((R ^ 2 - r ^ 2) / (R + r) ^ 4) := by
    have : R ^ 2 - r ^ 2 ≠ 0 := by linarith
    field_simp
  have h3 : (R ^ 2 - r ^ 2) / (R + r) ^ 4 ≤
      (R ^ 2 - ‖w'‖ ^ 2) / (‖ζ - w'‖ ^ 2 * ‖ζ - conj w'‖ ^ 2) := by
    have h4 := hRr.trans_le ha'0
    have h5 := hRr.trans_le hb'0
    apply div_le_div₀ (by nlinarith) (by nlinarith) (by positivity)
    calc ‖ζ - w'‖ ^ 2 * ‖ζ - conj w'‖ ^ 2 ≤ (R + r) ^ 2 * (R + r) ^ 2 := by gcongr
      _ = (R + r) ^ 4 := by ring
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left h3 (by positivity))

/-- The kernel `k_w(ζ) = (R² - |w|²)/(|ζ-w|² |ζ-w̄|²)` of the representation of `Im h(w)/Im w`. -/
def pickKer (R : ℝ) (w ζ : ℂ) : ℝ := (R ^ 2 - ‖w‖ ^ 2) / (‖ζ - w‖ ^ 2 * ‖ζ - conj w‖ ^ 2)

theorem continuousOn_pickKer {R : ℝ} {w : ℂ} (hw : ‖w‖ < R) :
    ContinuousOn (pickKer R w) (sphere 0 |R|) := by
  intro ζ hζ
  have hR : 0 < R := (norm_nonneg w).trans_lt hw
  rw [mem_sphere_zero_iff_norm, abs_of_pos hR] at hζ
  have hne : ζ ≠ w := by rintro rfl; linarith
  have hne' : ζ ≠ conj w := by rintro rfl; rw [Complex.norm_conj] at hζ; linarith
  apply ContinuousAt.continuousWithinAt
  have h1 : ‖ζ - w‖ ^ 2 * ‖ζ - conj w‖ ^ 2 ≠ 0 := by
    apply mul_ne_zero <;> simpa [sub_eq_zero]
  show ContinuousAt (fun ζ ↦ (R ^ 2 - ‖w‖ ^ 2) / (‖ζ - w‖ ^ 2 * ‖ζ - conj w‖ ^ 2)) ζ
  exact ContinuousAt.div (by fun_prop) (by fun_prop) h1

/-- `Im h(w)/Im w = 2 ⨍_{|ζ| = R} k_w(ζ) Im ζ Im h(ζ)` for nonreal `w`, `|w| < R`. -/
theorem im_div_im_eq_circleAverage {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ z, h (conj z) = conj (h z)) {R : ℝ} {w : ℂ} (hw : w.im ≠ 0) (hwR : ‖w‖ < R) :
    (h w).im / w.im =
      2 * Real.circleAverage (fun ζ ↦ pickKer R w ζ * (ζ.im * (h ζ).im)) 0 R := by
  have hR : 0 < R := (norm_nonneg w).trans_lt hwR
  have h2 := two_mul_im_eq_circleAverage hd hreal hwR
  have hcongr : Real.circleAverage
      (fun ζ ↦ (poissonKernel 0 w ζ - poissonKernel 0 (conj w) ζ) * (h ζ).im) 0 R =
      Real.circleAverage ((4 * w.im) • fun ζ ↦ pickKer R w ζ * (ζ.im * (h ζ).im)) 0 R := by
    apply Real.circleAverage_congr_sphere
    intro ζ hζ
    rw [mem_sphere_zero_iff_norm, abs_of_pos hR] at hζ
    simp only [Pi.smul_apply, smul_eq_mul, pickKer]
    rw [poissonKernel_sub_conj hζ hwR]
    ring
  rw [hcongr, Real.circleAverage_smul, smul_eq_mul] at h2
  rw [div_eq_iff hw]
  linear_combination h2 / 2

/-- One half of `im_div_im_eq`: `Im h(w)/Im w ≤ Im h(w')/Im w'`. -/
theorem im_div_im_le {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ z, h (conj z) = conj (h z)) (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im)
    {w w' : ℂ} (hw : w.im ≠ 0) (hw' : w'.im ≠ 0) :
    (h w).im / w.im ≤ (h w').im / w'.im := by
  set r := max ‖w‖ ‖w'‖ + 1 with hr_def
  have hr : 0 < r := by positivity
  have hwr : ‖w‖ ≤ r := by rw [hr_def]; have := le_max_left ‖w‖ ‖w'‖; linarith
  have hw'r : ‖w'‖ ≤ r := by rw [hr_def]; have := le_max_right ‖w‖ ‖w'‖; linarith
  set κ : ℝ → ℝ := fun R ↦ (R + r) ^ 4 / ((R - r) ^ 4 * (1 - r ^ 2 / R ^ 2)) with hκ_def
  set m : ℂ → ℝ := fun ζ ↦ ζ.im * (h ζ).im with hm_def
  have hm : ∀ ζ, 0 ≤ m ζ := im_mul_im_nonneg hreal hpos
  have hmc : Continuous m := by
    simp only [hm_def]
    exact Complex.continuous_im.mul (Complex.continuous_im.comp hd.continuous)
  -- the comparison for each `R > r`
  have hcomp : ∀ R : ℝ, r < R → (h w).im / w.im ≤ κ R * ((h w').im / w'.im) := by
    intro R hrR
    have hR : 0 < R := hr.trans hrR
    have hwR : ‖w‖ < R := hwr.trans_lt hrR
    have hw'R : ‖w'‖ < R := hw'r.trans_lt hrR
    rw [im_div_im_eq_circleAverage hd hreal hw hwR, im_div_im_eq_circleAverage hd hreal hw' hw'R]
    have hle : Real.circleAverage (fun ζ ↦ pickKer R w ζ * m ζ) 0 R ≤
        Real.circleAverage (κ R • fun ζ ↦ pickKer R w' ζ * m ζ) 0 R := by
      apply Real.circleAverage_mono
      · exact ((continuousOn_pickKer hwR).mul hmc.continuousOn).circleIntegrable'
      · exact (((continuousOn_pickKer hw'R).mul hmc.continuousOn).const_smul
          (κ R)).circleIntegrable'
      · intro ζ hζ
        rw [mem_sphere_zero_iff_norm, abs_of_pos hR] at hζ
        show pickKer R w ζ * m ζ ≤ κ R * (pickKer R w' ζ * m ζ)
        exact (mul_le_mul_of_nonneg_right (kernel_ratio_le hr hrR hwr hw'r hζ) (hm ζ)).trans_eq
          (mul_assoc _ _ _)
    rw [Real.circleAverage_smul, smul_eq_mul] at hle
    simp only [hm_def] at hle
    nlinarith
  -- `κ R → 1`
  have hlim : Filter.Tendsto κ Filter.atTop (nhds 1) := by
    have ht : Filter.Tendsto (fun R : ℝ ↦ r / R) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop Filter.tendsto_id
    have hg : ContinuousAt (fun t : ℝ ↦ (1 + t) ^ 4 / ((1 - t) ^ 4 * (1 - t ^ 2))) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    have h1 := hg.tendsto.comp ht
    norm_num at h1
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop r] with R hR
    have hR0 : R ≠ 0 := (hr.trans hR).ne'
    have hRr : R - r ≠ 0 := sub_ne_zero.mpr hR.ne'
    simp only [Function.comp_apply, hκ_def]
    field_simp
  have hlim' : Filter.Tendsto (fun R ↦ κ R * ((h w').im / w'.im)) Filter.atTop
      (nhds ((h w').im / w'.im)) := by
    simpa using hlim.mul_const ((h w').im / w'.im)
  exact ge_of_tendsto hlim' ((Filter.eventually_gt_atTop r).mono hcomp)

/-- `Im h(w) / Im w` does not depend on `w` (nonreal). -/
theorem im_div_im_eq {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ z, h (conj z) = conj (h z)) (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im)
    {w w' : ℂ} (hw : w.im ≠ 0) (hw' : w'.im ≠ 0) :
    (h w).im / w.im = (h w').im / w'.im :=
  le_antisymm (im_div_im_le hd hreal hpos hw hw') (im_div_im_le hd hreal hpos hw' hw)

/-- An entire function with values in `ℝ` (zero imaginary part) is constant. -/
theorem entire_im_eq_zero_const {g : ℂ → ℂ} (hd : Differentiable ℂ g) (him : ∀ z, (g z).im = 0) :
    ∀ z, g z = g 0 := by
  have han : AnalyticOnNhd ℂ g univ := fun z _ ↦ hd.analyticAt z
  rcases han.is_constant_or_isOpen isPreconnected_univ with ⟨c, hc⟩ | hopen
  · intro z; rw [hc z trivial, hc 0 trivial]
  · exfalso
    have ho := hopen univ subset_rfl isOpen_univ
    have hmem : g 0 ∈ g '' univ := mem_image_of_mem g trivial
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho (g 0) hmem
    have hin : g 0 + ((ε / 2 : ℝ) : ℂ) * I ∈ g '' univ := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    obtain ⟨z, _, hz⟩ := hin
    have h1 := him z
    rw [hz] at h1
    simp [him 0] at h1
    linarith

/-- **Lemma L.**  An entire Pick function that is real on `ℝ` is `p z + q`, `p ≥ 0`. -/
theorem entire_pick_linear {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ z, h (conj z) = conj (h z)) (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im) :
    ∃ p q : ℝ, 0 ≤ p ∧ ∀ z, h z = p * z + q := by
  set p := (h I).im with hp
  have hlin_im : ∀ z, (h z).im = p * z.im := by
    intro z
    by_cases hz : z.im = 0
    · have hzr : conj z = z := Complex.conj_eq_iff_im.mpr hz
      have h1 := congrArg Complex.im (hreal z)
      rw [hzr, Complex.conj_im] at h1
      rw [hz, mul_zero]
      linarith
    · have h1 := im_div_im_eq hd hreal hpos hz (w' := I) (by simp)
      rw [Complex.I_im, div_one, ← hp] at h1
      field_simp at h1
      linarith
  set g : ℂ → ℂ := fun z ↦ h z - p * z with hg
  have hgd : Differentiable ℂ g := hd.sub (differentiable_id.const_mul _)
  have hgim : ∀ z, (g z).im = 0 := by
    intro z; simp [hg, hlin_im]
  have hconst := entire_im_eq_zero_const hgd hgim
  refine ⟨p, (g 0).re, hpos I (by simp), fun z ↦ ?_⟩
  have h2 : g 0 = ((g 0).re : ℂ) := by apply Complex.ext <;> simp [hgim 0]
  calc h z = p * z + g z := by simp [hg]
    _ = p * z + (g 0).re := by rw [hconst z, ← h2]

end FF
