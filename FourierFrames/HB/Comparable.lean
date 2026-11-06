import FourierFrames.HB.DeBranges
import FourierFrames.HB.MeanValue

/-!
# M02 — the "evident fact" of p. 799: `|E| ≃ e^{π Im z}` on `Im z ≥ 0` implies `H(E) = PW`

See `blueprint/M02_HB.md`, §9.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Auxiliary estimates -/

theorem enorm_div_sq_le {a b : ℂ} {m : ℝ} (hm : 0 < m) (hb : m ≤ ‖b‖) :
    ‖a / b‖ₑ ^ 2 ≤ ENNReal.ofReal (m ^ 2)⁻¹ * ‖a‖ₑ ^ 2 := by
  rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_div, div_pow, div_eq_inv_mul]
  have : (‖b‖ ^ 2)⁻¹ ≤ (m ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hm.le hb 2)
  nlinarith [sq_nonneg ‖a‖]

theorem le_enorm_div_sq {a b : ℂ} {M : ℝ} (hb0 : b ≠ 0) (hb : ‖b‖ ≤ M) :
    ENNReal.ofReal (M ^ 2)⁻¹ * ‖a‖ₑ ^ 2 ≤ ‖a / b‖ₑ ^ 2 := by
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have hM : 0 < M := lt_of_lt_of_le hbpos hb
  rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_div, div_pow, div_eq_inv_mul]
  have : (M ^ 2)⁻¹ ≤ (‖b‖ ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hbpos.le hb 2)
  nlinarith [sq_nonneg ‖a‖]

/-- Line integral bound for `h ∈ PW` divided by `E`. -/
theorem line_div_le (hPW : PaleyWienerThm) {E h : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (hlow : ∀ z : ℂ, 0 ≤ z.im → c * Real.exp (Real.pi * z.im) ≤ ‖E z‖)
    (hh : MemPW h) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖h ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤
      ENNReal.ofReal (c ^ 2)⁻¹ * pwNormSq h := by
  have hpt : ∀ x : ℝ, ‖h ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤
      ENNReal.ofReal ((c * Real.exp (Real.pi * y)) ^ 2)⁻¹ * ‖h ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 := by
    intro x
    refine enorm_div_sq_le (by positivity) ?_
    have := hlow ((x : ℂ) + (y : ℂ) * I) (by simp [hy.le])
    simpa using this
  calc ∫⁻ x : ℝ, ‖h ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2
      ≤ ∫⁻ x : ℝ, ENNReal.ofReal ((c * Real.exp (Real.pi * y)) ^ 2)⁻¹ *
          ‖h ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 := lintegral_mono hpt
    _ = ENNReal.ofReal ((c * Real.exp (Real.pi * y)) ^ 2)⁻¹ *
          ∫⁻ x : ℝ, ‖h ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((c * Real.exp (Real.pi * y)) ^ 2)⁻¹ *
          (ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * pwNormSq h) := by
        gcongr
        exact pw_line_integral_le hPW hh y
    _ = ENNReal.ofReal (c ^ 2)⁻¹ * pwNormSq h := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), abs_of_pos hy]
        congr 2
        rw [mul_pow, ← Real.exp_nat_mul]
        have : Real.exp (2 * Real.pi * y) ≠ 0 := (Real.exp_pos _).ne'
        field_simp
        congr 1; push_cast; ring

theorem isH2Upper_div_of_memPW (hPW : PaleyWienerThm) {E h : ℂ → ℂ} (hE : Differentiable ℂ E)
    {c : ℝ} (hc : 0 < c)
    (hlow : ∀ z : ℂ, 0 ≤ z.im → c * Real.exp (Real.pi * z.im) ≤ ‖E z‖)
    (hh : MemPW h) : IsH2Upper (fun z ↦ h z / E z) := by
  refine ⟨fun z hz ↦ (hh.1.differentiableAt.div (hE.differentiableAt) ?_).differentiableWithinAt,
    (ENNReal.ofReal (c ^ 2)⁻¹ * pwNormSq h).toNNReal, fun y hy ↦ ?_⟩
  · have := hlow z (le_of_lt hz)
    have h2 : 0 < c * Real.exp (Real.pi * z.im) := by positivity
    exact norm_pos_iff.mp (lt_of_lt_of_le h2 this)
  · rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (pwNormSq_ne_top hh))]
    exact line_div_le hPW hc hlow hh hy

/-- **Fatou step**: the `L²` norm on `ℝ` of a function continuous at the real axis is bounded by
the `H²` constant. -/
theorem lintegral_real_le_of_isH2 {G : ℂ → ℂ} (hd : DifferentiableOn ℂ G {z : ℂ | 0 < z.im})
    (hcont : ∀ t : ℝ, ContinuousAt G (t : ℂ)) {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, 0 < y → ∫⁻ x : ℝ, ‖G ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ C) :
    ∫⁻ t : ℝ, ‖G (t : ℂ)‖ₑ ^ 2 ≤ C := by
  set Fn : ℕ → ℝ → ℝ≥0∞ := fun n t ↦
    ‖G ((t : ℂ) + (((1 : ℝ) / (n + 1) : ℝ) : ℂ) * I)‖ₑ ^ 2 with hFn
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n ↦ by positivity
  have hmeas : ∀ n, Measurable (Fn n) := fun n ↦ measurable_line_sq hd (hpos n)
  have hlim : ∀ t : ℝ, Tendsto (fun n ↦ Fn n t) atTop (𝓝 (‖G (t : ℂ)‖ₑ ^ 2)) := by
    intro t
    have h1 : Tendsto (fun n : ℕ ↦ (t : ℂ) + (((1 : ℝ) / (n + 1) : ℝ) : ℂ) * I) atTop (𝓝 (t : ℂ)) := by
      have : Tendsto (fun n : ℕ ↦ (((1 : ℝ) / (n + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
        have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        exact (Complex.continuous_ofReal.tendsto' (0 : ℝ) 0 (by simp)).comp h0
      simpa using (tendsto_const_nhds (x := (t : ℂ))).add (this.mul_const I)
    have h2 := (hcont t).tendsto.comp h1
    have h3 : Continuous fun z : ℂ ↦ ‖z‖ₑ ^ 2 := (ENNReal.continuous_pow 2).comp continuous_enorm
    exact (h3.tendsto _).comp h2
  calc ∫⁻ t : ℝ, ‖G (t : ℂ)‖ₑ ^ 2 = ∫⁻ t : ℝ, liminf (fun n ↦ Fn n t) atTop :=
        lintegral_congr fun t ↦ (hlim t).liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ t : ℝ, Fn n t) atTop := lintegral_liminf_le hmeas
    _ ≤ C := by
        apply Filter.liminf_le_of_frequently_le'
        exact Filter.Eventually.frequently (Filter.Eventually.of_forall fun n ↦ hC _ (hpos n))

theorem enorm_sq_le_mul {a e : ℂ} {B : ℝ} (he : e ≠ 0) (hB : ‖e‖ ≤ B) :
    ‖a‖ₑ ^ 2 ≤ ENNReal.ofReal (B ^ 2) * ‖a / e‖ₑ ^ 2 := by
  rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hepos : 0 < ‖e‖ := norm_pos_iff.mpr he
  have : ‖a‖ = ‖a / e‖ * ‖e‖ := by rw [norm_div]; field_simp
  rw [this, mul_pow]
  have h1 : ‖e‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hepos.le hB 2
  nlinarith [sq_nonneg ‖a / e‖]

theorem real_sq_le_of_enorm {a : ℂ} {r : ℝ} (hr : 0 ≤ r) {C : ℝ≥0}
    (h : ‖a‖ₑ ^ 2 ≤ ENNReal.ofReal r * (C : ℝ≥0∞)) : ‖a‖ ^ 2 ≤ r * C := by
  rw [enorm_sq_eq_ofReal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hr,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h

/-- Quadratic growth bound for `f ∈ H(E)` when `E` is comparable to `e^{π Im z}`. -/
theorem norm_sq_le_of_memHE {E f : ℂ → ℂ} (hE : IsHB E) {c C : ℝ} (hc : 0 < c)
    (hcomp : ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im))
    (hf : MemHE E f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, ‖f z‖ ^ 2 ≤ K * Real.exp (2 * Real.pi * |z.im|) := by
  obtain ⟨hfd, ⟨hd1, C₁, h1⟩, ⟨hd2, C₂, h2⟩⟩ := hf
  have hC : 0 < C := by
    have := hcomp 0 (by simp)
    simp only [Complex.zero_im, mul_zero, Real.exp_zero, mul_one] at this
    linarith [this.1, this.2]
  have hE0 : ∀ w : ℂ, 0 < w.im → E w ≠ 0 := hE.2.1
  have hEb : ∀ w : ℂ, 0 < w.im → ‖E w‖ ≤ C * Real.exp (Real.pi * w.im) :=
    fun w hw ↦ (hcomp w hw.le).2
  have hgen : ∀ (g : ℂ → ℂ) (C' : ℝ≥0),
      DifferentiableOn ℂ (fun z ↦ g z / E z) {z : ℂ | 0 < z.im} →
      (∀ y : ℝ, 0 < y → ∫⁻ x : ℝ, ‖g ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ C') →
      (∀ w : ℂ, 1 ≤ w.im → ‖g w‖ ^ 2 ≤ (4 / Real.pi * C' * C ^ 2) * Real.exp (2 * Real.pi * w.im)) ∧
      (∀ s : ℝ, 0 < s → s < 2 → ∫⁻ x : ℝ, ‖g ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2 ≤
        ENNReal.ofReal (C ^ 2 * Real.exp (4 * Real.pi)) * C') := by
    intro g C' hd hbd
    have hpt : ∀ w : ℂ, 0 < w.im → ‖g w‖ₑ ^ 2 ≤
        ENNReal.ofReal ((C * Real.exp (Real.pi * w.im)) ^ 2) * ‖g w / E w‖ₑ ^ 2 :=
      fun w hw ↦ enorm_sq_le_mul (hE0 w hw) (hEb w hw)
    refine ⟨fun w hw ↦ ?_, fun s hs0 hs2 ↦ ?_⟩
    · have hwpos : 0 < w.im := by linarith
      have hG := IsH2Upper.enorm_sq_le hd (C := C') hbd hwpos
      have hG' : ‖g w / E w‖ ^ 2 ≤ 4 / (Real.pi * w.im) * C' :=
        real_sq_le_of_enorm (by positivity) hG
      have hf' : ‖g w‖ ^ 2 ≤ (C * Real.exp (Real.pi * w.im)) ^ 2 * ‖g w / E w‖ ^ 2 := by
        have := hpt w hwpos
        rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, ← ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
        exact this
      have h4 : 4 / (Real.pi * w.im) * C' ≤ 4 / Real.pi * C' := by
        have : Real.pi ≤ Real.pi * w.im := by nlinarith [Real.pi_pos]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) Real.pi_pos this)
          C'.coe_nonneg
      calc ‖g w‖ ^ 2 ≤ (C * Real.exp (Real.pi * w.im)) ^ 2 * ‖g w / E w‖ ^ 2 := hf'
        _ ≤ (C * Real.exp (Real.pi * w.im)) ^ 2 * (4 / Real.pi * C') := by
          gcongr; exact hG'.trans h4
        _ = (4 / Real.pi * C' * C ^ 2) * Real.exp (2 * Real.pi * w.im) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          have : ((2 : ℕ) : ℝ) * (Real.pi * w.im) = 2 * Real.pi * w.im := by push_cast; ring
          rw [this]; ring
    · calc ∫⁻ x : ℝ, ‖g ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2
          ≤ ∫⁻ x : ℝ, ENNReal.ofReal (C ^ 2 * Real.exp (4 * Real.pi)) *
              ‖g ((x : ℂ) + (s : ℂ) * I) / E ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2 := by
            refine lintegral_mono fun x ↦ (hpt _ (by simpa using hs0)).trans ?_
            gcongr
            simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
              Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
            rw [mul_pow, ← Real.exp_nat_mul]
            have : ((2 : ℕ) : ℝ) * (Real.pi * s) ≤ 4 * Real.pi := by
              push_cast; nlinarith [Real.pi_pos]
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) (sq_nonneg C)
        _ = ENNReal.ofReal (C ^ 2 * Real.exp (4 * Real.pi)) *
              ∫⁻ x : ℝ, ‖g ((x : ℂ) + (s : ℂ) * I) / E ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2 := by
            rw [lintegral_const_mul']; exact ENNReal.ofReal_ne_top
        _ ≤ _ := by gcongr; exact hbd s hs0
  have hf1 := hgen f C₁ hd1 h1
  have hf2 := hgen (fstar f) C₂ hd2 h2
  have hπ := Real.pi_pos
  have hC₁ : (0 : ℝ) ≤ C₁ := C₁.coe_nonneg
  have hC₂ : (0 : ℝ) ≤ C₂ := C₂.coe_nonneg
  have he4 : 1 ≤ Real.exp (4 * Real.pi) := Real.one_le_exp (by positivity)
  set K : ℝ := 4 / Real.pi * ((C₁ : ℝ) + C₂) * C ^ 2 * (1 + Real.exp (4 * Real.pi)) with hK
  have hKnn : 0 ≤ K := by positivity
  refine ⟨K, hKnn, fun z ↦ ?_⟩
  have hexp1 : 1 ≤ Real.exp (2 * Real.pi * |z.im|) := Real.one_le_exp (by positivity)
  have hbase : ∀ D : ℝ≥0, (D : ℝ) ≤ (C₁ : ℝ) + C₂ → 4 / Real.pi * D * C ^ 2 ≤ K := by
    intro D hD
    rw [hK]
    have h1 : 0 ≤ 4 / Real.pi * C ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hD h1, Real.exp_pos (4 * Real.pi)]
  by_cases hz1 : 1 ≤ z.im
  · have := (hf1.1 z hz1)
    rw [abs_of_pos (by linarith)]
    calc ‖f z‖ ^ 2 ≤ (4 / Real.pi * C₁ * C ^ 2) * Real.exp (2 * Real.pi * z.im) := this
      _ ≤ K * Real.exp (2 * Real.pi * z.im) := by
        gcongr; exact hbase C₁ (by linarith)
  by_cases hz2 : z.im ≤ -1
  · have hu : 1 ≤ (conj z).im := by simp; linarith
    have := hf2.1 (conj z) hu
    have hn : ‖fstar f (conj z)‖ = ‖f z‖ := by rw [norm_fstar, Complex.conj_conj]
    rw [hn] at this
    have hi : (conj z).im = |z.im| := by
      rw [abs_of_nonpos (by linarith)]; simp
    rw [hi] at this
    calc ‖f z‖ ^ 2 ≤ (4 / Real.pi * C₂ * C ^ 2) * Real.exp (2 * Real.pi * |z.im|) := this
      _ ≤ K * Real.exp (2 * Real.pi * |z.im|) := by
        gcongr; exact hbase C₂ (by linarith)
  -- the strip `|Im z| < 1`
  push Not at hz1 hz2
  set K₀ : ℝ≥0∞ := ENNReal.ofReal (C ^ 2 * Real.exp (4 * Real.pi)) * ((C₁ + C₂ : ℝ≥0) : ℝ≥0∞) with hK₀
  have hae : ∀ᵐ s : ℝ, s ≠ 0 := by rw [ae_iff]; simp
  have hlines : ∀ᵐ s : ℝ, s ∈ Ioo (z.im - 1) (z.im + 1) →
      ∫⁻ x : ℝ, ‖f ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2 ≤ K₀ := by
    filter_upwards [hae] with s hs0 hsI
    have hs2 : |s| < 2 := by
      rw [abs_lt]; constructor <;> linarith [hsI.1, hsI.2, abs_lt.mp (show |z.im| < 1 from abs_lt.mpr ⟨by linarith, by linarith⟩)]
    rcases lt_or_gt_of_ne hs0 with hneg | hpos
    · have hb := hf2.2 (-s) (by linarith) (by linarith [abs_lt.mp hs2])
      refine le_trans (le_of_eq ?_) (hb.trans ?_)
      · refine lintegral_congr fun x ↦ ?_
        have hn : ‖f ((x : ℂ) + (s : ℂ) * I)‖ =
            ‖fstar f ((x : ℂ) + ((-s : ℝ) : ℂ) * I)‖ := by
          rw [norm_fstar]
          congr 1
          apply Complex.ext <;> simp
        rw [← ofReal_norm, ← ofReal_norm (fstar f _), hn]
      · rw [hK₀]; exact mul_le_mul_right (ENNReal.coe_le_coe.mpr le_add_self) _
    · have hb := hf1.2 s hpos (by linarith [abs_lt.mp hs2])
      refine hb.trans ?_
      rw [hK₀]; exact mul_le_mul_right (ENNReal.coe_le_coe.mpr le_self_add) _
  have hmain := enorm_sq_le_of_lines (G := f) (c := z) (r := 1) one_pos hfd.differentiableOn hlines
  have hreal : ‖f z‖ ^ 2 ≤ 2 / (Real.pi * 1) * (C ^ 2 * Real.exp (4 * Real.pi)) * ((C₁ + C₂ : ℝ≥0) : ℝ) := by
    apply real_sq_le_of_enorm (by positivity) (C := C₁ + C₂)
    rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    rwa [hK₀] at hmain
  have hle : 2 / (Real.pi * 1) * (C ^ 2 * Real.exp (4 * Real.pi)) * ((C₁ + C₂ : ℝ≥0) : ℝ) ≤ K := by
    push_cast
    rw [hK]
    have h0 : 0 ≤ ((C₁ : ℝ) + C₂) * C ^ 2 := by positivity
    have : 2 / (Real.pi * 1) = 2 / Real.pi := by rw [mul_one]
    rw [this]
    have e1 : 2 / Real.pi * (C ^ 2 * Real.exp (4 * Real.pi)) * ((C₁ : ℝ) + C₂) =
        2 / Real.pi * (((C₁ : ℝ) + C₂) * C ^ 2) * Real.exp (4 * Real.pi) := by ring
    have e2 : 4 / Real.pi * ((C₁ : ℝ) + C₂) * C ^ 2 * (1 + Real.exp (4 * Real.pi)) =
        4 / Real.pi * (((C₁ : ℝ) + C₂) * C ^ 2) * (1 + Real.exp (4 * Real.pi)) := by ring
    rw [e1, e2]
    have h2 : 0 ≤ 4 / Real.pi * (((C₁ : ℝ) + C₂) * C ^ 2) := by positivity
    have h3 : 2 / Real.pi * (((C₁ : ℝ) + C₂) * C ^ 2) ≤ 4 / Real.pi * (((C₁ : ℝ) + C₂) * C ^ 2) := by
      gcongr; norm_num
    nlinarith [Real.exp_pos (4 * Real.pi)]
  calc ‖f z‖ ^ 2 ≤ K := hreal.trans hle
    _ = K * 1 := (mul_one _).symm
    _ ≤ K * Real.exp (2 * Real.pi * |z.im|) := by gcongr

theorem memLp_two_of_lintegral_lt_top {g : ℝ → ℂ} (hg : Continuous g)
    (h : ∫⁻ x : ℝ, ‖g x‖ₑ ^ 2 < ⊤) : MemLp g 2 := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hg.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

/-- `PW ⊆ H(E)` with `‖f‖²_E ≤ c⁻² ‖f‖²` and `‖f‖²_E ≥ C⁻² ‖f‖²`. -/
theorem memHE_of_memPW (hPW : PaleyWienerThm) {E : ℂ → ℂ} (hE : IsHB E) {c C : ℝ} (hc : 0 < c)
    (hcomp : ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im))
    {f : ℂ → ℂ} (hf : MemPW f) :
    MemHE E f ∧ heNormSq E f ≤ ENNReal.ofReal (c ^ 2)⁻¹ * pwNormSq f ∧
      ENNReal.ofReal (C ^ 2)⁻¹ * pwNormSq f ≤ heNormSq E f := by
  have hlow : ∀ z : ℂ, 0 ≤ z.im → c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ := fun z hz ↦ (hcomp z hz).1
  have hmem : MemHE E f :=
    ⟨hf.1, isH2Upper_div_of_memPW hPW hE.1 hc hlow hf,
      isH2Upper_div_of_memPW hPW hE.1 hc hlow hf.fstar⟩
  have hC : 0 < C := by
    have := hcomp 0 (by simp)
    simp only [Complex.zero_im, mul_zero, Real.exp_zero, mul_one] at this
    linarith [this.1, this.2]
  have hreal : ∀ t : ℝ, c ≤ ‖E (t : ℂ)‖ ∧ ‖E (t : ℂ)‖ ≤ C := by
    intro t
    have := hcomp (t : ℂ) (by simp)
    simpa using this
  refine ⟨hmem, ?_, ?_⟩
  · unfold heNormSq pwNormSq
    calc ∫⁻ t : ℝ, ‖f (t : ℂ) / E (t : ℂ)‖ₑ ^ 2
        ≤ ∫⁻ t : ℝ, ENNReal.ofReal (c ^ 2)⁻¹ * ‖f (t : ℂ)‖ₑ ^ 2 :=
          lintegral_mono fun t ↦ enorm_div_sq_le hc (hreal t).1
      _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  · unfold heNormSq pwNormSq
    calc ENNReal.ofReal (C ^ 2)⁻¹ * ∫⁻ t : ℝ, ‖f (t : ℂ)‖ₑ ^ 2
        = ∫⁻ t : ℝ, ENNReal.ofReal (C ^ 2)⁻¹ * ‖f (t : ℂ)‖ₑ ^ 2 := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := lintegral_mono fun t ↦
          le_enorm_div_sq (norm_pos_iff.mp (lt_of_lt_of_le hc (hreal t).1)) (hreal t).2

/-- `H(E) ⊆ PW` with `‖f‖²_{PW} ≤ C² ‖f‖²_E`. -/
theorem memPW_of_memHE (hPW : PaleyWienerThm) {E : ℂ → ℂ} (hE : IsHB E) {c C : ℝ} (hc : 0 < c)
    (hcomp : ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im))
    {f : ℂ → ℂ} (hf : MemHE E f) :
    MemPW f ∧ pwNormSq f ≤ ENNReal.ofReal (C ^ 2) * heNormSq E f := by
  have hlow : ∀ z : ℂ, 0 ≤ z.im → c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ := fun z hz ↦ (hcomp z hz).1
  have hC : 0 < C := by
    have := hcomp 0 (by simp)
    simp only [Complex.zero_im, mul_zero, Real.exp_zero, mul_one] at this
    linarith [this.1, this.2]
  have hreal : ∀ t : ℝ, c ≤ ‖E (t : ℂ)‖ ∧ ‖E (t : ℂ)‖ ≤ C := by
    intro t
    have := hcomp (t : ℂ) (by simp)
    simpa using this
  have hE0 : ∀ t : ℝ, E (t : ℂ) ≠ 0 := fun t ↦
    norm_pos_iff.mp (lt_of_lt_of_le hc (hreal t).1)
  obtain ⟨K, hK0, hK⟩ := norm_sq_le_of_memHE hE hc hcomp hf
  obtain ⟨hfd, ⟨hd1, C₁, h1⟩, -⟩ := hf
  -- Fatou
  have hcont : ∀ t : ℝ, ContinuousAt (fun z ↦ f z / E z) (t : ℂ) := fun t ↦
    hfd.continuous.continuousAt.div hE.1.continuous.continuousAt (hE0 t)
  have hF := lintegral_real_le_of_isH2 hd1 hcont h1
  have hnorm : pwNormSq f ≤ ENNReal.ofReal (C ^ 2) * heNormSq E f := by
    unfold pwNormSq heNormSq
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun t ↦ enorm_sq_le_mul (hE0 t) (hreal t).2
  have hfin : pwNormSq f < ⊤ :=
    lt_of_le_of_lt hnorm (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt hF ENNReal.coe_lt_top))
  refine ⟨⟨hfd, ?_, memLp_two_of_lintegral_lt_top (hfd.continuous.comp Complex.continuous_ofReal) hfin⟩, hnorm⟩
  intro ε hε
  refine ⟨Real.sqrt K, fun z ↦ ?_⟩
  have h2 := hK z
  have h3 : ‖f z‖ ≤ Real.sqrt K * Real.exp (Real.pi * |z.im|) := by
    have : (‖f z‖) ^ 2 ≤ (Real.sqrt K * Real.exp (Real.pi * |z.im|)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK0, ← Real.exp_nat_mul]
      have : ((2 : ℕ) : ℝ) * (Real.pi * |z.im|) = 2 * Real.pi * |z.im| := by push_cast; ring
      rw [this]; exact h2
    exact le_of_sq_le_sq this (by positivity)
  refine h3.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.sqrt_nonneg _))
  have : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  nlinarith [Real.pi_pos, norm_nonneg z]

/-- **The "evident fact"** (p. 799): if `E ∈ \overline{HB}` and `|E(z)| ≃ e^{π Im z}` for
`Im z ≥ 0`, then `H(E) = PW`. -/
theorem heEqPW_of_comparable (hPW : PaleyWienerThm) {E : ℂ → ℂ} (hE : IsHB E)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) :
    HEEqPW E := by
  obtain ⟨c, C, hc, hcomp⟩ := hcomp
  have hC : 0 < C := by
    have := hcomp 0 (by simp)
    simp only [Complex.zero_im, mul_zero, Real.exp_zero, mul_one] at this
    linarith [this.1, this.2]
  refine ⟨fun f ↦ ⟨fun hf ↦ (memPW_of_memHE hPW hE hc hcomp hf).1,
    fun hf ↦ (memHE_of_memPW hPW hE hc hcomp hf).1⟩, ((C ^ 2)⁻¹).toNNReal, ((c ^ 2)⁻¹).toNNReal,
    by simpa using pow_pos hC 2, fun f hf ↦ ?_⟩
  obtain ⟨-, h1, h2⟩ := memHE_of_memPW hPW hE hc hcomp hf
  exact ⟨h2, h1⟩

end FF
