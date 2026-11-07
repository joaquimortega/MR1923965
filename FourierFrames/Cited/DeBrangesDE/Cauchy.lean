import FourierFrames.HB.Comparable

/-!
# P3 — Cauchy and Poisson formulas for `H²(ℂ₊)` functions continuous up to `ℝ`

See `blueprint/P3_DeBrangesDE.md`, §1.  No boundary-value theory: the class `IsH2Cont` consists of
`H²` functions that are continuous at every real point, so that their "boundary function" is
simply their restriction to `ℝ`.  The only inputs are the rectangle Cauchy–Goursat theorem of
Mathlib, the `L²`-line bound of `IsH2Upper`, and the Fatou step `lintegral_real_le_of_isH2` of
`HB/Comparable`.

Structure:
* §1.1 explicit integrals (`∫ dt/((t-a)²+y²) = π/y`);
* §1.2 basic facts on `IsH2Cont` (continuity on the closed half-plane, `L²` on every line `y ≥ 0`,
  a good sequence of vertical sides);
* §1.3 the **half-plane Cauchy–Goursat theorem** `IsH2Cont.integral_eq_zero_of_dominated`: if `G`
  is continuous on `{Im ≥ 0}`, holomorphic on `{Im > 0}` and `|G| ≤ |F|/|z-w₀| + A/|z-w₀|²` far
  from `w₀` for some `F ∈ IsH2Cont`, then `∫_ℝ G = 0` (rectangles `[-Rₙ,Rₙ]×[0,Y]`, sides along a
  good sequence `Rₙ`, then `Y → ∞`);
* §1.4 the Cauchy formulas: `w ∈ ℂ₋` (`integral_div_lower`), `w ∈ ℂ₊` (`cauchy_upper`), and the
  **regularized formula at a real point** (`cauchy_real`), which replaces any boundary limit;
* §1.5 the Poisson formula and the bound of line integrals by the boundary norm.

These lemmas are written for a general `F`, so that the proof of Theorem C (P4) can reuse them.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- `H²(ℂ₊)` functions that are continuous at every real point. -/
def IsH2Cont (F : ℂ → ℂ) : Prop :=
  IsH2Upper F ∧ ∀ t : ℝ, ContinuousAt F (t : ℂ)

/-! ## 1.1 Explicit integrals -/

theorem integrable_inv_sq_add_sq (a : ℝ) {y : ℝ} (hy : y ≠ 0) :
    Integrable fun t : ℝ ↦ ((t - a) ^ 2 + y ^ 2)⁻¹ := by
  have h := ((integrable_inv_one_add_mul_sq (inv_ne_zero hy)).comp_sub_right a).const_mul
    (y ^ 2)⁻¹
  refine h.congr (Eventually.of_forall fun t ↦ ?_)
  simp only
  field_simp
  ring

/-- `∫_ℝ dt / ((t - a)² + y²) = π / y` for `y > 0`. -/
theorem integral_inv_sq_add_sq (a : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ t : ℝ, ((t - a) ^ 2 + y ^ 2)⁻¹ = Real.pi / y := by
  have h : (fun t : ℝ ↦ ((t - a) ^ 2 + y ^ 2)⁻¹) =
      fun t ↦ (y ^ 2)⁻¹ * (fun s : ℝ ↦ (1 + (y⁻¹ * s) ^ 2)⁻¹) (t - a) := by
    funext t
    simp only
    field_simp
    ring
  rw [h, integral_const_mul, integral_sub_right_eq_self (fun s : ℝ ↦ (1 + (y⁻¹ * s) ^ 2)⁻¹) a,
    integral_univ_inv_one_add_mul_sq, abs_inv, abs_of_pos hy]
  field_simp

/-- `‖t + iy - w‖² = (t - Re w)² + (y - Im w)²`. -/
theorem norm_sq_line_sub (t y : ℝ) (w : ℂ) :
    ‖(t : ℂ) + (y : ℂ) * I - w‖ ^ 2 = (t - w.re) ^ 2 + (y - w.im) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

/-- For `‖z - w‖ ≥ r > 0`: `‖z - w‖⁻² ≤ 2 / ((Re z - Re w)² + r²)`. -/
theorem inv_norm_sq_le_of_le {z w : ℂ} {r : ℝ} (hr : 0 < r) (hzw : r ≤ ‖z - w‖) :
    (‖z - w‖ ^ 2)⁻¹ ≤ 2 * ((z.re - w.re) ^ 2 + r ^ 2)⁻¹ := by
  have hd : 0 < ‖z - w‖ := hr.trans_le hzw
  have h1 : |z.re - w.re| ≤ ‖z - w‖ := by simpa using Complex.abs_re_le_norm (z - w)
  have h2 : (z.re - w.re) ^ 2 ≤ ‖z - w‖ ^ 2 := by
    rw [← sq_abs]; gcongr
  have h3 : r ^ 2 ≤ ‖z - w‖ ^ 2 := by gcongr
  have hpos : 0 < (z.re - w.re) ^ 2 + r ^ 2 := by positivity
  calc (‖z - w‖ ^ 2)⁻¹ = 2 * (2 * ‖z - w‖ ^ 2)⁻¹ := by field_simp
    _ ≤ 2 * ((z.re - w.re) ^ 2 + r ^ 2)⁻¹ := by gcongr; linarith

/-! ## 1.2 Basic facts on `IsH2Cont` -/

/-- `F` is continuous on the closed upper half-plane. -/
theorem IsH2Cont.continuousOn {F : ℂ → ℂ} (hF : IsH2Cont F) :
    ContinuousOn F {z : ℂ | 0 ≤ z.im} := by
  intro z hz
  rcases (show (0 : ℝ) ≤ z.im from hz).lt_or_eq with h | h
  · exact (hF.1.1.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds h)).continuousAt.continuousWithinAt
  · have hz' : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [← h])
    have := (hF.2 z.re).continuousWithinAt (s := {z : ℂ | 0 ≤ z.im})
    rwa [hz'] at this

/-- Uniform `L²` bound on all lines `Im z = y ≥ 0` (for `y = 0` by the Fatou step
`lintegral_real_le_of_isH2`). -/
theorem IsH2Cont.exists_bound {F : ℂ → ℂ} (hF : IsH2Cont F) :
    ∃ C : ℝ≥0, ∀ y : ℝ, 0 ≤ y → ∫⁻ x : ℝ, ‖F ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ C := by
  obtain ⟨hd, C, hC⟩ := hF.1
  refine ⟨C, fun y hy ↦ ?_⟩
  rcases hy.lt_or_eq with h | h
  · exact hC y h
  · subst h
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    exact lintegral_real_le_of_isH2 hd hF.2 hC

/-- The boundary function of `F ∈ IsH2Cont` is in `L²(ℝ)`. -/
theorem IsH2Cont.lintegral_real_lt_top {F : ℂ → ℂ} (hF : IsH2Cont F) :
    ∫⁻ t : ℝ, ‖F (t : ℂ)‖ₑ ^ 2 < ⊤ := by
  obtain ⟨C, hC⟩ := hF.exists_bound
  have := hC 0 le_rfl
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
  exact this.trans_lt ENNReal.coe_lt_top

theorem IsH2Cont.memLp_line {F : ℂ → ℂ} (hF : IsH2Cont F) {y : ℝ} (hy : 0 ≤ y) :
    MemLp (fun x : ℝ ↦ F ((x : ℂ) + (y : ℂ) * I)) 2 := by
  obtain ⟨C, hC⟩ := hF.exists_bound
  refine memLp_two_of_lintegral_lt_top ?_ ((hC y hy).trans_lt ENNReal.coe_lt_top)
  exact hF.continuousOn.comp_continuous (by fun_prop) (fun x ↦ by simpa using hy)

theorem IsH2Cont.memLp_real {F : ℂ → ℂ} (hF : IsH2Cont F) :
    MemLp (fun t : ℝ ↦ F (t : ℂ)) 2 := by
  simpa using hF.memLp_line le_rfl

theorem IsH2Cont.add {F G : ℂ → ℂ} (hF : IsH2Cont F) (hG : IsH2Cont G) :
    IsH2Cont (fun z ↦ F z + G z) := by
  exact ⟨hF.1.add hG.1, fun t ↦ (hF.2 t).add (hG.2 t)⟩

theorem IsH2Cont.const_mul {F : ℂ → ℂ} (hF : IsH2Cont F) (c : ℂ) :
    IsH2Cont (fun z ↦ c * F z) := by
  exact ⟨hF.1.const_mul c, fun t ↦ continuousAt_const.mul (hF.2 t)⟩

/-- Tonelli on the strip `[0, Y]`: `∫_ℝ ∫_0^Y |F(x+iy)|² dy dx ≤ Y C`.  Hence there is a sequence
`Rₙ → ∞` along which the `L²` norms of `F` on the vertical sides `±Rₙ + i(0, Y]` are `≤ 1`. -/
theorem IsH2Cont.exists_side_seq {F : ℂ → ℂ} (hF : IsH2Cont F) {Y : ℝ} (hY : 0 < Y) :
    ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧ ∀ n, ∫⁻ y in Ioc (0 : ℝ) Y,
        (‖F ((R n : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 + ‖F (((-R n : ℝ) : ℂ) + (y : ℂ) * I)‖ₑ ^ 2) ≤ 1 := by
  sorry

/-! ## 1.3 The half-plane Cauchy–Goursat theorem -/

/-- **Contour shift across a strip.**  `G` continuous on the closed strip `0 ≤ Im z ≤ Y`,
holomorphic inside, integrable on the two boundary lines, with vertical sides tending to `0` along
a sequence `Rₙ → ∞`: then `∫_ℝ G(x) dx = ∫_ℝ G(x + iY) dx` (rectangle Cauchy–Goursat
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` on
`[-Rₙ, Rₙ] × [0, Y]` and `intervalIntegral_tendsto_integral`). -/
theorem integral_eq_integral_line_of_sides {G : ℂ → ℂ} {Y : ℝ} (hY : 0 < Y)
    (hc : ContinuousOn G {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Y})
    (hd : ∀ z : ℂ, 0 < z.im → z.im < Y → DifferentiableAt ℂ G z)
    (h0 : Integrable fun x : ℝ ↦ G (x : ℂ))
    (h1 : Integrable fun x : ℝ ↦ G ((x : ℂ) + (Y : ℂ) * I))
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop)
    (hside : Tendsto (fun n ↦ ∫⁻ y in Ioc (0 : ℝ) Y,
      (‖G ((R n : ℂ) + (y : ℂ) * I)‖ₑ + ‖G (((-R n : ℝ) : ℂ) + (y : ℂ) * I)‖ₑ)) atTop (𝓝 0)) :
    ∫ x : ℝ, G (x : ℂ) = ∫ x : ℝ, G ((x : ℂ) + (Y : ℂ) * I) := by
  sorry

section Dominated

variable {F G : ℂ → ℂ} {w₀ : ℂ} {A : ℝ}

/-- Line integrability under the domination hypothesis (continuity near `w₀`, AM–GM far away). -/
theorem IsH2Cont.integrable_line_of_dominated (hF : IsH2Cont F)
    (hc : ContinuousOn G {z : ℂ | 0 ≤ z.im})
    (hdom : ∀ z : ℂ, 0 ≤ z.im → 1 ≤ ‖z - w₀‖ → ‖G z‖ ≤ ‖F z‖ / ‖z - w₀‖ + A / ‖z - w₀‖ ^ 2)
    {y : ℝ} (hy : 0 ≤ y) :
    Integrable fun x : ℝ ↦ G ((x : ℂ) + (y : ℂ) * I) := by
  sorry

/-- The top side: `∫_ℝ G(x + iY) dx → 0` as `Y → ∞`. -/
theorem IsH2Cont.tendsto_integral_line_of_dominated (hF : IsH2Cont F)
    (hc : ContinuousOn G {z : ℂ | 0 ≤ z.im})
    (hdom : ∀ z : ℂ, 0 ≤ z.im → 1 ≤ ‖z - w₀‖ → ‖G z‖ ≤ ‖F z‖ / ‖z - w₀‖ + A / ‖z - w₀‖ ^ 2) :
    Tendsto (fun Y : ℝ ↦ ∫ x : ℝ, G ((x : ℂ) + (Y : ℂ) * I)) atTop (𝓝 0) := by
  sorry

/-- The vertical sides tend to `0` along the sequence of `IsH2Cont.exists_side_seq`. -/
theorem IsH2Cont.exists_sides_of_dominated (hF : IsH2Cont F)
    (hdom : ∀ z : ℂ, 0 ≤ z.im → 1 ≤ ‖z - w₀‖ → ‖G z‖ ≤ ‖F z‖ / ‖z - w₀‖ + A / ‖z - w₀‖ ^ 2)
    {Y : ℝ} (hY : 0 < Y) :
    ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧ Tendsto (fun n ↦ ∫⁻ y in Ioc (0 : ℝ) Y,
      (‖G ((R n : ℂ) + (y : ℂ) * I)‖ₑ + ‖G (((-R n : ℝ) : ℂ) + (y : ℂ) * I)‖ₑ)) atTop (𝓝 0) := by
  sorry

/-- **Half-plane Cauchy–Goursat theorem.**  If `G` is continuous on `{Im ≥ 0}`, holomorphic on
`{Im > 0}`, and dominated far from `w₀` by `|F|/|z - w₀| + A/|z - w₀|²` with `F ∈ IsH2Cont`,
then `∫_ℝ G = 0`. -/
theorem IsH2Cont.integral_eq_zero_of_dominated (hF : IsH2Cont F)
    (hc : ContinuousOn G {z : ℂ | 0 ≤ z.im}) (hd : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ G z)
    (hdom : ∀ z : ℂ, 0 ≤ z.im → 1 ≤ ‖z - w₀‖ → ‖G z‖ ≤ ‖F z‖ / ‖z - w₀‖ + A / ‖z - w₀‖ ^ 2) :
    ∫ x : ℝ, G (x : ℂ) = 0 := by
  sorry

end Dominated

/-! ## 1.4 The Cauchy formulas -/

/-- For `Im c < 0 ≤ Im z`, `0 ≤ Im w`: `|z - c| ≥ κ |z - w|` with
`κ = min (1/2) (-Im c / (2 |w - c|))`. -/
theorem norm_sub_ge_mul_norm_sub {z w c : ℂ} (hz : 0 ≤ z.im) (hc : c.im < 0) (hw : 0 ≤ w.im) :
    min (1 / 2) (-c.im / (2 * ‖w - c‖)) * ‖z - w‖ ≤ ‖z - c‖ := by
  have hδ : 0 < ‖w - c‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    rw [h] at hw
    linarith
  have hm : -c.im ≤ ‖z - c‖ := by
    have := Complex.im_le_norm (z - c)
    simp only [Complex.sub_im] at this
    linarith
  have htri : ‖z - w‖ ≤ ‖z - c‖ + ‖w - c‖ := by
    calc ‖z - w‖ = ‖(z - c) - (w - c)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  by_cases h : 2 * ‖w - c‖ ≤ ‖z - w‖
  · calc min (1 / 2) (-c.im / (2 * ‖w - c‖)) * ‖z - w‖ ≤ 1 / 2 * ‖z - w‖ := by
          gcongr; exact min_le_left _ _
      _ ≤ ‖z - c‖ := by linarith
  · rw [not_le] at h
    have hk : 0 ≤ -c.im / (2 * ‖w - c‖) := div_nonneg (by linarith) (by positivity)
    calc min (1 / 2) (-c.im / (2 * ‖w - c‖)) * ‖z - w‖
        ≤ (-c.im / (2 * ‖w - c‖)) * ‖z - w‖ := by gcongr; exact min_le_right _ _
      _ ≤ (-c.im / (2 * ‖w - c‖)) * (2 * ‖w - c‖) := by gcongr
      _ = -c.im := by field_simp
      _ ≤ _ := hm

/-- `F(t)/(t - w)` is integrable on `ℝ` for nonreal `w` (AM–GM:
`|F|/|t-w| ≤ (|F|² + |t-w|⁻²)/2`). -/
theorem IsH2Cont.integrable_div {F : ℂ → ℂ} (hF : IsH2Cont F) {w : ℂ} (hw : w.im ≠ 0) :
    Integrable fun t : ℝ ↦ F (t : ℂ) / ((t : ℂ) - w) := by
  sorry

/-- **Cauchy formula, `w ∈ ℂ₋`**: `∫_ℝ F(t)/(t - w) dt = 0`. -/
theorem IsH2Cont.integral_div_lower {F : ℂ → ℂ} (hF : IsH2Cont F) {w : ℂ} (hw : w.im < 0) :
    ∫ t : ℝ, F (t : ℂ) / ((t : ℂ) - w) = 0 := by
  sorry

/-- The regularized function `G = dslope (F - F(w) (w - c)/(· - c)) w` is continuous on the closed
half-plane, holomorphic on the open one, and dominated by `|F|/|z - w| + A/|z - w|²` for
`|z - w| ≥ 1` with `A = |F(w)| |w - c| / κ` (`norm_sub_ge_mul_norm_sub`).  In particular it is
integrable on `ℝ`. -/
theorem IsH2Cont.integrable_dslope {F : ℂ → ℂ} (hF : IsH2Cont F) {w c : ℂ}
    (hw : 0 ≤ w.im) (hdw : DifferentiableAt ℂ F w) (hc : c.im < 0) :
    Integrable fun t : ℝ ↦ dslope (fun z ↦ F z - F w * ((w - c) / (z - c))) w (t : ℂ) := by
  sorry

/-- **Regularized Cauchy formula.**  For `Im w ≥ 0` with `F` differentiable at `w`, and
`Im c < 0`, the function `G = dslope (F - F(w) (w - c)/(· - c)) w` satisfies `∫_ℝ G = 0`. -/
theorem IsH2Cont.integral_dslope_eq_zero {F : ℂ → ℂ} (hF : IsH2Cont F) {w c : ℂ}
    (hw : 0 ≤ w.im) (hdw : DifferentiableAt ℂ F w) (hc : c.im < 0) :
    ∫ t : ℝ, dslope (fun z ↦ F z - F w * ((w - c) / (z - c))) w (t : ℂ) = 0 := by
  sorry

/-- The Cauchy kernel pairing: `∫_ℝ (w - w̄)/((t - w)(t - w̄)) dt = 2πi` for `w ∈ ℂ₊`. -/
theorem integral_cauchy_pair {w : ℂ} (hw : 0 < w.im) :
    ∫ t : ℝ, (w - conj w) / (((t : ℂ) - w) * ((t : ℂ) - conj w)) = 2 * Real.pi * I := by
  have h : ∀ t : ℝ, (w - conj w) / (((t : ℂ) - w) * ((t : ℂ) - conj w)) =
      (2 * w.im * I) * ((((t - w.re) ^ 2 + w.im ^ 2)⁻¹ : ℝ) : ℂ) := by
    intro t
    have e1 : ((t : ℂ) - w) * ((t : ℂ) - conj w) = (((t - w.re) ^ 2 + w.im ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;> ring
    rw [e1, Complex.sub_conj]
    push_cast
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_complex_ofReal, integral_inv_sq_add_sq w.re hw]
  have : (w.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  push_cast
  field_simp

/-- **Cauchy formula, `w ∈ ℂ₊`**: `∫_ℝ F(t)/(t - w) dt = 2πi F(w)`. -/
theorem IsH2Cont.cauchy_upper {F : ℂ → ℂ} (hF : IsH2Cont F) {w : ℂ} (hw : 0 < w.im) :
    ∫ t : ℝ, F (t : ℂ) / ((t : ℂ) - w) = 2 * Real.pi * I * F w := by
  sorry

/-- Integrability of the regularized integrand at a real point. -/
theorem IsH2Cont.integrable_reg_real {F : ℂ → ℂ} (hF : IsH2Cont F) {x : ℝ}
    (hdx : DifferentiableAt ℂ F x) :
    Integrable fun t : ℝ ↦ (F (t : ℂ) - F x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x) := by
  sorry

/-- **Cauchy formula at a real point** (regularized, `ψ(t) = i/(t - x + i)`, `ψ(x) = 1`):
`∫_ℝ (F(t) - F(x) ψ(t))/(t - x) dt = 0`. -/
theorem IsH2Cont.cauchy_real {F : ℂ → ℂ} (hF : IsH2Cont F) {x : ℝ}
    (hdx : DifferentiableAt ℂ F x) :
    ∫ t : ℝ, (F (t : ℂ) - F x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x) = 0 := by
  sorry

/-- `∫_ℝ 2i/((t - x)² + 1) dt = 2πi`: the constant term of the real-point decomposition. -/
theorem integral_two_I_div (x : ℝ) :
    ∫ t : ℝ, 2 * I / ((((t - x) ^ 2 + 1 : ℝ)) : ℂ) = 2 * Real.pi * I := by
  have h : ∀ t : ℝ, 2 * I / ((((t - x) ^ 2 + 1 : ℝ)) : ℂ) =
      (2 * I) * ((((t - x) ^ 2 + 1 ^ 2)⁻¹ : ℝ) : ℂ) := by
    intro t
    push_cast
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_complex_ofReal, integral_inv_sq_add_sq x one_pos]
  push_cast
  ring

/-! ## 1.5 Poisson formula, line integrals bounded by the boundary norm -/

/-- **Poisson formula**: `F(x + iy) = ∫ P_y(x - t) F(t) dt`, `P_y(s) = y / (π (s² + y²))`
(difference of `cauchy_upper` at `w` and `integral_div_lower` at `w̄`). -/
theorem IsH2Cont.poisson {F : ℂ → ℂ} (hF : IsH2Cont F) {w : ℂ} (hw : 0 < w.im) :
    F w = ∫ t : ℝ, ((w.im / (Real.pi * ((t - w.re) ^ 2 + w.im ^ 2)) : ℝ) : ℂ) * F (t : ℂ) := by
  sorry

/-- **Line integrals are bounded by the boundary norm**:
`∫ |F(x+iy)|² dx ≤ ∫ |F(t)|² dt` for `y > 0` (Cauchy–Schwarz for the probability density
`P_y(x - ·)` and Tonelli). -/
theorem IsH2Cont.lintegral_line_le {F : ℂ → ℂ} (hF : IsH2Cont F) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖F ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ ∫⁻ t : ℝ, ‖F (t : ℂ)‖ₑ ^ 2 := by
  sorry

end FF
