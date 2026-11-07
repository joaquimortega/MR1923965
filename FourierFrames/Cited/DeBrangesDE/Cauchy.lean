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
  sorry

/-- `∫_ℝ dt / ((t - a)² + y²) = π / y` for `y > 0`. -/
theorem integral_inv_sq_add_sq (a : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ t : ℝ, ((t - a) ^ 2 + y ^ 2)⁻¹ = Real.pi / y := by
  sorry

/-- `‖t + iy - w‖² = (t - Re w)² + (y - Im w)²`. -/
theorem norm_sq_line_sub (t y : ℝ) (w : ℂ) :
    ‖(t : ℂ) + (y : ℂ) * I - w‖ ^ 2 = (t - w.re) ^ 2 + (y - w.im) ^ 2 := by
  sorry

/-- For `‖z - w‖ ≥ r > 0`: `‖z - w‖⁻² ≤ 2 / ((Re z - Re w)² + r²)`. -/
theorem inv_norm_sq_le_of_le {z w : ℂ} {r : ℝ} (hr : 0 < r) (hzw : r ≤ ‖z - w‖) :
    (‖z - w‖ ^ 2)⁻¹ ≤ 2 * ((z.re - w.re) ^ 2 + r ^ 2)⁻¹ := by
  sorry

/-! ## 1.2 Basic facts on `IsH2Cont` -/

/-- `F` is continuous on the closed upper half-plane. -/
theorem IsH2Cont.continuousOn {F : ℂ → ℂ} (hF : IsH2Cont F) :
    ContinuousOn F {z : ℂ | 0 ≤ z.im} := by
  sorry

/-- Uniform `L²` bound on all lines `Im z = y ≥ 0` (for `y = 0` by the Fatou step
`lintegral_real_le_of_isH2`). -/
theorem IsH2Cont.exists_bound {F : ℂ → ℂ} (hF : IsH2Cont F) :
    ∃ C : ℝ≥0, ∀ y : ℝ, 0 ≤ y → ∫⁻ x : ℝ, ‖F ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ C := by
  sorry

/-- The boundary function of `F ∈ IsH2Cont` is in `L²(ℝ)`. -/
theorem IsH2Cont.lintegral_real_lt_top {F : ℂ → ℂ} (hF : IsH2Cont F) :
    ∫⁻ t : ℝ, ‖F (t : ℂ)‖ₑ ^ 2 < ⊤ := by
  sorry

theorem IsH2Cont.memLp_line {F : ℂ → ℂ} (hF : IsH2Cont F) {y : ℝ} (hy : 0 ≤ y) :
    MemLp (fun x : ℝ ↦ F ((x : ℂ) + (y : ℂ) * I)) 2 := by
  sorry

theorem IsH2Cont.memLp_real {F : ℂ → ℂ} (hF : IsH2Cont F) :
    MemLp (fun t : ℝ ↦ F (t : ℂ)) 2 := by
  sorry

theorem IsH2Cont.add {F G : ℂ → ℂ} (hF : IsH2Cont F) (hG : IsH2Cont G) :
    IsH2Cont (fun z ↦ F z + G z) := by
  sorry

theorem IsH2Cont.const_mul {F : ℂ → ℂ} (hF : IsH2Cont F) (c : ℂ) :
    IsH2Cont (fun z ↦ c * F z) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
