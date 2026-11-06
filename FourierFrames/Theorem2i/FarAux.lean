import FourierFrames.Theorem2i.BelowAbove

/-!
# M08 helper (fork D1): middle cells at distance `≥ K₀ d_n`
-/

open MeasureTheory Set Complex Filter Topology

noncomputable section

namespace FF.D1

open FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M : ℝ}

theorem abs_log_one_add_le {v : ℝ} (hv : |v| ≤ 1 / 2) : |Real.log (1 + v)| ≤ 2 * |v| := by
  have hv' := abs_le.1 hv
  have hpos : 0 < 1 + v := by linarith
  rw [abs_le]
  constructor
  · have h1 := Real.one_sub_inv_le_log_of_pos hpos
    have e : 1 - (1 + v)⁻¹ = v / (1 + v) := by field_simp; ring
    rw [e] at h1
    have h2 : -(2 * |v|) ≤ v / (1 + v) := by
      rw [le_div_iff₀ hpos]
      rcases le_total 0 v with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_nonpos h]; nlinarith
    linarith
  · have := Real.log_le_sub_one_of_pos hpos
    have := le_abs_self v
    linarith [abs_nonneg v]

/-- Real core estimate for `|z - z_n|² - |z - r_n|²`. -/
theorem delta_bound {r θ x y u : ℝ} (hr : 0 < r) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hy : 0 ≤ y)
    (hu : 0 ≤ u) (hu2 : (x - r) ^ 2 + y ^ 2 = u ^ 2) :
    |(x - r * Real.cos θ) ^ 2 + (y + r * Real.sin θ) ^ 2 - u ^ 2| ≤
      r * θ * θ * u + 5 / 4 * (r * θ) ^ 2 + 2 * y * (r * θ) := by
  set e := r - r * Real.cos θ with he
  set b := r * Real.sin θ with hb
  have he0 : 0 ≤ e := by
    have := Real.cos_le_one θ
    rw [he]; nlinarith
  have he1 : e ≤ r * θ * θ / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := θ)
    rw [he]; nlinarith
  have hb0 : 0 ≤ b := by
    have : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by
      have := Real.pi_gt_three; linarith)
    rw [hb]; positivity
  have hb1 : b ≤ r * θ := by
    have := Real.sin_le hθ0.le
    rw [hb]; nlinarith
  have hxr : |x - r| ≤ u :=
    abs_le.2 (abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg y]) hu)
  have hxr' := abs_le.1 hxr
  have hc : r * Real.cos θ = r - e := by rw [he]; ring
  rw [hc]
  have hΔ : (x - (r - e)) ^ 2 + (y + b) ^ 2 - u ^ 2 = 2 * e * (x - r) + e ^ 2 + 2 * y * b + b ^ 2 := by
    linear_combination hu2
  rw [hΔ]
  have t1 : |2 * e * (x - r)| ≤ r * θ * θ * u := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 2 * e)]
    nlinarith
  have t2 : e ^ 2 ≤ 1 / 4 * (r * θ) ^ 2 := by
    have h1 : e ^ 2 ≤ (r * θ * θ / 2) ^ 2 := by gcongr
    have h2 : (r * θ * θ / 2) ^ 2 = (r * θ) ^ 2 * θ ^ 2 / 4 := by ring
    have h3 : (r * θ) ^ 2 * θ ^ 2 ≤ (r * θ) ^ 2 := by
      have : θ ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (r * θ)]
    linarith
  have t3 : 2 * y * b ≤ 2 * y * (r * θ) := by nlinarith
  have t4 : b ^ 2 ≤ (r * θ) ^ 2 := by gcongr
  rw [abs_le]
  have := abs_le.1 t1
  constructor <;> nlinarith [sq_nonneg e, sq_nonneg b, mul_nonneg hy hb0]

theorem zPt_re_im (_h : RegData ψ t C M) {n : ℕ} (_hn : 1 ≤ n) :
    (zPt ψ t C n).re = rCentre ψ t n * Real.cos (cAngle ψ t C * cellLen t n / rCentre ψ t n) ∧
    (zPt ψ t C n).im = -(rCentre ψ t n * Real.sin (cAngle ψ t C * cellLen t n / rCentre ψ t n)) := by
  have e : -(Complex.I * (((cAngle ψ t C * cellLen t n / rCentre ψ t n : ℝ)) : ℂ)) =
      ((-(cAngle ψ t C * cellLen t n / rCentre ψ t n) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  unfold zPt
  rw [e]
  constructor
  · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, Real.sin_neg]; ring

theorem norm_sub_ofReal_sq (z : ℂ) (r : ℝ) : ‖z - (r : ℂ)‖ ^ 2 = (z.re - r) ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem log_norm_one_sub_div_of_ne {z w : ℂ} (hw : w ≠ 0) (hwz : ‖w - z‖ ≠ 0) :
    Real.log ‖1 - z / w‖ = Real.log ‖w - z‖ - Real.log ‖w‖ := by
  have e : 1 - z / w = (w - z) / w := by field_simp
  rw [e, norm_div, Real.log_div hwz (norm_ne_zero_iff.2 hw)]

/-- The point-mass term `B_n` for far cells. -/
theorem B_far (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) {ρ₁ : ℝ} (hρ₁ : 0 ≤ ρ₁) {z : ℂ}
    (hz : 0 ≤ z.im) (hfar : (8 + 2 * ρ₁) * cellLen t n ≤ ‖z - (rCentre ψ t n : ℂ)‖)
    (hur : ‖z - (rCentre ψ t n : ℂ)‖ ≤ (ρ₁ + 1) * rCentre ψ t n) :
    |Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖ - Real.log ‖1 - z / zPt ψ t C n‖| ≤
      (3 + ρ₁) * (cellLen t n ^ 2 / ‖z - (rCentre ψ t n : ℂ)‖ ^ 2) +
        2 * (cellLen t n * z.im / ‖z - (rCentre ψ t n : ℂ)‖ ^ 2) := by
  set r := rCentre ψ t n with hr
  set d := cellLen t n with hd
  set c := cAngle ψ t C with hc
  set u := ‖z - (r : ℂ)‖ with hu
  have hr0 : 0 < r := rCentre_pos ψ t n
  have hd0 : 0 < d := cellLen_pos h hn
  have hc0 : 0 < c := h.cAngle_pos
  have hc1 : c < 1 := c_lt_one h
  have hu0 : 0 < u := by
    have : 0 < (8 + 2 * ρ₁) * d := by positivity
    linarith
  set θ := c * d / r with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by
    have := h.angle_le hn
    have := Real.pi_lt_four
    linarith
  have hrθ : r * θ = c * d := by rw [hθ]; field_simp
  obtain ⟨hre0, him0⟩ := zPt_re_im h hn
  have hre : (zPt ψ t C n).re = r * Real.cos θ := hre0
  have him : (zPt ψ t C n).im = -(r * Real.sin θ) := him0
  have hu2 : (z.re - r) ^ 2 + z.im ^ 2 = u ^ 2 := (norm_sub_ofReal_sq z r).symm
  have hδ := delta_bound (r := r) (θ := θ) (x := z.re) (y := z.im) hr0 hθ0 hθ1 hz hu0.le
    hu2
  rw [hrθ] at hδ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by
    have := Real.pi_gt_three; linarith)
  -- Q
  set Q := ‖zPt ψ t C n - z‖ with hQ
  have hQ2 : Q ^ 2 = (z.re - r * Real.cos θ) ^ 2 + (z.im + r * Real.sin θ) ^ 2 := by
    rw [hQ, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, hre, him]
    ring
  have hQ0 : 0 < Q := by
    apply norm_pos_iff.2
    intro h0
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, him, Complex.zero_im] at this
    nlinarith [mul_pos hr0 hs]
  -- bounds on Δ
  set Δ := Q ^ 2 - u ^ 2 with hΔ
  have hΔ1 : |Δ| ≤ c * d * θ * u + 5 / 4 * (c * d) ^ 2 + 2 * z.im * (c * d) := by
    rw [hΔ, hQ2]
    exact hδ
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have hcd : (c * d) ^ 2 ≤ d ^ 2 := by
    calc (c * d) ^ 2 = c ^ 2 * d ^ 2 := by ring
      _ ≤ 1 * d ^ 2 := by gcongr
      _ = d ^ 2 := one_mul _
  have hrθθ : c * d * θ * u ≤ (ρ₁ + 1) * d ^ 2 := by
    have e : c * d * θ * u = (c * d) * (c * d) * (u / r) := by
      rw [hθ]; field_simp
    rw [e]
    have : u / r ≤ ρ₁ + 1 := by rw [div_le_iff₀ hr0]; exact hur
    have h1 : (c * d) * (c * d) ≤ d ^ 2 := by rw [← sq]; exact hcd
    calc (c * d) * (c * d) * (u / r) ≤ d ^ 2 * (ρ₁ + 1) := by
          apply mul_le_mul h1 this (by positivity) (by positivity)
      _ = _ := by ring
  have hyd : 2 * z.im * (c * d) ≤ 2 * (d * z.im) := by
    have : c * d ≤ d := by nlinarith
    have := mul_le_mul_of_nonneg_left this hz
    linarith
  have hΔ2 : |Δ| ≤ (3 + ρ₁) * d ^ 2 + 2 * (d * z.im) := by linarith [sq_nonneg d]
  -- |v| ≤ 1/2
  have hyu : z.im ≤ u := by
    have := Complex.abs_im_le_norm (z - (r : ℂ))
    simpa [abs_of_nonneg hz] using this
  have hdu : (8 + 2 * ρ₁) * d ≤ u := hfar
  have hΔ3 : |Δ| ≤ 5 / 16 * u ^ 2 := by
    have h1 : (3 + ρ₁) * d ≤ u / 2 := by linarith
    have h2 : (3 + ρ₁) * d * d ≤ u / 2 * d := mul_le_mul_of_nonneg_right h1 hd0.le
    have h8 : 8 * d ≤ u := by linarith [mul_nonneg hρ₁ hd0.le]
    have h3 : d * u ≤ u / 8 * u := by
      have := mul_le_mul_of_nonneg_right h8 hu0.le
      linarith
    have h4 : d * z.im ≤ d * u := mul_le_mul_of_nonneg_left hyu hd0.le
    linarith
  set v := Δ / u ^ 2 with hv
  have hv1 : |v| ≤ 1 / 2 := by
    rw [hv, abs_div, abs_of_pos (by positivity : 0 < u ^ 2), div_le_iff₀ (by positivity)]
    linarith [sq_nonneg u]
  have hQu : Q ^ 2 / u ^ 2 = 1 + v := by
    rw [hv, hΔ]; field_simp; ring
  -- the logs
  have hQne : ‖zPt ψ t C n - z‖ ≠ 0 := hQ0.ne'
  have hune : ‖(r : ℂ) - z‖ ≠ 0 := by
    rw [norm_sub_rev]; exact hu0.ne'
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hznz : zPt ψ t C n ≠ 0 := zPt_ne_zero h hn
  have hnz := h.norm_zPt hn
  have hr_norm : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
  rw [log_norm_one_sub_div_of_ne hrne hune, log_norm_one_sub_div_of_ne hznz hQne, hnz, hr_norm,
    norm_sub_rev (r : ℂ) z]
  have hlogQ : Real.log Q - Real.log u = Real.log (1 + v) / 2 := by
    rw [← hQu, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hB : Real.log u - Real.log r - (Real.log Q - Real.log r) = -(Real.log (1 + v) / 2) := by
    rw [← hlogQ]; ring
  rw [hB, abs_neg, abs_div, abs_two]
  have hl := abs_log_one_add_le hv1
  have hvb : |v| ≤ (3 + ρ₁) * (d ^ 2 / u ^ 2) + 2 * (d * z.im / u ^ 2) := by
    rw [hv, abs_div, abs_of_pos (by positivity : 0 < u ^ 2)]
    calc |Δ| / u ^ 2 ≤ ((3 + ρ₁) * d ^ 2 + 2 * (d * z.im)) / u ^ 2 := by gcongr
      _ = _ := by ring
  linarith

/-- Far cells (with `ρ₁ = 2 (1 + C)`, `K₀ = 8 + 2 ρ₁` unfolded). -/
theorem abs_cellTerm_far_aux (h : RegData ψ t C M) {n : ℕ} (hn : 2 ≤ n) {z : ℂ}
    (hz : 0 ≤ z.im) (hz1 : ‖z‖ ≤ 2 * (1 + C) * rCentre ψ t n)
    (hz2 : rCentre ψ t n ≤ 2 * (1 + C) * ‖z‖)
    (hfar : (8 + 2 * (2 * (1 + C))) * cellLen t n ≤ ‖z - (rCentre ψ t n : ℂ)‖) :
    |cellTerm ψ t C n z| ≤
      (2 * (2 * (1 + C)) * (1 + C) ^ 3 + (3 + 2 * (1 + C))) *
          (cellLen t n ^ 2 / ‖z - (rCentre ψ t n : ℂ)‖ ^ 2)
        + 2 * (cellLen t n * z.im / ‖z - (rCentre ψ t n : ℂ)‖ ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hC := h.one_le
  set ρ₁ : ℝ := 2 * (1 + C) with hρ₁
  have hρ₁4 : 4 ≤ ρ₁ := by rw [hρ₁]; linarith
  set r := rCentre ψ t n with hr
  set d := cellLen t n with hd
  set u := ‖z - (r : ℂ)‖ with hu
  have hr0 : 0 < r := rCentre_pos ψ t n
  have hd0 : 0 < d := cellLen_pos h hn1
  have ha : 0 < t (n - 1) := t_pos h (by omega)
  have hlt := h.mono (show n - 1 < n by omega)
  have hu0 : 0 < u := by
    have : 0 < (8 + 2 * ρ₁) * d := by positivity
    linarith
  have h8 : 8 * d ≤ u := by nlinarith
  obtain ⟨har, hrb⟩ := h.rCentre_mem hn1
  have hta : t n ≤ (1 + C) * t (n - 1) := h.t_le hn
  have hs_norm : ∀ s : ℝ, 0 ≤ s → ‖(s : ℂ)‖ = s := fun s hs => by
    rw [Complex.norm_real, Real.norm_of_nonneg hs]
  have hsz : ∀ s ∈ Icc (t (n - 1)) (t n), u / 2 ≤ ‖(s : ℂ) - z‖ := by
    intro s hs
    have h1 : ‖(r : ℂ) - z‖ - ‖(s : ℂ) - (r : ℂ)‖ ≤ ‖(s : ℂ) - z‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub (r : ℂ) (s : ℂ) z
      have e : ‖(r : ℂ) - z‖ ≤ ‖(r : ℂ) - (s : ℂ)‖ + ‖(s : ℂ) - z‖ := this
      rw [norm_sub_rev (r : ℂ) (s : ℂ)] at e
      linarith
    have h2 : ‖(s : ℂ) - (r : ℂ)‖ ≤ d := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      unfold cellLen at hd
      constructor <;> linarith [hs.1, hs.2, har, hrb]
    have h3 : ‖(r : ℂ) - z‖ = u := by rw [hu, norm_sub_rev]
    linarith
  have hszne : ∀ s ∈ Icc (t (n - 1)) (t n), (s : ℂ) ≠ z := fun s hs hsz' => by
    have := hsz s hs
    rw [hsz', sub_self, norm_zero] at this
    linarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz2
    linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hcz := cellTerm_eq h hn hszne
  set M' : ℝ := 4 * ρ₁ * (1 + C) * r ^ 2 / u ^ 2 with hM'
  have hA := A_bound h hn (z := z) (M' := M') (fun s hs => by
    have hs0 : 0 < s := ha.trans_le hs.1
    have hD : u ^ 2 / 4 ≤ ‖(s : ℂ) - z‖ ^ 2 := by nlinarith [hsz s hs]
    have hDpos : 0 < ‖(s : ℂ) - z‖ ^ 2 := by nlinarith
    refine ⟨by nlinarith [hsz s hs], ?_⟩
    rw [div_le_iff₀ hDpos]
    have h1 : s ≤ (1 + C) * r := by
      have : t n ≤ (1 + C) * r := by nlinarith
      linarith [hs.2]
    have h2 : ‖z‖ * s ≤ ρ₁ * r * ((1 + C) * r) :=
      mul_le_mul hz1 h1 hs0.le (by positivity)
    have h3 : M' * (u ^ 2 / 4) = ρ₁ * (1 + C) * r ^ 2 := by
      rw [hM']; field_simp
    have h4 : M' * (u ^ 2 / 4) ≤ M' * ‖(s : ℂ) - z‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    nlinarith)
  -- λ bound
  have hlam0 := lam_nonneg h hn
  have hlam1 := lam_le_div h hn
  have hr_le : r / (1 + C) ≤ t (n - 1) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hlam2 : Real.log (t n) - Real.log (t (n - 1)) ≤ (1 + C) * d / r := by
    refine hlam1.trans ?_
    rw [div_le_div_iff₀ ha hr0]
    have : d * (r / (1 + C)) ≤ d * t (n - 1) := mul_le_mul_of_nonneg_left hr_le hd0.le
    have e : d * (r / (1 + C)) * (1 + C) = d * r := by field_simp
    nlinarith
  have hlam3 : (Real.log (t n) - Real.log (t (n - 1))) ^ 2 ≤ ((1 + C) * d / r) ^ 2 := by
    gcongr
  have hA2 : M' / 2 * (Real.log (t n) - Real.log (t (n - 1))) ^ 2 ≤
      2 * ρ₁ * (1 + C) ^ 3 * (d ^ 2 / u ^ 2) := by
    refine (mul_le_mul_of_nonneg_left hlam3 (by positivity)).trans (le_of_eq ?_)
    rw [hM']; field_simp; ring
  have hur : u ≤ (ρ₁ + 1) * r := by
    have : ‖z - (r : ℂ)‖ ≤ ‖z‖ + ‖(r : ℂ)‖ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_of_nonneg hr0.le] at this
    nlinarith
  have hB := B_far h hn1 (ρ₁ := ρ₁) (by linarith) hz hfar hur
  rw [hcz]
  calc |_| ≤ |∫ s in cell t n, (Real.log ‖1 - z / (s : ℂ)‖ - Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖) *
        deriv ψ s| + |Real.log ‖1 - z / (rCentre ψ t n : ℂ)‖ - Real.log ‖1 - z / zPt ψ t C n‖| :=
        abs_add_le _ _
    _ ≤ 2 * ρ₁ * (1 + C) ^ 3 * (d ^ 2 / u ^ 2) + ((3 + ρ₁) * (d ^ 2 / u ^ 2) +
        2 * (d * z.im / u ^ 2)) := add_le_add (hA.trans hA2) hB
    _ = _ := by ring

end FF.D1
