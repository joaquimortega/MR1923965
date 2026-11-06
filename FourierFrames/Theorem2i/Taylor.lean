import FourierFrames.Theorem2i.Basic

/-!
# M08 helper (fork D1): second-order Taylor estimate and derivatives of `h_z`

Pure real analysis: the one-sided/two-sided second-order Taylor bound with constant `M/2`,
the derivatives of `H_z(σ) = log ‖e^σ - z‖ - σ`, and an elementary `log` comparison lemma.
-/

open MeasureTheory Set Complex Filter Topology

noncomputable section

namespace FF.D1

/-- One-sided Taylor bound. -/
theorem onesided {φ φ' : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x) (h0 : φ a = 0)
    (hb : ∀ x ∈ Icc a b, |φ' x| ≤ M * (x - a)) : |φ b| ≤ M / 2 * (b - a) ^ 2 := by
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := φ) (f' := φ')
    (a := a) (b := b)
    (fun x hx => (hφ x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hφ x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (B := fun u => M / 2 * (u - a) ^ 2) (B' := fun u => M * (u - a))
    (by simp [h0])
    (by fun_prop)
    (fun x _ => by
      have : HasDerivAt (fun u : ℝ => M / 2 * (u - a) ^ 2) (M / 2 * (2 * (x - a))) x := by
        have h1 : HasDerivAt (fun u : ℝ => (u - a)) 1 x := (hasDerivAt_id x).sub_const a
        simpa using (h1.pow 2).const_mul (M / 2)
      have e : M / 2 * (2 * (x - a)) = M * (x - a) := by ring
      rw [e] at this
      exact this.hasDerivWithinAt)
    (fun x hx => by simpa [Real.norm_eq_abs] using hb x (Ico_subset_Icc_self hx))
    (x := b) ⟨hab, le_rfl⟩
  simpa [Real.norm_eq_abs] using key

/-- Second-order Taylor bound with Lagrange-type constant `M/2`. -/
theorem taylor2 {H H1 H2 : ℝ → ℝ} {α β σ0 M : ℝ}
    (h1 : ∀ σ ∈ Icc α β, HasDerivAt H (H1 σ) σ)
    (h2 : ∀ σ ∈ Icc α β, HasDerivAt H1 (H2 σ) σ)
    (hM : ∀ σ ∈ Icc α β, |H2 σ| ≤ M) (hσ0 : σ0 ∈ Icc α β) {σ : ℝ} (hσ : σ ∈ Icc α β) :
    |H σ - H σ0 - H1 σ0 * (σ - σ0)| ≤ M / 2 * (σ - σ0) ^ 2 := by
  -- Lipschitz bound for `H1`
  have hconv : Convex ℝ (Icc α β) := convex_Icc α β
  have lip : ∀ u ∈ Icc α β, |H1 u - H1 σ0| ≤ M * |u - σ0| := by
    intro u hu
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := H1) (f' := H2) (C := M)
      (fun x hx => (h2 x hx).hasDerivWithinAt) (fun x hx => by simpa [Real.norm_eq_abs] using hM x hx)
      hσ0 hu
    simpa [Real.norm_eq_abs] using this
  rcases le_total σ0 σ with hle | hle
  · -- σ0 ≤ σ
    have := onesided (φ := fun u => H u - H σ0 - H1 σ0 * (u - σ0)) (φ' := fun u => H1 u - H1 σ0)
      (a := σ0) (b := σ) (M := M) hle
      (fun x hx => by
        have hxm : x ∈ Icc α β := ⟨hσ0.1.trans hx.1, hx.2.trans hσ.2⟩
        have := ((h1 x hxm).sub_const (H σ0)).sub (((hasDerivAt_id x).sub_const σ0).const_mul (H1 σ0))
        exact this.congr_deriv (by simp))
      (by simp)
      (fun x hx => by
        have hxm : x ∈ Icc α β := ⟨hσ0.1.trans hx.1, hx.2.trans hσ.2⟩
        have := lip x hxm
        rwa [abs_of_nonneg (sub_nonneg.2 hx.1)] at this)
    simpa using this
  · -- σ ≤ σ0 : reflect
    have := onesided (φ := fun v => H (2 * σ0 - v) - H σ0 - H1 σ0 * ((2 * σ0 - v) - σ0))
      (φ' := fun v => -(H1 (2 * σ0 - v) - H1 σ0)) (a := σ0) (b := 2 * σ0 - σ) (M := M)
      (by linarith)
      (fun x hx => by
        have hxm : 2 * σ0 - x ∈ Icc α β := by
          constructor <;> [skip; skip] <;> linarith [hx.1, hx.2, hσ.1, hσ0.2, hσ0.1]
        have hc : HasDerivAt (fun v : ℝ => 2 * σ0 - v) (-1) x := by
          simpa using ((hasDerivAt_id x).const_sub (2 * σ0))
        have := (((h1 _ hxm).comp x hc).sub_const (H σ0)).sub
          ((((hc.sub_const σ0)).const_mul (H1 σ0)))
        exact this.congr_deriv (by ring))
      (by simp only [show 2 * σ0 - σ0 = σ0 by ring]; ring)
      (fun x hx => by
        have hxm : 2 * σ0 - x ∈ Icc α β := by
          constructor <;> linarith [hx.1, hx.2, hσ.1, hσ0.2, hσ0.1]
        have := lip _ hxm
        rw [abs_neg]
        have e : (2 * σ0 - x) - σ0 = -(x - σ0) := by ring
        rw [e, abs_neg, abs_of_nonneg (sub_nonneg.2 hx.1)] at this
        exact this)
    have e1 : 2 * σ0 - (2 * σ0 - σ) = σ := by ring
    rw [e1] at this
    have e2 : (2 * σ0 - σ - σ0) ^ 2 = (σ - σ0) ^ 2 := by ring
    rw [e2] at this
    simpa using this

/-! ### The function `H_z(σ) = log ‖e^σ - z‖ - σ` -/

/-- `D(σ) = |e^σ - z|²`, `z = x + i y`. -/
def Dd (x y σ : ℝ) : ℝ := (Real.exp σ - x) ^ 2 + y ^ 2

/-- `H_z(σ) = ½ log D(σ) - σ`. -/
def Hfun (x y σ : ℝ) : ℝ := Real.log (Dd x y σ) / 2 - σ

/-- First derivative `(x e^σ - |z|²)/D`. -/
def H1 (x y σ : ℝ) : ℝ := (x * Real.exp σ - (x ^ 2 + y ^ 2)) / Dd x y σ

/-- Second derivative. -/
def H2 (x y σ : ℝ) : ℝ :=
  Real.exp σ * (-x * Real.exp σ ^ 2 + 2 * (x ^ 2 + y ^ 2) * Real.exp σ - (x ^ 2 + y ^ 2) * x) /
    Dd x y σ ^ 2

theorem hasDerivAt_Dd (x y σ : ℝ) :
    HasDerivAt (Dd x y) (2 * (Real.exp σ - x) * Real.exp σ) σ := by
  have h := (((Real.hasDerivAt_exp σ).sub_const x).pow 2).add_const (y ^ 2)
  exact h.congr_deriv (by simp)

theorem hasDerivAt_Hfun {x y σ : ℝ} (hD : Dd x y σ ≠ 0) :
    HasDerivAt (Hfun x y) (H1 x y σ) σ := by
  have h := (((hasDerivAt_Dd x y σ).log hD).div_const 2).sub (hasDerivAt_id σ)
  refine h.congr_deriv ?_
  unfold H1 Dd at *
  field_simp
  ring

theorem hasDerivAt_H1 {x y σ : ℝ} (hD : Dd x y σ ≠ 0) :
    HasDerivAt (H1 x y) (H2 x y σ) σ := by
  have hn : HasDerivAt (fun σ => x * Real.exp σ - (x ^ 2 + y ^ 2)) (x * Real.exp σ) σ := by
    simpa using ((Real.hasDerivAt_exp σ).const_mul x).sub_const (x ^ 2 + y ^ 2)
  have h := hn.div (hasDerivAt_Dd x y σ) hD
  refine h.congr_deriv ?_
  unfold H2 Dd at *
  field_simp
  ring

theorem Dd_pos {x y σ : ℝ} (h : Dd x y σ ≠ 0) : 0 < Dd x y σ :=
  lt_of_le_of_ne (by unfold Dd; positivity) (Ne.symm h)

/-- `|H''| ≤ |z| e^σ / D`. -/
theorem abs_H2_le {x y σ : ℝ} (hD : 0 < Dd x y σ) :
    |H2 x y σ| ≤ Real.sqrt (x ^ 2 + y ^ 2) * Real.exp σ / Dd x y σ := by
  set R := Real.sqrt (x ^ 2 + y ^ 2) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  have hxR : |x| ≤ R := by
    rw [hR]; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg y])
  have hxR' := abs_le.1 hxR
  set s := Real.exp σ with hs
  have hs0 : 0 < s := Real.exp_pos σ
  have hDe : Dd x y σ = s ^ 2 - 2 * x * s + R ^ 2 := by unfold Dd; rw [hR2]; ring
  have hN : |-x * s ^ 2 + 2 * (x ^ 2 + y ^ 2) * s - (x ^ 2 + y ^ 2) * x| ≤ R * Dd x y σ := by
    rw [← hR2, hDe]
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (by linarith : 0 ≤ R - x) (sq_nonneg (s + R))]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ R + x) (sq_nonneg (s - R))]
  unfold H2
  rw [abs_div, abs_mul, abs_of_pos hs0, abs_of_pos (by positivity : 0 < Dd x y σ ^ 2),
    div_le_div_iff₀ (by positivity) hD]
  have := mul_le_mul_of_nonneg_left hN hs0.le
  calc s * |-x * s ^ 2 + 2 * (x ^ 2 + y ^ 2) * s - (x ^ 2 + y ^ 2) * x| * Dd x y σ
      ≤ s * (R * Dd x y σ) * Dd x y σ := by gcongr
    _ = R * s * Dd x y σ ^ 2 := by ring

theorem norm_ofReal_sub_sq (s : ℝ) (z : ℂ) : ‖(s : ℂ) - z‖ ^ 2 = (s - z.re) ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem Dd_log (z : ℂ) (s : ℝ) (hs : 0 < s) : Dd z.re z.im (Real.log s) = ‖(s : ℂ) - z‖ ^ 2 := by
  rw [norm_ofReal_sub_sq, Dd, Real.exp_log hs]

/-- `log ‖1 - z/s‖ = H_z(log s)`. -/
theorem log_norm_one_sub_div_eq (z : ℂ) {s : ℝ} (hs : 0 < s) (hsz : (s : ℂ) ≠ z) :
    Real.log ‖1 - z / (s : ℂ)‖ = Hfun z.re z.im (Real.log s) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have h1 : 1 - z / (s : ℂ) = ((s : ℂ) - z) / s := by field_simp
  have hne : ‖(s : ℂ) - z‖ ≠ 0 := by simpa [sub_eq_zero] using hsz
  rw [h1, norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, Real.log_div hne hs.ne',
    Hfun, Dd_log z s hs, Real.log_pow]
  push_cast
  ring

/-- Comparison of logs of norms. -/
theorem abs_log_norm_sub_le {w1 w2 : ℂ} {m : ℝ} (hm : 0 < m) (h1 : m ≤ ‖w1‖) (h2 : m ≤ ‖w2‖) :
    |Real.log ‖w1‖ - Real.log ‖w2‖| ≤ ‖w1 - w2‖ / m := by
  have p1 : 0 < ‖w1‖ := hm.trans_le h1
  have p2 : 0 < ‖w2‖ := hm.trans_le h2
  have key : ∀ a b : ℂ, 0 < ‖a‖ → 0 < ‖b‖ → m ≤ ‖b‖ →
      Real.log ‖a‖ - Real.log ‖b‖ ≤ ‖a - b‖ / m := by
    intro a b ha hb hmb
    rw [← Real.log_div ha.ne' hb.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ha hb)
    have e : ‖a‖ / ‖b‖ - 1 = (‖a‖ - ‖b‖) / ‖b‖ := by field_simp
    have h3 : ‖a‖ - ‖b‖ ≤ ‖a - b‖ := by
      have := norm_sub_norm_le a b; exact this
    calc Real.log (‖a‖ / ‖b‖) ≤ (‖a‖ - ‖b‖) / ‖b‖ := by rw [← e]; exact this
      _ ≤ ‖a - b‖ / ‖b‖ := by gcongr
      _ ≤ ‖a - b‖ / m := by gcongr
  rw [abs_le]
  constructor
  · have := key w2 w1 p2 p1 h1
    rw [norm_sub_rev] at this
    linarith
  · exact key w1 w2 p1 p2 h2

end FF.D1
