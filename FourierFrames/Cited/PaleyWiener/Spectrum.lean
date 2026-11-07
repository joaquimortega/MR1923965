import FourierFrames.Cited.PaleyWiener.L2Fourier

/-!
# P1 — Gaussian regularisation and the spectrum of an entire function of exponential type

Key estimate (blueprint §3).  Let `f` be entire, `f|ℝ ∈ L²`, and
`|f(x + iy)| ≤ C e^{a|x| + b|y|}`.  Then the `L²` Fourier transform of `f|ℝ` vanishes a.e. on
`{w : 2π|w| > a + b}`.

Proof idea: `f_η(x) = f(x) e^{-ηx²} ∈ L¹ ∩ L²`; shift the contour of
`∫ f_η(x) e^{-iξx} dx` to `Im z = ∓Y`, `Y = (|ξ| - b)/(2η)`, giving
`|𝓕 f_η| ≲ η^{-1/2} exp((a² - (|ξ|-b)²)/(4η)) → 0`; and `𝓕 f_η → 𝓕 f` in `L²` (Plancherel +
dominated convergence), so a subsequence converges a.e.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform

noncomputable section

namespace FF.PW1

/-! ### 3.1 Contour shift for entire functions with Gaussian decay -/

theorem integral_line_shift {H : ℂ → ℂ} (hH : Differentiable ℂ H) (y : ℝ)
    (hint0 : Integrable (fun x : ℝ ↦ H x))
    (hinty : Integrable (fun x : ℝ ↦ H (x + y * I)))
    (hR : Tendsto (fun R : ℝ ↦ ∫ s in (0 : ℝ)..y, ‖H (R + s * I)‖) atTop (𝓝 0))
    (hR' : Tendsto (fun R : ℝ ↦ ∫ s in (0 : ℝ)..y, ‖H (-R + s * I)‖) atTop (𝓝 0)) :
    ∫ x : ℝ, H x = ∫ x : ℝ, H (x + y * I) := by
  have hrect : ∀ R : ℝ, (∫ x : ℝ in (-R)..R, H x) - (∫ x : ℝ in (-R)..R, H (x + y * I)) +
      I • (∫ s : ℝ in (0 : ℝ)..y, H (R + s * I)) -
      I • (∫ s : ℝ in (0 : ℝ)..y, H (-R + s * I)) = 0 := fun R ↦ by
    have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H (-(R : ℂ)) (R + y * I)
      hH.differentiableOn
    simpa using this
  have hA : Tendsto (fun R : ℝ ↦ ∫ x : ℝ in (-R)..R, H x) atTop (𝓝 (∫ x : ℝ, H x)) :=
    intervalIntegral_tendsto_integral hint0 tendsto_neg_atTop_atBot tendsto_id
  have hB : Tendsto (fun R : ℝ ↦ ∫ x : ℝ in (-R)..R, H (x + y * I)) atTop
      (𝓝 (∫ x : ℝ, H (x + y * I))) :=
    intervalIntegral_tendsto_integral hinty tendsto_neg_atTop_atBot tendsto_id
  have key : ∀ {T : ℝ → ℝ → ℂ},
      Tendsto (fun R : ℝ ↦ ∫ s in (0 : ℝ)..y, ‖T R s‖) atTop (𝓝 0) →
      Tendsto (fun R : ℝ ↦ ∫ s in (0 : ℝ)..y, T R s) atTop (𝓝 0) := by
    intro T hT
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun R ↦ norm_nonneg _) (fun R ↦
      intervalIntegral.norm_integral_le_abs_integral_norm (a := 0) (b := y)
        (f := fun s ↦ T R s)) ?_
    simpa using hT.abs
  have hV := key (T := fun R s ↦ H (R + s * I)) hR
  have hV' := key (T := fun R s ↦ H (-R + s * I)) hR'
  have h1 : Tendsto (fun R : ℝ ↦ (∫ x : ℝ in (-R)..R, H x) - (∫ x : ℝ in (-R)..R, H (x + y * I)) +
      I • (∫ s : ℝ in (0 : ℝ)..y, H (R + s * I)) -
      I • (∫ s : ℝ in (0 : ℝ)..y, H (-R + s * I))) atTop
      (𝓝 ((∫ x : ℝ, H x) - (∫ x : ℝ, H (x + y * I)) + I • 0 - I • 0)) :=
    ((hA.sub hB).add (hV.const_smul I)).sub (hV'.const_smul I)
  simp only [hrect] at h1
  have := tendsto_nhds_unique h1 tendsto_const_nhds
  simp only [smul_zero, add_zero, sub_zero] at this
  exact sub_eq_zero.1 this

/-! ### 3.2 Gaussian integrals -/

theorem exp_lin_sub_sq_eq (b : ℝ) {η : ℝ} (hη : 0 < η) (x : ℝ) :
    Real.exp (b * x - η * x ^ 2) =
      Real.exp (b ^ 2 / (4 * η)) * Real.exp (-η * (x - b / (2 * η)) ^ 2) := by
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

theorem integrable_exp_lin_sub_sq (b : ℝ) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x : ℝ ↦ Real.exp (b * x - η * x ^ 2)) := by
  simp_rw [exp_lin_sub_sq_eq b hη]
  exact ((integrable_exp_neg_mul_sq hη).comp_sub_right (b / (2 * η))).const_mul _

theorem integral_exp_lin_sub_sq (b : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫ x : ℝ, Real.exp (b * x - η * x ^ 2) = Real.sqrt (Real.pi / η) * Real.exp (b ^ 2 / (4 * η)) := by
  simp_rw [exp_lin_sub_sq_eq b hη]
  rw [integral_const_mul, integral_sub_right_eq_self (fun x : ℝ ↦ Real.exp (-η * x ^ 2))
    (b / (2 * η))]
  have := integral_gaussian η
  simp_rw [neg_mul] at this ⊢
  rw [this, mul_comm]

theorem exp_abs_sub_sq_le (a : ℝ) {η : ℝ} (x : ℝ) :
    Real.exp (a * |x| - η * x ^ 2) ≤
      Real.exp (a * x - η * x ^ 2) + Real.exp (-a * x - η * x ^ 2) := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos h]
    have : a * -x = -a * x := by ring
    rw [this]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

theorem integrable_exp_abs_sub_sq {a : ℝ} {η : ℝ} (hη : 0 < η) :
    Integrable (fun x : ℝ ↦ Real.exp (a * |x| - η * x ^ 2)) := by
  refine Integrable.mono' ((integrable_exp_lin_sub_sq a hη).add (integrable_exp_lin_sub_sq (-a) hη))
    (by fun_prop) (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_abs_sub_sq_le a x

theorem integral_exp_abs_sub_sq_le {a : ℝ} {η : ℝ} (hη : 0 < η) :
    ∫ x : ℝ, Real.exp (a * |x| - η * x ^ 2) ≤
      2 * Real.sqrt (Real.pi / η) * Real.exp (a ^ 2 / (4 * η)) := by
  calc ∫ x : ℝ, Real.exp (a * |x| - η * x ^ 2)
      ≤ ∫ x : ℝ, (Real.exp (a * x - η * x ^ 2) + Real.exp (-a * x - η * x ^ 2)) :=
        integral_mono (integrable_exp_abs_sub_sq hη)
          ((integrable_exp_lin_sub_sq a hη).add (integrable_exp_lin_sub_sq (-a) hη))
          fun x ↦ exp_abs_sub_sq_le a x
    _ = _ := by
        rw [integral_add (integrable_exp_lin_sub_sq a hη) (integrable_exp_lin_sub_sq (-a) hη),
          integral_exp_lin_sub_sq a hη, integral_exp_lin_sub_sq (-a) hη]
        ring_nf

/-! ### 3.3 The pointwise bound on `∫ f(x) e^{-ηx²} e^{-iξx} dx` -/

/-- The Gaussian-regularised, modulated integrand. -/
def gaussH (f : ℂ → ℂ) (η ξ : ℝ) (z : ℂ) : ℂ :=
  f z * Complex.exp (-(η : ℂ) * z ^ 2) * Complex.exp (-I * ξ * z)

theorem differentiable_gaussH {f : ℂ → ℂ} (hd : Differentiable ℂ f) (η ξ : ℝ) :
    Differentiable ℂ (gaussH f η ξ) := by
  unfold gaussH
  fun_prop

theorem norm_gaussH_le {f : ℂ → ℂ} {C a b : ℝ}
    (hC : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (a * |z.re| + b * |z.im|)) (η ξ x s : ℝ) :
    ‖gaussH f η ξ (x + s * I)‖ ≤
      |C| * Real.exp (a * |x| - η * x ^ 2) * Real.exp (η * s ^ 2 + b * |s| + ξ * s) := by
  unfold gaussH
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
  have h1 := hC (x + s * I)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, zero_add,
    Complex.mul_im] at h1
  have e1 : (-(η : ℂ) * (x + s * I) ^ 2).re = -η * (x ^ 2 - s ^ 2) := by
    simp [pow_two]
  have e2 : (-I * (ξ : ℂ) * (x + s * I)).re = ξ * s := by
    simp
  rw [e1, e2]
  have h2 : C * Real.exp (a * |x| + b * |s|) ≤ |C| * Real.exp (a * |x| + b * |s|) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
  calc ‖f (x + s * I)‖ * Real.exp (-η * (x ^ 2 - s ^ 2)) * Real.exp (ξ * s)
      ≤ (|C| * Real.exp (a * |x| + b * |s|)) * Real.exp (-η * (x ^ 2 - s ^ 2)) * Real.exp (ξ * s) := by
        gcongr
        exact h1.trans h2
    _ = _ := by
        rw [mul_assoc, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

theorem tendsto_exp_gauss_zero (a : ℝ) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun R : ℝ ↦ Real.exp (a * R - η * R ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun R : ℝ ↦ η * R ^ 2 - a * R) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_ge_atTop ((a + 1) / η), eventually_ge_atTop 0] with R hR hR0
    have : (a + 1) ≤ η * R := by
      rwa [div_le_iff₀ hη, mul_comm] at hR
    simp only [id]
    nlinarith [mul_nonneg hR0 (sub_nonneg.2 this)]
  have := Real.tendsto_exp_neg_atTop_nhds_zero.comp h
  refine this.congr fun R ↦ ?_
  simp only [Function.comp]
  congr 1; ring

theorem norm_integral_gauss_mul_le {f : ℂ → ℂ} (hd : Differentiable ℂ f) {C a b : ℝ}
    (hb : 0 ≤ b) (hC : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (a * |z.re| + b * |z.im|))
    {η : ℝ} (hη : 0 < η) {ξ : ℝ} (hξ : b ≤ |ξ|) :
    ‖∫ x : ℝ, f x * Complex.exp (-(η : ℂ) * (x : ℂ) ^ 2) * Complex.exp (-I * ξ * x)‖ ≤
      2 * |C| * Real.sqrt (Real.pi / η) * Real.exp ((a ^ 2 - (|ξ| - b) ^ 2) / (4 * η)) := by
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = |ξ| - b := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = κ / (2 * η) := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  obtain ⟨y, hy1, hy2⟩ : ∃ y : ℝ, |y| = Y ∧ ξ * y = -(|ξ| * Y) := by
    rcases le_total 0 ξ with h | h
    · exact ⟨-Y, by simp [abs_of_nonneg hY0], by rw [abs_of_nonneg h]; ring⟩
    · exact ⟨Y, abs_of_nonneg hY0, by rw [abs_of_nonpos h]; ring⟩
  have hHd := differentiable_gaussH hd η ξ
  have hHc : Continuous (gaussH f η ξ) := hHd.continuous
  have hbd := norm_gaussH_le hC η ξ
  have hint : ∀ s : ℝ, Integrable (fun x : ℝ ↦ gaussH f η ξ (x + s * I)) := by
    intro s
    refine Integrable.mono' ((integrable_exp_abs_sub_sq (a := a) hη).const_mul
      (|C| * Real.exp (η * s ^ 2 + b * |s| + ξ * s))) ?_ ?_
    · exact (hHc.comp (by fun_prop)).aestronglyMeasurable
    · refine Eventually.of_forall fun x ↦ ?_
      refine (hbd x s).trans (le_of_eq ?_)
      ring
  have hV : ∀ X : ℝ, ‖∫ s in (0 : ℝ)..y, ‖gaussH f η ξ (X + s * I)‖‖ ≤
      (|C| * Real.exp (η * Y ^ 2 + (b + |ξ|) * Y) * Real.exp (a * |X| - η * X ^ 2)) * |y| := by
    intro X
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := y)
      (f := fun s ↦ ‖gaussH f η ξ (X + s * I)‖)
      (C := |C| * Real.exp (η * Y ^ 2 + (b + |ξ|) * Y) * Real.exp (a * |X| - η * X ^ 2))
      (fun s hs ↦ by
        have hs' : |s| ≤ Y := by
          rw [← hy1]
          rcases le_total 0 y with h | h
          · rw [Set.uIoc_of_le h] at hs
            rw [abs_of_nonneg h, abs_of_nonneg hs.1.le]; exact hs.2
          · rw [Set.uIoc_of_ge h] at hs
            rw [abs_of_nonpos h, abs_of_nonpos hs.2]; linarith [hs.1]
        rw [norm_norm]
        refine (hbd X s).trans ?_
        have h1 : η * s ^ 2 + b * |s| + ξ * s ≤ η * Y ^ 2 + (b + |ξ|) * Y := by
          have e1 : s ^ 2 ≤ Y ^ 2 := by
            rw [← sq_abs s]; exact pow_le_pow_left₀ (abs_nonneg _) hs' 2
          have e2 : ξ * s ≤ |ξ| * Y := by
            calc ξ * s ≤ |ξ * s| := le_abs_self _
              _ = |ξ| * |s| := abs_mul _ _
              _ ≤ |ξ| * Y := mul_le_mul_of_nonneg_left hs' (abs_nonneg _)
          nlinarith [mul_le_mul_of_nonneg_left hs' hb]
        calc |C| * Real.exp (a * |X| - η * X ^ 2) * Real.exp (η * s ^ 2 + b * |s| + ξ * s)
            ≤ |C| * Real.exp (a * |X| - η * X ^ 2) * Real.exp (η * Y ^ 2 + (b + |ξ|) * Y) := by
              gcongr
          _ = _ := by ring)
    simpa [Real.norm_eq_abs] using this
  have hgb : ∀ X : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → |X R| = R) →
      Tendsto (fun R : ℝ ↦ ∫ s in (0 : ℝ)..y, ‖gaussH f η ξ (X R + s * I)‖) atTop (𝓝 0) := by
    intro X hX
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun R : ℝ ↦ (|C| * Real.exp (η * Y ^ 2 + (b + |ξ|) * Y) *
      Real.exp (a * R - η * R ^ 2)) * |y|) (Eventually.of_forall fun R ↦ norm_nonneg _) ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with R hR
      have := hV (X R)
      rw [hX R hR, show η * X R ^ 2 = η * R ^ 2 by rw [← sq_abs (X R), hX R hR]] at this
      exact this
    · have := (((tendsto_exp_gauss_zero a hη).const_mul
        (|C| * Real.exp (η * Y ^ 2 + (b + |ξ|) * Y))).mul_const |y|)
      simpa [mul_assoc] using this
  have hR := hgb (fun R ↦ R) (fun R hR ↦ abs_of_nonneg hR)
  have hR' := hgb (fun R ↦ -R) (fun R hR ↦ by rw [abs_neg, abs_of_nonneg hR])
  simp only [Complex.ofReal_neg] at hR'
  have hshift := integral_line_shift hHd y (by simpa using hint 0) (hint y) hR hR'
  have hexp : η * y ^ 2 + b * |y| + ξ * y = -(κ ^ 2 / (4 * η)) := by
    have : y ^ 2 = Y ^ 2 := by rw [← sq_abs y, hy1]
    rw [this, hy1, hy2, hY]
    have hη' : η ≠ 0 := hη.ne'
    have : b = |ξ| - κ := by linarith
    rw [this]
    field_simp
    ring
  have e : (∫ x : ℝ, f x * Complex.exp (-(η : ℂ) * (x : ℂ) ^ 2) * Complex.exp (-I * ξ * x)) =
      ∫ x : ℝ, gaussH f η ξ x := rfl
  rw [e, hshift, ← hκ]
  calc ‖∫ x : ℝ, gaussH f η ξ (x + y * I)‖ ≤ ∫ x : ℝ, ‖gaussH f η ξ (x + y * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, |C| * Real.exp (-(κ ^ 2 / (4 * η))) * Real.exp (a * |x| - η * x ^ 2) :=
        integral_mono (hint y).norm ((integrable_exp_abs_sub_sq hη).const_mul _) fun x ↦
          (hbd x y).trans (le_of_eq (by rw [hexp]; ring))
    _ = |C| * Real.exp (-(κ ^ 2 / (4 * η))) * ∫ x : ℝ, Real.exp (a * |x| - η * x ^ 2) :=
        integral_const_mul _ _
    _ ≤ |C| * Real.exp (-(κ ^ 2 / (4 * η))) *
          (2 * Real.sqrt (Real.pi / η) * Real.exp (a ^ 2 / (4 * η))) :=
        mul_le_mul_of_nonneg_left (integral_exp_abs_sub_sq_le hη) (by positivity)
    _ = _ := by
        have : (a ^ 2 - κ ^ 2) / (4 * η) = a ^ 2 / (4 * η) + -(κ ^ 2 / (4 * η)) := by ring
        rw [this, Real.exp_add]
        ring

theorem tendsto_gauss_bound {a κ : ℝ} (ha : 0 ≤ a) (hκ : a < κ) (C : ℝ) :
    Tendsto (fun η : ℝ ↦
      2 * |C| * Real.sqrt (Real.pi / η) * Real.exp ((a ^ 2 - κ ^ 2) / (4 * η)))
      (𝓝[>] 0) (𝓝 0) := by
  sorry

/-! ### 3.4 `f e^{-η·²} → f` in `L²` and the a.e. limit -/

theorem memLp_mul_gauss {f : ℝ → ℂ} (hf : MemLp f 2) {η : ℝ} (hη : 0 < η) :
    MemLp (fun x : ℝ ↦ f x * ((Real.exp (-η * x ^ 2) : ℝ) : ℂ)) 2 ∧
    Integrable (fun x : ℝ ↦ f x * ((Real.exp (-η * x ^ 2) : ℝ) : ℂ)) := by
  sorry

theorem tendsto_eLpNorm_mul_gauss {f : ℝ → ℂ} (hf : MemLp f 2) :
    Tendsto (fun n : ℕ ↦ eLpNorm (fun x : ℝ ↦ f x * ((Real.exp (-(1 / ((n : ℝ) + 1)) * x ^ 2) : ℝ) : ℂ)
      - f x) 2 volume) atTop (𝓝 0) := by
  sorry

/-- **Spectrum lemma.** -/
theorem spectrum_vanish {f : ℂ → ℂ} (hd : Differentiable ℂ f) (hL2 : MemLp (fun x : ℝ ↦ f x) 2)
    {C a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (a * |z.re| + b * |z.im|)) :
    ∀ᵐ w : ℝ, a + b < 2 * Real.pi * |w| →
      (F2 (hL2.toLp (fun x : ℝ ↦ f x)) : ℝ → ℂ) w = 0 := by
  sorry

end FF.PW1
