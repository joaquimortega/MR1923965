import OrtegaCerdaSeip.Bernstein.PhragmenLindelof

/-!
# M02 (Bernstein) — `sinc` functions and finite products of sines

See `blueprint/M02_Bernstein.md`, §1.7–§1.8.

* `csinc w = sin w / w` (`csinc 0 = 1`), the complex `sinc`; `S_{δ,a}(z) = csinc (δ (z - a))`
  is in `𝓑_δ`, has modulus `≤ 1` on `ℝ` (for real `a`), value `1` at `a`, and
  `|S_{δ,a}(z)| ≤ e^{δ|Im z|}/(δ|z - a|)` for `z ≠ a`.  Used on p. 414 (and in Lemma 4, M05).
* `sineProduct s P z = ∏_{w ∈ s} sin(π(z - w)/P)`, the function `G` of p. 414: entire, of
  exponential type `π |s| / P`, vanishing on `s`, with `P`-periodic modulus, and a global maximum
  of `|G|` on `ℝ` attained in any closed interval of length `P`, where `G ≠ 0`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-! ### `sinc` -/

/-- The complex `sinc` function: `sin w / w`, with the value `1` at `0`. -/
def csinc (w : ℂ) : ℂ := if w = 0 then 1 else Complex.sin w / w

@[simp] theorem csinc_zero : csinc 0 = 1 := by simp [csinc]

theorem csinc_of_ne_zero {w : ℂ} (hw : w ≠ 0) : csinc w = Complex.sin w / w := by
  simp [csinc, hw]

theorem csinc_eq_dslope : csinc = dslope Complex.sin 0 := by
  funext w
  by_cases hw : w = 0
  · subst hw
    simp [dslope_same, Complex.deriv_sin]
  · rw [csinc_of_ne_zero hw, dslope_of_ne _ hw, slope_def_module]
    simp [div_eq_inv_mul]

theorem differentiable_csinc : Differentiable ℂ csinc := by
  rw [csinc_eq_dslope, ← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
  exact Complex.differentiable_sin.differentiableOn

theorem csinc_ofReal (x : ℝ) : csinc x = (Real.sinc x : ℂ) := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [csinc_of_ne_zero (by exact_mod_cast hx), Real.sinc_of_ne_zero hx]
    push_cast
    rfl

theorem norm_csinc_ofReal_le_one (x : ℝ) : ‖csinc x‖ ≤ 1 := by
  rw [csinc_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sinc_le_one x

/-- `|sin w| ≤ cosh (Im w) ≤ e^{|Im w|}`. -/
theorem norm_sin_le_exp_abs_im (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  have h1 : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]
    simp
  have h2 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]
    simp
  have h : ‖Complex.sin w‖ ≤ (Real.exp w.im + Real.exp (-w.im)) / 2 := by
    rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
    gcongr
    calc ‖Complex.exp (-w * I) - Complex.exp (w * I)‖
        ≤ ‖Complex.exp (-w * I)‖ + ‖Complex.exp (w * I)‖ := norm_sub_le _ _
      _ = Real.exp w.im + Real.exp (-w.im) := by rw [h1, h2]
  refine h.trans ?_
  have h3 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.2 (le_abs_self _)
  have h4 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.2 (neg_le_abs _)
  linarith

/-- `|sinc w| ≤ e^{|Im w|}` on all of `ℂ` (Phragmén–Lindelöf, or `sinc w = ∫₀¹ cos (t w) dt`). -/
theorem norm_csinc_le_exp_abs_im (w : ℂ) : ‖csinc w‖ ≤ Real.exp |w.im| := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    differentiable_csinc.continuous.continuousOn
  have hK1 : 0 ≤ max K 1 := zero_le_one.trans (le_max_right _ _)
  have hexp : IsExpTypeLE 1 csinc := by
    refine IsExpTypeLE.of_bound (C := max K 1) fun w ↦ ?_
    by_cases hw : ‖w‖ ≤ 1
    · calc ‖csinc w‖ ≤ K := hK w (mem_closedBall_zero_iff.2 hw)
        _ ≤ max K 1 := le_max_left _ _
        _ ≤ max K 1 * Real.exp (1 * ‖w‖) :=
            le_mul_of_one_le_right hK1 (Real.one_le_exp (by positivity))
    · rw [not_le] at hw
      have hw0 : w ≠ 0 := by
        rintro rfl
        simp at hw
        linarith
      calc ‖csinc w‖ ≤ Real.exp |w.im| / ‖w‖ := by
            rw [csinc_of_ne_zero hw0, norm_div]
            gcongr
            exact norm_sin_le_exp_abs_im w
        _ ≤ Real.exp |w.im| := div_le_self (Real.exp_pos _).le hw.le
        _ ≤ Real.exp (1 * ‖w‖) := by
            rw [one_mul]
            exact Real.exp_le_exp.2 (Complex.abs_im_le_norm w)
        _ ≤ max K 1 * Real.exp (1 * ‖w‖) :=
            le_mul_of_one_le_left (Real.exp_pos _).le (le_max_right _ _)
  have := norm_le_mul_exp_abs_im differentiable_csinc hexp zero_le_one (M := 1)
    norm_csinc_ofReal_le_one w
  simpa using this

theorem norm_csinc_le_div {w : ℂ} (hw : w ≠ 0) : ‖csinc w‖ ≤ Real.exp |w.im| / ‖w‖ := by
  rw [csinc_of_ne_zero hw, norm_div]
  gcongr
  exact norm_sin_le_exp_abs_im w

/-- `S_{δ,a} = csinc (δ (· - a)) ∈ 𝓑_δ`. -/
theorem memBernstein_csinc {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    MemBernstein δ (fun z ↦ csinc (δ * (z - a))) := by
  refine ⟨differentiable_csinc.comp ((differentiable_id.sub_const _).const_mul _), ?_,
    ⟨1, fun x ↦ ?_⟩⟩
  · refine IsExpTypeLE.of_bound (C := 1) fun z ↦ ?_
    refine (norm_csinc_le_exp_abs_im _).trans ?_
    rw [one_mul]
    apply Real.exp_le_exp.2
    have : ((δ : ℂ) * (z - a)).im = δ * z.im := by simp
    rw [this, abs_mul, abs_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) hδ
  · have := norm_csinc_ofReal_le_one (δ * (x - a))
    push_cast at this
    exact this

theorem norm_csinc_mul_sub_ofReal_le_one (δ a x : ℝ) : ‖csinc (δ * ((x : ℂ) - a))‖ ≤ 1 := by
  have := norm_csinc_ofReal_le_one (δ * (x - a))
  push_cast at this
  exact this

theorem csinc_mul_sub_self (δ a : ℝ) : csinc (δ * ((a : ℂ) - a)) = 1 := by
  simp

/-- `|S_{δ,a}(z)| ≤ e^{δ|Im z|} / (δ |z - a|)` for real `a` and `z ≠ a`. -/
theorem norm_csinc_mul_sub_le {δ : ℝ} (hδ : 0 < δ) (a : ℝ) {z : ℂ} (hz : z ≠ a) :
    ‖csinc (δ * (z - a))‖ ≤ Real.exp (δ * |z.im|) / (δ * ‖z - a‖) := by
  have hw : (δ : ℂ) * (z - a) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hδ.ne') (sub_ne_zero.2 hz)
  refine (norm_csinc_le_div hw).trans (le_of_eq ?_)
  have h1 : ((δ : ℂ) * (z - a)).im = δ * z.im := by simp
  rw [h1, abs_mul, abs_of_pos hδ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ.le]

/-! ### Finite products of sines -/

/-- `G(z) = ∏_{w ∈ s} sin(π (z - w) / P)` (p. 414, with `P = R - 2r`). -/
def sineProduct (s : Finset ℂ) (P : ℝ) (z : ℂ) : ℂ :=
  ∏ w ∈ s, Complex.sin (Real.pi * (z - w) / P)

theorem differentiable_sineProduct (s : Finset ℂ) (P : ℝ) :
    Differentiable ℂ (sineProduct s P) := by
  unfold sineProduct
  fun_prop

theorem sineProduct_eq_zero (s : Finset ℂ) (P : ℝ) {w : ℂ} (hw : w ∈ s) :
    sineProduct s P w = 0 := by
  exact Finset.prod_eq_zero hw (by simp)

/-- `|G|` is `P`-periodic (on all of `ℂ`): `sin(θ + π) = - sin θ`. -/
theorem norm_sineProduct_add (s : Finset ℂ) (P : ℝ) (z : ℂ) :
    ‖sineProduct s P (z + P)‖ = ‖sineProduct s P z‖ := by
  by_cases hP : P = 0
  · subst hP
    simp
  · have hP' : (P : ℂ) ≠ 0 := by exact_mod_cast hP
    unfold sineProduct
    rw [norm_prod, norm_prod]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    have : (Real.pi : ℂ) * (z + P - w) / P = Real.pi * (z - w) / P + Real.pi := by
      field_simp
      ring
    rw [this, Complex.sin_add_pi, norm_neg]

theorem norm_sineProduct_le (s : Finset ℂ) {P : ℝ} (hP : 0 < P) (z : ℂ) :
    ‖sineProduct s P z‖ ≤
      Real.exp (Real.pi * s.card * |z.im| / P + Real.pi * (∑ w ∈ s, |w.im|) / P) := by
  unfold sineProduct
  rw [norm_prod]
  calc ∏ w ∈ s, ‖Complex.sin (Real.pi * (z - w) / P)‖
      ≤ ∏ w ∈ s, Real.exp (Real.pi * |z.im| / P + Real.pi * |w.im| / P) :=
        Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun w _ ↦ ?_
    _ = Real.exp (∑ w ∈ s, (Real.pi * |z.im| / P + Real.pi * |w.im| / P)) :=
        (Real.exp_sum _ _).symm
    _ = Real.exp (Real.pi * s.card * |z.im| / P + Real.pi * (∑ w ∈ s, |w.im|) / P) := by
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div,
          ← Finset.mul_sum]
        ring
  refine (norm_sin_le_exp_abs_im _).trans (Real.exp_le_exp.2 ?_)
  have : ((Real.pi : ℂ) * (z - w) / P).im = Real.pi * (z.im - w.im) / P := by simp
  rw [this, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hP, ← add_div, ← mul_add]
  gcongr
  exact abs_sub _ _

theorem isExpTypeLE_sineProduct (s : Finset ℂ) {P : ℝ} (hP : 0 < P) :
    IsExpTypeLE (Real.pi * s.card / P) (sineProduct s P) := by
  refine IsExpTypeLE.of_bound (C := Real.exp (Real.pi * (∑ w ∈ s, |w.im|) / P)) fun z ↦ ?_
  refine (norm_sineProduct_le s hP z).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : Real.pi * s.card * |z.im| / P ≤ Real.pi * s.card / P * ‖z‖ := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) (by positivity)
  linarith

theorem memBernstein_sineProduct (s : Finset ℂ) {P : ℝ} (hP : 0 < P) :
    MemBernstein (Real.pi * s.card / P) (sineProduct s P) := by
  refine ⟨differentiable_sineProduct s P, isExpTypeLE_sineProduct s hP,
    ⟨Real.exp (Real.pi * (∑ w ∈ s, |w.im|) / P), fun x ↦ ?_⟩⟩
  simpa using norm_sineProduct_le s hP x

/-- The maximum of `|G|` over a closed interval of length `P` is a global maximum on `ℝ`
(periodicity), and `G` does not vanish there. -/
theorem exists_max_sineProduct (s : Finset ℂ) {P : ℝ} (hP : 0 < P) (a : ℝ) :
    ∃ x₀ ∈ Icc a (a + P), sineProduct s P x₀ ≠ 0 ∧
      ∀ x : ℝ, ‖sineProduct s P x‖ ≤ ‖sineProduct s P x₀‖ := by
  set G : ℝ → ℝ := fun x ↦ ‖sineProduct s P x‖ with hG
  have hGc : Continuous G :=
    ((differentiable_sineProduct s P).continuous.comp continuous_ofReal).norm
  have hper : Function.Periodic G P := fun x ↦ by
    simp only [hG, ofReal_add]
    exact norm_sineProduct_add s P x
  have haP : a ≤ a + P := by linarith
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 haP) hGc.continuousOn
  -- the real zeros of `G` in `[a, a + P]` are finitely many
  set Z : Set ℝ := ⋃ w ∈ (s : Set ℂ),
    (fun k : ℤ ↦ w.re + k * P) '' Icc ⌈(a - w.re) / P⌉ ⌊(a + P - w.re) / P⌋ with hZ
  have hZf : Z.Finite :=
    Set.Finite.biUnion s.finite_toSet fun w _ ↦ (Set.finite_Icc _ _).image _
  have hzero : ∀ x ∈ Icc a (a + P), sineProduct s P x = 0 → x ∈ Z := by
    intro x hx h0
    obtain ⟨w, hw, hw0⟩ := Finset.prod_eq_zero_iff.1 h0
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 hw0
    have hre := congrArg Complex.re hk
    simp only [div_ofReal_re, mul_re, ofReal_re, ofReal_im, sub_re, sub_im, zero_mul,
      sub_zero, intCast_re, intCast_im, mul_zero] at hre
    have hxk : x = w.re + k * P := by
      field_simp at hre
      nlinarith [Real.pi_pos]
    rw [hZ, Set.mem_iUnion₂]
    refine ⟨w, hw, k, ⟨?_, ?_⟩, hxk.symm⟩
    · rw [Int.ceil_le, div_le_iff₀ hP]
      linarith [hx.1]
    · rw [Int.le_floor, le_div_iff₀ hP]
      linarith [hx.2]
  obtain ⟨x₁, hx₁, hx₁Z⟩ := ((Set.Icc_infinite (by linarith : a < a + P)).sdiff hZf).nonempty
  have hx₁0 : sineProduct s P x₁ ≠ 0 := fun h ↦ hx₁Z (hzero x₁ hx₁ h)
  refine ⟨x₀, hx₀, ?_, fun x ↦ ?_⟩
  · intro h0
    have h1 : G x₁ ≤ G x₀ := isMaxOn_iff.1 hmax x₁ hx₁
    simp only [hG, h0, norm_zero] at h1
    exact hx₁0 (norm_le_zero_iff.1 h1)
  · obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico hP x a
    have h1 : G y ≤ G x₀ := isMaxOn_iff.1 hmax y (Ico_subset_Icc_self hy)
    change G x ≤ G x₀
    rw [hxy]
    exact h1

end OCS
