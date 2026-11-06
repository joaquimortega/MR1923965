import FourierFrames.Construction.Gaps
import FourierFrames.Construction.Comparable
import FourierFrames.Construction.Limits
import OrtegaCerdaSeip.Bernstein.NormalFamily

/-!
# Limits of translates of `A` (aux file for `Construction.lean`, M07 §2.7(a))
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace FF

namespace Translate

variable {m : ℝ → ℝ} {a b : ℝ}

theorem norm_multF_comparable_of_hU (hw : OCS.IsMultWeight m a b) {κ : ℝ}
    (hU : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℂ,
      c₁ * Real.exp (Real.pi * |z.im| + κ * z.re) * min 1 (infDist z (OCS.multGammaC m)) ≤
        ‖OCS.multF m 0 z‖ ∧
      ‖OCS.multF m 0 z‖ ≤
        c₂ * Real.exp (Real.pi * |z.im| + κ * z.re) * min 1 (infDist z (OCS.multGammaC m)) := by
  obtain ⟨C, hC⟩ := hU
  have hCall : ∀ z : ℂ, |OCS.multU m 0 z - (Real.pi * |z.im| + κ * z.re)| ≤ C := by
    intro z
    rcases le_total 0 z.im with h | h
    · rw [abs_of_nonneg h]; have := hC z h; rwa [sub_sub] at this
    · have := hC (conj z) (by simpa using h)
      rw [OCS.multU_conj] at this
      simp only [Complex.conj_im, Complex.conj_re, mul_neg, sub_neg_eq_add] at this
      rw [abs_of_nonpos h]
      convert this using 2
      ring
  obtain ⟨c₁, c₂, hc₁, hc₂, hc⟩ := Comparable.norm_multF_comparable hw
  refine ⟨c₁ * Real.exp (-C), c₂ * Real.exp C, by positivity, by positivity, fun z ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hc z
  have hb := abs_le.1 (hCall z)
  have e1 : Real.exp (-C) * Real.exp (Real.pi * |z.im| + κ * z.re) ≤
      Real.exp (OCS.multU m 0 z) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have e2 : Real.exp (OCS.multU m 0 z) ≤
      Real.exp C * Real.exp (Real.pi * |z.im| + κ * z.re) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have hm : 0 ≤ min 1 (infDist z (OCS.multGammaC m)) := le_min zero_le_one infDist_nonneg
  constructor
  · refine le_trans ?_ h1
    have : c₁ * (Real.exp (-C) * Real.exp (Real.pi * |z.im| + κ * z.re)) ≤
        c₁ * Real.exp (OCS.multU m 0 z) := by gcongr
    nlinarith [mul_le_mul_of_nonneg_right this hm]
  · refine h2.trans ?_
    have : c₂ * Real.exp (OCS.multU m 0 z) ≤
        c₂ * (Real.exp C * Real.exp (Real.pi * |z.im| + κ * z.re)) := by gcongr
    nlinarith [mul_le_mul_of_nonneg_right this hm]

/-- The normalised translates `G_s(z) = F(z+s) e^{-κ(z+s)}`. -/
def Gk (m : ℝ → ℝ) (κ s : ℝ) (z : ℂ) : ℂ :=
  OCS.multF m 0 (z + s) * Complex.exp (-((κ : ℂ) * (z + s)))

theorem norm_Gk (m : ℝ → ℝ) (κ s : ℝ) (z : ℂ) :
    ‖Gk m κ s z‖ = ‖OCS.multF m 0 (z + s)‖ * Real.exp (-(κ * (z.re + s))) := by
  unfold Gk
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp

theorem Gk_bounds (hw : OCS.IsMultWeight m a b) {κ : ℝ}
    (hU : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (s : ℝ) (z : ℂ),
      c₁ * Real.exp (Real.pi * |z.im|) * min 1 (infDist (z + s) (OCS.multGammaC m)) ≤
        ‖Gk m κ s z‖ ∧
      ‖Gk m κ s z‖ ≤
        c₂ * Real.exp (Real.pi * |z.im|) * min 1 (infDist (z + s) (OCS.multGammaC m)) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hc⟩ := norm_multF_comparable_of_hU hw hU
  refine ⟨c₁, c₂, hc₁, hc₂, fun s z ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hc (z + s)
  have hE : Real.exp (Real.pi * |z.im| + κ * (z.re + s)) * Real.exp (-(κ * (z.re + s))) =
      Real.exp (Real.pi * |z.im|) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero] at h1 h2
  rw [norm_Gk]
  have hpos := Real.exp_pos (-(κ * (z.re + s)))
  constructor
  · calc c₁ * Real.exp (Real.pi * |z.im|) * min 1 (infDist (z + s) (OCS.multGammaC m))
        = (c₁ * Real.exp (Real.pi * |z.im| + κ * (z.re + s)) *
            min 1 (infDist (z + s) (OCS.multGammaC m))) * Real.exp (-(κ * (z.re + s))) := by
          rw [← hE]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hpos.le
  · calc ‖OCS.multF m 0 (z + s)‖ * Real.exp (-(κ * (z.re + s)))
        ≤ (c₂ * Real.exp (Real.pi * |z.im| + κ * (z.re + s)) *
            min 1 (infDist (z + s) (OCS.multGammaC m))) * Real.exp (-(κ * (z.re + s))) :=
          mul_le_mul_of_nonneg_right h2 hpos.le
      _ = _ := by rw [← hE]; ring

theorem sin_re' (z : ℂ) : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [Complex.sin_add, Complex.cos_mul_I]
  simp [Complex.sin_mul_I, ← Complex.ofReal_cosh, Complex.sin_ofReal_re]

theorem sin_im' (z : ℂ) : (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [Complex.sin_add, Complex.cos_mul_I]
  simp [Complex.sin_mul_I, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.cos_ofReal_re,
    Complex.sin_ofReal_im]

theorem norm_sin_sq (z : ℂ) : ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, sin_re', sin_im']
  have := Real.cosh_sq z.im
  have h2 := Real.sin_sq_add_cos_sq z.re
  nlinarith [this, h2]

theorem sinh_lower_large {t : ℝ} (ht : 1 ≤ t) : Real.exp t / 4 ≤ Real.sinh t := by
  rw [Real.sinh_eq]
  have h2 : (2 : ℝ) ≤ Real.exp (2 * t) := by
    have := Real.add_one_le_exp (2 * t); linarith
  have e3 : Real.exp (-t) * Real.exp (2 * t) = Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  have hp := Real.exp_pos t
  have hq := Real.exp_pos (-t)
  nlinarith

/-- Lower bound for `|sin π w|`. -/
theorem sin_lower : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ w : ℂ, ∃ n : ℤ,
    c₀ * Real.exp (Real.pi * |w.im|) * min 1 ‖w - n‖ ≤ ‖Complex.sin (Real.pi * w)‖ := by
  refine ⟨min (1 / 4) (2 * Real.exp (-2)), lt_min (by norm_num) (by positivity), fun w ↦ ?_⟩
  refine ⟨round w.re, ?_⟩
  set n : ℤ := round w.re with hn
  have hsq := norm_sin_sq (Real.pi * w)
  have hre : ((Real.pi : ℂ) * w).re = Real.pi * w.re := by simp
  have him : ((Real.pi : ℂ) * w).im = Real.pi * w.im := by simp
  rw [hre, him] at hsq
  have hδ : |w.re - n| ≤ 1 / 2 := abs_sub_round w.re
  have hm0 : 0 ≤ min 1 ‖w - n‖ := le_min zero_le_one (norm_nonneg _)
  have hm1 : min 1 ‖w - n‖ ≤ 1 := min_le_left _ _
  have hE0 := Real.exp_pos (Real.pi * |w.im|)
  have hc1 : min (1 / 4) (2 * Real.exp (-2)) ≤ 1 / 4 := min_le_left _ _
  have hc2 : min (1 / 4) (2 * Real.exp (-2)) ≤ 2 * Real.exp (-2) := min_le_right _ _
  have hsinh : |Real.sinh (Real.pi * w.im)| = Real.sinh (Real.pi * |w.im|) := by
    rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos]
  have hsinhsq : Real.sinh (Real.pi * w.im) ^ 2 = Real.sinh (Real.pi * |w.im|) ^ 2 := by
    rw [← sq_abs, hsinh]
  by_cases hy : 1 / 2 ≤ |w.im|
  · have ht : 1 ≤ Real.pi * |w.im| := by nlinarith [Real.pi_gt_three]
    have h1 := sinh_lower_large ht
    have h2 : 0 ≤ Real.sinh (Real.pi * |w.im|) := by
      have := Real.exp_pos (Real.pi * |w.im|); linarith
    have h3 : Real.sinh (Real.pi * |w.im|) ≤ ‖Complex.sin (Real.pi * w)‖ := by
      by_contra hc; push Not at hc
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * w.re), sq_nonneg (Real.sin (Real.pi * w.re)),
        norm_nonneg (Complex.sin (Real.pi * w))]
    calc min (1 / 4) (2 * Real.exp (-2)) * Real.exp (Real.pi * |w.im|) * min 1 ‖w - n‖
        ≤ (1 / 4) * Real.exp (Real.pi * |w.im|) * 1 := by gcongr
      _ ≤ _ := by linarith
  · push Not at hy
    -- small imaginary part
    set δ := w.re - n with hδdef
    have hs1 : 2 * |δ| ≤ |Real.sin (Real.pi * δ)| := by
      have h := Real.mul_le_sin (x := Real.pi * |δ|) (by positivity) (by
        have := abs_nonneg δ; nlinarith [Real.pi_pos])
      have h' : 2 / Real.pi * (Real.pi * |δ|) = 2 * |δ| := by field_simp
      rw [h'] at h
      rcases le_total 0 δ with hd | hd
      · rw [abs_of_nonneg hd] at h ⊢
        exact h.trans (le_abs_self _)
      · rw [abs_of_nonpos hd] at h ⊢
        have : Real.sin (Real.pi * -δ) = -Real.sin (Real.pi * δ) := by
          rw [mul_neg, Real.sin_neg]
        rw [this] at h
        exact h.trans (neg_le_abs _)
    have hsinx : Real.sin (Real.pi * w.re) ^ 2 = Real.sin (Real.pi * δ) ^ 2 := by
      have : Real.pi * w.re = Real.pi * δ + n * Real.pi := by rw [hδdef]; ring
      rw [this, Real.sin_add_int_mul_pi, mul_pow]
      have : (((-1 : ℝ) ^ n) ^ 2) = 1 := by
        rcases Int.even_or_odd n with h | h
        · rw [h.neg_one_zpow]; simp
        · rw [h.neg_one_zpow]; simp
      rw [this, one_mul]
    have hs2 : 2 * |δ| ≤ |Real.sin (Real.pi * w.re)| := by
      have : |Real.sin (Real.pi * w.re)| = |Real.sin (Real.pi * δ)| := by
        rw [← sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _), sq_abs, sq_abs, hsinx]
      rw [this]; exact hs1
    have hs3 : Real.pi * |w.im| ≤ |Real.sinh (Real.pi * w.im)| := by
      rw [hsinh]
      exact Real.self_le_sinh_iff.2 (by positivity)
    have hnorm : ‖w - n‖ ^ 2 = δ ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [hδdef]; ring
    have hlow : 4 * (δ ^ 2 + w.im ^ 2) ≤ ‖Complex.sin (Real.pi * w)‖ ^ 2 := by
      rw [hsq]
      have a1 : 4 * δ ^ 2 ≤ Real.sin (Real.pi * w.re) ^ 2 := by
        have hh : -|Real.sin (Real.pi * w.re)| ≤ 2 * |δ| := by
          nlinarith [abs_nonneg δ, abs_nonneg (Real.sin (Real.pi * w.re))]
        have := sq_le_sq' hh hs2
        nlinarith [sq_abs δ, sq_abs (Real.sin (Real.pi * w.re))]
      have a2 : Real.pi ^ 2 * w.im ^ 2 ≤ Real.sinh (Real.pi * w.im) ^ 2 := by
        have hh : -|Real.sinh (Real.pi * w.im)| ≤ Real.pi * |w.im| := by
          nlinarith [abs_nonneg w.im, Real.pi_pos, abs_nonneg (Real.sinh (Real.pi * w.im))]
        have := sq_le_sq' hh hs3
        nlinarith [sq_abs w.im, sq_abs (Real.sinh (Real.pi * w.im))]
      have hpi : 4 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      have := mul_le_mul_of_nonneg_right hpi (sq_nonneg w.im)
      linarith
    have hmin2 : (min 1 ‖w - n‖) ^ 2 ≤ δ ^ 2 + w.im ^ 2 := by
      rw [← hnorm]
      exact pow_le_pow_left₀ hm0 (min_le_right _ _) 2
    have hsn : 2 * min 1 ‖w - n‖ ≤ ‖Complex.sin (Real.pi * w)‖ := by
      have h4 : (2 * min 1 ‖w - n‖) ^ 2 ≤ ‖Complex.sin (Real.pi * w)‖ ^ 2 := by
        calc (2 * min 1 ‖w - n‖) ^ 2 = 4 * (min 1 ‖w - n‖) ^ 2 := by ring
          _ ≤ 4 * (δ ^ 2 + w.im ^ 2) := by linarith only [hmin2]
          _ ≤ _ := hlow
      exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h4
    have hexp : Real.exp (Real.pi * |w.im|) ≤ Real.exp 2 := by
      apply Real.exp_le_exp.2
      nlinarith [Real.pi_lt_four, abs_nonneg w.im]
    have hee : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
    calc min (1 / 4) (2 * Real.exp (-2)) * Real.exp (Real.pi * |w.im|) * min 1 ‖w - n‖
        ≤ (2 * Real.exp (-2)) * Real.exp 2 * min 1 ‖w - n‖ := by gcongr
      _ = 2 * min 1 ‖w - n‖ := by rw [mul_assoc 2, hee]; ring
      _ ≤ _ := hsn

theorem sin_shift_eq_zero_iff (θ : ℝ) (z : ℂ) :
    Complex.sin (Real.pi * (z - θ)) = 0 ↔ ∃ n : ℤ, z = θ + n := by
  rw [Complex.sin_eq_zero_iff]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : z - θ = k := by
      apply mul_left_cancel₀ hpi; rw [hk]; ring
    linear_combination this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

theorem sin_zero_unique (θ : ℝ) {z z' : ℂ} (hz : Complex.sin (Real.pi * (z - θ)) = 0)
    (hz' : Complex.sin (Real.pi * (z' - θ)) = 0) (h : ‖z - z'‖ < 1) : z = z' := by
  obtain ⟨n, rfl⟩ := (sin_shift_eq_zero_iff θ z).1 hz
  obtain ⟨k, rfl⟩ := (sin_shift_eq_zero_iff θ z').1 hz'
  have : ((n - k : ℤ) : ℂ) = (n : ℂ) - k := by push_cast; ring
  have h2 : ‖((n - k : ℤ) : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs]
    have : (((θ : ℂ) + n) - ((θ : ℂ) + k)) = ((n - k : ℤ) : ℝ) := by push_cast; ring
    rw [this, Complex.norm_real] at h
    simpa using h
  rw [Real.norm_eq_abs] at h2
  have : n - k = 0 := by
    have h3 : |n - k| < 1 := by exact_mod_cast h2
    rw [abs_lt] at h3; omega
  have : n = k := by omega
  rw [this]

/-- If `|G| ≤ K |sin π (· - θ)|` and `G` is entire, then `G = c sin π (· - θ)`. -/
theorem eq_const_mul_sin {G : ℂ → ℂ} (hd : Differentiable ℂ G) (θ K : ℝ)
    (hK : ∀ z, ‖G z‖ ≤ K * ‖Complex.sin (Real.pi * (z - θ))‖) :
    ∃ c : ℂ, ∀ z, G z = c * Complex.sin (Real.pi * (z - θ)) := by
  set S : ℂ → ℂ := fun z ↦ Complex.sin (Real.pi * (z - θ)) with hSdef
  have hSd : Differentiable ℂ S := by rw [hSdef]; fun_prop
  set f : ℂ → ℂ := fun z ↦ G z / S z with hf
  set Q : ℂ → ℂ := fun z ↦ limUnder (𝓝[≠] z) f with hQ
  have hfK : ∀ z, S z ≠ 0 → ‖f z‖ ≤ K := by
    intro z hz
    have h1 := hK z
    have h2 : 0 < ‖S z‖ := norm_pos_iff.2 hz
    rw [hf]; simp only [norm_div]
    rw [div_le_iff₀ h2]; exact h1
  have hQeq : ∀ z, S z ≠ 0 → Q z = f z := by
    intro z hz
    have hc : ContinuousAt f z := (hd.continuous.continuousAt).div hSd.continuous.continuousAt hz
    exact (hc.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  have hball : ∀ p, S p = 0 → ∀ z' ∈ ball p 1, z' ≠ p → S z' ≠ 0 := by
    intro p hp z' hz' hne h0
    refine hne (sin_zero_unique θ h0 hp ?_)
    rw [mem_ball, dist_eq_norm] at hz'; exact hz'
  have hQd : Differentiable ℂ Q := by
    intro p
    by_cases hp : S p = 0
    · have hsd : DifferentiableOn ℂ f (ball p 1 \ {p}) := by
        intro z' hz'
        have hne := hball p hp z' hz'.1 hz'.2
        exact ((hd z').div (hSd z') hne).differentiableWithinAt
      have hb : BddAbove (norm ∘ f '' (ball p 1 \ {p})) := by
        refine ⟨K, ?_⟩
        rintro _ ⟨z', hz', rfl⟩
        exact hfK z' (hball p hp z' hz'.1 hz'.2)
      have := Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds p one_pos) hsd hb
      have hev : Q =ᶠ[𝓝 p] Function.update f p (limUnder (𝓝[≠] p) f) := by
        filter_upwards [ball_mem_nhds p one_pos] with z' hz'
        by_cases hzp : z' = p
        · subst hzp; simp [hQ]
        · rw [Function.update_of_ne hzp]; exact hQeq z' (hball p hp z' hz' hzp)
      exact DifferentiableAt.congr_of_eventuallyEq
        (this.differentiableAt (ball_mem_nhds p one_pos)) hev
    · have hev : Q =ᶠ[𝓝 p] f := by
        have : {z' | S z' ≠ 0} ∈ 𝓝 p :=
          (isOpen_ne_fun hSd.continuous continuous_const).mem_nhds hp
        filter_upwards [this] with z' hz' using hQeq z' hz'
      exact DifferentiableAt.congr_of_eventuallyEq ((hd p).div (hSd p) hp) hev
  have hQb : ∀ z, ‖Q z‖ ≤ K := by
    intro p
    by_cases hp : S p = 0
    · have hev : ∀ᶠ z' in 𝓝[≠] p, ‖Q z'‖ ≤ K := by
        have : {p}ᶜ ∩ ball p 1 ∈ 𝓝[≠] p :=
          inter_mem_nhdsWithin _ (ball_mem_nhds p one_pos)
        filter_upwards [this] with z' hz'
        rw [hQeq z' (hball p hp z' hz'.2 hz'.1)]
        exact hfK z' (hball p hp z' hz'.2 hz'.1)
      exact le_of_tendsto ((hQd.continuous.tendsto p).mono_left nhdsWithin_le_nhds).norm hev
    · rw [hQeq p hp]; exact hfK p hp
  have hconst : ∀ z, Q z = Q 0 := fun z ↦
    hQd.apply_eq_apply_of_bounded
      (isBounded_iff_forall_norm_le.2 ⟨K, by rintro _ ⟨z, rfl⟩; exact hQb z⟩) z 0
  refine ⟨Q 0, fun z ↦ ?_⟩
  by_cases hz : S z = 0
  · have := hK z
    rw [show Complex.sin (Real.pi * (z - θ)) = 0 from hz, norm_zero, mul_zero] at this
    rw [norm_le_zero_iff.1 this, show Complex.sin (Real.pi * (z - θ)) = 0 from hz, mul_zero]
  · rw [← hconst z, hQeq z hz, hf]
    simp only
    rw [div_mul_cancel₀ _ hz]

/-! ### The zeros near `s` -/

section Zeros

variable (hw : OCS.IsMultWeight m a b)
include hw

theorem tt_bound (s : ℝ) :
    |OCS.multBary m (OCS.multIdx m s) - s| ≤ 1 / a := by
  have h1 := OCS.multIdx_mem hw s
  have h2 := OCS.multBary_mem hw (OCS.multIdx m s)
  have h3 := (OCS.multPt_succ_sub_bounds hw (OCS.multIdx m s)).2
  have hc : 0 < a / (2 * b ^ 2) := by have := hw.b_pos; have := hw.pos; positivity
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem tendsto_idx_cofinite {s : ℕ → ℝ} (hs : Tendsto (fun k ↦ |s k|) atTop atTop) :
    Tendsto (fun k ↦ OCS.multIdx m (s k)) atTop cofinite := by
  intro T hT
  rw [Filter.mem_cofinite] at hT
  obtain ⟨R, hR⟩ := (hT.image Int.natAbs).bddAbove
  set M : ℝ := max |OCS.multPt m (-(R : ℤ))| |OCS.multPt m ((R : ℤ) + 1)|
  have hev := hs.eventually_gt_atTop M
  rw [Filter.mem_map]
  filter_upwards [hev] with k hk
  by_contra hkT
  have hjT : OCS.multIdx m (s k) ∈ Tᶜ := hkT
  have hj : (OCS.multIdx m (s k)).natAbs ≤ R := hR ⟨_, hjT, rfl⟩
  have h1 := OCS.multIdx_mem hw (s k)
  have hmono := (OCS.strictMono_multPt hw).monotone
  have h2 : OCS.multPt m (-(R : ℤ)) ≤ OCS.multPt m (OCS.multIdx m (s k)) := hmono (by omega)
  have h3 : OCS.multPt m (OCS.multIdx m (s k) + 1) ≤ OCS.multPt m ((R : ℤ) + 1) :=
    hmono (by omega)
  have hl := le_max_left |OCS.multPt m (-(R : ℤ))| |OCS.multPt m ((R : ℤ) + 1)|
  have hr := le_max_right |OCS.multPt m (-(R : ℤ))| |OCS.multPt m ((R : ℤ) + 1)|
  have e1 := le_abs_self (OCS.multPt m ((R : ℤ) + 1))
  have e2 := neg_abs_le (OCS.multPt m (-(R : ℤ)))
  rw [lt_abs] at hk
  rcases hk with hk | hk <;> linarith [h1.1, h1.2]

end Zeros

theorem tendsto_multBary_add (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) (n : ℤ) :
    Tendsto (fun j : ℤ ↦ OCS.multBary m (j + n) - OCS.multBary m j) cofinite (𝓝 (n : ℝ)) := by
  have hg := Gaps.tendsto_multBary_succ_sub hw hlim
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have h1 := hg.comp (add_left_injective (i : ℤ)).tendsto_cofinite
    have h2 : Tendsto (fun j : ℤ ↦ OCS.multBary m (j + ((i : ℤ) + 1)) - OCS.multBary m j) cofinite
        (𝓝 (1 + ((i : ℤ) : ℝ))) := (h1.add ih).congr fun j ↦ by
      simp only [Function.comp]
      rw [show j + ((i : ℤ) + 1) = j + i + 1 by ring]
      ring
    convert h2 using 2
    push_cast; ring
  | pred i ih =>
    have h1 := hg.comp (add_left_injective (-(i : ℤ) - 1)).tendsto_cofinite
    have h2 : Tendsto (fun j : ℤ ↦ OCS.multBary m (j + (-(i : ℤ) - 1)) - OCS.multBary m j) cofinite
        (𝓝 (((-(i : ℤ) : ℤ) : ℝ) - 1)) := (ih.sub h1).congr fun j ↦ by
      simp only [Function.comp]
      rw [show j + (-(i : ℤ) - 1) + 1 = j + -(i : ℤ) by ring]
      ring
    convert h2 using 2
    push_cast; ring

/-- `t_k = γ_{j(s_k)} - s_k`. -/
def tt (m : ℝ → ℝ) (s : ℕ → ℝ) (k : ℕ) : ℝ :=
  OCS.multBary m (OCS.multIdx m (s k)) - s k

theorem tendsto_shifted (hw : OCS.IsMultWeight m a b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1))
    {s : ℕ → ℝ} (hs : Tendsto (fun k ↦ |s k|) atTop atTop) {θ : ℝ}
    (ht : Tendsto (tt m s) atTop (𝓝 θ)) (n : ℤ) :
    Tendsto (fun k ↦ OCS.multBary m (OCS.multIdx m (s k) + n) - s k) atTop (𝓝 (θ + n)) := by
  have h1 := (tendsto_multBary_add hw hlim n).comp (tendsto_idx_cofinite hw hs)
  have h2 := h1.add ht
  have h3 : Tendsto (fun k ↦ OCS.multBary m (OCS.multIdx m (s k) + n) - s k) atTop
      (𝓝 ((n : ℝ) + θ)) := h2.congr fun k ↦ by
    simp only [Function.comp, tt]
    ring
  rwa [add_comm] at h3

theorem tendsto_gap (hw : OCS.IsMultWeight m a b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1))
    {s : ℕ → ℝ} (hs : Tendsto (fun k ↦ |s k|) atTop atTop) :
    Tendsto (fun k ↦ OCS.multBary m (OCS.multIdx m (s k) + 1) -
      OCS.multBary m (OCS.multIdx m (s k))) atTop (𝓝 1) :=
  (Gaps.tendsto_multBary_succ_sub hw hlim).comp (tendsto_idx_cofinite hw hs)

/-- The point `θ + 1/2 + s_k` stays at distance `≥ 1/4` from `Γ`. -/
theorem eventually_infDist_ge (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1))
    {s : ℕ → ℝ} (hs : Tendsto (fun k ↦ |s k|) atTop atTop) {θ : ℝ}
    (ht : Tendsto (tt m s) atTop (𝓝 θ)) :
    ∀ᶠ k in atTop, 1 / 4 ≤ infDist (((θ + 1 / 2 : ℝ) : ℂ) + (s k : ℂ)) (OCS.multGammaC m) := by
  have e1 : Tendsto (fun k ↦ θ + 1 / 2 - tt m s k) atTop (𝓝 (1 / 2)) := by
    have := (tendsto_const_nhds (x := θ + 1 / 2)).sub ht
    simpa using this
  have e2 : Tendsto (fun k ↦ tt m s k + (OCS.multBary m (OCS.multIdx m (s k) + 1) -
      OCS.multBary m (OCS.multIdx m (s k))) - θ - 1 / 2) atTop (𝓝 (1 / 2)) := by
    have := ((ht.add (tendsto_gap hw hlim hs)).sub (tendsto_const_nhds (x := θ))).sub
      (tendsto_const_nhds (x := (1 / 2 : ℝ)))
    convert this using 2
    ring
  filter_upwards [(tendsto_order.1 e1).1 (1 / 4 : ℝ) (by norm_num),
    (tendsto_order.1 e2).1 (1 / 4 : ℝ) (by norm_num)]
    with k hk1 hk2
  simp only [tt] at hk1 hk2
  have hne : (OCS.multGammaC m).Nonempty := ⟨_, ⟨_, ⟨0, rfl⟩, rfl⟩⟩
  rw [le_infDist hne]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  rw [Complex.dist_eq]
  have : (((θ + 1 / 2 : ℝ) : ℂ) + (s k : ℂ)) - ((OCS.multBary m j : ℝ) : ℂ) =
      ((θ + 1 / 2 + s k - OCS.multBary m j : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  have hmono := (OCS.strictMono_multBary hw).monotone
  rcases le_or_gt j (OCS.multIdx m (s k)) with hj | hj
  · have := hmono hj
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have := hmono (show OCS.multIdx m (s k) + 1 ≤ j by omega)
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem differentiable_Gk (hw : OCS.IsMultWeight m a b) (κ s : ℝ) :
    Differentiable ℂ (Gk m κ s) := by
  have := OCS.differentiable_multF hw 0
  unfold Gk
  fun_prop

theorem Gk_im_real (hw : OCS.IsMultWeight m a b) (κ s x : ℝ) : (Gk m κ s (x : ℂ)).im = 0 := by
  have h := OCS.multF_conj hw 0 ((x : ℂ) + s)
  have hc : conj ((x : ℂ) + s) = (x : ℂ) + s := by simp
  rw [hc] at h
  have h2 : (OCS.multF m 0 ((x : ℂ) + s)).im = 0 := Complex.conj_eq_iff_im.1 h.symm
  unfold Gk
  have h3 : (Complex.exp (-((κ : ℂ) * ((x : ℂ) + s)))).im = 0 := by
    have : -((κ : ℂ) * ((x : ℂ) + s)) = ((-(κ * (x + s)) : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_exp]; exact Complex.ofReal_im _
  rw [Complex.mul_im, h2, h3]; ring

/-- **Identification of the limit.** -/
theorem identify_limit (hw : OCS.IsMultWeight m a b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1))
    {κ : ℝ}
    (hU : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C)
    {s : ℕ → ℝ} (hs : Tendsto (fun k ↦ |s k|) atTop atTop) {θ : ℝ}
    (ht : Tendsto (tt m s) atTop (𝓝 θ)) {G : ℂ → ℂ} (hd : Differentiable ℂ G)
    (hG : TendstoLocallyUniformly (fun k z ↦ Gk m κ (s k) z) G atTop) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ z, G z = c * Complex.sin (Real.pi * (z - θ)) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hc⟩ := Gk_bounds hw hU
  obtain ⟨c₀, hc₀, hsin⟩ := sin_lower
  have hpt : ∀ z, Tendsto (fun k ↦ Gk m κ (s k) z) atTop (𝓝 (G z)) := fun z ↦
    (tendstoLocallyUniformlyOn_univ.2 hG).tendsto_at (mem_univ z)
  -- upper bound
  have hup : ∀ (z : ℂ) (n : ℤ), ‖G z‖ ≤
      c₂ * Real.exp (Real.pi * |z.im|) * min 1 ‖z - θ - n‖ := by
    intro z n
    have hp := tendsto_shifted hw hlim hs ht n
    have h1 : Tendsto (fun k ↦ c₂ * Real.exp (Real.pi * |z.im|) *
        min 1 ‖z - ((OCS.multBary m (OCS.multIdx m (s k) + n) - s k : ℝ) : ℂ)‖) atTop
        (𝓝 (c₂ * Real.exp (Real.pi * |z.im|) * min 1 ‖z - ((θ + n : ℝ) : ℂ)‖)) := by
      refine tendsto_const_nhds.mul ?_
      refine (tendsto_const_nhds.min ?_)
      exact ((tendsto_const_nhds.sub ((Complex.continuous_ofReal.tendsto _).comp hp))).norm
    have h2 : Tendsto (fun k ↦ ‖Gk m κ (s k) z‖) atTop (𝓝 ‖G z‖) := (hpt z).norm
    have := le_of_tendsto_of_tendsto h2 h1 (Eventually.of_forall fun k ↦ ?_)
    · refine this.trans (le_of_eq ?_)
      congr 3
      push_cast; ring_nf
    · refine (hc (s k) z).2.trans ?_
      have hmem : ((OCS.multBary m (OCS.multIdx m (s k) + n) : ℝ) : ℂ) ∈ OCS.multGammaC m :=
        ⟨_, ⟨_, rfl⟩, rfl⟩
      have hd1 := infDist_le_dist_of_mem (x := z + (s k : ℂ)) hmem
      have : dist (z + (s k : ℂ)) ((OCS.multBary m (OCS.multIdx m (s k) + n) : ℝ) : ℂ) =
          ‖z - ((OCS.multBary m (OCS.multIdx m (s k) + n) - s k : ℝ) : ℂ)‖ := by
        rw [dist_eq_norm]; congr 1; push_cast; ring
      rw [this] at hd1
      have hpos : 0 ≤ c₂ * Real.exp (Real.pi * |z.im|) := by positivity
      exact mul_le_mul_of_nonneg_left (min_le_min le_rfl hd1) hpos
  -- comparison with the sine
  have hK : ∀ z, ‖G z‖ ≤ (c₂ / c₀) * ‖Complex.sin (Real.pi * (z - θ))‖ := by
    intro z
    obtain ⟨n, hn⟩ := hsin (z - θ)
    have him : (z - (θ : ℂ)).im = z.im := by simp
    rw [him] at hn
    have := hup z n
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
    calc ‖G z‖ * c₀ ≤ c₂ * Real.exp (Real.pi * |z.im|) * min 1 ‖z - θ - n‖ * c₀ := by gcongr
      _ = c₂ * (c₀ * Real.exp (Real.pi * |z.im|) * min 1 ‖z - θ - n‖) := by ring
      _ ≤ _ := by gcongr
  obtain ⟨c, hcG⟩ := eq_const_mul_sin hd θ (c₂ / c₀) hK
  -- the value at θ + 1/2
  set z₀ : ℂ := ((θ + 1 / 2 : ℝ) : ℂ) with hz₀
  have hsin0 : Complex.sin (Real.pi * (z₀ - θ)) = 1 := by
    rw [hz₀]
    have : (Real.pi : ℂ) * (((θ + 1 / 2 : ℝ) : ℂ) - θ) = (Real.pi / 2 : ℝ) := by
      push_cast; ring
    rw [this, ← Complex.ofReal_sin, Real.sin_pi_div_two]; simp
  have hGz0 : G z₀ = c := by rw [hcG z₀, hsin0, mul_one]
  have hlow : c₁ / 4 ≤ ‖G z₀‖ := by
    have h2 : Tendsto (fun k ↦ ‖Gk m κ (s k) z₀‖) atTop (𝓝 ‖G z₀‖) := (hpt z₀).norm
    refine ge_of_tendsto h2 ?_
    filter_upwards [eventually_infDist_ge hw hlim hs ht] with k hk
    refine (hc (s k) z₀).1.trans' ?_
    have him : z₀.im = 0 := by rw [hz₀]; exact Complex.ofReal_im _
    rw [him]
    simp only [abs_zero, mul_zero, Real.exp_zero, mul_one]
    have : (1 / 4 : ℝ) ≤ min 1 (infDist (z₀ + (s k : ℂ)) (OCS.multGammaC m)) :=
      le_min (by norm_num) hk
    calc c₁ / 4 = c₁ * (1 / 4) := by ring
      _ ≤ _ := by gcongr
  have hcim : c.im = 0 := by
    have h2 : Tendsto (fun k ↦ (Gk m κ (s k) z₀).im) atTop (𝓝 (G z₀).im) :=
      (Complex.continuous_im.tendsto _).comp (hpt z₀)
    have h3 : Tendsto (fun k ↦ (Gk m κ (s k) z₀).im) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr fun k ↦ ?_
      exact (Gk_im_real hw κ (s k) (θ + 1 / 2)).symm
    rw [← hGz0]; exact tendsto_nhds_unique h2 h3
  have hcne : c ≠ 0 := by
    intro h0
    rw [hGz0, h0, norm_zero] at hlow
    linarith
  refine ⟨c.re, fun h ↦ hcne (Complex.ext (by simpa using h) (by simpa using hcim)), fun z ↦ ?_⟩
  rw [hcG z]
  congr 1
  exact Complex.ext (by simp) (by simp [hcim])

end Translate

end FF
