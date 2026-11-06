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

end Translate

end FF
