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
      nlinarith [Real.pi_gt_three, sq_nonneg w.im]
    have hmin2 : (min 1 ‖w - n‖) ^ 2 ≤ δ ^ 2 + w.im ^ 2 := by
      rw [← hnorm]
      exact pow_le_pow_left₀ hm0 (min_le_right _ _) 2
    have hsn : 2 * min 1 ‖w - n‖ ≤ ‖Complex.sin (Real.pi * w)‖ := by
      by_contra hc; push Not at hc
      nlinarith [norm_nonneg (Complex.sin (Real.pi * w))]
    have hexp : Real.exp (Real.pi * |w.im|) ≤ Real.exp 2 := by
      apply Real.exp_le_exp.2
      nlinarith [Real.pi_lt_four, abs_nonneg w.im]
    have hee : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
    calc min (1 / 4) (2 * Real.exp (-2)) * Real.exp (Real.pi * |w.im|) * min 1 ‖w - n‖
        ≤ (2 * Real.exp (-2)) * Real.exp 2 * min 1 ‖w - n‖ := by gcongr
      _ = 2 * min 1 ‖w - n‖ := by rw [mul_assoc 2, hee]; ring
      _ ≤ _ := hsn

end Translate

end FF
