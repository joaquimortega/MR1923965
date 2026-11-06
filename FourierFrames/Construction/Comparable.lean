import OrtegaCerdaSeip.Lemma3.Main

/-!
# Comparability of `A = OCS.multF m 0` on all of `ℂ` (aux file for `Construction.lean`, M07 §2.1)
-/

open MeasureTheory Metric Set Complex Filter Topology

noncomputable section

namespace FF

namespace Comparable

variable {m : ℝ → ℝ} {a b : ℝ}

theorem abs_im_le_infDist (z : ℂ) :
    |z.im| ≤ infDist z (OCS.multGammaC m) := by
  have hmem : ((OCS.multBary m 0 : ℝ) : ℂ) ∈ OCS.multGammaC m := ⟨_, ⟨0, rfl⟩, rfl⟩
  have hne : (OCS.multGammaC m).Nonempty := ⟨_, hmem⟩
  rw [le_infDist hne]
  intro y hy
  have := OCS.im_eq_zero_of_mem_multGammaC hy
  rw [dist_eq_norm]
  calc |z.im| = |(z - y).im| := by simp [this]
    _ ≤ ‖z - y‖ := Complex.abs_im_le_norm _

theorem infDist_le_add (hw : OCS.IsMultWeight m a b) (z : ℂ) :
    infDist z (OCS.multGammaC m) ≤ |z.im| + 1 / a := by
  have ha := hw.pos
  set k := OCS.multIdx m z.re
  have h1 := OCS.multIdx_mem hw z.re
  have h2 := OCS.multBary_mem hw k
  have h3 := (OCS.multPt_succ_sub_bounds hw k).2
  have hmem : ((OCS.multBary m k : ℝ) : ℂ) ∈ OCS.multGammaC m := ⟨_, ⟨k, rfl⟩, rfl⟩
  refine (infDist_le_dist_of_mem hmem).trans ?_
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  have hapos : 0 < a / (2 * b ^ 2) := by have := hw.b_pos; positivity
  have : |z.re - OCS.multBary m k| ≤ 1 / a := by
    rw [abs_le]; constructor <;> linarith [h2.1, h2.2, h1.1, h1.2]
  linarith [abs_sub_comm z.re (OCS.multBary m k)]

theorem norm_multF_far (hw : OCS.IsMultWeight m a b) {z : ℂ} (hz : 1 ≤ |z.im|) :
    Real.exp (-(Real.pi / (2 * a))) * Real.exp (OCS.multU m 0 z) ≤ ‖OCS.multF m 0 z‖ ∧
      ‖OCS.multF m 0 z‖ ≤ Real.exp (Real.pi / (2 * a)) * Real.exp (OCS.multU m 0 z) := by
  have hz0 : z.im ≠ 0 := by
    intro h; rw [h] at hz; simp at hz; linarith
  have ha := hw.pos
  have h3 := OCS.multF_estimate_three hw 0 hz0
  have hbd : Real.pi / (2 * a) / |z.im| ≤ Real.pi / (2 * a) := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ Real.pi / (2 * a) := by positivity
    nlinarith
  have hre := Complex.abs_re_le_norm
    (OCS.multL m 0 z - OCS.multU m 0 z - Complex.I * OCS.multV m 0 z)
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at hre
  have hn : ‖OCS.multF m 0 z‖ = Real.exp (OCS.multL m 0 z).re := by
    rw [← OCS.exp_multL hw 0 hz0, Complex.norm_exp]
  have hb : |(OCS.multL m 0 z).re - OCS.multU m 0 z| ≤ Real.pi / (2 * a) := by
    refine hre.trans (h3.trans hbd) |>.trans' ?_
    simp
  rw [abs_le] at hb
  rw [hn]
  constructor
  · rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  · rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)

/-- `A` is comparable to `e^U min(1, dist(·, Γ))` on all of `ℂ`. -/
theorem norm_multF_comparable (hw : OCS.IsMultWeight m a b) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℂ,
      c₁ * Real.exp (OCS.multU m 0 z) * min 1 (infDist z (OCS.multGammaC m)) ≤
        ‖OCS.multF m 0 z‖ ∧
      ‖OCS.multF m 0 z‖ ≤
        c₂ * Real.exp (OCS.multU m 0 z) * min 1 (infDist z (OCS.multGammaC m)) := by
  have ha := hw.pos
  obtain ⟨d₁, d₂, hd₁, hd₂, hd⟩ := OCS.multF_estimate_two hw 0
  set D := 1 + 1 / a with hD
  have hD1 : 1 ≤ D := by have : 0 < 1 / a := by positivity
                         linarith
  refine ⟨min (Real.exp (-(Real.pi / (2 * a)))) d₁, max (Real.exp (Real.pi / (2 * a))) (d₂ * D),
    lt_min (Real.exp_pos _) hd₁, lt_max_of_lt_left (Real.exp_pos _), fun z ↦ ?_⟩
  have hU := Real.exp_pos (OCS.multU m 0 z)
  have hdn : 0 ≤ infDist z (OCS.multGammaC m) := infDist_nonneg
  by_cases hz : 1 ≤ |z.im|
  · have hmin : min 1 (infDist z (OCS.multGammaC m)) = 1 :=
      min_eq_left (hz.trans (abs_im_le_infDist z))
    obtain ⟨h1, h2⟩ := norm_multF_far hw hz
    rw [hmin, mul_one, mul_one]
    constructor
    · exact le_trans (by gcongr; exact min_le_left _ _) h1
    · exact le_trans h2 (by gcongr; exact le_max_left _ _)
  · push Not at hz
    obtain ⟨h1, h2⟩ := hd z hz.le
    have hexp : ‖OCS.multF m 0 z‖ * Real.exp (-OCS.multU m 0 z) =
        ‖OCS.multF m 0 z‖ / Real.exp (OCS.multU m 0 z) := by
      rw [Real.exp_neg, div_eq_mul_inv]
    rw [hexp, le_div_iff₀ hU] at h1
    rw [hexp, div_le_iff₀ hU] at h2
    have hdD : infDist z (OCS.multGammaC m) ≤ D := by
      refine (infDist_le_add hw z).trans ?_
      rw [hD]; linarith
    have hm1 : min 1 (infDist z (OCS.multGammaC m)) ≤ infDist z (OCS.multGammaC m) := min_le_right _ _
    have hm2 : infDist z (OCS.multGammaC m) ≤ D * min 1 (infDist z (OCS.multGammaC m)) := by
      rcases le_total (infDist z (OCS.multGammaC m)) 1 with h | h
      · rw [min_eq_right h]; nlinarith
      · rw [min_eq_left h]; linarith
    have hm0 : 0 ≤ min 1 (infDist z (OCS.multGammaC m)) := le_min zero_le_one hdn
    constructor
    · calc _ ≤ d₁ * Real.exp (OCS.multU m 0 z) * min 1 (infDist z (OCS.multGammaC m)) := by
            gcongr; exact min_le_right _ _
        _ ≤ d₁ * infDist z (OCS.multGammaC m) * Real.exp (OCS.multU m 0 z) := by
            nlinarith [mul_nonneg hU.le hm0, mul_pos hd₁ hU]
        _ ≤ _ := h1
    · calc ‖OCS.multF m 0 z‖ ≤ d₂ * infDist z (OCS.multGammaC m) * Real.exp (OCS.multU m 0 z) := h2
        _ ≤ d₂ * (D * min 1 (infDist z (OCS.multGammaC m))) * Real.exp (OCS.multU m 0 z) := by
            gcongr
        _ = (d₂ * D) * Real.exp (OCS.multU m 0 z) * min 1 (infDist z (OCS.multGammaC m)) := by ring
        _ ≤ _ := by gcongr; exact le_max_right _ _

end Comparable

end FF
