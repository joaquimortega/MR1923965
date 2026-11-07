module

public import TauCeti.Analysis.PDE.Harnack.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.CauchyIntegral

/-! Uniform lower bounds for zero-free bounded entire functions on rectangles. -/

public section

open Set Complex InnerProductSpace

namespace FF.Pavlov

/-- An open rectangle with a horizontal margin of `r`. -/
def rect (a b r : ℝ) : Set ℂ :=
  {z | a-r < z.re ∧ z.re < b+r ∧ |z.im| < r}

private lemma interpolation_bounds {a b p q D δ s : ℝ}
    (hp : p ∈ Icc a b) (hq : q ∈ Icc a b) (hD : b-a ≤ D)
    (hδ : 0 ≤ δ) (hs : -δ ≤ s ∧ s ≤ 1+δ) :
    a-D*δ ≤ p+(q-p)*s ∧ p+(q-p)*s ≤ b+D*δ := by
  have hpq : -D ≤ q-p ∧ q-p ≤ D := by constructor <;> linarith [hp.1,hp.2,hq.1,hq.2]
  by_cases hd : 0 ≤ q-p
  · have hlo := mul_le_mul_of_nonneg_left hs.1 hd
    have hhi := mul_le_mul_of_nonneg_left hs.2 hd
    have he := mul_le_mul_of_nonneg_right hpq.2 hδ
    constructor <;> nlinarith [hp.1, hq.2]
  · have hd' : q-p ≤ 0 := le_of_not_ge hd
    have hlo := mul_le_mul_of_nonpos_left hs.2 hd'
    have hhi := mul_le_mul_of_nonpos_left hs.1 hd'
    have he := mul_le_mul_of_nonneg_right hpq.1 hδ
    constructor <;> nlinarith [hp.2, hq.1]

private lemma affine_mem_rect {r D δ a b t₀ x y : ℝ}
    (hr : 0 < r) (hD : 0 < D) (hδ : 0 < δ)
    (hsmall : δ*(D+r) < r/2)
    (ht : t₀ ∈ Icc a b) (hx : x ∈ Icc a b) (hlen : b-a ≤ D)
    (hy : |y| ≤ r/2) {w : ℂ} (hw : w ∈ rect 0 1 δ) :
    (t₀ : ℂ) + (((x : ℂ)+(y : ℂ)*I)-(t₀ : ℂ))*w ∈ rect a b r := by
  obtain ⟨hslo,hshi,htim⟩ := hw
  have hs : -δ ≤ w.re ∧ w.re ≤ 1+δ := by constructor <;> linarith
  have hi := interpolation_bounds ht hx hlen hδ.le hs
  have hdx : |x-t₀| ≤ D := by rw [abs_le]; constructor <;> linarith [ht.1,ht.2,hx.1,hx.2]
  have hyt : |y*w.im| ≤ (r/2)*δ := by
    rw [abs_mul]
    exact mul_le_mul hy htim.le (abs_nonneg _) (by positivity)
  have hys : |y*w.re| ≤ (r/2)*(1+δ) := by
    rw [abs_mul]
    have hsr : |w.re| ≤ 1+δ := by rw [abs_le]; constructor <;> linarith
    exact mul_le_mul hy hsr (abs_nonneg _) (by positivity)
  have hdt : |(x-t₀)*w.im| ≤ D*δ := by
    rw [abs_mul]
    exact mul_le_mul hdx htim.le (abs_nonneg _) hD.le
  simp only [rect, Set.mem_ofPred_eq, add_re, mul_re, sub_re, ofReal_re, ofReal_im,
    I_re, I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add, add_im, mul_im, sub_im] at ⊢
  simp only [← add_sub_assoc]
  change a-r < t₀+(x-t₀)*w.re-y*w.im ∧
    t₀+(x-t₀)*w.re-y*w.im < b+r ∧ |(x-t₀)*w.im+y*w.re| < r
  refine ⟨?_, ?_, ?_⟩
  · have := (abs_le.mp hyt).2
    nlinarith [hi.1]
  · have := (abs_le.mp hyt).1
    nlinarith [hi.2]
  · calc
      |(x-t₀)*w.im+y*w.re| ≤ |(x-t₀)*w.im|+|y*w.re| := abs_add_le _ _
      _ ≤ D*δ+(r/2)*(1+δ) := add_le_add hdt hys
      _ < r := by nlinarith

private lemma isOpen_rect (a b r : ℝ) : IsOpen (rect a b r) := by
  exact (isOpen_lt continuous_const continuous_re).inter
    ((isOpen_lt continuous_re continuous_const).inter
      (isOpen_lt (continuous_im.abs) continuous_const))

private lemma convex_rect (a b r : ℝ) : Convex ℝ (rect a b r) := by
  have heq : rect a b r =
      {z : ℂ | a-r < z.re} ∩ {z : ℂ | z.re < b+r} ∩
      ({z : ℂ | -r < z.im} ∩ {z : ℂ | z.im < r}) := by
    ext z
    simp only [rect, mem_ofPred_eq, mem_inter_iff, abs_lt]
    tauto
  rw [heq]
  exact ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).inter
    ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))

/-- Normalization at one real point gives a uniform lower bound on the inner rectangle. -/
theorem norm_lower_on_rectangle
    {r D M : ℝ} (hr : 0 < r) (hD : 0 < D) :
    ∃ c : ℝ, 0 < c ∧ ∀ (f : ℂ → ℂ) (a b t₀ : ℝ),
      a ≤ t₀ → t₀ ≤ b → b-a ≤ D →
      Differentiable ℂ f →
      (∀ z ∈ rect a b r, f z ≠ 0) →
      (∀ z ∈ rect a b r, ‖f z‖ ≤ M) →
      f (t₀ : ℂ) = 1 →
      ∀ x ∈ Set.Icc a b, ∀ y : ℝ, |y| ≤ r/2 →
        c ≤ ‖f ((x : ℂ) + (y : ℂ)*Complex.I)‖ := by
  let δ := r / (8*(D+r+1))
  have hden : 0 < 8*(D+r+1) := by positivity
  have hδ : 0 < δ := div_pos hr hden
  have hsmall : δ*(D+r) < r/2 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith
  let U := rect 0 1 δ
  have hzero : (0 : ℂ) ∈ U := by
    change 0-δ < (0 : ℂ).re ∧ (0 : ℂ).re < 1+δ ∧ |(0 : ℂ).im| < δ
    simp only [zero_re, zero_im, abs_zero]
    constructor
    · linarith
    constructor <;> linarith
  have hone : (1 : ℂ) ∈ U := by
    change 0-δ < (1 : ℂ).re ∧ (1 : ℂ).re < 1+δ ∧ |(1 : ℂ).im| < δ
    simp only [one_re, one_im, abs_zero]
    constructor
    · linarith
    constructor <;> linarith
  obtain ⟨C, hC, hcomp⟩ := (isCompact_singleton.insert (0 : ℂ)).harnack_inequality
    (isOpen_rect 0 1 δ) (convex_rect 0 1 δ).isPreconnected
    (show ({0, 1} : Set ℂ) ⊆ U from by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hzero
      · exact hone)
  refine ⟨Real.exp ((1-C)*Real.log M), Real.exp_pos _, ?_⟩
  intro f a b t₀ hat htb hlen hf hn hb hnorm x hx y hy
  let g : ℂ → ℂ := fun w ↦ f ((t₀ : ℂ)+(((x : ℂ)+(y : ℂ)*I)-(t₀ : ℂ))*w)
  have hg : Differentiable ℂ g := by dsimp [g]; fun_prop
  have hmap : ∀ w ∈ U, (t₀ : ℂ)+(((x : ℂ)+(y : ℂ)*I)-(t₀ : ℂ))*w ∈ rect a b r :=
    fun w hw ↦ affine_mem_rect hr hD hδ hsmall ⟨hat,htb⟩ hx hlen hy hw
  let u : ℂ → ℝ := fun w ↦ Real.log M - Real.log ‖g w‖
  have hu : HarmonicOnNhd u U := fun w hw ↦
    (harmonicAt_const _).sub ((hg.analyticAt w).harmonicAt_log_norm (hn _ (hmap w hw)))
  have hu0 : ∀ w ∈ U, 0 ≤ u w := by
    intro w hw
    exact sub_nonneg.mpr (Real.log_le_log (norm_pos_iff.mpr (hn _ (hmap w hw))) (hb _ (hmap w hw)))
  have hineq := hcomp u hu hu0 1 (by simp) 0 (by simp)
  have hg0 : g 0 = 1 := by simpa [g] using hnorm
  have hg1 : g 1 = f ((x : ℂ)+(y : ℂ)*I) := by simp [g]
  have hpos : 0 < ‖f ((x : ℂ)+(y : ℂ)*I)‖ := by
    rw [← hg1]
    exact norm_pos_iff.mpr (hn _ (hmap 1 hone))
  simp only [u, hg0, hg1, norm_one, Real.log_one, sub_zero] at hineq
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  linarith

end FF.Pavlov
