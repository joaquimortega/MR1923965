import FourierFrames.Cited.Pavlov.Cardinal
import FourierFrames.Cited.Pavlov.Harnack

/-!
# Uniform comparison of a generator on its Voronoi cells

The normalized cardinal function has no zeros near its own closed cell.
Its PW bound and normalization give a uniform lower bound by Harnack.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section
namespace FF.Pavlov

variable {Γ : Set ℝ}

/-- Removing the central zero leaves a zero-free neighborhood of its whole cell. -/
theorem cardinal_ne_zero_rect (g : Grid Γ) (d : GeneratingData Γ) (k : ℤ)
    {r : ℝ} (hr : r < g.lower/2) :
    ∀ z ∈ rect ((g.point (k-1)+g.point k)/2) ((g.point k+g.point (k+1))/2) r,
      cardinal d.G (g.point k) z ≠ 0 := by
  intro z hz hn
  obtain ⟨t, ht, hne, rfl⟩ := (d.cardinal_zero_iff (g.point_mem k) z).mp hn
  obtain ⟨j, rfl⟩ := g.range_eq.symm.subset ht
  have hj : j ≠ k := fun h ↦ hne (congrArg g.point h)
  rcases lt_or_gt_of_ne hj with hj | hj
  · have he := g.strictMono.monotone (show j ≤ k-1 by omega)
    have hp := g.gap_lower (k-1)
    have hk : k-1+1 = k := by omega
    rw [hk] at hp
    have hleft := hz.1
    simp only [Complex.ofReal_re] at hleft
    linarith
  · have he := g.strictMono.monotone (show k+1 ≤ j by omega)
    have hp := g.gap_lower k
    have hright := hz.2.1
    simp only [Complex.ofReal_re] at hright
    linarith

/-- A single lower and upper bound works for every cardinal on its cell strip. -/
theorem cardinal_cell_bounds (g : Grid Γ) (d : CardinalData Γ) :
    ∃ ε c C : ℝ, 0 < ε ∧ ε < g.lower/8 ∧ 0 < c ∧ 0 < C ∧
      ∀ k : ℤ, ∀ x ∈ cell g k, ∀ y : ℝ, |y| ≤ ε →
        c ≤ ‖cardinal d.G (g.point k) ((x : ℂ)+(y : ℂ)*I)‖ ∧
        ‖cardinal d.G (g.point k) ((x : ℂ)+(y : ℂ)*I)‖ ≤ C := by
  let r : ℝ := g.lower/8
  have hr : 0 < r := div_pos g.lower_pos (by norm_num)
  let L : ℝ := Real.exp (2*Real.pi*r) * d.normBound
  have hL : 0 ≤ L := (mul_pos (Real.exp_pos _) d.normBound_pos).le
  let M : ℝ := Real.sqrt L+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hupper : ∀ k : ℤ, ∀ z : ℂ, |z.im| ≤ r →
      ‖cardinal d.G (g.point k) z‖ ≤ M := by
    intro k z hz
    have hp := pw_norm_sq_le paleyWiener_holds (d.toGeneratingData.cardinal_mem (g.point_mem k)) z
    have he : Real.exp (2*Real.pi*|z.im|) ≤ Real.exp (2*Real.pi*r) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    have hn := d.cardinal_norm (g.point k) (g.point_mem k)
    have hsq : ‖cardinal d.G (g.point k) z‖ ^ 2 ≤ L :=
      hp.trans (mul_le_mul he hn ENNReal.toReal_nonneg (Real.exp_pos _).le)
    have hs := Real.sq_sqrt hL
    have hs0 := Real.sqrt_nonneg L
    have hn0 := norm_nonneg (cardinal d.G (g.point k) z)
    dsimp only [M]
    nlinarith
  obtain ⟨c, hc, hlow⟩ := norm_lower_on_rectangle (M := M) hr g.upper_pos
  refine ⟨r/2, c, M, by positivity, ?_, hc, hM, ?_⟩
  · dsimp [r]
    linarith [g.lower_pos]
  · intro k x hx y hy
    have hm := g.point_mem_cell k
    have hlen := (g.cell_length_bounds k).2
    have hcenter : cardinal d.G (g.point k) (g.point k : ℂ) = 1 := by
      simp [cardinal, dslope_same, d.toGeneratingData.simple (g.point_mem k)]
    refine ⟨hlow _ _ _ _ hm.1 hm.2 hlen
      (d.toGeneratingData.cardinal_mem (g.point_mem k)).1
      (cardinal_ne_zero_rect g d.toGeneratingData k (by dsimp [r]; linarith [g.lower_pos]))
      (fun z hz ↦ hupper k z hz.2.2.le) hcenter x hx y hy, ?_⟩
    apply hupper
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.ofReal_re, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
    linarith

theorem GeneratingData.norm_generating_eq (d : GeneratingData Γ) {γ : ℝ}
    (hγ : γ ∈ Γ) (z : ℂ) :
    ‖d.G z‖ = ‖deriv d.G (γ : ℂ)‖ * ‖z-(γ : ℂ)‖ * ‖cardinal d.G γ z‖ := by
  rw [← d.cardinal_mul_sub hγ z, norm_mul, norm_mul]

/-- Uniform upper and lower comparison with the generator derivative on every cell. -/
theorem generating_cell_bounds (g : Grid Γ) (d : CardinalData Γ) :
    ∃ ε c C : ℝ, 0 < ε ∧ ε < g.lower/8 ∧ 0 < c ∧ 0 < C ∧
      ∀ k : ℤ, ∀ x ∈ cell g k,
        (c * ‖deriv d.G (g.point k : ℂ)‖ ≤ ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖ ∧
         ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖ ≤ C * ‖deriv d.G (g.point k : ℂ)‖) ∧
        (c * ‖deriv d.G (g.point k : ℂ)‖ * |x-g.point k| ≤ ‖d.G (x : ℂ)‖ ∧
         ‖d.G (x : ℂ)‖ ≤ C * ‖deriv d.G (g.point k : ℂ)‖ * |x-g.point k|) := by
  obtain ⟨ε, c, C, hε, hεl, hc, hC, hbd⟩ := cardinal_cell_bounds g d
  let R := g.upper/2+ε
  have hR : 0 < R := by dsimp [R]; linarith [g.upper_pos]
  refine ⟨ε, min (c*ε) c, max (C*R) C, hε, hεl,
    lt_min (mul_pos hc hε) hc, lt_of_lt_of_le hC (le_max_right _ _), ?_⟩
  intro k x hx
  have hs := hbd k x hx ε (by rw [abs_of_pos hε])
  have ht := hbd k x hx 0 (by simp; exact hε.le)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at ht
  have hnlo : ε ≤ ‖(x : ℂ)+(ε : ℂ)*I-(g.point k : ℂ)‖ := by
    simpa [abs_of_pos hε] using
      (Complex.abs_im_le_norm ((x : ℂ)+(ε : ℂ)*I-(g.point k : ℂ)))
  have hnhi : ‖(x : ℂ)+(ε : ℂ)*I-(g.point k : ℂ)‖ ≤ R := by
    calc
      _ = ‖((x-g.point k : ℝ) : ℂ)+(ε : ℂ)*I‖ := by congr 1; push_cast; ring
      _ ≤ ‖((x-g.point k : ℝ) : ℂ)‖+‖(ε : ℂ)*I‖ := norm_add_le _ _
      _ = |x-g.point k|+ε := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_pos hε]
      _ ≤ R := by dsimp [R]; linarith [g.abs_sub_center_le hx]
  have hDs := norm_nonneg (deriv d.G (g.point k : ℂ))
  have hd := norm_nonneg ((x : ℂ)+(ε : ℂ)*I-(g.point k : ℂ))
  have hx0 := abs_nonneg (x-g.point k)
  constructor
  · rw [d.toGeneratingData.norm_generating_eq (g.point_mem k)]
    constructor
    · calc
        min (c*ε) c * ‖deriv d.G (g.point k : ℂ)‖ ≤
            c*ε*‖deriv d.G (g.point k : ℂ)‖ := mul_le_mul_of_nonneg_right (min_le_left _ _) hDs
        _ = ‖deriv d.G (g.point k : ℂ)‖*ε*c := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hnlo hDs) hs.1 hc.le (mul_nonneg hDs hd)
    · calc
        _ ≤ ‖deriv d.G (g.point k : ℂ)‖*R*C := mul_le_mul (mul_le_mul_of_nonneg_left hnhi hDs) hs.2 (norm_nonneg _) (mul_nonneg hDs hR.le)
        _ = C*R*‖deriv d.G (g.point k : ℂ)‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hDs
  · rw [d.toGeneratingData.norm_generating_eq (g.point_mem k)]
    have he : ‖(x : ℂ)-(g.point k : ℂ)‖ = |x-g.point k| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [he]
    constructor
    · calc
        min (c*ε) c * ‖deriv d.G (g.point k : ℂ)‖ * |x-g.point k| ≤
            c*‖deriv d.G (g.point k : ℂ)‖*|x-g.point k| := by gcongr; exact min_le_right _ _
        _ = ‖deriv d.G (g.point k : ℂ)‖*|x-g.point k| *c := by ring
        _ ≤ _ := by gcongr; exact ht.1
    · calc
        _ ≤ ‖deriv d.G (g.point k : ℂ)‖*|x-g.point k| *C := by gcongr; exact ht.2
        _ = C*‖deriv d.G (g.point k : ℂ)‖*|x-g.point k| := by ring
        _ ≤ _ := by gcongr; exact le_max_right _ _

/-- The real logarithmic singularity is exactly the logarithm of the distance to the node. -/
theorem generating_log_cell_comparison (g : Grid Γ) (d : CardinalData Γ) :
    ∃ ε B : ℝ, 0 < ε ∧ ε < g.lower/8 ∧ 0 ≤ B ∧
      ∀ k : ℤ, ∀ x ∈ cell g k, x ≠ g.point k →
        |Real.log ‖d.G (x : ℂ)‖ - Real.log ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖ -
          Real.log (abs (x-g.point k))| ≤ B := by
  obtain ⟨ε, c, C, hε, hεl, hc, hC, hbd⟩ := generating_cell_bounds g d
  refine ⟨ε, |Real.log C-Real.log c|, hε, hεl, abs_nonneg _, ?_⟩
  intro k x hx hne
  obtain ⟨⟨hsL, hsU⟩, ⟨hrL, hrU⟩⟩ := hbd k x hx
  have hd : 0 < ‖deriv d.G (g.point k : ℂ)‖ :=
    norm_pos_iff.mpr (d.toGeneratingData.simple (g.point_mem k))
  have ht : 0 < |x-g.point k| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hr : 0 < ‖d.G (x : ℂ)‖ := (mul_pos (mul_pos hc hd) ht).trans_le hrL
  have hs : 0 < ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖ := (mul_pos hc hd).trans_le hsL
  have hsL' := Real.log_le_log (mul_pos hc hd) hsL
  have hsU' := Real.log_le_log hs hsU
  have hrL' := Real.log_le_log (mul_pos (mul_pos hc hd) ht) hrL
  have hrU' := Real.log_le_log hr hrU
  rw [Real.log_mul hc.ne' hd.ne'] at hsL'
  rw [Real.log_mul hC.ne' hd.ne'] at hsU'
  rw [Real.log_mul (mul_pos hc hd).ne' ht.ne', Real.log_mul hc.ne' hd.ne'] at hrL'
  rw [Real.log_mul (mul_pos hC hd).ne' ht.ne', Real.log_mul hC.ne' hd.ne'] at hrU'
  have ha := le_abs_self (Real.log C-Real.log c)
  apply abs_le.mpr
  constructor <;> linarith

end FF.Pavlov
