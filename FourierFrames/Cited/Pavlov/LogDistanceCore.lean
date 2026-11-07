import FourierFrames.Cited.Pavlov.Cardinal
import FourierFrames.Cited.Pavlov.BMO

/-! # Geometry and logarithmic distance of a separated bounded-gap grid
See `blueprint/P5_LogDistance.md`. -/

open MeasureTheory Metric Set Filter Topology
noncomputable section
namespace FF.Pavlov
variable {Γ : Set ℝ}

/-- The central node minimizes distance throughout its closed Voronoi cell. -/
theorem Grid.abs_sub_center_le_node (g : Grid Γ) {k : ℤ} {x : ℝ}
    (hx : x ∈ cell g k) (j : ℤ) : |x-g.point k| ≤ |x-g.point j| := by
  rcases lt_trichotomy j k with hj | rfl | hj
  · have he := g.strictMono.monotone (show j ≤ k-1 by omega)
    have hp := g.strictMono.monotone (show k-1 ≤ k by omega)
    obtain ⟨hl, hr⟩ := hx
    apply abs_le.mpr
    constructor
    · have h : g.point k-x ≤ x-g.point j := by linarith
      linarith [le_abs_self (x-g.point j)]
    · have h : x-g.point k ≤ x-g.point j := by linarith
      exact h.trans (le_abs_self _)
  · exact le_rfl
  · have he := g.strictMono.monotone (show k+1 ≤ j by omega)
    have hn := g.strictMono.monotone (show k ≤ k+1 by omega)
    obtain ⟨hl, hr⟩ := hx
    apply abs_le.mpr
    constructor
    · have h : g.point k-x ≤ -(x-g.point j) := by linarith
      linarith [neg_le_abs (x-g.point j)]
    · have h : x-g.point k ≤ -(x-g.point j) := by linarith
      exact h.trans (neg_le_abs _)

/-- On a closed Voronoi cell, distance to the grid is distance to its center. -/
theorem Grid.infDist_eq_abs_sub (g : Grid Γ) {k : ℤ} {x : ℝ}
    (hx : x ∈ cell g k) : Metric.infDist x Γ = |x-g.point k| := by
  apply le_antisymm
  · simpa only [Real.dist_eq] using infDist_le_dist_of_mem (x := x) (g.point_mem k)
  · apply (le_infDist ⟨g.point k, g.point_mem k⟩).mpr
    intro y hy
    obtain ⟨j, rfl⟩ := g.range_eq.symm.subset hy
    simpa only [Real.dist_eq] using g.abs_sub_center_le_node hx j

theorem Grid.countable (g : Grid Γ) : Γ.Countable := by
  rw [← g.range_eq]
  exact Set.countable_range g.point

theorem Grid.ae_not_mem (g : Grid Γ) : ∀ᵐ x : ℝ, x ∉ Γ := by
  apply ae_iff.mpr
  simpa only [not_not, Set.ofPred_mem_eq] using g.countable.measure_zero volume

/-- Distance to a bounded-gap grid has a uniform upper bound. -/
theorem Grid.infDist_le (g : Grid Γ) (x : ℝ) : Metric.infDist x Γ ≤ g.upper/2 := by
  obtain ⟨k, hx⟩ := g.exists_cell x
  rw [g.infDist_eq_abs_sub hx]
  exact g.abs_sub_center_le hx

/-- The logarithm of distance is integrable on each closed Voronoi cell. -/
theorem Grid.integrableOn_log_infDist_cell (g : Grid Γ) (k : ℤ) :
    IntegrableOn (fun x ↦ Real.log (Metric.infDist x Γ)) (cell g k) := by
  let a := (g.point (k-1)+g.point k)/2
  let b := (g.point k+g.point (k+1))/2
  have hi : IntervalIntegrable (fun x : ℝ ↦ Real.log (x-g.point k)) volume a b := by
    simpa only [sub_add_cancel] using
      (intervalIntegral.intervalIntegrable_log' (a := a-g.point k) (b := b-g.point k)).comp_sub_right
        (g.point k)
  have hab : a ≤ b := by
    have := (g.cell_length_bounds k).1
    dsimp [a, b]
    linarith [g.lower_pos]
  have hi' := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi
  apply hi'.congr_fun _ measurableSet_Icc
  intro x hx
  change Real.log (x-g.point k) = Real.log (Metric.infDist x Γ)
  rw [g.infDist_eq_abs_sub hx, Real.log_abs]

/-- Local integrability includes the logarithmic singularities at grid nodes. -/
theorem Grid.locallyIntegrable_log_infDist (g : Grid Γ) :
    LocallyIntegrable (fun x ↦ Real.log (Metric.infDist x Γ)) := by
  intro x
  obtain ⟨k, hx⟩ := g.exists_cell x
  let a := (g.point (k-2)+g.point (k-1))/2
  let b := (g.point (k+1)+g.point (k+2))/2
  have hleft : a < x := by
    have he := g.strictMono (show k-2 < k by omega)
    have hh := hx.1
    dsimp [a]
    linarith
  have hright : x < b := by
    have he := g.strictMono (show k < k+2 by omega)
    have hh := hx.2
    dsimp [b]
    linarith
  refine ⟨(cell g (k-1) ∪ cell g k) ∪ cell g (k+1), ?_,
    ((g.integrableOn_log_infDist_cell (k-1)).union
      (g.integrableOn_log_infDist_cell k)).union
        (g.integrableOn_log_infDist_cell (k+1))⟩
  apply mem_of_superset (Ioo_mem_nhds hleft hright)
  intro t ht
  by_cases hl : t ≤ (g.point (k-1)+g.point k)/2
  · apply Or.inl; apply Or.inl
    constructor
    · have he : k-1-1 = k-2 := by omega
      simpa only [cell, he] using ht.1.le
    · have he : k-1+1 = k := by omega
      simpa only [cell, he] using hl
  · by_cases hr : t ≤ (g.point k+g.point (k+1))/2
    · exact Or.inl (Or.inr ⟨(not_le.mp hl).le, hr⟩)
    · apply Or.inr
      constructor
      · have he : k+1-1 = k := by omega
        simpa only [cell, he] using (not_le.mp hr).le
      · have he : k+1+1 = k+2 := by omega
        simpa only [cell, he] using ht.2.le

/-- On intervals far from the grid the logarithmic distance has bounded oscillation. -/
theorem Grid.meanOsc_log_infDist_le_of_far (g : Grid Γ) {a b : ℝ} (hab : a < b)
    (hfar : 2*(b-a) ≤ Metric.infDist a Γ) :
    meanOsc (fun x ↦ Real.log (Metric.infDist x Γ)) a b ≤ 2*Real.log 2 := by
  let d := Metric.infDist a Γ
  have hd : 0 < d := lt_of_lt_of_le (by linarith) hfar
  have hi := g.locallyIntegrable_log_infDist
  have hbound : ∀ x ∈ Icc a b,
      |Real.log (Metric.infDist x Γ)-Real.log d| ≤ Real.log 2 := by
    intro x hx
    have hdist : dist x a ≤ b-a := by rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
    have h₁ := Metric.infDist_le_infDist_add_dist (x := x) (y := a) (s := Γ)
    have h₂ := Metric.infDist_le_infDist_add_dist (x := a) (y := x) (s := Γ)
    rw [dist_comm a x] at h₂
    have hl : d/2 ≤ Metric.infDist x Γ := by dsimp [d] at *; linarith
    have hu : Metric.infDist x Γ ≤ 2*d := by dsimp [d] at *; linarith
    have hxpos : 0 < Metric.infDist x Γ := lt_of_lt_of_le (by positivity) hl
    have hlo := Real.log_le_log (show 0 < d/2 by positivity) hl
    have hup := Real.log_le_log hxpos hu
    rw [Real.log_div hd.ne' (by norm_num)] at hlo
    rw [Real.log_mul (by norm_num) hd.ne'] at hup
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have he : (∫ x in a..b, |Real.log (Metric.infDist x Γ)-Real.log d|) ≤
      (b-a)*Real.log 2 := by
    calc
      _ ≤ ∫ _ in a..b, Real.log 2 := by
        apply intervalIntegral.integral_mono_on hab.le
          ((hi.integrableOn_isCompact isCompact_uIcc).intervalIntegrable.sub
            intervalIntegrable_const).abs intervalIntegrable_const
        intro x hx
        exact hbound x hx
      _ = _ := by simp
  have he' := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (sub_pos.mpr hab).le)
  rw [← mul_assoc, inv_mul_cancel₀ (sub_pos.mpr hab).ne', one_mul] at he'
  exact (meanOsc_le_twice_comparison hi hab (Real.log d)).trans
    (mul_le_mul_of_nonneg_left he' (by norm_num))

/-- Every point within half the lower gap belongs to the central Voronoi cell. -/
theorem Grid.mem_cell_of_abs_sub_le (g : Grid Γ) {k : ℤ} {x : ℝ}
    (hx : |x-g.point k| ≤ g.lower/2) : x ∈ cell g k := by
  have hxl := (abs_le.mp hx).1
  have hxr := (abs_le.mp hx).2
  have hl := g.gap_lower (k-1)
  have hr := g.gap_lower k
  have he : k-1+1 = k := by omega
  rw [he] at hl
  constructor <;> linarith

/-- On a short interval starting near the grid, one node is nearest everywhere. -/
theorem Grid.exists_nearest_on_short_interval (g : Grid Γ) {a b : ℝ}
    (hab : a < b) (hsmall : b-a < g.lower/8)
    (hnear : Metric.infDist a Γ < 2*(b-a)) :
    ∃ k : ℤ, |g.point k-a| < 2*(b-a) ∧
      ∀ x ∈ Icc a b, Metric.infDist x Γ = |x-g.point k| := by
  obtain ⟨k, hk⟩ := g.exists_cell a
  rw [g.infDist_eq_abs_sub hk] at hnear
  refine ⟨k, by simpa only [abs_sub_comm] using hnear, ?_⟩
  intro x hx
  apply g.infDist_eq_abs_sub
  apply g.mem_cell_of_abs_sub_le
  have hxa : |x-a| ≤ b-a := by
    rw [abs_of_nonneg (by linarith [hx.1])]
    linarith [hx.2]
  have he := abs_sub_le x a (g.point k)
  linarith

/-- Local equality on an interval preserves its mean oscillation. -/
theorem meanOsc_congr_on_Icc {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfg : EqOn f g (Icc a b)) : meanOsc f a b = meanOsc g a b := by
  have hm : intervalMean f a b = intervalMean g a b := by
    unfold intervalMean
    congr 1
    apply intervalIntegral.integral_congr
    simpa only [uIcc_of_le hab] using hfg
  unfold meanOsc
  rw [hm]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [hfg (by simpa only [uIcc_of_le hab] using hx)]

end FF.Pavlov
