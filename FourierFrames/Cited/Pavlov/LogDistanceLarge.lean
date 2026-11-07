import FourierFrames.Cited.Pavlov.LogDistanceCore
import FourierFrames.Cited.Pavlov.BMO

/-! # Uniform integral bounds for logarithmic distance on large intervals -/

open MeasureTheory Metric Set Filter Topology
noncomputable section
namespace FF.Pavlov
variable {Γ : Set ℝ}

/-- Left endpoint of a closed Voronoi cell. -/
def Grid.edge (g : Grid Γ) (k : ℤ) : ℝ := (g.point (k-1)+g.point k)/2

theorem Grid.cell_eq_Icc_edges (g : Grid Γ) (k : ℤ) :
    cell g k = Icc (g.edge k) (g.edge (k+1)) := by
  have he : k+1-1 = k := by omega
  simp only [cell, Grid.edge, he]

theorem Grid.edge_gap_lower (g : Grid Γ) (k : ℤ) :
    g.lower ≤ g.edge (k+1)-g.edge k := by
  have he : k+1-1 = k := by omega
  simpa only [Grid.edge, he] using (g.cell_length_bounds k).1

theorem Grid.edge_strictMono (g : Grid Γ) : StrictMono g.edge := by
  apply strictMono_int_of_lt_succ
  intro k
  have h := g.edge_gap_lower k
  linarith [g.lower_pos]

theorem Grid.edge_mono_sub_lower (g : Grid Γ) :
    Monotone (fun k : ℤ ↦ g.edge k-g.lower*(k : ℝ)) := by
  apply monotone_int_of_le_succ
  intro k
  have h := g.edge_gap_lower k
  push_cast
  linarith

/-- Endpoint cells give a finite cover with at most length/lower-gap plus two cells. -/
theorem Grid.exists_cell_cover (g : Grid Γ) {a b : ℝ} (hab : a < b) :
    ∃ m n : ℤ, m ≤ n ∧
      Icc a b ⊆ ⋃ k ∈ Finset.Icc m n, cell g k ∧
      ((n-m+1 : ℤ) : ℝ) ≤ (b-a)/g.lower+2 := by
  obtain ⟨m, hm⟩ := g.exists_cell a
  obtain ⟨n, hn⟩ := g.exists_cell b
  rw [g.cell_eq_Icc_edges] at hm hn
  have hmn : m ≤ n := by
    by_contra h
    have he := g.edge_strictMono.monotone (show n+1 ≤ m by omega)
    linarith [hm.1, hn.2]
  refine ⟨m, n, hmn, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj⟩ := g.exists_cell x
    rw [g.cell_eq_Icc_edges] at hj
    have hmem : ∃ k ∈ Finset.Icc m n, x ∈ cell g k := by
      by_cases hjm : j < m
      · refine ⟨m, Finset.mem_Icc.mpr ⟨le_rfl, hmn⟩, ?_⟩
        rw [g.cell_eq_Icc_edges]
        have he := g.edge_strictMono.monotone (show j+1 ≤ m by omega)
        exact ⟨hm.1.trans hx.1, le_trans hj.2 (he.trans (g.edge_strictMono.monotone (by omega)))⟩
      · by_cases hjn : n < j
        · refine ⟨n, Finset.mem_Icc.mpr ⟨hmn, le_rfl⟩, ?_⟩
          rw [g.cell_eq_Icc_edges]
          have he := g.edge_strictMono.monotone (show n+1 ≤ j by omega)
          exact ⟨(g.edge_strictMono.monotone (by omega)).trans (he.trans hj.1), hx.2.trans hn.2⟩
        · exact ⟨j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by rwa [g.cell_eq_Icc_edges]⟩
    obtain ⟨k, hk, hxk⟩ := hmem
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, hxk⟩⟩
  · by_cases h : m+1 ≤ n
    · have hmono := g.edge_mono_sub_lower h
      push_cast at hmono
      have he' : g.lower*((n : ℝ)-(m : ℝ)-1) ≤ g.edge n-g.edge (m+1) := by
        nlinarith
      rw [← sub_le_iff_le_add, le_div_iff₀ g.lower_pos]
      push_cast
      nlinarith [hm.2, hn.1]
    · have hnm : n = m := by omega
      subst n
      have hp : 0 < (b-a)/g.lower := div_pos (sub_pos.mpr hab) g.lower_pos
      norm_num
      linarith

/-- A finite consecutive collection of cells surrounds any bounded interval. -/
theorem Grid.exists_cell_span (g : Grid Γ) {a b : ℝ} (hab : a < b) :
    ∃ m n : ℤ, m ≤ n ∧ g.edge m ≤ a ∧ b ≤ g.edge (n+1) ∧
      ((n-m+1 : ℤ) : ℝ) ≤ (b-a)/g.lower+2 := by
  obtain ⟨m, n, hmn, hcover, hcount⟩ := g.exists_cell_cover hab
  have ha := hcover (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
  have hb := hcover (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
  simp only [mem_iUnion] at ha hb
  obtain ⟨i, hi, hai⟩ := ha
  obtain ⟨j, hj, hbj⟩ := hb
  rw [g.cell_eq_Icc_edges] at hai hbj
  exact ⟨m, n, hmn,
    (g.edge_strictMono.monotone (Finset.mem_Icc.mp hi).1).trans hai.1,
    hbj.2.trans (g.edge_strictMono.monotone (by have h := (Finset.mem_Icc.mp hj).2; omega)), hcount⟩

/-- The symmetric logarithm integral bounds the contribution of every cell. -/
theorem Grid.integral_abs_log_infDist_cell_le (g : Grid Γ) (k : ℤ) :
    (∫ x in g.edge k..g.edge (k+1), |Real.log (Metric.infDist x Γ)|) ≤
      ∫ x in (-g.upper/2)..(g.upper/2), |Real.log x| := by
  have hab : g.edge k ≤ g.edge (k+1) := (g.edge_strictMono (by omega)).le
  have heq : (∫ x in g.edge k..g.edge (k+1), |Real.log (Metric.infDist x Γ)|) =
      ∫ x in g.edge k..g.edge (k+1), |Real.log (x-g.point k)| := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hcell : x ∈ cell g k := by
      rw [g.cell_eq_Icc_edges]
      simpa only [uIcc_of_le hab] using hx
    dsimp only
    rw [g.infDist_eq_abs_sub hcell, Real.log_abs]
  rw [heq, intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ |Real.log x|) (g.point k)]
  have hp := g.gap_upper (k-1)
  have hn := g.gap_upper k
  have hk : k-1+1 = k := by omega
  rw [hk] at hp
  have hl : -g.upper/2 ≤ g.edge k-g.point k := by dsimp [Grid.edge]; linarith
  have hr : g.edge (k+1)-g.point k ≤ g.upper/2 := by
    dsimp [Grid.edge]
    rw [show k+1-1 = k by omega]
    linarith
  exact intervalIntegral.integral_mono_interval hl (by linarith) hr
    (Eventually.of_forall fun x ↦ abs_nonneg _) intervalIntegral.intervalIntegrable_log'.abs

/-- A block of N consecutive cells contributes at most N symmetric logarithm integrals. -/
theorem Grid.integral_abs_log_infDist_span_le (g : Grid Γ) (m : ℤ) (N : ℕ) :
    (∫ x in g.edge m..g.edge (m+(N : ℤ)), |Real.log (Metric.infDist x Γ)|) ≤
      (N : ℝ) * ∫ x in (-g.upper/2)..(g.upper/2), |Real.log x| := by
  have hi : ∀ i : ℕ, IntervalIntegrable (fun x ↦ |Real.log (Metric.infDist x Γ)|)
      volume (g.edge (m+(i : ℤ))) (g.edge (m+((i+1 : ℕ) : ℤ))) := by
    intro i
    exact ((g.locallyIntegrable_log_infDist.integrableOn_isCompact isCompact_uIcc).intervalIntegrable).abs
  have heq := intervalIntegral.sum_integral_adjacent_intervals (n := N) (fun i _ ↦ hi i)
  simp only [Nat.cast_zero, add_zero] at heq
  rw [← heq]
  calc
    _ ≤ ∑ _i ∈ Finset.range N, (∫ x in (-g.upper/2)..(g.upper/2), |Real.log x|) := by
      apply Finset.sum_le_sum
      intro i _
      have h := g.integral_abs_log_infDist_cell_le (m+(i : ℤ))
      simpa only [Nat.cast_add, Nat.cast_one, Int.natCast_add, Int.natCast_one, add_assoc] using h
    _ = _ := by simp

/-- The mean absolute logarithmic distance is uniformly bounded on intervals above the grid scale. -/
theorem Grid.exists_large_interval_log_infDist_bound (g : Grid Γ) :
    ∃ K : ℝ, ∀ a b : ℝ, a < b → g.lower/8 ≤ b-a →
      (b-a)⁻¹ * (∫ x in a..b, |Real.log (Metric.infDist x Γ)|) ≤ K := by
  let J : ℝ := ∫ x in (-g.upper/2)..(g.upper/2), |Real.log x|
  have hJ : 0 ≤ J := intervalIntegral.integral_nonneg_of_forall
    (by linarith [g.upper_pos]) (fun x ↦ abs_nonneg _)
  refine ⟨17*J/g.lower, ?_⟩
  intro a b hab hlarge
  obtain ⟨m, n, hmn, hleft, hright, hcount⟩ := g.exists_cell_span hab
  let N : ℕ := (n-m+1).toNat
  have hN : (N : ℤ) = n-m+1 := Int.toNat_of_nonneg (by omega)
  have hEnd : m+(N : ℤ) = n+1 := by omega
  have hNr : (N : ℝ) = ((n-m+1 : ℤ) : ℝ) := by exact_mod_cast hN
  have hcount' : (N : ℝ) ≤ (b-a)/g.lower+2 := by rw [hNr]; exact hcount
  have htwo : (2 : ℝ) ≤ 16*(b-a)/g.lower :=
    (le_div_iff₀ g.lower_pos).mpr (by linarith)
  have hNbound : (N : ℝ) ≤ 17*(b-a)/g.lower := by
    have heq : 17*(b-a)/g.lower = (b-a)/g.lower+16*(b-a)/g.lower := by ring
    rw [heq]
    linarith
  have hspan := g.integral_abs_log_infDist_span_le m N
  rw [hEnd] at hspan
  have hi : IntervalIntegrable (fun x ↦ |Real.log (Metric.infDist x Γ)|) volume
      (g.edge m) (g.edge (n+1)) :=
    ((g.locallyIntegrable_log_infDist.integrableOn_isCompact isCompact_uIcc).intervalIntegrable).abs
  have hsub := intervalIntegral.integral_mono_interval hleft hab.le hright
    (Eventually.of_forall fun x ↦ abs_nonneg (Real.log (Metric.infDist x Γ))) hi
  have hfull : (∫ x in a..b, |Real.log (Metric.infDist x Γ)|) ≤
      (17*(b-a)/g.lower)*J :=
    hsub.trans (hspan.trans (mul_le_mul_of_nonneg_right hNbound hJ))
  calc
    (b-a)⁻¹ * (∫ x in a..b, |Real.log (Metric.infDist x Γ)|) ≤
        (b-a)⁻¹ * ((17*(b-a)/g.lower)*J) :=
      mul_le_mul_of_nonneg_left hfull (inv_pos.mpr (sub_pos.mpr hab)).le
    _ = 17*J/g.lower := by field_simp

end FF.Pavlov
