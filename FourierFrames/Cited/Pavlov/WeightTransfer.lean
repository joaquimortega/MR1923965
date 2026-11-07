import FourierFrames.Cited.Pavlov.Weights
import FourierFrames.Cited.Pavlov.LogDistanceLarge

/-! # Transfer of discrete weight bounds to Voronoi cells -/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal

noncomputable section
namespace FF.Pavlov

/-- A nonnegative cellwise bound integrates to at most the full cell lengths. -/
theorem Grid.integral_le_cell_sum {Γ : Set ℝ} (g : Grid Γ)
    (s : Finset ℤ) (v : ℤ → ℝ) (hv : ∀ k ∈ s, 0 ≤ v k)
    {w : ℝ → ℝ} {a b : ℝ} (hw : IntegrableOn w (Icc a b))
    (hcover : ∀ x ∈ Icc a b, ∃ k ∈ s, x ∈ cell g k)
    (hbound : ∀ k ∈ s, ∀ x ∈ cell g k, w x ≤ v k) :
    (∫ x in Icc a b, w x) ≤ g.upper * ∑ k ∈ s, v k := by
  classical
  let F : ℤ → ℝ → ℝ := fun k ↦ (cell g k).indicator (fun _ ↦ v k)
  have hi (k : ℤ) : Integrable (F k) := by
    exact (integrableOn_const (by simp [cell])).integrable_indicator measurableSet_Icc
  have hnon (k : ℤ) (hk : k ∈ s) (x : ℝ) : 0 ≤ F k x := by
    exact Set.indicator_nonneg (fun _ _ ↦ hv k hk) x
  have hsum := integrable_finsetSum s (fun k _ ↦ hi k)
  have hpoint : ∀ x ∈ Icc a b, w x ≤ ∑ k ∈ s, F k x := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := hcover x hx
    calc
      w x ≤ v k := hbound k hk x hxk
      _ = F k x := by simp [F, hxk]
      _ ≤ ∑ j ∈ s, F j x := Finset.single_le_sum (fun j hj ↦ hnon j hj x) hk
  have hmono : (∫ x in Icc a b, w x) ≤ ∫ x in Icc a b, ∑ k ∈ s, F k x := by
    apply integral_mono_ae hw hsum.integrableOn
    exact (ae_restrict_mem measurableSet_Icc).mono (fun x hx ↦ hpoint x hx)
  calc
    _ ≤ ∫ x in Icc a b, ∑ k ∈ s, F k x := hmono
    _ ≤ ∫ x, ∑ k ∈ s, F k x := setIntegral_le_integral hsum
      (Filter.Eventually.of_forall (fun x ↦ Finset.sum_nonneg (fun k hk ↦ hnon k hk x)))
    _ = ∑ k ∈ s, ∫ x, F k x := integral_finsetSum s (fun k _ ↦ hi k)
    _ ≤ ∑ k ∈ s, g.upper * v k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [show (∫ x, F k x) =
        (((g.point k+g.point (k+1))/2)-((g.point (k-1)+g.point k)/2))*v k by
          rw [show F k = (cell g k).indicator (fun _ ↦ v k) from rfl,
            cell, integral_indicator measurableSet_Icc, setIntegral_const]
          simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
          rw [ENNReal.toReal_ofReal (g.lower_pos.le.trans (g.cell_length_bounds k).1)]]
      exact mul_le_mul_of_nonneg_right (g.cell_length_bounds k).2 (hv k hk)
    _ = _ := by rw [Finset.mul_sum]

/-- The same finite cover bounds the average even when the interval is tiny. -/
theorem Grid.integral_le_length_cell_sum {Γ : Set ℝ} (g : Grid Γ)
    (s : Finset ℤ) (v : ℤ → ℝ) (hv : ∀ k ∈ s, 0 ≤ v k)
    {w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hw : IntegrableOn w (Icc a b))
    (hcover : ∀ x ∈ Icc a b, ∃ k ∈ s, x ∈ cell g k)
    (hbound : ∀ k ∈ s, ∀ x ∈ cell g k, w x ≤ v k) :
    (∫ x in Icc a b, w x) ≤ (b-a) * ∑ k ∈ s, v k := by
  have hp : ∀ x ∈ Icc a b, w x ≤ ∑ k ∈ s, v k := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := hcover x hx
    exact (hbound k hk x hxk).trans (Finset.single_le_sum hv hk)
  have h := integral_mono_ae hw (integrableOn_const (by simp) (by simp))
    ((ae_restrict_mem measurableSet_Icc).mono (fun x hx ↦ hp x hx))
  simpa only [setIntegral_const, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul] using h

/-- The effective length in the finite-cell bound is the smaller of interval and cell lengths. -/
theorem Grid.integral_le_min_cell_sum {Γ : Set ℝ} (g : Grid Γ)
    (s : Finset ℤ) (v : ℤ → ℝ) (hv : ∀ k ∈ s, 0 ≤ v k)
    {w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hw : IntegrableOn w (Icc a b))
    (hcover : ∀ x ∈ Icc a b, ∃ k ∈ s, x ∈ cell g k)
    (hbound : ∀ k ∈ s, ∀ x ∈ cell g k, w x ≤ v k) :
    (∫ x in Icc a b, w x) ≤ min g.upper (b-a) * ∑ k ∈ s, v k := by
  by_cases h : g.upper ≤ b-a
  · rw [min_eq_left h]
    exact g.integral_le_cell_sum s v hv hw hcover hbound
  · rw [min_eq_right (le_of_not_ge h)]
    exact g.integral_le_length_cell_sum s v hv hab hw hcover hbound

/-- The number of cells is harmless after using the shorter effective length. -/
theorem Grid.min_length_mul_card_le {Γ : Set ℝ} (g : Grid Γ) {L n : ℝ}
    (hL : 0 < L) (hn : 0 ≤ n) (hcard : n ≤ L/g.lower+2) :
    min g.upper L * n ≤ (3*g.upper/g.lower)*L := by
  have hq := g.lower_pos
  have hD := g.upper_pos
  have hratio : 1 ≤ g.upper/g.lower := (le_div_iff₀ hq).mpr (by simpa using g.lower_le_upper)
  by_cases h : g.lower ≤ L
  · have hc : n ≤ 3*(L/g.lower) := by
      have hh : 1 ≤ L/g.lower := (le_div_iff₀ hq).mpr (by simpa using h)
      linarith
    calc
      _ ≤ g.upper * n := mul_le_mul_of_nonneg_right (min_le_left _ _) hn
      _ ≤ g.upper * (3*(L/g.lower)) := mul_le_mul_of_nonneg_left hc hD.le
      _ = _ := by ring
  · have hc : n ≤ 3 := by
      have hh : L/g.lower ≤ 1 := (div_le_iff₀ hq).mpr (by simpa using le_of_not_ge h)
      linarith
    calc
      _ ≤ L*n := mul_le_mul_of_nonneg_right (min_le_right _ _) hn
      _ ≤ L*3 := mul_le_mul_of_nonneg_left hc hL.le
      _ ≤ (3*g.upper/g.lower)*L := by
        have hh := mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hL.le)
        convert hh using 1 <;> ring

/-- A discrete A2 bound transfers across uniformly bounded Voronoi cells. -/
theorem Grid.integral_A2_of_cells {Γ : Set ℝ} (g : Grid Γ)
    (v : ℤ → ℝ) (hv : ∀ k, 0 < v k) {w : ℝ → ℝ}
    (hw : LocallyIntegrable w) (hwi : LocallyIntegrable (fun x ↦ (w x)⁻¹))
    {c C A : ℝ} (hc : 0 < c) (hC : 0 < C) (hA : 0 < A)
    (hcell : ∀ k, ∀ x ∈ cell g k, c*v k ≤ w x ∧ w x ≤ C*v k)
    (hdiscrete : ∀ m n : ℤ, m ≤ n →
      (∑ k ∈ Finset.Icc m n, v k) * (∑ k ∈ Finset.Icc m n, (v k)⁻¹) ≤
        A * (((n-m+1 : ℤ) : ℝ))^2)
    (hcover : ∀ a b : ℝ, a < b → ∃ m n : ℤ, m ≤ n ∧
      (∀ x ∈ Icc a b, ∃ k ∈ Finset.Icc m n, x ∈ cell g k) ∧
      (((n-m+1 : ℤ) : ℝ)) ≤ (b-a)/g.lower+2) :
    ∀ a b : ℝ, a < b →
      (∫ x in Icc a b, w x) * (∫ x in Icc a b, (w x)⁻¹) ≤
        (C/c*A*(3*g.upper/g.lower)^2)*(b-a)^2 := by
  intro a b hab
  obtain ⟨m, n, hmn, hcov, hnum⟩ := hcover a b hab
  let s := Finset.Icc m n
  let e := min g.upper (b-a)
  have he : 0 ≤ e := le_min g.upper_pos.le (sub_pos.mpr hab).le
  have hp (x : ℝ) (hx : x ∈ Icc a b) : 0 < w x := by
    obtain ⟨k, hk, hxk⟩ := hcov x hx
    exact (mul_pos hc (hv k)).trans_le (hcell k x hxk).1
  have hI := g.integral_le_min_cell_sum s (fun k ↦ C*v k)
    (fun k _ ↦ (mul_pos hC (hv k)).le) hab.le
    (hw.integrableOn_isCompact isCompact_Icc) hcov (fun k _ x hx ↦ (hcell k x hx).2)
  have hJ := g.integral_le_min_cell_sum s (fun k ↦ c⁻¹*(v k)⁻¹)
    (fun k _ ↦ (mul_pos (inv_pos.mpr hc) (inv_pos.mpr (hv k))).le) hab.le
    (hwi.integrableOn_isCompact isCompact_Icc) hcov (fun k _ x hx ↦ ?_)
  · rw [← Finset.mul_sum] at hI hJ
    have hI0 : 0 ≤ ∫ x in Icc a b, w x :=
      integral_nonneg_of_ae ((ae_restrict_mem measurableSet_Icc).mono (fun x hx ↦ (hp x hx).le))
    have hJ0 : 0 ≤ ∫ x in Icc a b, (w x)⁻¹ :=
      integral_nonneg_of_ae ((ae_restrict_mem measurableSet_Icc).mono (fun x hx ↦ (inv_pos.mpr (hp x hx)).le))
    have hsum : 0 ≤ ∑ k ∈ s, v k := Finset.sum_nonneg (fun k _ ↦ (hv k).le)
    have hm := mul_le_mul hI hJ hJ0 (mul_nonneg he (mul_nonneg hC.le hsum))
    have hdn := hdiscrete m n hmn
    have hn0 : (0 : ℝ) ≤ (((n-m+1 : ℤ) : ℝ)) := by exact_mod_cast (show (0 : ℤ) ≤ n-m+1 by omega)
    have hgeom := g.min_length_mul_card_le (sub_pos.mpr hab) hn0 hnum
    have hsq := pow_le_pow_left₀ (mul_nonneg he hn0) hgeom 2
    calc
      _ ≤ (e*(C*∑ k ∈ s, v k)) * (e*(c⁻¹*∑ k ∈ s, (v k)⁻¹)) := hm
      _ = (e^2*(C/c))*((∑ k ∈ s, v k)*(∑ k ∈ s, (v k)⁻¹)) := by ring
      _ ≤ (e^2*(C/c))*(A*(((n-m+1 : ℤ) : ℝ))^2) :=
        mul_le_mul_of_nonneg_left hdn (mul_nonneg (sq_nonneg _) (div_pos hC hc).le)
      _ = (C/c*A)*(e*(((n-m+1 : ℤ) : ℝ)))^2 := by ring
      _ ≤ (C/c*A)*((3*g.upper/g.lower)*(b-a))^2 :=
        mul_le_mul_of_nonneg_left hsq (mul_pos (div_pos hC hc) hA).le
      _ = _ := by ring
  · have hh := (hcell k x hx).1
    have hwx : 0 < w x := (mul_pos hc (hv k)).trans_le hh
    simpa only [mul_inv] using (inv_le_inv₀ hwx (mul_pos hc (hv k))).mpr hh

/-- An integer-interval form of the generator's discrete A2 bound. -/
theorem CardinalData.discrete_A2_Icc {Γ : Set ℝ} (d : CardinalData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) :
    ∃ A : ℝ, 0 < A ∧ ∀ m n : ℤ, m ≤ n →
      (∑ k ∈ Finset.Icc m n, ‖deriv d.G (g.point k : ℂ)‖^2) *
        (∑ k ∈ Finset.Icc m n, (‖deriv d.G (g.point k : ℂ)‖^2)⁻¹) ≤
          A * (((n-m+1 : ℤ) : ℝ))^2 := by
  obtain ⟨A, hA, hbound⟩ := d.discrete_A2 g hΓ
  refine ⟨A, hA, ?_⟩
  intro m n hmn
  let N : ℕ := (n-m+1).toNat
  have hN : 0 < N := by dsimp [N]; omega
  have hcast : (N : ℤ) = n-m+1 := Int.toNat_of_nonneg (by omega)
  have h := hbound m N hN
  simp only [weightSum, invWeightSum, Grid.block, Finset.sum_map, Grid.nodeEmbedding] at h
  have he : m+(N : ℤ) = n+1 := by omega
  rw [he, Finset.Ico_add_one_right_eq_Icc] at h
  have hr : (N : ℝ) = ((n-m+1 : ℤ) : ℝ) := by exact_mod_cast hcast
  change (∑ k ∈ Finset.Icc m n, ‖deriv d.G (g.point k : ℂ)‖^2) *
    (∑ k ∈ Finset.Icc m n, (‖deriv d.G (g.point k : ℂ)‖^2)⁻¹) ≤ A*(N : ℝ)^2 at h
  rwa [hr] at h

/-- The A2 transfer works at any fixed height with the stated uniform cell bounds. -/
theorem CardinalData.shifted_A2_of_bounds {Γ : Set ℝ} (d : CardinalData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) (ε c C : ℝ)
    (hc : 0 < c) (hC : 0 < C)
    (hbounds : ∀ k : ℤ, ∀ x ∈ cell g k,
      c * ‖deriv d.G (g.point k : ℂ)‖ ≤ ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖ ∧
      ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖ ≤ C * ‖deriv d.G (g.point k : ℂ)‖) :
    ∃ K : ℝ, 0 < K ∧
      LocallyIntegrable (fun x : ℝ ↦ ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2) ∧
      LocallyIntegrable (fun x : ℝ ↦ (‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2)⁻¹) ∧
      (∀ x : ℝ, 0 < ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2) ∧
      ∀ a b : ℝ, a < b →
        intervalMean (fun x : ℝ ↦ ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2) a b *
          intervalMean (fun x : ℝ ↦ (‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2)⁻¹) a b ≤ K := by
  obtain ⟨A, hA, hdisc⟩ := d.discrete_A2_Icc g hΓ
  let w : ℝ → ℝ := fun x ↦ ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2
  let v : ℤ → ℝ := fun k ↦ ‖deriv d.G (g.point k : ℂ)‖^2
  have hv (k : ℤ) : 0 < v k := sq_pos_of_pos
    (norm_pos_iff.mpr (d.toGeneratingData.simple (g.point_mem k)))
  have hcell : ∀ k, ∀ x ∈ cell g k, c^2*v k ≤ w x ∧ w x ≤ C^2*v k := by
    intro k x hx
    obtain ⟨hl, hu⟩ := hbounds k x hx
    have hder : 0 ≤ ‖deriv d.G (g.point k : ℂ)‖ := norm_nonneg _
    constructor
    · simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg hc.le hder) hl 2
    · simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hu 2
  have hpos (x : ℝ) : 0 < w x := by
    obtain ⟨k, hk⟩ := g.exists_cell x
    exact (mul_pos (sq_pos_of_pos hc) (hv k)).trans_le (hcell k x hk).1
  have hcont : Continuous w := by
    dsimp [w]
    exact (d.entire.continuous.comp (Complex.continuous_ofReal.add continuous_const)).norm.pow 2
  have hw : LocallyIntegrable w := hcont.locallyIntegrable
  have hwi : LocallyIntegrable (fun x ↦ (w x)⁻¹) :=
    (hcont.inv₀ (fun x ↦ (hpos x).ne')).locallyIntegrable
  let K := C^2/c^2*A*(3*g.upper/g.lower)^2
  have hq := g.lower_pos
  have hD := g.upper_pos
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, hw, hwi, hpos, ?_⟩
  intro a b hab
  have hi := g.integral_A2_of_cells v hv hw hwi (sq_pos_of_pos hc) (sq_pos_of_pos hC) hA
    hcell hdisc (fun a b hab ↦ ?_) a b hab
  · change intervalMean w a b * intervalMean (fun x ↦ (w x)⁻¹) a b ≤ K
    simp only [intervalMean, intervalIntegral.integral_of_le hab.le,
      ← integral_Icc_eq_integral_Ioc]
    calc
      _ = ((∫ x in Icc a b, w x)*(∫ x in Icc a b, (w x)⁻¹))/(b-a)^2 := by
        field_simp [(sub_pos.mpr hab).ne']
      _ ≤ K := (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hab))).mpr hi
  · obtain ⟨m, n, hmn, hcov, hnum⟩ := g.exists_cell_cover hab
    refine ⟨m, n, hmn, ?_, hnum⟩
    intro x hx
    simpa only [Set.mem_iUnion, exists_prop] using hcov hx


/-- The positive shifted generator weight satisfies the continuous A2 condition. -/
theorem CardinalData.shifted_A2 {Γ : Set ℝ} (d : CardinalData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) :
    ∃ ε K : ℝ, 0 < ε ∧ ε < g.lower/8 ∧ 0 < K ∧
      LocallyIntegrable (fun x : ℝ ↦ ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2) ∧
      LocallyIntegrable (fun x : ℝ ↦ (‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2)⁻¹) ∧
      (∀ x : ℝ, 0 < ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2) ∧
      ∀ a b : ℝ, a < b →
        intervalMean (fun x : ℝ ↦ ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2) a b *
          intervalMean (fun x : ℝ ↦ (‖d.G ((x : ℂ)+(ε : ℂ)*I)‖^2)⁻¹) a b ≤ K := by
  obtain ⟨ε, c, C, hε, hεl, hc, hC, hbounds⟩ := generating_cell_bounds g d
  obtain ⟨K, hK, hw, hwi, hpos, hmean⟩ := d.shifted_A2_of_bounds g hΓ ε c C hc hC
    (fun k x hx ↦ (hbounds k x hx).1)
  exact ⟨ε, K, hε, hεl, hK, hw, hwi, hpos, hmean⟩

end FF.Pavlov
