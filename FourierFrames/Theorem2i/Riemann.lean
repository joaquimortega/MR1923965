import FourierFrames.Theorem2i.Counting

/-!
# M08 helper (D2): the Poisson Riemann sum (blueprint §6.8)
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

namespace D2

theorem poisson_eq (x y s : ℝ) (hy : 0 < y) :
    y / ((s - x) ^ 2 + y ^ 2) = y⁻¹ * (1 + (y⁻¹ * (s - x)) ^ 2)⁻¹ := by
  have : (1 + (y⁻¹ * (s - x)) ^ 2) = ((s - x) ^ 2 + y ^ 2) / y ^ 2 := by
    field_simp; ring
  rw [this]; field_simp

theorem poisson_integrable (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (fun s : ℝ => y / ((s - x) ^ 2 + y ^ 2)) := by
  have h1 : Integrable (fun s : ℝ => (1 + (y⁻¹ * (s - x)) ^ 2)⁻¹) :=
    (integrable_inv_one_add_mul_sq (inv_ne_zero hy.ne')).comp_sub_right x
  exact (h1.const_mul y⁻¹).congr (Filter.Eventually.of_forall fun s => (poisson_eq x y s hy).symm)

theorem poisson_integral (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ s : ℝ, y / ((s - x) ^ 2 + y ^ 2) = Real.pi := by
  have : (fun s : ℝ => y / ((s - x) ^ 2 + y ^ 2)) =
      fun s => y⁻¹ * (1 + (y⁻¹ * (s - x)) ^ 2)⁻¹ := funext fun s => poisson_eq x y s hy
  rw [this, integral_const_mul, integral_sub_right_eq_self
    (fun s : ℝ => (1 + (y⁻¹ * s) ^ 2)⁻¹) x, integral_univ_inv_one_add_mul_sq]
  rw [abs_of_pos (inv_pos.mpr hy)]
  field_simp

theorem cell_disjoint (h : RegData ψ t C M) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≠ m) :
    Disjoint (cell t n) (cell t m) := by
  rcases lt_or_gt_of_ne hnm with hlt | hlt
  · refine Set.disjoint_left.mpr fun s hs1 hs2 => ?_
    have : t n ≤ t (m - 1) := h.mono.monotone (by omega)
    exact absurd (lt_of_le_of_lt this hs2.1) (not_lt.mpr hs1.2)
  · refine Set.disjoint_left.mpr fun s hs1 hs2 => ?_
    have : t m ≤ t (n - 1) := h.mono.monotone (by omega)
    exact absurd (lt_of_le_of_lt this hs1.1) (not_lt.mpr hs2.2)

/-- `|r_n - s| ≤ d_n` for `s` in the `n`-th cell. -/
theorem abs_sub_centre_le (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : s ∈ cell t n) :
    |rCentre ψ t n - s| ≤ cellLen t n := by
  obtain ⟨h1, h2⟩ := h.rCentre_mem hn
  rw [abs_le]; unfold cellLen; constructor <;> linarith [hs.1, hs.2]

end D2

/-- Finset form of the Riemann-sum bound `sum_far_im_le`: valid for every `k ≥ 8`. -/
theorem RegData.finset_sum_far_im_le (h : RegData ψ t C M) {z : ℂ} {k : ℝ} (hk : 8 ≤ k)
    (F : Finset ℕ)
    (hF : ∀ n ∈ F, 1 ≤ n ∧ k * cellLen t n ≤ ‖z - (rCentre ψ t n : ℂ)‖) :
    ∑ n ∈ F, cellLen t n * z.im / ‖z - (rCentre ψ t n : ℂ)‖ ^ 2 ≤ 9 / 4 * Real.pi := by
  have hpi := Real.pi_pos
  rcases le_or_gt z.im 0 with hy | hy
  · refine le_trans (Finset.sum_nonpos fun n hn => ?_) (by positivity)
    have := D2.cellLen_pos h (hF n hn).1
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos this.le hy) (by positivity)
  set P : ℝ → ℝ := fun s => z.im / ((s - z.re) ^ 2 + z.im ^ 2) with hP
  have hPint := D2.poisson_integrable z.re hy
  have hPnn : ∀ s, 0 ≤ P s := fun s => by simp only [hP]; positivity
  have hPc : Continuous P := by
    simp only [hP]
    refine Continuous.div continuous_const (by fun_prop) fun s => by positivity
  have hterm : ∀ n ∈ F, cellLen t n * z.im / ‖z - (rCentre ψ t n : ℂ)‖ ^ 2 ≤
      81 / 64 * ∫ s in cell t n, P s := by
    intro n hn
    obtain ⟨hn1, hfar⟩ := hF n hn
    have hd := D2.cellLen_pos h hn1
    have hu : 0 < ‖z - (rCentre ψ t n : ℂ)‖ := lt_of_lt_of_le (by positivity) hfar
    set u := ‖z - (rCentre ψ t n : ℂ)‖ with hu_def
    have hdu : cellLen t n ≤ u / 8 := by
      have : k * cellLen t n ≥ 8 * cellLen t n := by nlinarith
      linarith
    have hpt : ∀ s ∈ cell t n, 64 / 81 * (z.im / u ^ 2) ≤ P s := by
      intro s hs
      have h1 : ‖z - (s : ℂ)‖ ≤ 9 / 8 * u := by
        have h2 : ‖z - (s : ℂ)‖ ≤ ‖z - (rCentre ψ t n : ℂ)‖ + ‖(rCentre ψ t n : ℂ) - s‖ := by
          have := norm_add_le (z - (rCentre ψ t n : ℂ)) ((rCentre ψ t n : ℂ) - s)
          simpa using this
        have h3 : ‖(rCentre ψ t n : ℂ) - s‖ ≤ cellLen t n := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact D2.abs_sub_centre_le h hn1 hs
        linarith
      have h4 : ‖z - (s : ℂ)‖ ^ 2 = (s - z.re) ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have h5 : (s - z.re) ^ 2 + z.im ^ 2 ≤ (9 / 8 * u) ^ 2 := by
        rw [← h4]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      simp only [hP]
      have h6 : 0 < (s - z.re) ^ 2 + z.im ^ 2 := by positivity
      have e : 64 / 81 * (z.im / u ^ 2) = (64 * z.im) / (81 * u ^ 2) := by field_simp
      rw [e, div_le_div_iff₀ (by positivity) h6]
      nlinarith [mul_le_mul_of_nonneg_left h5 hy.le]
    have hmeas : MeasurableSet (cell t n) := measurableSet_Ioc
    have hI := setIntegral_ge_of_const_le_real (μ := volume) hmeas (by simp [cell]) hpt
      (hPint.integrableOn)
    have hvol : volume.real (cell t n) = cellLen t n := by
      simp [cell, cellLen, Real.volume_real_Ioc_of_le (h.mono.monotone (Nat.sub_le n 1))]
    rw [hvol] at hI
    have : cellLen t n * z.im / u ^ 2 = cellLen t n * (z.im / u ^ 2) := by ring
    rw [this]
    nlinarith
  have hsum : ∑ n ∈ F, ∫ s in cell t n, P s ≤ Real.pi := by
    rw [← integral_biUnion_finset F (s := fun n => cell t n) (fun n _ => measurableSet_Ioc)
      (fun n hn m hm hnm => D2.cell_disjoint h (hF n hn).1 (hF m hm).1 hnm)
      (fun n _ => hPint.integrableOn)]
    calc _ ≤ ∫ s, P s := setIntegral_le_integral hPint (Filter.Eventually.of_forall hPnn)
      _ = Real.pi := D2.poisson_integral z.re hy
  calc _ ≤ ∑ n ∈ F, 81 / 64 * ∫ s in cell t n, P s := Finset.sum_le_sum hterm
    _ = 81 / 64 * ∑ n ∈ F, ∫ s in cell t n, P s := by rw [Finset.mul_sum]
    _ ≤ 81 / 64 * Real.pi := by gcongr
    _ ≤ _ := by nlinarith

end FF
