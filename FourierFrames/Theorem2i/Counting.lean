import FourierFrames.Theorem2i.Basic

/-!
# M08 helper (D2): counting estimates in finset form

Uniform finset versions of the counting bounds of blueprint §6.8 (these do not need
summability, so they can be combined without worrying about junk values of `tsum`).
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

namespace D2

theorem cellLen_pos (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) : 0 < cellLen t n := by
  unfold cellLen
  have := h.mono (show n - 1 < n by omega)
  linarith

theorem t_nonneg (h : RegData ψ t C M) (n : ℕ) : 0 ≤ t n := by
  have := h.mono.monotone (Nat.zero_le n)
  rwa [h.t0] at this

/-- `M ≥ 1`: the cell `n = 1` contributes `1` to the sum at `x = t 1`. -/
theorem one_le_M (h : RegData ψ t C M) : 1 ≤ M := by
  have h1 : 0 < t 1 := by
    have := h.mono (show 0 < 1 by norm_num)
    rwa [h.t0] at this
  have hs := h.sum_le (t 1) h1
  have hmem : (1 : ℕ) ∈ {n : ℕ | 1 ≤ n ∧ t 1 / 2 < t n ∧ t n < 2 * t 1} :=
    ⟨le_rfl, by linarith, by linarith⟩
  have h2 := le_trans (ENNReal.le_tsum (f := fun n : {n : ℕ | 1 ≤ n ∧ t 1 / 2 < t n ∧
      t n < 2 * t 1} => ENNReal.ofReal ((t n - t (n - 1)) ^ 2 /
        ((t 1 - t n) ^ 2 + (t n - t (n - 1)) ^ 2))) ⟨1, hmem⟩) hs
  have h3 : (t 1 - t 0) ^ 2 / ((t 1 - t 1) ^ 2 + (t 1 - t 0) ^ 2) = 1 := by
    rw [h.t0]; field_simp; simp
  simp only [Nat.sub_self, h3] at h2
  simpa using (ENNReal.one_le_ofReal.mp (by simpa using h2))

/-- Finset form of `sum_le`. -/
theorem finset_sum_le (h : RegData ψ t C M) {x : ℝ} (hx : 0 < x) (F : Finset ℕ)
    (hF : ∀ n ∈ F, 1 ≤ n ∧ x / 2 < t n ∧ t n < 2 * x) :
    ∑ n ∈ F, cellLen t n ^ 2 / ((x - t n) ^ 2 + cellLen t n ^ 2) ≤ M := by
  classical
  have hM := one_le_M h
  have hs := h.sum_le x hx
  set S : Set ℕ := {n : ℕ | 1 ≤ n ∧ x / 2 < t n ∧ t n < 2 * x} with hS
  set g : ℕ → ℝ := fun n => cellLen t n ^ 2 / ((x - t n) ^ 2 + cellLen t n ^ 2) with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by positivity
  have hsub : ENNReal.ofReal (∑ n ∈ F, g n) ≤ ENNReal.ofReal M := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => hg0 n)]
    have e : ∑ n ∈ F, ENNReal.ofReal (g n) =
        ∑ s ∈ F.subtype (fun n => n ∈ S), ENNReal.ofReal (g s.1) := by
      exact (Finset.sum_subtype_of_mem (p := fun n => n ∈ S) (fun n => ENNReal.ofReal (g n))
        (fun n hn => hF n hn)).symm
    rw [e]
    refine le_trans (ENNReal.sum_le_tsum (f := fun s : S => ENNReal.ofReal (g s.1)) _) ?_
    exact hs
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hsub

/-- Key comparison between the cell kernel centred at `z` and the one at `‖z‖`. -/
theorem key (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    cellLen t n ^ 2 / (‖z - (rCentre ψ t n : ℂ)‖ ^ 2 + cellLen t n ^ 2) ≤
      3 * (cellLen t n ^ 2 / ((‖z‖ - t n) ^ 2 + cellLen t n ^ 2)) := by
  have hd := cellLen_pos h hn
  obtain ⟨hr1, hr2⟩ := h.rCentre_mem hn
  have hr0 : 0 ≤ rCentre ψ t n := by
    have := t_nonneg h (n - 1); linarith
  have h1 : |‖z‖ - rCentre ψ t n| ≤ ‖z - (rCentre ψ t n : ℂ)‖ := by
    have := abs_norm_sub_norm_le z (rCentre ψ t n : ℂ)
    simpa [abs_of_nonneg hr0] using this
  have h2 : (‖z‖ - rCentre ψ t n) ^ 2 ≤ ‖z - (rCentre ψ t n : ℂ)‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : (rCentre ψ t n - t n) ^ 2 ≤ cellLen t n ^ 2 := by
    unfold cellLen at *
    nlinarith
  have h4 : (‖z‖ - t n) ^ 2 + cellLen t n ^ 2 ≤
      3 * (‖z - (rCentre ψ t n : ℂ)‖ ^ 2 + cellLen t n ^ 2) := by
    nlinarith [sq_nonneg (‖z‖ - rCentre ψ t n - (rCentre ψ t n - t n))]
  have hA : 0 < (‖z‖ - t n) ^ 2 + cellLen t n ^ 2 := by positivity
  have hB : 0 < ‖z - (rCentre ψ t n : ℂ)‖ ^ 2 + cellLen t n ^ 2 := by positivity
  rw [← mul_div_assoc, div_le_div_iff₀ hB hA]
  have := mul_le_mul_of_nonneg_left h4 (sq_nonneg (cellLen t n))
  nlinarith

end D2

/-- Number of near cells of the window (finset form of `card_near_le`). -/
theorem RegData.finset_card_near_le (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0) {k : ℝ}
    (hk : 0 < k) (F : Finset ℕ)
    (hF : ∀ n ∈ F, 1 ≤ n ∧ ‖z‖ / 2 < t n ∧ t n < 2 * ‖z‖ ∧
      ‖z - (rCentre ψ t n : ℂ)‖ < k * cellLen t n) :
    (F.card : ℝ) ≤ 3 * (1 + k ^ 2) * M := by
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hS := D2.finset_sum_le h hz F (fun n hn => ⟨(hF n hn).1, (hF n hn).2.1, (hF n hn).2.2.1⟩)
  have hpt : ∀ n ∈ F, 1 / (1 + k ^ 2) ≤
      3 * (cellLen t n ^ 2 / ((‖z‖ - t n) ^ 2 + cellLen t n ^ 2)) := by
    intro n hn
    obtain ⟨hn1, -, -, hnear⟩ := hF n hn
    have hd := D2.cellLen_pos h hn1
    refine le_trans ?_ (D2.key h hn1 z)
    have hu : ‖z - (rCentre ψ t n : ℂ)‖ ^ 2 ≤ (k * cellLen t n) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnear.le 2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (cellLen t n)]
  have h1 : (F.card : ℝ) * (1 / (1 + k ^ 2)) ≤ 3 * M := by
    calc (F.card : ℝ) * (1 / (1 + k ^ 2)) = ∑ n ∈ F, 1 / (1 + k ^ 2) := by simp
      _ ≤ ∑ n ∈ F, 3 * (cellLen t n ^ 2 / ((‖z‖ - t n) ^ 2 + cellLen t n ^ 2)) :=
          Finset.sum_le_sum hpt
      _ = 3 * ∑ n ∈ F, cellLen t n ^ 2 / ((‖z‖ - t n) ^ 2 + cellLen t n ^ 2) := by
          rw [Finset.mul_sum]
      _ ≤ 3 * M := by linarith
  have hk2 : 0 < 1 + k ^ 2 := by positivity
  rw [mul_one_div, div_le_iff₀ hk2] at h1
  linarith

/-- The near set is finite. -/
theorem RegData.finite_near (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0) {k : ℝ} (hk : 0 < k) :
    ({n : ℕ | 1 ≤ n ∧ ‖z‖ / 2 < t n ∧ t n < 2 * ‖z‖ ∧
        ‖z - (rCentre ψ t n : ℂ)‖ < k * cellLen t n} : Set ℕ).Finite := by
  by_contra hinf
  obtain ⟨F, hFs, hFc⟩ := Set.Infinite.exists_subset_card_eq hinf
    (⌈3 * (1 + k ^ 2) * M⌉₊ + 1)
  have := RegData.finset_card_near_le h hz0 hk F (fun n hn => hFs hn)
  rw [hFc] at this
  have h2 := Nat.le_ceil (3 * (1 + k ^ 2) * M)
  push_cast at this
  linarith

/-- Far cells of the window (finset form of `sum_far_le`). -/
theorem RegData.finset_sum_far_le (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0) {k : ℝ}
    (hk : 0 < k) (F : Finset ℕ)
    (hF : ∀ n ∈ F, 1 ≤ n ∧ ‖z‖ / 2 < t n ∧ t n < 2 * ‖z‖ ∧
      k * cellLen t n ≤ ‖z - (rCentre ψ t n : ℂ)‖) :
    ∑ n ∈ F, cellLen t n ^ 2 / ‖z - (rCentre ψ t n : ℂ)‖ ^ 2 ≤ 3 * (1 + k⁻¹ ^ 2) * M := by
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hS := D2.finset_sum_le h hz F (fun n hn => ⟨(hF n hn).1, (hF n hn).2.1, (hF n hn).2.2.1⟩)
  have hpt : ∀ n ∈ F, cellLen t n ^ 2 / ‖z - (rCentre ψ t n : ℂ)‖ ^ 2 ≤
      (1 + k⁻¹ ^ 2) * (3 * (cellLen t n ^ 2 / ((‖z‖ - t n) ^ 2 + cellLen t n ^ 2))) := by
    intro n hn
    obtain ⟨hn1, -, -, hfar⟩ := hF n hn
    have hd := D2.cellLen_pos h hn1
    have hu0 : 0 < ‖z - (rCentre ψ t n : ℂ)‖ := lt_of_lt_of_le (by positivity) hfar
    have hkey := D2.key h hn1 z
    have h1 : cellLen t n ^ 2 / ‖z - (rCentre ψ t n : ℂ)‖ ^ 2 ≤
        (1 + k⁻¹ ^ 2) * (cellLen t n ^ 2 /
          (‖z - (rCentre ψ t n : ℂ)‖ ^ 2 + cellLen t n ^ 2)) := by
      have hd2 : cellLen t n ^ 2 ≤ k⁻¹ ^ 2 * ‖z - (rCentre ψ t n : ℂ)‖ ^ 2 := by
        have : cellLen t n ≤ k⁻¹ * ‖z - (rCentre ψ t n : ℂ)‖ := by
          rw [inv_mul_eq_div, le_div_iff₀ hk]; linarith
        calc cellLen t n ^ 2 ≤ (k⁻¹ * ‖z - (rCentre ψ t n : ℂ)‖) ^ 2 :=
              pow_le_pow_left₀ hd.le this 2
          _ = _ := by ring
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (cellLen t n)]
    exact le_trans h1 (mul_le_mul_of_nonneg_left hkey (by positivity))
  calc ∑ n ∈ F, cellLen t n ^ 2 / ‖z - (rCentre ψ t n : ℂ)‖ ^ 2
      ≤ ∑ n ∈ F, (1 + k⁻¹ ^ 2) * (3 * (cellLen t n ^ 2 /
          ((‖z‖ - t n) ^ 2 + cellLen t n ^ 2))) := Finset.sum_le_sum hpt
    _ = (1 + k⁻¹ ^ 2) * 3 * ∑ n ∈ F, cellLen t n ^ 2 /
          ((‖z‖ - t n) ^ 2 + cellLen t n ^ 2) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
    _ ≤ (1 + k⁻¹ ^ 2) * 3 * M := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by ring

end FF
