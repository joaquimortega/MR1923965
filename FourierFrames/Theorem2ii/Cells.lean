import FourierFrames.Defs

/-!
# M09 helper: sums over `Λ(ψ)` by unit cells

* `tsum_cells_le`: a point set with at most `N` points per cell `[j, j+1)` has `ℝ≥0∞`-sum bounded
  by `N` times a sum over the cells.
* `LambdaPsi` has at most `N(ψ)` points per cell.
* harmonic-type sums.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace FF

namespace T2ii

lemma tsum_cells_le {A : Set ℝ} (hA0 : A ⊆ Ici 0) {N : ℕ}
    (hcnt : ∀ (j : ℕ) (F : Finset ℝ), (↑F : Set ℝ) ⊆ A → (∀ x ∈ F, (j : ℝ) ≤ x ∧ x < j + 1) →
      F.card ≤ N)
    (φ : ℝ → ℝ≥0∞) (H : ℕ → ℝ≥0∞) (hH : ∀ l ∈ A, φ l ≤ H ⌊l⌋₊) (T : ℝ≥0∞)
    (hT : ∀ J : Finset ℕ, ∑ j ∈ J, H j ≤ T) :
    ∑' l : A, φ l ≤ N * T := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F ↦ ?_
  classical
  have hcard : ∀ j : ℕ, (F.filter (fun x : A ↦ ⌊(x : ℝ)⌋₊ = j)).card ≤ N := by
    intro j
    have := hcnt j ((F.filter (fun x : A ↦ ⌊(x : ℝ)⌋₊ = j)).image Subtype.val)
      (by
        intro x hx
        simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hx
        obtain ⟨y, _, rfl⟩ := hx
        exact y.2)
      (by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_filter] at hx
        obtain ⟨y, ⟨_, hy⟩, rfl⟩ := hx
        have h0 : (0 : ℝ) ≤ y := hA0 y.2
        rw [← hy]
        exact ⟨Nat.floor_le h0, Nat.lt_floor_add_one _⟩)
    rwa [Finset.card_image_of_injective _ Subtype.val_injective] at this
  calc ∑ x ∈ F, φ x ≤ ∑ x ∈ F, H ⌊(x : ℝ)⌋₊ := Finset.sum_le_sum fun x _ ↦ hH x x.2
    _ = ∑ j ∈ F.image (fun x : A ↦ ⌊(x : ℝ)⌋₊),
          ∑ x ∈ F.filter (fun x : A ↦ ⌊(x : ℝ)⌋₊ = j), H ⌊(x : ℝ)⌋₊ := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : A ↦ ⌊(x : ℝ)⌋₊)
          (t := F.image (fun x : A ↦ ⌊(x : ℝ)⌋₊)) (fun x hx ↦ Finset.mem_image_of_mem _ hx)]
    _ = ∑ j ∈ F.image (fun x : A ↦ ⌊(x : ℝ)⌋₊),
          (F.filter (fun x : A ↦ ⌊(x : ℝ)⌋₊ = j)).card • H j := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_congr rfl (g := fun _ ↦ H j) (fun x hx ↦ by
          rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const]
    _ ≤ ∑ j ∈ F.image (fun x : A ↦ ⌊(x : ℝ)⌋₊), N • H j :=
        Finset.sum_le_sum fun j _ ↦ by gcongr; exact hcard j
    _ = N * ∑ j ∈ F.image (fun x : A ↦ ⌊(x : ℝ)⌋₊), H j := by
        rw [← Finset.smul_sum, nsmul_eq_mul]
    _ ≤ N * T := mul_le_mul_right (hT _) _

lemma exists_bound_deriv {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |deriv ψ x| ≤ B := by
  have hcont : Continuous (deriv ψ) := hψ.1.continuous_deriv le_rfl
  have hT := hψ.2.2.2
  have hev : ∀ᶠ x in cocompact ℝ, |deriv ψ x| < 1 := by
    have := hT.eventually (Metric.ball_mem_nhds 0 one_pos)
    filter_upwards [this] with x hx
    simpa using hx
  obtain ⟨K, hK, hKs⟩ := (Filter.mem_cocompact.1 hev)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), fun x ↦ ?_⟩
  by_cases hx : x ∈ K
  · exact (by simpa using hC x hx : |deriv ψ x| ≤ C).trans (le_max_left _ _)
  · exact (hKs hx).le.trans (le_max_right _ _)

lemma lambda_sep {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {B : ℝ} (hB : ∀ x, |deriv ψ x| ≤ B)
    {x y : ℝ} (hx : x ∈ LambdaPsi ψ) (hy : y ∈ LambdaPsi ψ) (hxy : x < y) :
    1 ≤ (y - x) * (1 + B) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨k', hk'⟩ := hy
  have hd : Differentiable ℝ ψ := hψ.1.differentiable one_ne_zero
  have hmono := hψ.2.1
  have h1 : ψ y - ψ x ≤ B * (y - x) :=
    image_sub_le_mul_sub_of_deriv_le hd (fun t ↦ (le_abs_self _).trans (hB t)) hxy.le
  have h2 : (k : ℝ) < k' := by
    have := hmono hxy.le
    linarith
  have h3 : (k : ℝ) + 1 ≤ k' := by exact_mod_cast (Int.cast_lt.1 h2 : k < k')
  nlinarith

lemma lambda_cell_count {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |deriv ψ x| ≤ B) (j : ℝ) (F : Finset ℝ) (hF : (↑F : Set ℝ) ⊆ LambdaPsi ψ)
    (hj : ∀ x ∈ F, j ≤ x ∧ x < j + 1) : F.card ≤ ⌊1 + B⌋₊ + 1 := by
  have hmap : ∀ x ∈ F, ⌊(x - j) * (1 + B)⌋₊ ∈ Finset.range (⌊1 + B⌋₊ + 1) := by
    intro x hx
    have h1 := (hj x hx).1
    have h2 := (hj x hx).2
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (by nlinarith)
  have hinj : Set.InjOn (fun x : ℝ ↦ ⌊(x - j) * (1 + B)⌋₊) ↑F := by
    have key : ∀ x ∈ F, ∀ y ∈ F, x < y → ⌊(x - j) * (1 + B)⌋₊ < ⌊(y - j) * (1 + B)⌋₊ := by
      intro x hx y hy hxy
      have hsep := lambda_sep hψ hB (hF hx) (hF hy) hxy
      have hx0 : 0 ≤ (x - j) * (1 + B) := by
        have := (hj x hx).1; nlinarith
      have h1 : (x - j) * (1 + B) + 1 ≤ (y - j) * (1 + B) := by nlinarith
      calc ⌊(x - j) * (1 + B)⌋₊ < ⌊(x - j) * (1 + B)⌋₊ + 1 := Nat.lt_succ_self _
        _ = ⌊(x - j) * (1 + B) + 1⌋₊ := (Nat.floor_add_one hx0).symm
        _ ≤ _ := Nat.floor_le_floor h1
    intro x hx y hy hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (key x hx y hy h).ne hxy
    · exact (key y hy x hx h).ne hxy.symm
  have := Finset.card_le_card_of_injOn _ hmap hinj
  simpa using this

/-! ### Harmonic-type sums -/

lemma harm_sum_le {x₀ : ℝ} (hx₀ : 0 < x₀) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), 1 / (x₀ + i) ≤ 1 / x₀ + Real.log ((x₀ + n) / x₀) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : 0 < x₀ + n := by positivity
    have h1 : 1 / (x₀ + ((n + 1 : ℕ) : ℝ)) ≤ Real.log ((x₀ + ((n + 1 : ℕ) : ℝ)) / (x₀ + n)) := by
      have := Real.one_sub_inv_le_log_of_pos (show 0 < (x₀ + ((n + 1 : ℕ) : ℝ)) / (x₀ + n) by
        positivity)
      refine le_trans (le_of_eq ?_) this
      push_cast
      field_simp
      ring
    have h2 : Real.log ((x₀ + ((n + 1 : ℕ) : ℝ)) / x₀) =
        Real.log ((x₀ + n) / x₀) + Real.log ((x₀ + ((n + 1 : ℕ) : ℝ)) / (x₀ + n)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    rw [h2]
    linarith

lemma inv_sq_sum_le {x₀ : ℝ} (hx₀ : 1 / 2 < x₀) (n : ℕ) :
    ∑ i ∈ Finset.range n, 1 / (x₀ + i) ^ 2 ≤ 1 / (x₀ - 1 / 2) - 1 / (x₀ + n - 1 / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : 0 < x₀ + n - 1 / 2 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have h2 : 1 / (x₀ + n) ^ 2 ≤ 1 / (x₀ + n - 1 / 2) - 1 / (x₀ + ((n + 1 : ℕ) : ℝ) - 1 / 2) := by
      push_cast
      have hq : 0 < x₀ + n := by linarith
      have h3 : 0 < x₀ + (n + 1) - 1 / 2 := by linarith
      rw [div_sub_div _ _ h1.ne' h3.ne']
      rw [div_le_div_iff₀ (pow_pos hq 2) (mul_pos h1 h3)]
      nlinarith [sq_nonneg (x₀ + n)]
    linarith

lemma sum_Icc_inv_half {J₀ J₁ : ℕ} (h : J₀ ≤ J₁) :
    ∑ j ∈ Finset.Icc J₀ J₁, 1 / ((j : ℝ) + 1 / 2) ≤
      1 / ((J₀ : ℝ) + 1 / 2) + Real.log (((J₁ : ℝ) + 1 / 2) / ((J₀ : ℝ) + 1 / 2)) := by
  have e : Finset.Icc J₀ J₁ = Finset.Ico J₀ (J₁ + 1) := by
    ext x; simp
  rw [e, Finset.sum_Ico_eq_sum_range]
  have hx₀ : 0 < (J₀ : ℝ) + 1 / 2 := by positivity
  have := harm_sum_le hx₀ (J₁ - J₀)
  have e2 : J₁ + 1 - J₀ = (J₁ - J₀) + 1 := by omega
  rw [e2]
  have e3 : ((J₀ : ℝ) + 1 / 2 + ((J₁ - J₀ : ℕ) : ℝ)) = (J₁ : ℝ) + 1 / 2 := by
    rw [Nat.cast_sub h]; ring
  rw [e3] at this
  refine le_trans (le_of_eq ?_) this
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  push_cast; ring_nf

lemma sum_Ico_inv_sq {J₁ : ℕ} (hJ : 1 ≤ J₁) (M : ℕ) :
    ∑ j ∈ Finset.Ico J₁ M, 1 / ((j : ℝ) + 1 / 2) ^ 2 ≤ 1 / (J₁ : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hx₀ : 1 / 2 < (J₁ : ℝ) + 1 / 2 := by
    have : (1 : ℝ) ≤ J₁ := by exact_mod_cast hJ
    linarith
  have := inv_sq_sum_le hx₀ (M - J₁)
  have h1 : (0 : ℝ) < (J₁ : ℝ) := by exact_mod_cast hJ
  have h2 : 0 < 1 / ((J₁ : ℝ) + 1 / 2 + ((M - J₁ : ℕ) : ℝ) - 1 / 2) := by
    have : (0 : ℝ) ≤ ((M - J₁ : ℕ) : ℝ) := Nat.cast_nonneg _
    apply one_div_pos.2; linarith
  have e : (J₁ : ℝ) + 1 / 2 - 1 / 2 = J₁ := by ring
  rw [e] at this
  refine le_trans (le_of_eq ?_) (this.trans (by linarith))
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  push_cast; ring_nf

/-! ### Cell-sum bounds in `ℝ≥0∞` -/

lemma sumH_finset (J : Finset ℕ) (S : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) :
    ∑ j ∈ J, (if j ∈ S then ENNReal.ofReal (g j) else 0) ≤ ENNReal.ofReal (∑ j ∈ S, g j) := by
  classical
  rw [Finset.sum_ite_mem, ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hg j)]
  exact Finset.sum_le_sum_of_subset (Finset.inter_subset_right)

lemma sumH_tail (J : Finset ℕ) (J₁ : ℕ) (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) (T : ℝ)
    (hT : ∀ M, ∑ j ∈ Finset.Ico J₁ M, g j ≤ T) :
    ∑ j ∈ J, (if J₁ ≤ j then ENNReal.ofReal (g j) else 0) ≤ ENNReal.ofReal T := by
  classical
  set M := J.sup id + 1 with hM
  have hsub : J.filter (fun j ↦ J₁ ≤ j) ⊆ Finset.Ico J₁ M := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_Ico]
    refine ⟨hj.2, ?_⟩
    have : j ≤ J.sup id := Finset.le_sup (f := id) hj.1
    omega
  rw [← Finset.sum_filter]
  calc ∑ j ∈ J.filter (fun j ↦ J₁ ≤ j), ENNReal.ofReal (g j)
      ≤ ∑ j ∈ Finset.Ico J₁ M, ENNReal.ofReal (g j) :=
        Finset.sum_le_sum_of_subset hsub
    _ = ENNReal.ofReal (∑ j ∈ Finset.Ico J₁ M, g j) :=
        (ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hg j)).symm
    _ ≤ ENNReal.ofReal T := ENNReal.ofReal_le_ofReal (hT M)

end T2ii

end FF
