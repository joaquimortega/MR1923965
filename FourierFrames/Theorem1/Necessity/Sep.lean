import FourierFrames.PW.Basic

/-! Helper lemmas on separated sets: summability of `1/(1+λ²)` over a separated set. -/

open Set Filter Topology

noncomputable section

namespace FF

theorem summable_int_one_add_sq : Summable fun n : ℤ ↦ 1 / (1 + (n : ℝ) ^ 2) := by
  have h := (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  refine Summable.of_norm_bounded_eventually h ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le hpos (by linarith)

theorem one_add_sq_floor_le {x : ℝ} {n : ℤ} (hx : (n : ℝ) ≤ x) (hx' : x < n + 1) :
    1 / (1 + x ^ 2) ≤ 3 * (1 / (1 + (n : ℝ) ^ 2)) := by
  have h1 : (n : ℝ) ^ 2 ≤ 2 * x ^ 2 + 2 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg ((n : ℝ) - x), sq_nonneg ((n : ℝ) + x)]
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg x]

/-- At most `N` points of a `δ`-separated set in a half-open interval of length one. -/
theorem card_fiber_le {Λ : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ |a - b|) (n : ℤ) :
    Finite {x : Λ // ⌊(x : ℝ)⌋ = n} ∧ Nat.card {x : Λ // ⌊(x : ℝ)⌋ = n} ≤ ⌊1 / δ⌋₊ + 1 := by
  let g : {x : Λ // ⌊(x : ℝ)⌋ = n} → Fin (⌊1 / δ⌋₊ + 1) := fun x ↦
    ⟨⌊(((x.1 : Λ) : ℝ) - n) / δ⌋₊, by
      have h1 := Int.floor_le (x.1 : ℝ)
      have h2 := Int.lt_floor_add_one (x.1 : ℝ)
      rw [x.2] at h1 h2
      have h3 : (((x.1 : Λ) : ℝ) - n) / δ < 1 / δ := by
        apply div_lt_div_of_pos_right _ hδ; linarith
      have h4 : (0 : ℝ) ≤ (((x.1 : Λ) : ℝ) - n) / δ := div_nonneg (by linarith) hδ.le
      have h5 : 1 / δ < ⌊1 / δ⌋₊ + 1 := Nat.lt_floor_add_one _
      rw [Nat.floor_lt h4]
      push_cast
      linarith⟩
  have hg : Function.Injective g := by
    intro x y hxy
    have hxy' : ⌊(((x.1 : Λ) : ℝ) - n) / δ⌋₊ = ⌊(((y.1 : Λ) : ℝ) - n) / δ⌋₊ :=
      congrArg Fin.val hxy
    have hx1 := Int.floor_le (x.1 : ℝ)
    have hx2 := Int.lt_floor_add_one (x.1 : ℝ)
    have hy1 := Int.floor_le (y.1 : ℝ)
    have hy2 := Int.lt_floor_add_one (y.1 : ℝ)
    rw [x.2] at hx1 hx2
    rw [y.2] at hy1 hy2
    have hax : (0 : ℝ) ≤ (((x.1 : Λ) : ℝ) - n) / δ := div_nonneg (by linarith) hδ.le
    have hay : (0 : ℝ) ≤ (((y.1 : Λ) : ℝ) - n) / δ := div_nonneg (by linarith) hδ.le
    have a1 := Nat.floor_le hax
    have a2 := Nat.lt_floor_add_one ((((x.1 : Λ) : ℝ) - n) / δ)
    have b1 := Nat.floor_le hay
    have b2 := Nat.lt_floor_add_one ((((y.1 : Λ) : ℝ) - n) / δ)
    rw [hxy'] at a1 a2
    have hlt : |(((x.1 : Λ) : ℝ) - n) / δ - (((y.1 : Λ) : ℝ) - n) / δ| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    have : |((x.1 : Λ) : ℝ) - ((y.1 : Λ) : ℝ)| < δ := by
      have : (((x.1 : Λ) : ℝ) - n) / δ - (((y.1 : Λ) : ℝ) - n) / δ =
          (((x.1 : Λ) : ℝ) - ((y.1 : Λ) : ℝ)) / δ := by ring
      rw [this, abs_div, abs_of_pos hδ, div_lt_one hδ] at hlt
      exact hlt
    by_contra hne
    have hne' : ((x.1 : Λ) : ℝ) ≠ ((y.1 : Λ) : ℝ) := by
      intro h
      exact hne (Subtype.ext (Subtype.ext h))
    exact absurd (hsep _ x.1.2 _ y.1.2 hne') (not_le.2 this)
  have : Finite {x : Λ // ⌊(x : ℝ)⌋ = n} := Finite.of_injective g hg
  refine ⟨this, ?_⟩
  simpa using Nat.card_le_card_of_injective g hg

theorem IsSeparated.summable_inv_one_add_sq' {Λ : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ |a - b|) :
    Summable fun x : Λ ↦ 1 / (1 + (x : ℝ) ^ 2) := by
  set N : ℕ := ⌊1 / δ⌋₊ + 1 with hN
  let e : Λ ≃ Σ n : ℤ, {x : Λ // ⌊(x : ℝ)⌋ = n} :=
    (Equiv.sigmaFiberEquiv (fun x : Λ ↦ ⌊(x : ℝ)⌋)).symm
  rw [← e.symm.summable_iff]
  change Summable fun p : (Σ n : ℤ, {x : Λ // ⌊(x : ℝ)⌋ = n}) ↦
    (fun x : Λ ↦ 1 / (1 + (x : ℝ) ^ 2)) (e.symm p)
  have hnn : ∀ p : (Σ n : ℤ, {x : Λ // ⌊(x : ℝ)⌋ = n}),
      0 ≤ (fun x : Λ ↦ 1 / (1 + (x : ℝ) ^ 2)) (e.symm p) := fun p ↦ by positivity
  rw [summable_sigma_of_nonneg hnn]
  have hfib : ∀ n : ℤ, ∀ y : {x : Λ // ⌊(x : ℝ)⌋ = n},
      (fun x : Λ ↦ 1 / (1 + (x : ℝ) ^ 2)) (e.symm ⟨n, y⟩) ≤ 3 * (1 / (1 + (n : ℝ) ^ 2)) := by
    intro n y
    have h1 := Int.floor_le (y.1 : ℝ)
    have h2 := Int.lt_floor_add_one (y.1 : ℝ)
    rw [y.2] at h1 h2
    have : (e.symm ⟨n, y⟩ : Λ) = y.1 := by simp [e]
    simp only [this]
    exact one_add_sq_floor_le h1 h2
  refine ⟨fun n ↦ ?_, ?_⟩
  · have := (card_fiber_le hδ hsep n).1
    exact (Summable.of_finite)
  · refine Summable.of_nonneg_of_le (fun n ↦ tsum_nonneg fun y ↦ hnn ⟨n, y⟩)
      (fun n ↦ ?_) ((summable_int_one_add_sq.mul_left (3 * (N : ℝ))))
    obtain ⟨hfin, hcard⟩ := card_fiber_le hδ hsep n
    have := hfin
    let := Fintype.ofFinite {x : Λ // ⌊(x : ℝ)⌋ = n}
    rw [tsum_fintype]
    calc ∑ y : {x : Λ // ⌊(x : ℝ)⌋ = n}, (fun x : Λ ↦ 1 / (1 + (x : ℝ) ^ 2)) (e.symm ⟨n, y⟩)
        ≤ ∑ _y : {x : Λ // ⌊(x : ℝ)⌋ = n}, 3 * (1 / (1 + (n : ℝ) ^ 2)) :=
          Finset.sum_le_sum fun y _ ↦ hfib n y
      _ = (Fintype.card {x : Λ // ⌊(x : ℝ)⌋ = n} : ℝ) * (3 * (1 / (1 + (n : ℝ) ^ 2))) := by
          simp
      _ ≤ (N : ℝ) * (3 * (1 / (1 + (n : ℝ) ^ 2))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : Fintype.card {x : Λ // ⌊(x : ℝ)⌋ = n} ≤ N := by
            rw [Fintype.card_eq_nat_card]; exact hcard
          exact_mod_cast this
      _ = 3 * N * (1 / (1 + (n : ℝ) ^ 2)) := by ring

end FF
