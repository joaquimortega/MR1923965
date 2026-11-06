import OrtegaCerdaSeip.Lemma3.Main

/-!
# Gaps of `Γ` (aux file for `Construction.lean`, M07 §2.2)

Proofs of the statements `tendsto_multBary_sub_multPt`, … of `Construction.lean`.
-/

open MeasureTheory Metric Set Complex Filter Topology

noncomputable section

namespace FF

namespace Gaps

variable {m : ℝ → ℝ} {a b : ℝ}

/-- From `m → 1`: `|m t - 1| ≤ ε` for `|t| ≥ X`. -/
theorem exists_abs_sub_one_le (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ t : ℝ, X ≤ |t| → |m t - 1| ≤ ε := by
  have h := (Metric.tendsto_nhds.1 hlim) ε hε
  rw [cocompact_eq_atBot_atTop, eventually_sup, eventually_atBot, eventually_atTop] at h
  obtain ⟨⟨X₁, h1⟩, ⟨X₂, h2⟩⟩ := h
  refine ⟨max (-X₁) X₂, fun t ht ↦ ?_⟩
  rcases le_abs'.1 ht with h | h
  · have := h1 t (by linarith [le_max_left (-X₁) X₂])
    exact (Real.dist_eq _ _ ▸ this).le
  · have := h2 t (by linarith [le_max_right (-X₁) X₂])
    exact (Real.dist_eq _ _ ▸ this).le

theorem multPt_nonneg_of_nonneg (hw : OCS.IsMultWeight m a b) {j : ℤ} (hj : 0 ≤ j) :
    0 ≤ OCS.multPt m j := by
  by_contra h
  push Not at h
  have := (OCS.strictMono_multPrim hw) h
  rw [OCS.multPrim_zero, OCS.multPrim_multPt hw] at this
  have : (j : ℝ) < 0 := this
  have : (0 : ℝ) ≤ j := by exact_mod_cast hj
  linarith

theorem multPt_nonpos_of_nonpos (hw : OCS.IsMultWeight m a b) {j : ℤ} (hj : j ≤ 0) :
    OCS.multPt m j ≤ 0 := by
  by_contra h
  push Not at h
  have := (OCS.strictMono_multPrim hw) h
  rw [OCS.multPrim_zero, OCS.multPrim_multPt hw] at this
  have : (0 : ℝ) < j := this
  have : (j : ℝ) ≤ 0 := by exact_mod_cast hj
  linarith

/-- On `I_j`, `|m - 1| ≤ ε` once `|j|` is large. -/
theorem exists_index_near (hw : OCS.IsMultWeight m a b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j : ℤ, J ≤ |j| → ∀ t ∈ Icc (OCS.multPt m j) (OCS.multPt m (j + 1)),
      |m t - 1| ≤ ε := by
  obtain ⟨X, hX⟩ := exists_abs_sub_one_le hlim hε
  have hb := hw.b_pos
  obtain ⟨J, hJ⟩ := exists_nat_gt (b * (|X| + 1) + 1)
  refine ⟨J, fun j hj t ht ↦ hX t ?_⟩
  have hjJ : (J : ℝ) ≤ |(j : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast hj
  rcases le_or_gt 0 j with h0 | h0
  · have h1 := OCS.abs_multPt_ge hw j
    have h2 := multPt_nonneg_of_nonneg hw h0
    rw [abs_of_nonneg h2] at h1
    have : X ≤ OCS.multPt m j := by
      have : b * (|X| + 1) ≤ |(j : ℝ)| := by linarith
      rw [div_le_iff₀ hb] at h1
      nlinarith [le_abs_self X, abs_nonneg X]
    rw [abs_of_nonneg (h2.trans ht.1)]
    linarith [ht.1]
  · have h1 := OCS.abs_multPt_ge hw (j + 1)
    have h2 := multPt_nonpos_of_nonpos hw (show j + 1 ≤ 0 by omega)
    rw [abs_of_nonpos h2] at h1
    have hj1 : (J : ℝ) - 1 ≤ |((j + 1 : ℤ) : ℝ)| := by
      have : |(j : ℝ)| ≤ |((j + 1 : ℤ) : ℝ)| + 1 := by
        push_cast
        calc |(j : ℝ)| = |((j : ℝ) + 1) - 1| := by ring_nf
          _ ≤ |(j : ℝ) + 1| + |(1 : ℝ)| := abs_sub _ _
          _ = _ := by simp
      linarith
    have : X ≤ -OCS.multPt m (j + 1) := by
      rw [div_le_iff₀ hb] at h1
      nlinarith [le_abs_self X, abs_nonneg X]
    have h3 : t ≤ OCS.multPt m (j + 1) := ht.2
    rw [abs_of_nonpos (h3.trans h2)]
    linarith

/-- Quantitative form: `|I_j| ≈ 1` and `γ_j - x_j ≈ 1/2`. -/
theorem near_of_eps (hw : OCS.IsMultWeight m a b) (j : ℤ) {ε : ℝ} (hε : 0 ≤ ε)
    (hj : ∀ t ∈ Icc (OCS.multPt m j) (OCS.multPt m (j + 1)), |m t - 1| ≤ ε) :
    |(OCS.multPt m (j + 1) - OCS.multPt m j) - 1| ≤ ε / a ∧
    |OCS.multBary m j - OCS.multPt m j - 1 / 2| ≤
      (1 / a ^ 2 + (1 + 1 / a) / (2 * a)) * ε := by
  have ha := hw.pos
  set x₀ := OCS.multPt m j with hx₀
  set x₁ := OCS.multPt m (j + 1) with hx₁
  have hlt : x₀ < x₁ := OCS.multPt_lt_succ hw j
  have hL := OCS.multPt_succ_sub_bounds hw j
  set L := x₁ - x₀ with hLdef
  have hL0 : 0 < L := sub_pos.2 hlt
  have hLa : L ≤ 1 / a := hL.2
  have habs : |x₁ - x₀| = L := abs_of_pos hL0
  have hmint : IntervalIntegrable m volume x₀ x₁ := hw.intervalIntegrable _ _
  have hi1 : ∫ t in x₀..x₁, (m t - 1) = 1 - L := by
    rw [intervalIntegral.integral_sub hmint intervalIntegrable_const, OCS.integral_multPt hw]
    simp [hLdef]
  have hb1 : |∫ t in x₀..x₁, (m t - 1)| ≤ ε * L := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₀) (b := x₁)
      (f := fun t ↦ m t - 1) (C := ε) (fun t ht ↦ by
        rw [Set.uIoc_of_le hlt.le] at ht
        exact hj t ⟨ht.1.le, ht.2⟩)
    rw [habs] at this
    simpa [Real.norm_eq_abs, mul_comm] using this
  have hLm : |L - 1| ≤ ε / a := by
    rw [hi1] at hb1
    have : |L - 1| ≤ ε * L := by simpa [abs_sub_comm] using hb1
    calc |L - 1| ≤ ε * L := this
      _ ≤ ε * (1 / a) := by gcongr
      _ = ε / a := by ring
  refine ⟨hLm, ?_⟩
  -- barycentre
  have hbar := OCS.multBary_sub_multPt hw j
  have hid : IntervalIntegrable (fun t : ℝ ↦ (t - x₀) * m t) volume x₀ x₁ :=
    hw.intervalIntegrable_mul ((continuous_id.sub continuous_const).intervalIntegrable _ _)
  have hid1 : IntervalIntegrable (fun t : ℝ ↦ (t - x₀)) volume x₀ x₁ :=
    (continuous_id.sub continuous_const).intervalIntegrable _ _
  have hI1 : ∫ t in x₀..x₁, (t - x₀) = L ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id intervalIntegrable_const]
    simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul, hLdef]
    ring
  have hb2 : |∫ t in x₀..x₁, ((t - x₀) * m t - (t - x₀))| ≤ (L * ε) * L := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₀) (b := x₁)
      (f := fun t ↦ (t - x₀) * m t - (t - x₀)) (C := L * ε) (fun t ht ↦ by
        rw [Set.uIoc_of_le hlt.le] at ht
        have h1 := hj t ⟨ht.1.le, ht.2⟩
        have : (t - x₀) * m t - (t - x₀) = (t - x₀) * (m t - 1) := by ring
        rw [this, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [ht.1])]
        exact mul_le_mul (by linarith [ht.2]) h1 (abs_nonneg _) hL0.le)
    rw [habs] at this
    simpa [Real.norm_eq_abs, mul_comm] using this
  rw [intervalIntegral.integral_sub hid hid1, hI1] at hb2
  rw [hbar]
  have hLε : L ^ 2 * ε ≤ ε / a ^ 2 := by
    have : L ^ 2 ≤ (1 / a) ^ 2 := pow_le_pow_left₀ hL0.le hLa 2
    calc L ^ 2 * ε ≤ (1 / a) ^ 2 * ε := by gcongr
      _ = ε / a ^ 2 := by ring
  have hLsq : |L ^ 2 / 2 - 1 / 2| ≤ (1 + 1 / a) / 2 * (ε / a) := by
    have : L ^ 2 / 2 - 1 / 2 = (L - 1) * (L + 1) / 2 := by ring
    rw [this, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [abs_of_pos (by linarith : 0 < L + 1)]
    have : L + 1 ≤ 1 + 1 / a := by linarith
    calc |L - 1| * (L + 1) / 2 ≤ (ε / a) * (1 + 1 / a) / 2 := by gcongr
      _ = _ := by ring
  have key : |(∫ t in x₀..x₁, (t - x₀) * m t) - 1 / 2| ≤
      |(∫ t in x₀..x₁, (t - x₀) * m t) - L ^ 2 / 2| + |L ^ 2 / 2 - 1 / 2| := by
    have := abs_add_le ((∫ t in x₀..x₁, (t - x₀) * m t) - L ^ 2 / 2) (L ^ 2 / 2 - 1 / 2)
    simpa using this
  have e1 : |(∫ t in x₀..x₁, (t - x₀) * m t) - L ^ 2 / 2| ≤ ε / a ^ 2 := by
    refine le_trans ?_ hLε
    nlinarith [hb2]
  refine key.trans ?_
  have : (1 + 1 / a) / 2 * (ε / a) = (1 + 1 / a) / (2 * a) * ε := by field_simp
  have e2 : ε / a ^ 2 = 1 / a ^ 2 * ε := by ring
  rw [add_mul]
  linarith [hLsq, e1, e2, this]

theorem eventually_cofinite_of_abs {P : ℤ → Prop} (J : ℕ) (h : ∀ j : ℤ, J ≤ |j| → P j) :
    ∀ᶠ j in cofinite, P j := by
  rw [eventually_cofinite]
  refine (Set.finite_Icc (-(J : ℤ)) J).subset fun j hj ↦ ?_
  by_contra hc
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hc
  exact hj (h j (by rw [Int.abs_eq_natAbs]; rcases hc with h | h <;> omega))

theorem exists_index_of_cofinite {P : ℤ → Prop} (h : ∀ᶠ j in cofinite, P j) :
    ∃ J : ℕ, ∀ j : ℤ, J ≤ |j| → P j := by
  rw [eventually_cofinite] at h
  obtain ⟨R, hR⟩ := (h.image Int.natAbs).bddAbove
  refine ⟨R + 1, fun j hj ↦ ?_⟩
  by_contra hc
  have := hR ⟨j, hc, rfl⟩
  rw [Int.abs_eq_natAbs] at hj
  omega

/-- Choice of the `ε`-parameters. -/
theorem exists_index_delta (hw : OCS.IsMultWeight m a b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ J : ℕ, ∀ j : ℤ, J ≤ |j| → (∀ t ∈ Icc (OCS.multPt m j) (OCS.multPt m (j + 1)),
        |m t - 1| ≤ δ) ∧ |(OCS.multPt m (j + 1) - OCS.multPt m j) - 1| ≤ δ ∧
      |OCS.multBary m j - OCS.multPt m j - 1 / 2| ≤ δ := by
  have ha := hw.pos
  set K := 1 / a ^ 2 + (1 + 1 / a) / (2 * a) with hK
  have hK0 : 0 < K := by positivity
  set ε := δ / (1 / a + K + 1) with hε
  have hden : 0 < 1 / a + K + 1 := by positivity
  have hε0 : 0 < ε := div_pos hδ hden
  obtain ⟨J, hJ⟩ := exists_index_near hw hlim hε0
  refine ⟨J, fun j hj ↦ ?_⟩
  have h1 := hJ j hj
  obtain ⟨h2, h3⟩ := near_of_eps hw j hε0.le h1
  have hεδ : ε * (1 / a + K + 1) = δ := by rw [hε]; field_simp
  have : 0 < 1 / a := by positivity
  refine ⟨fun t ht ↦ (h1 t ht).trans ?_, h2.trans ?_, h3.trans ?_⟩
  · nlinarith
  · have : ε / a = ε * (1 / a) := by ring
    nlinarith
  · nlinarith

theorem tendsto_multBary_sub_multPt (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    Tendsto (fun j : ℤ ↦ OCS.multBary m j - OCS.multPt m j) cofinite (𝓝 (1 / 2)) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨J, hJ⟩ := exists_index_delta hw hlim (half_pos hδ)
  refine eventually_cofinite_of_abs J fun j hj ↦ ?_
  have := (hJ j hj).2.2
  rw [Real.dist_eq]
  linarith [abs_sub_comm (OCS.multBary m j - OCS.multPt m j) (1 / 2), this]

theorem tendsto_multPt_succ_sub (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    Tendsto (fun j : ℤ ↦ OCS.multPt m (j + 1) - OCS.multPt m j) cofinite (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨J, hJ⟩ := exists_index_delta hw hlim (half_pos hδ)
  refine eventually_cofinite_of_abs J fun j hj ↦ ?_
  have := (hJ j hj).2.1
  rw [Real.dist_eq]
  linarith

theorem tendsto_multBary_succ_sub (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    Tendsto (fun j : ℤ ↦ OCS.multBary m (j + 1) - OCS.multBary m j) cofinite (𝓝 1) := by
  have h1 := (tendsto_multBary_sub_multPt hw hlim).comp (add_left_injective (1 : ℤ)).tendsto_cofinite
  have h2 := tendsto_multPt_succ_sub hw hlim
  have h3 := tendsto_multBary_sub_multPt hw hlim
  have := (h1.add h2).sub h3
  rw [show (1 : ℝ) = 1 / 2 + 1 - 1 / 2 by norm_num]
  refine this.congr fun j ↦ ?_
  simp only [Function.comp]
  ring

theorem tendsto_multPrim_multBary (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    Tendsto (fun j : ℤ ↦ OCS.multPrim m (OCS.multBary m j) - (j + 1 / 2)) cofinite (𝓝 0) := by
  have ha := hw.pos
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hδ' : 0 < min (δ / 4) (a * δ / 4) := lt_min (by positivity) (by positivity)
  obtain ⟨J, hJ⟩ := exists_index_delta hw hlim hδ'
  refine eventually_cofinite_of_abs J fun j hj ↦ ?_
  obtain ⟨h1, h2, h3⟩ := hJ j hj
  set η := min (δ / 4) (a * δ / 4) with hη
  have hη1 : η ≤ δ / 4 := min_le_left _ _
  have hη2 : η ≤ a * δ / 4 := min_le_right _ _
  have hmem := OCS.multBary_mem hw j
  have hlt := OCS.multPt_lt_succ hw j
  have hapos : 0 < a / (2 * b ^ 2) := by have := hw.b_pos; positivity
  have hx0 : OCS.multPt m j ≤ OCS.multBary m j := by linarith [hmem.1]
  have hx1 : OCS.multBary m j ≤ OCS.multPt m (j + 1) := by linarith [hmem.2]
  have hLa := (OCS.multPt_succ_sub_bounds hw j).2
  have hd : OCS.multBary m j - OCS.multPt m j ≤ 1 / a := by linarith
  have hint : OCS.multPrim m (OCS.multBary m j) - j =
      (OCS.multBary m j - OCS.multPt m j) + ∫ t in OCS.multPt m j..OCS.multBary m j, (m t - 1) := by
    have e := OCS.multPrim_sub_eq hw (OCS.multPt m j) (OCS.multBary m j)
    rw [OCS.multPrim_multPt hw] at e
    rw [intervalIntegral.integral_sub (hw.intervalIntegrable _ _) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    linarith
  have hb : |∫ t in OCS.multPt m j..OCS.multBary m j, (m t - 1)| ≤
      η * (OCS.multBary m j - OCS.multPt m j) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := OCS.multPt m j)
      (b := OCS.multBary m j) (f := fun t ↦ m t - 1) (C := η) (fun t ht ↦ by
        rw [Set.uIoc_of_le hx0] at ht
        exact h1 t ⟨ht.1.le, ht.2.trans hx1⟩)
    rw [abs_of_nonneg (sub_nonneg.2 hx0)] at this
    simpa [Real.norm_eq_abs, mul_comm] using this
  have hbd : η * (OCS.multBary m j - OCS.multPt m j) ≤ δ / 4 := by
    calc _ ≤ η * (1 / a) := by gcongr
      _ ≤ (a * δ / 4) * (1 / a) := by gcongr
      _ = δ / 4 := by field_simp
  rw [Real.dist_eq, sub_zero]
  have : OCS.multPrim m (OCS.multBary m j) - (j + 1 / 2) =
      ((OCS.multBary m j - OCS.multPt m j) - 1 / 2) +
        ∫ t in OCS.multPt m j..OCS.multBary m j, (m t - 1) := by linarith
  rw [this]
  calc _ ≤ |(OCS.multBary m j - OCS.multPt m j) - 1 / 2| +
        |∫ t in OCS.multPt m j..OCS.multBary m j, (m t - 1)| := abs_add_le _ _
    _ < δ := by linarith

theorem tendsto_multPrim_sub (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) (T : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ |x| → ∀ τ : ℝ, |τ| ≤ T →
      |OCS.multPrim m (x + τ) - OCS.multPrim m x - τ| ≤ ε := by
  intro ε hε
  have hT : 0 < |T| + 1 := by positivity
  obtain ⟨X₀, hX₀⟩ := exists_abs_sub_one_le hlim (div_pos hε hT)
  refine ⟨X₀ + |T|, fun x hx τ hτ ↦ ?_⟩
  have e := OCS.multPrim_sub_eq hw x (x + τ)
  have hint : OCS.multPrim m (x + τ) - OCS.multPrim m x - τ = ∫ t in x..x + τ, (m t - 1) := by
    rw [intervalIntegral.integral_sub (hw.intervalIntegrable _ _) intervalIntegrable_const, ← e]
    simp
  rw [hint]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x + τ)
    (f := fun t ↦ m t - 1) (C := ε / (|T| + 1)) (fun t ht ↦ by
      have h1 : |t - x| ≤ |τ| := by
        rcases le_total τ 0 with h | h
        · rw [Set.uIoc_of_ge (by linarith)] at ht
          rw [abs_of_nonpos h]
          rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        · rw [Set.uIoc_of_le (by linarith)] at ht
          rw [abs_of_nonneg h]
          rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      refine hX₀ t ?_
      have h2 := abs_sub_abs_le_abs_sub x t
      rw [abs_sub_comm x t] at h2
      have h3 : |τ| ≤ |T| := hτ.trans (le_abs_self T)
      linarith)
  rw [Real.norm_eq_abs, add_sub_cancel_left] at this
  refine this.trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ hT]
  have : |τ| ≤ |T| := hτ.trans (le_abs_self T)
  nlinarith [abs_nonneg τ]

theorem exists_gap_index (hw : OCS.IsMultWeight m a b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    ∃ N : ℕ, ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j :=
  exists_index_of_cofinite
    ((tendsto_multBary_succ_sub hw hlim).eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))

theorem exists_gap_index_strong (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    ∃ N : ℕ, ∀ j : ℤ, N ≤ |j| → 3 / 4 < OCS.multBary m (j + 1) - OCS.multBary m j :=
  exists_index_of_cofinite
    ((tendsto_multBary_succ_sub hw hlim).eventually (lt_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1)))

end Gaps

end FF
