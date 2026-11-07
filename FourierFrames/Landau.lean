import FourierFrames.Corollary1

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF

/-!
# M05 — Landau's inequality from John–Nirenberg and Pavlov (p. 799)

See `blueprint/M05_Landau.md`.
-/

/-! ## Counting -/

/-- A separated set meets bounded intervals in finite sets. -/
theorem sep_count_aux {Γ : Set ℝ} {q : ℝ} (hq : 0 < q)
    (hΓ : ∀ x ∈ Γ, ∀ y ∈ Γ, x ≠ y → q ≤ |x - y|) {a b : ℝ} (hab : a ≤ b) :
    (Γ ∩ Ioc a b).Finite ∧ ((Γ ∩ Ioc a b).ncard : ℝ) ≤ (b - a) / q + 1 := by
  set S := Γ ∩ Ioc a b with hS
  set f : ℝ → ℤ := fun x ↦ ⌊(x - a) / q⌋ with hf
  set N : ℤ := ⌊(b - a) / q⌋ with hN
  have hinj : Set.InjOn f S := by
    have key : ∀ x ∈ S, ∀ y ∈ S, x < y → f x < f y := by
      intro x hx y hy hxy
      have h := hΓ x hx.1 y hy.1 hxy.ne
      rw [abs_sub_comm, abs_of_pos (by linarith)] at h
      have h1 : (x - a) / q + 1 ≤ (y - a) / q := by
        rw [← sub_nonneg]
        have : (y - a) / q - ((x - a) / q + 1) = (y - x - q) / q := by field_simp; ring
        rw [this]; exact div_nonneg (by linarith) hq.le
      have h3 : ⌊(x - a) / q⌋ + 1 ≤ ⌊(y - a) / q⌋ := by
        apply Int.le_floor.mpr
        push_cast
        linarith [Int.floor_le ((x - a) / q)]
      simp only [hf]; omega
    intro x hx y hy hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (key x hx y hy h).ne hxy
    · exact (key y hy x hx h).ne hxy.symm
  have hmaps : f '' S ⊆ ↑(Finset.Icc (0 : ℤ) N) := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [Finset.coe_Icc, Set.mem_Icc, hf, hN]
    constructor
    · apply Int.floor_nonneg.mpr
      exact div_nonneg (by linarith [hx.2.1]) hq.le
    · apply Int.floor_le_floor
      exact div_le_div_of_nonneg_right (by linarith [hx.2.2]) hq.le
  have hfin : (f '' S).Finite := (Finset.finite_toSet _).subset hmaps
  refine ⟨Set.Finite.of_finite_image hfin hinj, ?_⟩
  have h1 : S.ncard = (f '' S).ncard := hinj.ncard_image.symm
  have h2 : (f '' S).ncard ≤ (Finset.Icc (0 : ℤ) N : Set ℤ).ncard :=
    Set.ncard_le_ncard hmaps (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Int.card_Icc] at h2
  have hN0 : 0 ≤ N := Int.floor_nonneg.mpr (div_nonneg (by linarith) hq.le)
  have h3 : ((N + 1 - 0).toNat : ℝ) = (N : ℝ) + 1 := by
    have : ((N + 1 - 0).toNat : ℤ) = N + 1 := by omega
    have h' : (((N + 1 - 0).toNat : ℤ) : ℝ) = ((N + 1 : ℤ) : ℝ) := by rw [this]
    push_cast at h' ⊢; linarith
  have h4 : (S.ncard : ℝ) ≤ ((N + 1 - 0).toNat : ℝ) := by rw [h1]; exact_mod_cast h2
  have h5 : (N : ℝ) ≤ (b - a) / q := Int.floor_le _
  linarith

theorem IsSeparated.finite_inter_Ioc {Γ : Set ℝ} (hΓ : IsSeparated Γ) (a b : ℝ) :
    (Γ ∩ Ioc a b).Finite := by
  obtain ⟨δ, hδ, hsep⟩ := hΓ
  rcases le_or_gt a b with hab | hab
  · exact (sep_count_aux hδ hsep hab).1
  · rw [Set.Ioc_eq_empty (not_lt.mpr hab.le)]; simp

/-- `n_Γ(b) - n_Γ(a) = #(Γ ∩ (a, b])` for `a ≤ b`, when `Γ ∩ (a, b]` is finite for all `a, b`. -/
theorem ncard_Ioc_add {Γ : Set ℝ} (hfin : ∀ a b : ℝ, (Γ ∩ Ioc a b).Finite) {a b c : ℝ}
    (h1 : a ≤ b) (h2 : b ≤ c) :
    (Γ ∩ Ioc a c).ncard = (Γ ∩ Ioc a b).ncard + (Γ ∩ Ioc b c).ncard := by
  rw [← Set.ncard_union_eq _ (hfin a b) (hfin b c), ← Set.inter_union_distrib_left,
    Set.Ioc_union_Ioc_eq_Ioc h1 h2]
  rw [Set.disjoint_left]
  rintro x ⟨-, hx⟩ ⟨-, hy⟩
  exact absurd hx.2 (not_le.mpr hy.1)

theorem countFn_sub {Γ : Set ℝ} (hfin : ∀ a b : ℝ, (Γ ∩ Ioc a b).Finite) {a b : ℝ}
    (hab : a ≤ b) : countFn Γ b - countFn Γ a = ((Γ ∩ Ioc a b).ncard : ℝ) := by
  unfold countFn
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans hab
    simp only [ha, hb, ite_true]
    have := ncard_Ioc_add hfin ha hab
    rw [this]; push_cast; ring
  · by_cases hb : 0 ≤ b
    · simp only [ha, hb, ite_true, ite_false]
      have := ncard_Ioc_add hfin (not_le.mp ha).le hb
      rw [this]; push_cast; ring
    · simp only [ha, hb, ite_false]
      have := ncard_Ioc_add hfin hab (not_le.mp hb).le
      rw [this]; push_cast; ring

/-- A `q`-separated set has at most `(b - a)/q + 1` points in `(a, b]`. -/
theorem ncard_inter_Ioc_le {Γ : Set ℝ} {q : ℝ} (hq : 0 < q)
    (hΓ : ∀ x ∈ Γ, ∀ y ∈ Γ, x ≠ y → q ≤ |x - y|) {a b : ℝ} (hab : a ≤ b) :
    ((Γ ∩ Ioc a b).ncard : ℝ) ≤ (b - a) / q + 1 :=
  (sep_count_aux hq hΓ hab).2

/-- `n_Λ(b) - n_Λ(a) ≥ n_Γ(b) - n_Γ(a) - 1` when every `[γ_k, γ_{k+1})` contains a point of `Λ`
(p. 799, first display). -/
theorem ncard_Ioc_ge {Λ : Set ℝ} {γ : ℤ → ℝ} (hγ : StrictMono γ)
    (hΛγ : ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1))
    (hfinΛ : ∀ a b : ℝ, (Λ ∩ Ioc a b).Finite) (hfinΓ : ∀ a b : ℝ, (Set.range γ ∩ Ioc a b).Finite)
    (a b : ℝ) :
    ((Set.range γ ∩ Ioc a b).ncard : ℝ) - 1 ≤ ((Λ ∩ Ioc a b).ncard : ℝ) := by
  classical
  choose x hxΛ hx1 hx2 using hΛγ
  set J : Set ℤ := {k | γ k ∈ Ioc a b} with hJ
  have hSJ : Set.range γ ∩ Ioc a b = γ '' J := by
    ext y
    constructor
    · rintro ⟨⟨k, rfl⟩, hy⟩; exact ⟨k, hy, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, rfl⟩, hk⟩
  have hJfin : J.Finite := by
    have := (hfinΓ a b).preimage hγ.injective.injOn
    convert this using 1
    ext k; simp [hJ]
  have hcard : (Set.range γ ∩ Ioc a b).ncard = J.ncard := by
    rw [hSJ]; exact Set.ncard_image_of_injective J hγ.injective
  rw [hcard]
  have key : J.ncard ≤ (Λ ∩ Ioc a b).ncard + 1 := by
    rcases J.eq_empty_or_nonempty with h | hne
    · rw [h]; simp
    · obtain ⟨j₂, hj₂, hmax⟩ : ∃ j₂ ∈ J, ∀ j ∈ J, j ≤ j₂ := by
        refine ⟨hJfin.toFinset.max' (by simpa using hne), ?_, ?_⟩
        · have := Finset.max'_mem hJfin.toFinset (by simpa using hne)
          simpa using this
        · intro j hj
          exact Finset.le_max' _ _ (by simpa using hj)
      have h1 := Set.ncard_sdiff_singleton_add_one hj₂ hJfin
      have h2 : (J \ {j₂}).ncard ≤ (Λ ∩ Ioc a b).ncard := by
        apply Set.ncard_le_ncard_of_injOn x _ _ (hfinΛ a b)
        · intro j hj
          have hjJ : j ∈ J := hj.1
          have hne2 : j ≠ j₂ := hj.2
          have hle : j + 1 ≤ j₂ := by have := hmax j hjJ; omega
          have hjb : γ (j + 1) ≤ b := by
            have := (hγ.monotone hle)
            exact this.trans hj₂.2
          refine ⟨hxΛ j, ?_, ?_⟩
          · exact lt_of_lt_of_le hjJ.1 (hx1 j)
          · exact (hx2 j).le.trans hjb
        · intro j hj j' hj' hjj'
          by_contra hne3
          rcases lt_or_gt_of_ne hne3 with h | h
          · have : γ (j + 1) ≤ γ j' := hγ.monotone (by omega)
            have := hx2 j; have := hx1 j'
            linarith
          · have : γ (j' + 1) ≤ γ j := hγ.monotone (by omega)
            have := hx2 j'; have := hx1 j
            linarith
      omega
  have : (J.ncard : ℝ) ≤ (Λ ∩ Ioc a b).ncard + 1 := by exact_mod_cast key
  linarith

/-! ## The oscillation bound from John–Nirenberg -/

/-- **Core of the Claim.** If `h ∈ BMO` has the local growth bound
`|h(b) - h(a)| ≤ K (b - a) + D` (`a ≤ b`), then `|h(b) - h(a)| ≤ A log⁺(b - a) + B`. -/
theorem osc_bound_of_JN (hJN : JohnNirenberg) {h : ℝ → ℝ} (hbmo : MemBMO h) {K D : ℝ}
    (hK : 0 ≤ K) (hloc : ∀ a b : ℝ, a ≤ b → |h b - h a| ≤ K * (b - a) + D) :
    ∃ A B : ℝ, ∀ a b : ℝ, a < b → |h b - h a| ≤ A * Real.posLog (b - a) + B := by
  obtain ⟨C, c, hC, hc, hJ⟩ := hJN
  obtain ⟨hli, M₀, hM₀⟩ := hbmo
  set M : ℝ := max M₀ 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMo : ∀ a b : ℝ, a < b → meanOsc h a b ≤ M := fun a b hab ↦
    (hM₀ a b hab).trans (le_max_left _ _)
  set A₁ : ℝ := 2 * M / c with hA₁
  have hA₁pos : 0 < A₁ := by positivity
  set L₀ : ℝ := max 2 (C + 1) with hL₀
  have hL₀2 : 2 ≤ L₀ := le_max_left _ _
  have hL₀C : C + 1 ≤ L₀ := le_max_right _ _
  refine ⟨2 * A₁, max (2 * (K + D)) (K * L₀ + D), fun a b hab ↦ ?_⟩
  have hpl : 0 ≤ Real.posLog (b - a) := Real.posLog_nonneg
  have hA0 : 0 ≤ 2 * A₁ * Real.posLog (b - a) := by positivity
  by_cases hL : b - a < L₀
  · have h1 := hloc a b hab.le
    have h2 : K * (b - a) ≤ K * L₀ := mul_le_mul_of_nonneg_left hL.le hK
    have h3 := le_max_right (2 * (K + D)) (K * L₀ + D)
    linarith
  push Not at hL
  set L := b - a with hLdef
  have hL2 : 2 ≤ L := hL₀2.trans hL
  have hlogpos : 0 < Real.log L := Real.log_pos (by linarith)
  set s : ℝ := A₁ * Real.log L with hs
  have hspos : 0 < s := by positivity
  set m : ℝ := intervalMean h a b with hm
  set J : Set ℝ := {t ∈ Icc a b | s ≤ |h t - m|} with hJdef
  have hvol : volume J < 1 := by
    have h1 := hJ h hli M hM hMo a b hab s hspos
    have h2 : c * s / M = 2 * Real.log L := by
      simp only [hs, hA₁]; field_simp
    have h3 : Real.exp (-(c * s / M)) = (L ^ 2)⁻¹ := by
      rw [h2, Real.exp_neg, two_mul, Real.exp_add, Real.exp_log (by linarith)]
      congr 1; ring
    have h4 : C * Real.exp (-(c * s / M)) * (b - a) < 1 := by
      rw [h3]
      have hLp : 0 < L := by linarith
      have : C * (L ^ 2)⁻¹ * L = C / L := by field_simp
      rw [this, div_lt_one hLp]; linarith
    exact lt_of_le_of_lt h1 (by rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr h4)
  have hnear : ∀ t ∈ Icc a b, ∃ t' ∈ Icc a b, t' ∉ J ∧ |t - t'| ≤ 1 := by
    intro t ht
    have key : ∀ W : Set ℝ, W ⊆ Icc a b → volume W = 1 → (∃ u v, W = Icc u v ∧ ∀ t' ∈ W, |t - t'| ≤ 1) →
        ∃ t' ∈ Icc a b, t' ∉ J ∧ |t - t'| ≤ 1 := by
      intro W hW hWv ⟨u, v, hWe, hnb⟩
      by_contra hcon
      push Not at hcon
      have : W ⊆ J := by
        intro t' ht'
        by_contra hnj
        exact absurd (hnb t' ht') (not_le.mpr (hcon t' (hW ht') hnj))
      have := measure_mono (μ := volume) this
      rw [hWv] at this
      exact absurd (lt_of_lt_of_le hvol this) (lt_irrefl _)
    by_cases hb1 : t + 1 ≤ b
    · apply key (Icc t (t + 1))
      · exact Icc_subset_Icc ht.1 hb1
      · rw [Real.volume_Icc]; simp
      · refine ⟨t, t + 1, rfl, fun t' ht' ↦ ?_⟩
        rw [abs_le]; constructor <;> linarith [ht'.1, ht'.2]
    · apply key (Icc (t - 1) t)
      · exact Icc_subset_Icc (by linarith [ht.2]) ht.2
      · rw [Real.volume_Icc]; simp
      · refine ⟨t - 1, t, rfl, fun t' ht' ↦ ?_⟩
        rw [abs_le]; constructor <;> linarith [ht'.1, ht'.2]
  have hclose : ∀ u v : ℝ, |u - v| ≤ 1 → |h u - h v| ≤ K + D := by
    intro u v huv
    rcases le_total v u with h1 | h1
    · have := hloc v u h1
      rw [abs_of_nonneg (sub_nonneg.mpr h1)] at huv
      have : K * (u - v) ≤ K := by nlinarith
      linarith [abs_of_nonneg (sub_nonneg.mpr h1)]
    · have := hloc u v h1
      rw [abs_sub_comm] at huv ⊢
      rw [abs_of_nonneg (sub_nonneg.mpr h1)] at huv
      have : K * (v - u) ≤ K := by nlinarith
      linarith
  have hdev : ∀ t ∈ Icc a b, |h t - m| ≤ K + D + s := by
    intro t ht
    obtain ⟨t', ht', hnj, hd⟩ := hnear t ht
    have h1 : |h t' - m| < s := by
      by_contra hh; exact hnj ⟨ht', not_lt.mp hh⟩
    have h2 := hclose t t' hd
    calc |h t - m| = |(h t - h t') + (h t' - m)| := by ring_nf
      _ ≤ |h t - h t'| + |h t' - m| := abs_add_le _ _
      _ ≤ K + D + s := by linarith
  have hbd := hdev b ⟨hab.le, le_rfl⟩
  have had := hdev a ⟨le_rfl, hab.le⟩
  have hlog : Real.posLog L = Real.log L := Real.posLog_eq_log (by rw [abs_of_pos (by linarith)]; linarith)
  have hfin : |h b - h a| ≤ |h b - m| + |h a - m| := by
    calc |h b - h a| = |(h b - m) - (h a - m)| := by ring_nf
      _ ≤ |h b - m| + |h a - m| := abs_sub _ _
  have h3 := le_max_left (2 * (K + D)) (K * L₀ + D)
  rw [hlog]
  simp only [hs] at hbd had
  nlinarith

/-- **Claim** (p. 798): Landau's inequality (Theorem B) follows from the John–Nirenberg theorem,
Pavlov's theorem (Theorem A) and Theorem 1: for a separated sampling sequence `Λ`,
`n_Λ(b) - n_Λ(a) ≥ b - a - A log⁺(b - a) - B`. -/
theorem landau_inequality (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE)
    (hF : TheoremF) (hA : PavlovBMO) (hJN : JohnNirenberg)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ A B : ℝ, ∀ a b : ℝ, a < b →
      ENNReal.ofReal (b - a - A * Real.posLog (b - a) - B) ≤ ((Λ ∩ Ioc a b).encard : ℝ≥0∞) := by
  obtain ⟨γ, hγm, hsepΓ, hcis, hΛγ⟩ := corollary1_strong hPW hC hE hF hΛ hs
  have hbmo := hA _ hsepΓ hcis
  obtain ⟨q, hq, hqsep⟩ := hsepΓ
  have hfinΓ : ∀ a b : ℝ, (Set.range γ ∩ Ioc a b).Finite := fun a b ↦
    IsSeparated.finite_inter_Ioc ⟨q, hq, hqsep⟩ a b
  have hfinΛ : ∀ a b : ℝ, (Λ ∩ Ioc a b).Finite := fun a b ↦ IsSeparated.finite_inter_Ioc hΛ a b
  have hloc : ∀ a b : ℝ, a ≤ b →
      |(fun t ↦ countFn (Set.range γ) t - t) b - (fun t ↦ countFn (Set.range γ) t - t) a| ≤
        (1 + 1 / q) * (b - a) + 1 := by
    intro a b hab
    have h1 := countFn_sub hfinΓ hab
    have h2 := ncard_inter_Ioc_le hq hqsep hab
    have h3 : (0 : ℝ) ≤ ((Set.range γ ∩ Ioc a b).ncard : ℝ) := Nat.cast_nonneg _
    have h4 : (b - a) / q = (1 / q) * (b - a) := by ring
    have h5 : 0 ≤ (1 / q) * (b - a) := mul_nonneg (by positivity) (by linarith)
    simp only
    rw [abs_le]
    constructor <;> nlinarith
  obtain ⟨A, B, hAB⟩ := osc_bound_of_JN hJN hbmo (K := 1 + 1 / q) (D := 1)
    (by positivity) hloc
  refine ⟨A, B + 1, fun a b hab ↦ ?_⟩
  have h1 := countFn_sub hfinΓ hab.le
  have h2 := ncard_Ioc_ge hγm hΛγ hfinΛ hfinΓ a b
  have h3 := hAB a b hab
  beta_reduce at h3
  rw [abs_le] at h3
  have hreal : b - a - A * Real.posLog (b - a) - (B + 1) ≤ ((Λ ∩ Ioc a b).ncard : ℝ) := by
    linarith [h3.1]
  calc ENNReal.ofReal (b - a - A * Real.posLog (b - a) - (B + 1))
      ≤ ENNReal.ofReal ((Λ ∩ Ioc a b).ncard : ℝ) := ENNReal.ofReal_le_ofReal hreal
    _ = (((Λ ∩ Ioc a b).ncard : ℕ) : ℝ≥0∞) := ENNReal.ofReal_natCast _
    _ = ((Λ ∩ Ioc a b).encard : ℝ≥0∞) := by
        rw [← (hfinΛ a b).cast_ncard_eq]; rfl

end FF
