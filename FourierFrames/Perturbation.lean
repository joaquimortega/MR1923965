import FourierFrames.PW.PlancherelPolya
import FourierFrames.PW.Complete

/-!
# M07 — The perturbation lemma

See `blueprint/M07_Corollary2.md`, §1.  The paper (p. 800) quotes: "If a separated sequence `Γ` is
sampling, then `Γ' = {γ_k + δ_k}` is sampling whenever all `γ_k + δ_k` are distinct and
`δ_k → 0`.  (This follows from Lemma III in [DS52] and the elementary fact that `Γ` is sampling if
`δ_k = 0` except for finitely many integers `k`.)"

The "elementary fact" is false as stated for *arbitrary* finite modifications that change the
number of points (remove one point of `ℤ`); it is true when finitely many points are *replaced* by
the same number of new points (`isSampling_of_replace_finite`).  This is what is needed, since
`γ ↦ γ + δ(γ)` is injective.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Elementary facts on sampling sums and separated sets -/


/-- `sampleSum {a} f = |f(a)|²`. -/
theorem sampleSum_singleton (a : ℝ) (f : ℂ → ℂ) : sampleSum {a} f = ‖f (a : ℂ)‖ₑ ^ 2 := by
  rw [sampleSum_eq_tsum_indicator, tsum_eq_single a]
  · simp
  · intro b hb; simp [Set.indicator, hb]

/-- A separated set is closed (and discrete). -/
theorem IsSeparated.isClosed {Λ : Set ℝ} (h : IsSeparated Λ) : IsClosed Λ := by
  obtain ⟨δ, hδ, hs⟩ := h
  refine closure_subset_iff_isClosed.mp fun x hx ↦ ?_
  by_contra hxΛ
  obtain ⟨a, ha, hax⟩ := Metric.mem_closure_iff.mp hx (δ / 2) (by positivity)
  have hr : 0 < dist x a := dist_pos.mpr (fun h ↦ hxΛ (h ▸ ha))
  obtain ⟨b, hb, hbx⟩ := Metric.mem_closure_iff.mp hx (min (δ / 2) (dist x a)) (lt_min (by positivity) hr)
  have hba : b ≠ a := by
    rintro rfl
    exact absurd hbx (not_lt.mpr (min_le_right _ _))
  have := hs a ha b hb (Ne.symm hba)
  have h1 := lt_of_lt_of_le hbx (min_le_left _ _)
  rw [Real.dist_eq] at hax h1
  have : |a - b| ≤ |x - a| + |x - b| := by
    calc |a - b| = |(x - b) - (x - a)| := by ring_nf
      _ ≤ |x - b| + |x - a| := abs_sub _ _
      _ = _ := add_comm _ _
  rw [abs_sub_comm x a] at this
  rw [abs_sub_comm x b] at h1
  rw [abs_sub_comm x a] at hax
  linarith [abs_sub_comm x b]

/-- Adding one point to a separated set keeps it separated. -/
theorem IsSeparated.insert {Λ : Set ℝ} (h : IsSeparated Λ) {b : ℝ} (hb : b ∉ Λ) :
    IsSeparated (insert b Λ) := by
  obtain ⟨δ, hδ, hs⟩ := h
  have hc := (IsSeparated.isClosed ⟨δ, hδ, hs⟩)
  rcases Λ.eq_empty_or_nonempty with rfl | hne
  · refine ⟨1, one_pos, ?_⟩
    intro a ha c hc' hac
    simp at ha hc'
    exact absurd (ha.trans hc'.symm) hac
  have hd : 0 < Metric.infDist b Λ := (hc.notMem_iff_infDist_pos hne).mp hb
  refine ⟨min δ (Metric.infDist b Λ), lt_min hδ hd, ?_⟩
  have key : ∀ c ∈ Λ, Metric.infDist b Λ ≤ |b - c| := fun c hc ↦ by
    rw [← Real.dist_eq]; exact Metric.infDist_le_dist_of_mem hc
  intro x hx y hy hxy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact absurd rfl hxy
  · exact (min_le_right _ _).trans (key y hy)
  · rw [abs_sub_comm]; exact (min_le_right _ _).trans (key x hx)
  · exact (min_le_left _ _).trans (hs x hx y hy hxy)

/-- Union of a separated set and a finite set is separated. -/
theorem IsSeparated.union_finite {Λ G : Set ℝ} (h : IsSeparated Λ) (hG : G.Finite) :
    IsSeparated (Λ ∪ G) := by
  induction G, hG using Set.Finite.induction_on with
  | empty => simpa using h
  | @insert a s _ _ ih =>
    by_cases ha : a ∈ Λ ∪ s
    · have : Λ ∪ Insert.insert a s = Λ ∪ s := by
        ext x; simp only [mem_union, Set.mem_insert_iff]
        constructor
        · rintro (hx | rfl | hx)
          · exact Or.inl hx
          · simpa using ha
          · exact Or.inr hx
        · rintro (hx | hx) <;> simp [hx]
      rw [this]; exact ih
    · have : Λ ∪ Insert.insert a s = Insert.insert a (Λ ∪ s) := by
        ext x; simp only [mem_union, Set.mem_insert_iff]; tauto
      rw [this]; exact ih.insert ha


theorem sampleSum_const_mul (Λ : Set ℝ) (c : ℂ) (f : ℂ → ℂ) :
    sampleSum Λ (fun z ↦ c * f z) = ‖c‖ₑ ^ 2 * sampleSum Λ f := by
  unfold sampleSum
  rw [← ENNReal.tsum_mul_left]
  congr 1; ext x
  simp [enorm_mul, mul_pow]

theorem pwNormSq_const_mul (c : ℂ) (f : ℂ → ℂ) :
    pwNormSq (fun z ↦ c * f z) = ‖c‖ₑ ^ 2 * pwNormSq f := by
  unfold pwNormSq
  rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)]
  congr 1; ext x
  simp [enorm_mul, mul_pow]

theorem sampleSum_eq_zero_of_forall {Λ : Set ℝ} {f : ℂ → ℂ} (h : ∀ x ∈ Λ, f x = 0) :
    sampleSum Λ f = 0 := by
  unfold sampleSum
  simp only [ENNReal.tsum_eq_zero]
  intro x; simp [h x x.2]

theorem enorm_sq_le_sampleSum {Λ : Set ℝ} (f : ℂ → ℂ) {p : ℝ} (hp : p ∈ Λ) :
    ‖f (p : ℂ)‖ₑ ^ 2 ≤ sampleSum Λ f :=
  ENNReal.le_tsum (f := fun x : Λ ↦ ‖f ((x : ℝ) : ℂ)‖ₑ ^ 2) ⟨p, hp⟩

/-- Reduction of a lower sampling bound to normalised functions. -/
theorem exists_lower_of_normalized {Λ : Set ℝ}
    (h : ∃ A : ℝ≥0, 0 < A ∧ ∀ f : ℂ → ℂ, MemPW f → pwNormSq f = 1 → (A : ℝ≥0∞) ≤ sampleSum Λ f) :
    ∃ A : ℝ≥0, 0 < A ∧ ∀ f : ℂ → ℂ, MemPW f → (A : ℝ≥0∞) * pwNormSq f ≤ sampleSum Λ f := by
  obtain ⟨A, hA, h⟩ := h
  refine ⟨A, hA, fun f hf ↦ ?_⟩
  by_cases h0 : pwNormSq f = 0
  · simp [h0]
  have htop := pwNormSq_ne_top hf
  set N := pwNormSq f with hN
  have hNr : 0 < N.toReal := ENNReal.toReal_pos h0 htop
  set c : ℂ := (((Real.sqrt N.toReal)⁻¹ : ℝ) : ℂ) with hc
  have hc2 : ‖c‖ₑ ^ 2 * N = 1 := by
    have : ‖c‖ₑ ^ 2 = ENNReal.ofReal (N.toReal)⁻¹ := by
      have he : ‖c‖ₑ = ENNReal.ofReal (Real.sqrt N.toReal)⁻¹ := by
        rw [hc, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [he, ← ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [inv_pow, Real.sq_sqrt hNr.le]
    rw [this]
    have e := ENNReal.ofReal_toReal htop
    calc ENNReal.ofReal N.toReal⁻¹ * N = ENNReal.ofReal N.toReal⁻¹ * ENNReal.ofReal N.toReal := by rw [e]
      _ = 1 := by
        rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hNr.ne', ENNReal.ofReal_one]
  have hcf : MemPW (fun z ↦ c * f z) := hf.const_mul c
  have h1 : pwNormSq (fun z ↦ c * f z) = 1 := by rw [pwNormSq_const_mul]; exact hc2
  have := h _ hcf h1
  rw [sampleSum_const_mul] at this
  calc (A : ℝ≥0∞) * N ≤ (‖c‖ₑ ^ 2 * sampleSum Λ f) * N := by gcongr
    _ = (‖c‖ₑ ^ 2 * N) * sampleSum Λ f := by ring
    _ = _ := by rw [hc2, one_mul]



/-- **Replacing one point.**  If `Γ` is a separated sampling set, `a ∈ Γ` and `b ∉ Γ`, then
`(Γ \ {a}) ∪ {b}` is a (separated) sampling set. -/
theorem isSampling_replace_point (hPW : PaleyWienerThm) {Γ : Set ℝ} (hsep : IsSeparated Γ)
    (hs : IsSampling Γ) {a b : ℝ} (ha : a ∈ Γ) (hb : b ∉ Γ) :
    IsSampling (insert b (Γ \ {a})) := by
  obtain ⟨A, B, hA, hAB⟩ := hs
  set Γ' := (Insert.insert b (Γ \ {a}) : Set ℝ) with hΓ'
  have hsep' : IsSeparated Γ' := by
    obtain ⟨δ, hδ, hδs⟩ := hsep
    exact (IsSeparated.insert ⟨δ, hδ, IsSepBy.mono (hδs : IsSepBy δ Γ) le_rfl sdiff_subset⟩
      (fun h ↦ hb h.1))
  obtain ⟨δ', hδ', hs'⟩ := hsep'
  obtain ⟨C, hC⟩ := plancherelPolya hPW hδ'
  have hba : b ≠ a := fun h ↦ hb (h ▸ ha)
  have hsub : Γ \ {a} ⊆ Γ' := fun x hx ↦ Or.inr hx
  have hbΓ' : b ∈ Γ' := Or.inl rfl
  have hlow : ∃ A' : ℝ≥0, 0 < A' ∧ ∀ f : ℂ → ℂ, MemPW f → (A' : ℝ≥0∞) * pwNormSq f ≤ sampleSum Γ' f := by
    apply exists_lower_of_normalized
    by_contra hcon
    push Not at hcon
    have hn : ∀ n : ℕ, ∃ f : ℂ → ℂ, MemPW f ∧ pwNormSq f = 1 ∧
        sampleSum Γ' f < (((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) := fun n ↦ by
      obtain ⟨f, hf, h1, h2⟩ := hcon (((n : ℝ≥0) + 1)⁻¹) (by positivity)
      exact ⟨f, hf, h1, h2⟩
    choose f hf hf1 hfs using hn
    obtain ⟨φ, hφ, g, hg, hlu, -⟩ := pw_normal_family hPW hf (M := 1) (fun n ↦ by simp [hf1 n])
    have hT : Tendsto (fun n : ℕ ↦ sampleSum Γ' (f n)) atTop (𝓝 0) := by
      have hup : Tendsto (fun n : ℕ ↦ ((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
        have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
        refine this.congr fun n ↦ ?_
        simp [ENNReal.coe_inv]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n ↦ bot_le)
        (fun n ↦ (hfs n).le)
    have hT' : Tendsto (fun n : ℕ ↦ sampleSum Γ' (f (φ n))) atTop (𝓝 0) := hT.comp hφ.tendsto_atTop
    have hpt : ∀ p : ℝ, p ∈ Γ' → g p = 0 := by
      intro p hp
      have h1 : Tendsto (fun n ↦ ‖f (φ n) (p : ℂ)‖ₑ ^ 2) atTop (𝓝 (‖g p‖ₑ ^ 2)) :=
        ((ENNReal.continuous_pow 2).tendsto _).comp
          ((continuous_enorm.tendsto _).comp ((TendstoLocallyUniformly.tendstoLocallyUniformlyOn hlu (s := univ)).tendsto_at (mem_univ (p : ℂ))))
      have h2 : Tendsto (fun n ↦ ‖f (φ n) (p : ℂ)‖ₑ ^ 2) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT' (fun n ↦ bot_le)
          (fun n ↦ enorm_sq_le_sampleSum _ hp)
      have := tendsto_nhds_unique h1 h2
      simpa using this
    have hg0 : ∀ z, g z = 0 := by
      have hh : MemPW (fun z ↦ dslope g (b : ℂ) z * (z - (a : ℂ))) :=
        hg.mul_div_sub (by simpa using hpt b hbΓ') (a : ℂ)
      have hvan : ∀ x ∈ Γ, (fun z ↦ dslope g (b : ℂ) z * (z - (a : ℂ))) (x : ℂ) = 0 := by
        intro x hx
        by_cases hxa : x = a
        · simp [hxa]
        · have hxΓ' : x ∈ Γ' := hsub ⟨hx, hxa⟩
          have hxb : (x : ℂ) ≠ (b : ℂ) := by
            intro h; exact hb (by have := Complex.ofReal_injective h; rwa [this] at hx)
          simp only
          rw [dslope_of_ne _ hxb, slope_def_field, hpt x hxΓ', hpt b hbΓ']
          simp
      have h0 : sampleSum Γ (fun z ↦ dslope g (b : ℂ) z * (z - (a : ℂ))) = 0 :=
        sampleSum_eq_zero_of_forall hvan
      have h1 := (hAB _ hh).1
      rw [h0] at h1
      have h2 : pwNormSq (fun z ↦ dslope g (b : ℂ) z * (z - (a : ℂ))) = 0 := by
        have : (A : ℝ≥0∞) ≠ 0 := by exact_mod_cast hA.ne'
        simpa [this] using h1
      have h3 := hh.eq_zero_of_pwNormSq_eq_zero h2
      have hz : ∀ z : ℂ, z ≠ (a : ℂ) → g z = 0 := by
        intro z hz
        by_cases hzb : z = (b : ℂ)
        · rw [hzb]; simpa using hpt b hbΓ'
        · have := congrFun h3 z
          simp only [Pi.zero_apply] at this
          rw [dslope_of_ne _ hzb, slope_def_field] at this
          have hza : z - (a : ℂ) ≠ 0 := sub_ne_zero.mpr hz
          have hzb' : z - (b : ℂ) ≠ 0 := sub_ne_zero.mpr hzb
          have hgb : g (b : ℂ) = 0 := by simpa using hpt b hbΓ'
          rw [hgb] at this
          simpa [hza, hzb'] using this
      intro z
      by_cases hza : z = (a : ℂ)
      · have h1 : Tendsto g (𝓝[≠] (a : ℂ)) (𝓝 (g (a : ℂ))) :=
          (hg.1.continuous.tendsto _).mono_left nhdsWithin_le_nhds
        have h2 : Tendsto g (𝓝[≠] (a : ℂ)) (𝓝 0) :=
          tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun w hw ↦ (hz w hw).symm)
        rw [hza]; exact tendsto_nhds_unique h1 h2
      · exact hz z hza
    have hTa : Tendsto (fun n : ℕ ↦ ‖f (φ n) (a : ℂ)‖ₑ ^ 2) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n ↦ ‖f (φ n) (a : ℂ)‖ₑ ^ 2) atTop (𝓝 (‖g a‖ₑ ^ 2)) :=
        ((ENNReal.continuous_pow 2).tendsto _).comp
          ((continuous_enorm.tendsto _).comp ((TendstoLocallyUniformly.tendstoLocallyUniformlyOn hlu (s := univ)).tendsto_at (mem_univ (a : ℂ))))
      simpa [hg0] using h1
    have hsum := hT'.add hTa
    rw [add_zero] at hsum
    have hge : ∀ n, (A : ℝ≥0∞) ≤ sampleSum Γ' (f (φ n)) + ‖f (φ n) (a : ℂ)‖ₑ ^ 2 := fun n ↦ by
      have h1 := (hAB _ (hf (φ n))).1
      rw [hf1 (φ n), mul_one] at h1
      refine h1.trans ?_
      calc sampleSum Γ (f (φ n)) ≤ sampleSum (Γ' ∪ {a}) (f (φ n)) := by
            apply sampleSum_mono
            intro x hx
            by_cases hxa : x = a
            · exact Or.inr hxa
            · exact Or.inl (hsub ⟨hx, hxa⟩)
        _ ≤ sampleSum Γ' (f (φ n)) + sampleSum {a} (f (φ n)) := sampleSum_union_le _ _ _
        _ = _ := by rw [sampleSum_singleton]
    have := ge_of_tendsto' hsum hge
    have hA0 : (A : ℝ≥0∞) = 0 := le_antisymm this bot_le
    exact hA.ne' (by exact_mod_cast hA0)
  obtain ⟨A', hA', hA''⟩ := hlow
  exact ⟨A', C, hA', fun f hf ↦ ⟨hA'' f hf, hC Γ' hs' f hf⟩⟩


/-- **Replacing finitely many points by the same number of new points.**  (The "elementary fact"
of p. 800.) -/
theorem isSampling_of_replace_finite (hPW : PaleyWienerThm) {Γ Γ' : Set ℝ}
    (hsep : IsSeparated Γ) (hs : IsSampling Γ) (hsep' : IsSeparated Γ')
    (hD : (Γ \ Γ').Finite) (hD' : (Γ' \ Γ).Finite) (hcard : (Γ \ Γ').ncard = (Γ' \ Γ).ncard) :
    IsSampling Γ' := by
  have _ := hsep'
  suffices H : ∀ n : ℕ, ∀ Γ : Set ℝ, IsSeparated Γ → IsSampling Γ → (Γ \ Γ').Finite →
      (Γ' \ Γ).Finite → (Γ \ Γ').ncard = n → (Γ' \ Γ).ncard = n → IsSampling Γ' from
    H _ Γ hsep hs hD hD' rfl hcard.symm
  intro n
  induction n with
  | zero =>
    intro Γ hsep hs hD hD' h1 h2
    rw [Set.ncard_eq_zero hD] at h1
    rw [Set.ncard_eq_zero hD'] at h2
    have : Γ = Γ' := Set.Subset.antisymm (Set.sdiff_eq_empty.mp h1)
      (Set.sdiff_eq_empty.mp h2)
    rwa [this] at hs
  | succ n ih =>
    intro Γ hsep hs hD hD' h1 h2
    obtain ⟨a, haΓ, haΓ'⟩ := Set.nonempty_of_ncard_ne_zero (s := Γ \ Γ') (by omega)
    obtain ⟨b, hbΓ', hbΓ⟩ := Set.nonempty_of_ncard_ne_zero (s := Γ' \ Γ) (by omega)
    have hΓ₁ := isSampling_replace_point hPW hsep hs haΓ hbΓ
    have hsep₁ : IsSeparated (Insert.insert b (Γ \ {a}) : Set ℝ) := by
      obtain ⟨δ, hδ, hδs⟩ := hsep
      exact IsSeparated.insert ⟨δ, hδ, IsSepBy.mono (hδs : IsSepBy δ Γ) le_rfl sdiff_subset⟩
        (fun h ↦ hbΓ h.1)
    have e1 : (Insert.insert b (Γ \ {a}) : Set ℝ) \ Γ' = (Γ \ Γ') \ {a} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl | ⟨hx, hxa⟩, hx'⟩
        · exact absurd hbΓ' hx'
        · exact ⟨⟨hx, hx'⟩, hxa⟩
      · rintro ⟨⟨hx, hx'⟩, hxa⟩
        exact ⟨Or.inr ⟨hx, hxa⟩, hx'⟩
    have e2 : Γ' \ (Insert.insert b (Γ \ {a}) : Set ℝ) = (Γ' \ Γ) \ {b} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro ⟨hx, hx'⟩
        push Not at hx'
        refine ⟨⟨hx, fun hxΓ ↦ ?_⟩, hx'.1⟩
        exact haΓ' (by have := hx'.2 hxΓ; rwa [this] at hx)
      · rintro ⟨⟨hx, hxΓ⟩, hxb⟩
        refine ⟨hx, ?_⟩
        rintro (h | ⟨h, _⟩)
        · exact hxb h
        · exact hxΓ h
    refine ih _ hsep₁ hΓ₁ ?_ ?_ ?_ ?_
    · rw [e1]; exact hD.sdiff
    · rw [e2]; exact hD'.sdiff
    · rw [e1, Set.ncard_sdiff_singleton_of_mem (show a ∈ Γ \ Γ' from ⟨haΓ, haΓ'⟩)]; omega
    · rw [e2, Set.ncard_sdiff_singleton_of_mem (show b ∈ Γ' \ Γ from ⟨hbΓ', hbΓ⟩)]; omega


/-- A far part of a separated set, moved by small perturbations, stays separated. -/
theorem isSeparated_image_far {Γ : Set ℝ} {η : ℝ} (hη : 0 < η) (hΓ : IsSepBy η Γ) {δ : ℝ → ℝ}
    (S : Set ℝ) (hS : S ⊆ Γ) (hδ : ∀ x ∈ S, |δ x| ≤ η / 4) :
    IsSeparated ((fun x ↦ x + δ x) '' S) := by
  refine ⟨η / 2, by positivity, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hne
  have hyy : y ≠ y' := fun h ↦ hne (by rw [h])
  have h1 := hΓ y (hS hy) y' (hS hy') hyy
  have h2 := hδ y hy
  have h3 := hδ y' hy'
  have : |y - y'| ≤ |(y + δ y) - (y' + δ y')| + |δ y| + |δ y'| := by
    calc |y - y'| = |((y + δ y) - (y' + δ y')) - δ y + δ y'| := by ring_nf
      _ ≤ |((y + δ y) - (y' + δ y')) - δ y| + |δ y'| := abs_add_le _ _
      _ ≤ |(y + δ y) - (y' + δ y')| + |δ y| + |δ y'| := by
          gcongr; exact abs_sub _ _
  linarith

/-- **Perturbation lemma** (p. 800; Duffin–Schaeffer + finite modification). -/
theorem IsSampling.of_perturbation (hPW : PaleyWienerThm) (hDS : DSPerturbation) {Γ : Set ℝ}
    (hsep : IsSeparated Γ) (hs : IsSampling Γ) {δ : ℝ → ℝ}
    (hinj : InjOn (fun x ↦ x + δ x) Γ)
    (hδ : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x ∈ Γ, R ≤ |x| → |δ x| ≤ ε) :
    IsSampling ((fun x ↦ x + δ x) '' Γ) := by
  obtain ⟨η, hη, hΓη⟩ := hsep
  obtain ⟨L, hL, hDSL⟩ := hDS Γ ⟨η, hη, hΓη⟩ hs
  obtain ⟨R, hR⟩ := hδ (min L (η / 4)) (lt_min hL (by positivity))
  have hRL : ∀ x ∈ Γ, R ≤ |x| → |δ x| ≤ L := fun x hx h ↦ (hR x hx h).trans (min_le_left _ _)
  have hR4 : ∀ x ∈ Γ, R ≤ |x| → |δ x| ≤ η / 4 := fun x hx h ↦ (hR x hx h).trans (min_le_right _ _)
  set T : ℝ → ℝ := fun x ↦ x + δ x with hT
  set Nr : Set ℝ := {x ∈ Γ | |x| < R} with hNr
  set Fr : Set ℝ := {x ∈ Γ | R ≤ |x|} with hFr
  have hNfin : Nr.Finite := by
    refine ((IsSeparated.finite_inter_Icc ⟨η, hη, hΓη⟩ R)).subset ?_
    intro x ⟨hx, h⟩
    exact ⟨hx, abs_le.mp h.le⟩
  have hΓeq : Γ = Nr ∪ Fr := by
    ext x; simp only [hNr, hFr, mem_union, mem_ofPred_eq]
    constructor
    · intro hx; rcases lt_or_ge |x| R with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (h | h) <;> exact h.1
  set δ₁ : ℝ → ℝ := fun x ↦ if |x| < R then 0 else δ x with hδ₁
  set M : Set ℝ := T '' Fr with hM
  set G : Set ℝ := T '' Nr with hG
  have hNF : ∀ x ∈ Nr, ∀ y ∈ Fr, x ≠ T y := by
    intro x hx y hy hxy
    have h1 : |y - x| ≤ η / 4 := by
      have : y - x = -δ y := by rw [hxy, hT]; ring
      rw [this, abs_neg]; exact hR4 y hy.1 hy.2
    have hne : y ≠ x := by
      intro h; have := hx.2; have := hy.2; rw [h] at *; linarith
    have := hΓη y hy.1 x hx.1 hne
    linarith
  have hGM : ∀ x ∈ Nr, ∀ y ∈ Fr, T x ≠ T y := by
    intro x hx y hy h
    have e := hinj hx.1 hy.1 h
    have h1 := hx.2
    rw [e] at h1
    linarith [hy.2]
  have hδ₁L : ∀ x ∈ Γ, |δ₁ x| ≤ L := by
    intro x hx
    by_cases h : |x| < R
    · simp [hδ₁, h, hL.le]
    · simp only [hδ₁, h, ite_false]; exact hRL x hx (not_lt.mp h)
  have hΓ₁eq : (fun x ↦ x + δ₁ x) '' Γ = Nr ∪ M := by
    rw [hΓeq, image_union]
    congr 1
    · ext x; simp only [mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩; simp [hδ₁, hy.2]; exact hy
      · intro hx; exact ⟨x, hx, by simp [hδ₁, hx.2]⟩
    · ext x; simp only [hM, mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, by simp [hδ₁, hT, not_lt.mpr hy.2]⟩
      · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, by simp [hδ₁, hT, not_lt.mpr hy.2]⟩
  have hinj₁ : InjOn (fun x ↦ x + δ₁ x) Γ := by
    intro x hx y hy hxy
    by_cases hx' : |x| < R <;> by_cases hy' : |y| < R
    · simpa [hδ₁, hx', hy'] using hxy
    · exact absurd (by simpa [hδ₁, hx', hy'] using hxy) (hNF x ⟨hx, hx'⟩ y ⟨hy, not_lt.mp hy'⟩)
    · exact absurd (by simpa [hδ₁, hx', hy'] using hxy.symm) (hNF y ⟨hy, hy'⟩ x ⟨hx, not_lt.mp hx'⟩)
    · simpa [hδ₁, hx', hy', hT] using hinj hx hy (by simpa [hδ₁, hx', hy', hT] using hxy)
  have hS₁ := hDSL δ₁ hδ₁L hinj₁
  rw [hΓ₁eq] at hS₁
  have hMsep : IsSeparated M :=
    isSeparated_image_far hη hΓη Fr (fun x hx ↦ hx.1) (fun x hx ↦ hR4 x hx.1 hx.2)
  have hΓ'eq : T '' Γ = M ∪ G := by
    rw [hΓeq, image_union, union_comm]
  rw [hΓ'eq]
  have hsepΓ₁ : IsSeparated (Nr ∪ M) := by
    rw [union_comm]; exact IsSeparated.union_finite hMsep hNfin
  have hGfin : G.Finite := hNfin.image T
  have hsepΓ' : IsSeparated (M ∪ G) := IsSeparated.union_finite hMsep hGfin
  have hNM : ∀ x ∈ Nr, x ∉ M := by
    rintro x hx ⟨y, hy, hxy⟩
    exact hNF x hx y hy hxy.symm
  have hGM' : ∀ x ∈ G, x ∉ M := by
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    exact hGM x hx y hy hxy.symm
  have e1 : (Nr ∪ M) \ (M ∪ G) = Nr \ G := by
    ext x
    simp only [Set.mem_sdiff, mem_union]
    constructor
    · rintro ⟨hx | hx, hx'⟩
      · exact ⟨hx, fun h ↦ hx' (Or.inr h)⟩
      · exact absurd (Or.inl hx) hx'
    · rintro ⟨hx, hx'⟩
      exact ⟨Or.inl hx, fun h ↦ h.elim (hNM x hx) hx'⟩
  have e2 : (M ∪ G) \ (Nr ∪ M) = G \ Nr := by
    ext x
    simp only [Set.mem_sdiff, mem_union]
    constructor
    · rintro ⟨hx | hx, hx'⟩
      · exact absurd (Or.inr hx) hx'
      · exact ⟨hx, fun h ↦ hx' (Or.inl h)⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨Or.inr hx, fun h ↦ h.elim hx' (hGM' x hx)⟩
  have hGc : G.ncard = Nr.ncard := (hinj.mono (fun x hx ↦ hx.1)).ncard_image
  have c1 := Set.ncard_inter_add_ncard_sdiff_eq_ncard Nr G hNfin
  have c2 := Set.ncard_inter_add_ncard_sdiff_eq_ncard G Nr hGfin
  rw [inter_comm] at c2
  refine isSampling_of_replace_finite hPW hsepΓ₁ hS₁ hsepΓ' ?_ ?_ ?_
  · rw [e1]; exact hNfin.sdiff
  · rw [e2]; exact hGfin.sdiff
  · rw [e1, e2]; omega


end FF
