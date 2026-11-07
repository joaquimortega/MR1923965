import FourierFrames.HB.DeBranges
import FourierFrames.PW.PlancherelPolya
import FourierFrames.Theorem1.Sufficiency.LevelSet

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF
namespace Suff

theorem sampleSum_translate (Γ : Set ℝ) (g : ℂ → ℂ) (t : ℝ) :
    sampleSum Γ (fun z ↦ g (z - t)) = sampleSum ((fun x : ℝ ↦ x - t) '' Γ) g := by
  unfold sampleSum
  rw [← (Equiv.Set.image (fun x : ℝ ↦ x - t) Γ (sub_left_injective)).tsum_eq]
  congr 1
  ext x
  simp

/-- Translating a set whose points all stay far from `t` makes the sampling sum small. -/
theorem translate_tail (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) {f : ℂ → ℂ} (hf : MemPW f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ R : ℝ, ∀ (Γ : Set ℝ) (t : ℝ), IsSepBy δ Γ → (∀ x ∈ Γ, R ≤ |x - t|) →
      sampleSum Γ (fun z ↦ f (z - t)) ≤ ε := by
  obtain ⟨R, hR⟩ := plancherelPolya_tail hPW hδ hf hε
  refine ⟨R, fun Γ t hΓ hfar ↦ ?_⟩
  rw [sampleSum_translate]
  have hsep : IsSepBy δ ((fun x : ℝ ↦ x - t) '' Γ) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    have : a ≠ b := fun h ↦ hab (by rw [h])
    have := hΓ a ha b hb this
    simpa using this
  have := hR _ hsep
  rwa [Set.inter_eq_left.mpr] at this
  rintro _ ⟨a, ha, rfl⟩
  exact hfar a ha

theorem finite_phaseLevel_Icc {φ : ℝ → ℝ} (hφ : StrictMono φ) (α a b : ℝ) :
    (phaseLevel φ α ∩ {x : ℝ | a ≤ φ x ∧ φ x ≤ b}).Finite := by
  have hπ := Real.pi_pos
  apply Set.Finite.of_finite_image (f := φ) _ hφ.injective.injOn
  refine ((Set.finite_Icc (⌈(a - α) / Real.pi⌉) (⌊(b - α) / Real.pi⌋)).image
    (fun k : ℤ ↦ α + k * Real.pi)).subset ?_
  rintro _ ⟨x, ⟨⟨k, hk⟩, ha, hb⟩, rfl⟩
  refine ⟨k, ⟨?_, ?_⟩, hk.symm⟩
  · apply Int.ceil_le.mpr
    rw [div_le_iff₀ hπ]; linarith
  · apply Int.le_floor.mpr
    rw [le_div_iff₀ hπ]; linarith

theorem bddAbove_phaseLevel {φ : ℝ → ℝ} (hφ : StrictMono φ) (α b : ℝ) (hb : ∀ x, φ x ≤ b) :
    BddAbove (phaseLevel φ α) := by
  have hfin := finite_phaseLevel_Icc hφ α (φ 0) b
  have h1 : BddAbove (phaseLevel φ α ∩ {x : ℝ | φ 0 ≤ φ x ∧ φ x ≤ b}) := hfin.bddAbove
  refine (h1.union (bddAbove_Iio (a := (0 : ℝ)))).mono ?_
  intro x hx
  by_cases h0 : x < 0
  · exact Or.inr h0
  · refine Or.inl ⟨hx, hφ.monotone (not_lt.mp h0), hb x⟩

theorem bddBelow_phaseLevel {φ : ℝ → ℝ} (hφ : StrictMono φ) (α b : ℝ) (hb : ∀ x, b ≤ φ x) :
    BddBelow (phaseLevel φ α) := by
  have hfin := finite_phaseLevel_Icc hφ α b (φ 0)
  have h1 : BddBelow (phaseLevel φ α ∩ {x : ℝ | b ≤ φ x ∧ φ x ≤ φ 0}) := hfin.bddBelow
  refine (h1.union (bddBelow_Ioi (a := (0 : ℝ)))).mono ?_
  intro x hx
  by_cases h0 : 0 < x
  · exact Or.inr h0
  · exact Or.inl ⟨hx, hb x, hφ.monotone (not_lt.mp h0)⟩

/-- Lower bound for the sampling sums of translates, from `H(E) = PW` and the norm identity. -/
theorem translate_lower_bound_aux (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {α : ℝ}
    (hα : ¬ MemHE E (sAlpha E α)) {g : ℂ → ℂ} (hg : MemPW g) (hP : pwNormSq g ≠ 0) :
    ∃ ε₀ : ℝ≥0, 0 < ε₀ ∧ ∀ t : ℝ, (ε₀ : ℝ≥0∞) ≤ sampleSum (phaseLevel φ α) (fun z ↦ g (z - t)) := by
  have hπ := Real.pi_pos
  have hstrict : IsStrictHB E := HEEqPW.isStrictHB hEHB hEPW
  have hE0 : ∀ x : ℝ, E x ≠ 0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  obtain ⟨c, C, hc, hcC⟩ := hEPW.2
  obtain ⟨c1, hc1, hc1le⟩ := HEEqPW.phaseDeriv_mul_sq_ge hE hEHB hEPW
  have hTE := hE E hstrict hE0 φ hφ α hα
  obtain ⟨ε₀, hε₀, hlt⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := ENNReal.ofReal (Real.pi / c1)) ENNReal.ofReal_ne_top
    (b := (c : ℝ≥0∞) * pwNormSq g) (mul_ne_zero (by exact_mod_cast hc.ne') hP)
  refine ⟨ε₀, hε₀, fun t ↦ ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hgt : MemPW (fun z ↦ g (z - t)) := hg.comp_sub_ofReal t
  have hnormt : pwNormSq (fun z ↦ g (z - t)) = pwNormSq g := pwNormSq_comp_sub_ofReal g t
  have hHE : MemHE E (fun z ↦ g (z - t)) := (hEPW.1 _).mpr hgt
  have h1 : (c : ℝ≥0∞) * pwNormSq g ≤ heNormSq E (fun z ↦ g (z - t)) := by
    rw [← hnormt]; exact (hcC _ hgt).1
  have h2 : heNormSq E (fun z ↦ g (z - t)) ≤
      ENNReal.ofReal (Real.pi / c1) * sampleSum (phaseLevel φ α) (fun z ↦ g (z - t)) := by
    rw [hTE.1 _ hHE, sampleSum, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun x ↦ mul_le_mul' (orthWeight_le hc1 hc1le x) le_rfl
  have h3 := h1.trans h2
  have h4 : ENNReal.ofReal (Real.pi / c1) * sampleSum (phaseLevel φ α) (fun z ↦ g (z - t)) ≤
      ENNReal.ofReal (Real.pi / c1) * ε₀ := mul_le_mul' le_rfl hcon.le
  rw [mul_comm] at hlt
  exact absurd (lt_of_le_of_lt (h3.trans h4) hlt) (lt_irrefl _)


theorem phase_tendsto_aux (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ)
    (hφ' : ∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x) (hex : ∃ α : ℝ, ¬ MemHE E (sAlpha E α)) :
    Tendsto φ atTop atTop ∧ Tendsto φ atBot atBot := by
  have hstrict : IsStrictHB E := HEEqPW.isStrictHB hEHB hEPW
  have hE0 : ∀ x : ℝ, E x ≠ 0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  have hφm : StrictMono φ :=
    strictMono_of_hasDerivAt_pos hφ' (fun x ↦ hstrict.phaseDeriv_pos (hE0 x))
  obtain ⟨α, hα⟩ := hex
  obtain ⟨δ, hδ, hsep⟩ := levelSet_separated_aux hPW hE hEHB hEPW hφ hα
  obtain ⟨ε₀, hε₀, hlow⟩ := translate_lower_bound_aux hE hEHB hEPW hφ hα memPW_pwBump
    pwNormSq_pwBump_pos.ne'
  have hε : (ε₀ : ℝ≥0∞) / 2 ≠ 0 := by
    simp [hε₀.ne']
  obtain ⟨R, hR⟩ := translate_tail hPW hδ memPW_pwBump hε
  have hhalf : (ε₀ : ℝ≥0∞) / 2 < ε₀ :=
    ENNReal.half_lt_self (by exact_mod_cast hε₀.ne') ENNReal.coe_ne_top
  have contra : ∀ t : ℝ, (∀ x ∈ phaseLevel φ α, R ≤ |x - t|) → False := by
    intro t ht
    have h1 := hlow t
    have h2 := hR (phaseLevel φ α) t hsep ht
    exact absurd (lt_of_le_of_lt (h1.trans h2) hhalf) (lt_irrefl _)
  constructor
  · apply tendsto_atTop_atTop_of_monotone hφm.monotone
    intro b
    by_contra h
    push Not at h
    obtain ⟨M, hM⟩ := bddAbove_phaseLevel hφm α b (fun x ↦ (h x).le)
    refine contra (M + R) fun x hx ↦ ?_
    have := hM hx
    rw [abs_sub_comm]
    have : R ≤ M + R - x := by linarith
    exact this.trans (le_abs_self _)
  · rw [tendsto_atBot_atBot]
    intro b
    by_contra h
    push Not at h
    have hb : ∀ x, b < φ x := by
      intro x
      obtain ⟨a, ha, hlt⟩ := h x
      exact hlt.trans_le (hφm.monotone ha)
    obtain ⟨M, hM⟩ := bddBelow_phaseLevel hφm α b (fun x ↦ (hb x).le)
    refine contra (M - R) fun x hx ↦ ?_
    have := hM hx
    have : R ≤ x - (M - R) := by linarith
    exact this.trans (le_abs_self _)


theorem phase_mul_bijective_aux (hPW : PaleyWienerThm) (hE : TheoremE) {E G : ℂ → ℂ}
    (hEHB : IsHB E) (hGHB : IsHB G) (hEPW : HEEqPW E) (hG0 : ∀ x : ℝ, G x ≠ 0)
    {φE φG : ℝ → ℝ} (hφE : IsPhaseFunction E φE)
    (hφE' : ∀ x : ℝ, HasDerivAt φE (phaseDeriv E x) x)
    (hφG : IsPhaseFunction G φG) (hφG' : ∀ x : ℝ, HasDerivAt φG (phaseDeriv G x) x)
    (hex : ∃ α : ℝ, ¬ MemHE E (sAlpha E α)) :
    StrictMono (fun x ↦ φE x + φG x) ∧ Function.Surjective (fun x ↦ φE x + φG x) := by
  have hstrict : IsStrictHB E := HEEqPW.isStrictHB hEHB hEPW
  have hE0 : ∀ x : ℝ, E x ≠ 0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  have hGnn : ∀ x, 0 ≤ phaseDeriv G x := fun x ↦ hGHB.phaseDeriv_nonneg (hG0 x)
  have hmono : StrictMono (fun x ↦ φE x + φG x) :=
    strictMono_of_hasDerivAt_pos (f' := fun x ↦ phaseDeriv E x + phaseDeriv G x)
      (fun x ↦ (hφE' x).add (hφG' x))
      (fun x ↦ add_pos_of_pos_of_nonneg (hstrict.phaseDeriv_pos (hE0 x)) (hGnn x))
  refine ⟨hmono, ?_⟩
  have hGm : Monotone φG := monotone_of_hasDerivAt_nonneg hφG' hGnn
  obtain ⟨hT, hB⟩ := phase_tendsto_aux hPW hE hEHB hEPW hφE hφE' hex
  apply Continuous.surjective (hφE.1.add hφG.1)
  · refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (φG 0) hT)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact add_le_add le_rfl (hGm hx)
  · refine tendsto_atBot_mono' atBot ?_ (tendsto_atBot_add_const_right atBot (φG 0) hB)
    filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
    exact add_le_add le_rfl (hGm hx)

end Suff
end FF
