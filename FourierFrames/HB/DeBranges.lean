import FourierFrames.HB.Phase
import FourierFrames.HB.H2
import FourierFrames.PW.Complete

/-!
# M02 — de Branges spaces `H(E)`: basic facts

See `blueprint/M02_HB.md`, §6–§8.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Multiplication by `F ∈ \overline{HB}` -/

/-- Real zeros of an entire function that does not vanish identically form a countable set. -/
theorem countable_real_zeros {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hne : ∃ z, F z ≠ 0) :
    {x : ℝ | F (x : ℂ) = 0}.Countable := by
  set Z : Set ℝ := {x : ℝ | F (x : ℂ) = 0} with hZ
  have hiso : ∀ x ∈ Z, ∀ᶠ y in 𝓝[≠] x, y ∉ Z := by
    intro x hx
    have hana : AnalyticAt ℂ F (x : ℂ) := hF.analyticAt _
    rcases hana.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      obtain ⟨w, hw⟩ := hne
      have : AnalyticOnNhd ℂ F univ := fun z _ ↦ hF.analyticAt z
      exact hw (this.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (mem_univ _) h (mem_univ w))
    · have hc : Tendsto (fun y : ℝ ↦ (y : ℂ)) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        simpa using hy
      filter_upwards [hc.eventually h] with y hy
      exact hy
  have hdisc : DiscreteTopology Z := by
    rw [discreteTopology_subtype_iff']
    intro y hy
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.mp (hiso y hy)
    refine ⟨Metric.ball y ε, Metric.isOpen_ball, ?_⟩
    ext w
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hw1, hw2⟩
      by_contra hne
      exact hεs ⟨hw1, hne⟩ hw2
    · rintro rfl
      exact ⟨Metric.mem_ball_self hε, hy⟩
  have : Countable Z := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact Set.countable_coe_iff.mp this

/-- `F f ∈ H(E F)` for `f ∈ H(E)` and `F ∈ \overline{HB}`. -/
theorem MemHE.mul_isHB {E F f : ℂ → ℂ} (hF : IsHB F) (hf : MemHE E f) :
    MemHE (fun z ↦ E z * F z) (fun z ↦ F z * f z) := by
  obtain ⟨hfd, h1, h2⟩ := hf
  refine ⟨hF.1.mul hfd, h1.congr fun z hz ↦ ?_, ?_⟩
  · have hFz : F z ≠ 0 := hF.2.1 z hz
    show f z / E z = F z * f z / (E z * F z)
    rw [mul_comm (E z), mul_div_mul_left _ _ hFz]
  · have hB : DifferentiableOn ℂ (fun z ↦ fstar F z / F z) {z : ℂ | 0 < z.im} := fun z hz ↦
      (((Differentiable.fstar hF.1) z).div (hF.1 z) (hF.2.1 z hz)).differentiableWithinAt
    have hB1 : ∀ z : ℂ, 0 < z.im → ‖fstar F z / F z‖ ≤ 1 := by
      intro z hz
      rw [norm_div, div_le_one (norm_pos_iff.mpr (hF.2.1 z hz))]
      exact hF.norm_fstar_le hz
    refine (h2.mul_bounded hB hB1).congr fun z hz ↦ ?_
    have hFz : F z ≠ 0 := hF.2.1 z hz
    show fstar F z / F z * (fstar f z / E z) = fstar (fun z ↦ F z * f z) z / (E z * F z)
    rw [fstar_mul]
    by_cases hE : E z = 0
    · simp [hE]
    · field_simp

/-- `‖F f‖_{EF} = ‖f‖_E`. -/
theorem heNormSq_mul {E F f : ℂ → ℂ} (hF : IsHB F) :
    heNormSq (fun z ↦ E z * F z) (fun z ↦ F z * f z) = heNormSq E f := by
  unfold heNormSq
  have hnull : volume {t : ℝ | F (t : ℂ) = 0} = 0 :=
    (countable_real_zeros hF.1 ⟨I, hF.2.1 I (by simp)⟩).measure_zero _
  refine lintegral_congr_ae ?_
  have : ∀ᵐ t : ℝ, F (t : ℂ) ≠ 0 := by
    rw [ae_iff]; simpa using hnull
  filter_upwards [this] with t ht
  rw [mul_comm (E t) (F t), mul_div_mul_left _ _ ht]

/-! ## The functions `S_α = e^{iα} E - e^{-iα} E^*` -/

/-- `S_α = e^{iα} E - e^{-iα} E^*` (the function of Theorem E). -/
def sAlpha (E : ℂ → ℂ) (α : ℝ) : ℂ → ℂ :=
  fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z

/-- At most one `α` (mod `π`) has `S_α ∈ H(E)`. -/
theorem memHE_sAlpha_unique {E : ℂ → ℂ} (hE : IsHB E) {α β : ℝ}
    (hα : MemHE E (sAlpha E α)) (hβ : MemHE E (sAlpha E β)) :
    ∃ k : ℤ, β - α = k * Real.pi := by
  have hconst : ∀ z : ℂ, 0 < z.im →
      Complex.exp (I * α) * (sAlpha E α z / E z) - Complex.exp (I * β) * (sAlpha E β z / E z) =
        Complex.exp (2 * I * α) - Complex.exp (2 * I * β) := by
    intro z hz
    have hEz : E z ≠ 0 := hE.2.1 z hz
    simp only [sAlpha]
    have e1 : Complex.exp (I * α) * Complex.exp (-(I * α)) = 1 := by
      rw [← Complex.exp_add]; simp
    have e2 : Complex.exp (I * β) * Complex.exp (-(I * β)) = 1 := by
      rw [← Complex.exp_add]; simp
    have e3 : Complex.exp (2 * I * α) = Complex.exp (I * α) * Complex.exp (I * α) := by
      rw [← Complex.exp_add]; congr 1; ring
    have e4 : Complex.exp (2 * I * β) = Complex.exp (I * β) * Complex.exp (I * β) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [e3, e4]
    field_simp
    linear_combination (-(fstar E z)) * e1 + (fstar E z) * e2
  have hH2 : IsH2Upper (fun z ↦ Complex.exp (I * α) * (sAlpha E α z / E z) -
      Complex.exp (I * β) * (sAlpha E β z / E z)) :=
    (hα.2.1.const_mul _).sub (hβ.2.1.const_mul _)
  have hc : Complex.exp (2 * I * α) - Complex.exp (2 * I * β) = 0 :=
    IsH2Upper.const_eq_zero (hH2.congr hconst)
  have hexp : Complex.exp (2 * I * α) = Complex.exp (2 * I * β) := sub_eq_zero.mp hc
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨-k, ?_⟩
  have h4 : (I * 2) * (((β - α : ℝ) : ℂ) - ((-k : ℤ) : ℂ) * Real.pi) = 0 := by
    push_cast
    linear_combination (-1 : ℂ) * hk
  have h5 := (mul_eq_zero.mp h4).resolve_left (mul_ne_zero I_ne_zero two_ne_zero)
  have h6 : ((β - α : ℝ) : ℂ) = (((-k : ℤ) : ℝ) * Real.pi : ℝ) := by
    push_cast at h5 ⊢; linear_combination h5
  exact_mod_cast h6

/-! ## `H(E) = PW` forces `E` to be strict without real zeros -/

/-- If `H(E) = PW` (as sets), `E ∈ \overline{HB}` has no real zeros. -/
theorem HEEqPW.ne_zero_ofReal {E : ℂ → ℂ} (hE : IsHB E) (h : HEEqPW E) (x : ℝ) : E x ≠ 0 := by
  intro hx0
  obtain ⟨g, hg, hg0⟩ := exists_memPW_eval_ne_zero
  have hf : MemPW (fun z ↦ g (z - x)) := hg.comp_sub_ofReal x
  have hmem := (h.1 _).mpr hf
  refine not_isH2Upper_div_of_zero hE.1 hf.1 hE.2.1 hx0 ?_ hmem.2.1
  simp [hg0]

/-- If `H(E) = PW`, then `E ∈ \overline{HB}` is strict: `H(E) = {0}` when `E^* = cE`. -/
theorem HEEqPW.isStrictHB {E : ℂ → ℂ} (hE : IsHB E) (h : HEEqPW E) : IsStrictHB E := by
  rcases hE.isStrictHB_or_fstar_eq with hs | ⟨c, hc, hfc⟩
  · exact hs
  exfalso
  have hE0 : ∀ z : ℂ, E z ≠ 0 := by
    intro z
    rcases lt_trichotomy z.im 0 with hz | hz | hz
    · intro h0
      have h1 : E (conj z) ≠ 0 := hE.2.1 _ (by simp [hz])
      apply h1
      have := hfc z
      rw [h0, mul_zero] at this
      simpa [fstar] using this
    · have : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hz]
      rw [this]; exact HEEqPW.ne_zero_ofReal hE h _
    · exact hE.2.1 z hz
  obtain ⟨g, hg, hg0⟩ := exists_memPW_eval_ne_zero
  obtain ⟨-, ⟨-, C₁, h1⟩, ⟨-, C₂, h2⟩⟩ := (h.1 g).mpr hg
  set G : ℂ → ℂ := fun z ↦ g z / E z with hG
  have hGd : Differentiable ℂ G := fun z ↦ (hg.1 z).div (hE.1 z) (hE0 z)
  have hline : ∀ s : ℝ, s ≠ 0 → ∫⁻ x : ℝ, ‖G ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2 ≤ ((C₁ + C₂ : ℝ≥0) : ℝ≥0∞) := by
    intro s hs
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · have hle := h2 (-s) (by linarith)
      refine le_trans (le_of_eq ?_) (hle.trans (by push_cast; exact le_add_of_nonneg_left bot_le))
      refine lintegral_congr fun x ↦ ?_
      have hz : conj ((x : ℂ) + (s : ℂ) * I) = (x : ℂ) + ((-s : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp
      have hn1 : ‖E ((x : ℂ) + (s : ℂ) * I)‖ = ‖E (conj ((x : ℂ) + (s : ℂ) * I))‖ := by
        rw [← norm_fstar E, hfc, norm_mul, hc, one_mul]
      have hn2 : ‖g ((x : ℂ) + (s : ℂ) * I)‖ = ‖fstar g (conj ((x : ℂ) + (s : ℂ) * I))‖ := by
        rw [norm_fstar, Complex.conj_conj]
      have hnorm : ‖G ((x : ℂ) + (s : ℂ) * I)‖ =
          ‖fstar g ((x : ℂ) + ((-s : ℝ) : ℂ) * I) / E ((x : ℂ) + ((-s : ℝ) : ℂ) * I)‖ := by
        rw [hG]; simp only [norm_div]
        rw [hn1, hn2, hz]
      show ‖G ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2 =
        ‖fstar g ((x : ℂ) + ((-s : ℝ) : ℂ) * I) / E ((x : ℂ) + ((-s : ℝ) : ℂ) * I)‖ₑ ^ 2
      rw [← ofReal_norm, ← ofReal_norm, hnorm]
    · exact (h1 s hpos).trans (by push_cast; exact le_add_of_nonneg_right bot_le)
  have hz := eq_zero_of_lines_le hGd (K := ((C₁ + C₂ : ℝ≥0) : ℝ≥0∞)) ENNReal.coe_ne_top hline 0
  have : G 0 = 1 / E 0 := by simp [hG, hg0]
  rw [this] at hz
  exact one_div_ne_zero (hE0 0) hz

/-! ## `φ_E' |E|² ≃ 1` when `H(E) = PW` -/

/-- Lower bound: `φ_E'(x) |E(x)|² ≥ c > 0` on `ℝ` when `H(E) = PW`
(`c = π / (C₁ ‖g‖²_{PW})`, `C₁` the upper norm-equivalence constant, `g(0) = 1`). -/
theorem HEEqPW.phaseDeriv_mul_sq_ge (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hHB : IsHB E) (h : HEEqPW E) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, c ≤ phaseDeriv E x * ‖E x‖ ^ 2 := by
  sorry

/-- Upper bound: `φ_E'(x) |E(x)|² ≤ C` on `ℝ` when `H(E) = PW` (`C = π / c₁`, `c₁` the lower
norm-equivalence constant). -/
theorem HEEqPW.phaseDeriv_mul_sq_le (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hHB : IsHB E) (h : HEEqPW E) :
    ∃ C : ℝ, ∀ x : ℝ, phaseDeriv E x * ‖E x‖ ^ 2 ≤ C := by
  sorry

end FF
