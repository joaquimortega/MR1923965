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

/-- A phase function of `E` whose exceptional set `{x | S_{φ x} ∈ H(E)}` has dense complement. -/
theorem HEEqPW.exists_phase_data {E : ℂ → ℂ} (hHB : IsHB E) (h : HEEqPW E) :
    ∃ φ : ℝ → ℝ, IsPhaseFunction E φ ∧ StrictMono φ ∧
      Dense {x : ℝ | ¬ MemHE E (sAlpha E (φ x))} := by
  have hnz := HEEqPW.ne_zero_ofReal hHB h
  have hstrict := HEEqPW.isStrictHB hHB h
  obtain ⟨φ, hφ, -⟩ := exists_isPhaseFunction hHB.1 hnz
  have hmono := hφ.strictMono_of_isStrictHB hstrict hnz
  refine ⟨φ, hφ, hmono, ?_⟩
  set X : Set ℝ := {x : ℝ | MemHE E (sAlpha E (φ x))} with hX
  have hXc : X.Countable := by
    rcases X.eq_empty_or_nonempty with hempty | ⟨x₁, hx₁⟩
    · rw [hempty]; exact countable_empty
    · have hsub : X ⊆ ⋃ k : ℤ, φ ⁻¹' {φ x₁ + k * Real.pi} := by
        intro x hx
        obtain ⟨k, hk⟩ := memHE_sAlpha_unique hHB hx₁ hx
        simp only [mem_iUnion, mem_preimage, mem_singleton_iff]
        exact ⟨k, by linarith⟩
      refine Set.Countable.mono hsub (countable_iUnion fun k ↦ ?_)
      exact ((Set.subsingleton_singleton (a := φ x₁ + k * Real.pi)).preimage hmono.injective).countable
  exact Set.Countable.dense_compl ℝ hXc

/-- Lower bound: `φ_E'(x) |E(x)|² ≥ c > 0` on `ℝ` when `H(E) = PW`
(`c = π / (C₁ ‖g‖²_{PW})`, `C₁` the upper norm-equivalence constant, `g(0) = 1`). -/
theorem HEEqPW.phaseDeriv_mul_sq_ge (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hHB : IsHB E) (h : HEEqPW E) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, c ≤ phaseDeriv E x * ‖E x‖ ^ 2 := by
  have hnz := HEEqPW.ne_zero_ofReal hHB h
  have hstrict := HEEqPW.isStrictHB hHB h
  obtain ⟨φ, hφ, hmono, hdense⟩ := HEEqPW.exists_phase_data hHB h
  obtain ⟨c₀, hc₀, hev⟩ := pw_eval_lower
  obtain ⟨hset, c₁, C₁, hc₁, hnorm⟩ := h
  set κ : ℝ → ℝ := fun x ↦ phaseDeriv E x * ‖E x‖ ^ 2 with hκ
  have hκc : Continuous κ :=
    (continuous_phaseDeriv hHB.1 hnz).mul
      ((hHB.1.continuous.comp Complex.continuous_ofReal).norm.pow 2)
  have hκpos : ∀ x, 0 < κ x := fun x ↦
    mul_pos (hstrict.phaseDeriv_pos (hnz x)) (by have := norm_pos_iff.mpr (hnz x); positivity)
  have hgood : ∀ x₀ ∈ {x : ℝ | ¬ MemHE E (sAlpha E (φ x))}, Real.pi * c₀ ≤ C₁ * κ x₀ := by
    intro x₀ hx₀
    have hTE := hE E hstrict hnz φ hφ (φ x₀) hx₀
    have hmem : x₀ ∈ phaseLevel φ (φ x₀) := ⟨0, by simp⟩
    obtain ⟨f, hf, hfc, hf0, hftop⟩ := hev x₀
    have hfH : MemHE E f := (hset f).mpr hf
    have h1 := hTE.1 f hfH
    have h2 : orthWeight E x₀ * ‖f x₀‖ₑ ^ 2 ≤ heNormSq E f := by
      rw [h1]
      exact ENNReal.le_tsum (f := fun γ : phaseLevel φ (φ x₀) ↦ orthWeight E γ * ‖f γ‖ₑ ^ 2)
        ⟨x₀, hmem⟩
    have h3 := (hnorm f hf).2
    have hw : orthWeight E x₀ = ENNReal.ofReal (Real.pi / κ x₀) := rfl
    have h4 : (orthWeight E x₀ * c₀) * pwNormSq f ≤ C₁ * pwNormSq f := by
      calc (orthWeight E x₀ * c₀) * pwNormSq f = orthWeight E x₀ * (c₀ * pwNormSq f) := by ring
        _ ≤ orthWeight E x₀ * ‖f x₀‖ₑ ^ 2 := by gcongr
        _ ≤ heNormSq E f := h2
        _ ≤ C₁ * pwNormSq f := h3
    have h5 := (ENNReal.mul_le_mul_iff_left hf0 hftop).mp h4
    rw [hw, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by have := hκpos x₀; positivity),
      ← ENNReal.ofReal_coe_nnreal (p := C₁), ENNReal.ofReal_le_ofReal_iff C₁.coe_nonneg] at h5
    have hk := hκpos x₀
    rw [div_mul_eq_mul_div, div_le_iff₀ hk] at h5
    linarith
  have hclosed : IsClosed {x : ℝ | Real.pi * c₀ ≤ C₁ * κ x} :=
    isClosed_le continuous_const (continuous_const.mul hκc)
  have hall : ∀ x, Real.pi * c₀ ≤ C₁ * κ x := by
    intro x
    have : closure {x : ℝ | ¬ MemHE E (sAlpha E (φ x))} ⊆ {x : ℝ | Real.pi * c₀ ≤ C₁ * κ x} :=
      closure_minimal hgood hclosed
    rw [hdense.closure_eq] at this
    exact this (mem_univ x)
  have hC₁ : 0 < (C₁ : ℝ) := by
    by_contra hle
    have h0 : (C₁ : ℝ) = 0 := le_antisymm (not_lt.mp hle) C₁.coe_nonneg
    have := hall 0
    rw [h0, zero_mul] at this
    have hc0 : (0 : ℝ) < c₀ := hc₀
    nlinarith [Real.pi_pos]
  refine ⟨Real.pi * c₀ / C₁, by positivity, fun x ↦ ?_⟩
  rw [div_le_iff₀ hC₁]
  have := hall x
  show _ ≤ κ x * (C₁ : ℝ) 
  linarith

/-- Upper bound: `φ_E'(x) |E(x)|² ≤ C` on `ℝ` when `H(E) = PW` (`C = π / c₁`, `c₁` the lower
norm-equivalence constant). -/
theorem HEEqPW.phaseDeriv_mul_sq_le (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hHB : IsHB E) (h : HEEqPW E) :
    ∃ C : ℝ, ∀ x : ℝ, phaseDeriv E x * ‖E x‖ ^ 2 ≤ C := by
  have hnz := HEEqPW.ne_zero_ofReal hHB h
  have hstrict := HEEqPW.isStrictHB hHB h
  obtain ⟨φ, hφ, hmono, hdense⟩ := HEEqPW.exists_phase_data hHB h
  obtain ⟨hset, c₁, C₁, hc₁, hnorm⟩ := h
  set κ : ℝ → ℝ := fun x ↦ phaseDeriv E x * ‖E x‖ ^ 2 with hκ
  have hκc : Continuous κ :=
    (continuous_phaseDeriv hHB.1 hnz).mul
      ((hHB.1.continuous.comp Complex.continuous_ofReal).norm.pow 2)
  have hκpos : ∀ x, 0 < κ x := fun x ↦
    mul_pos (hstrict.phaseDeriv_pos (hnz x)) (by have := norm_pos_iff.mpr (hnz x); positivity)
  have hgood : ∀ x₀ ∈ {x : ℝ | ¬ MemHE E (sAlpha E (φ x))}, κ x₀ ≤ Real.pi / c₁ := by
    intro x₀ hx₀
    have hTE := hE E hstrict hnz φ hφ (φ x₀) hx₀
    have hmem : x₀ ∈ phaseLevel φ (φ x₀) := ⟨0, by simp⟩
    set a : ℝ → ℂ := fun γ ↦ if γ = x₀ then 1 else 0 with ha
    have hw : orthWeight E x₀ = ENNReal.ofReal (Real.pi / κ x₀) := rfl
    have hsum : ∑' γ : phaseLevel φ (φ x₀), orthWeight E γ * ‖a γ‖ₑ ^ 2 = orthWeight E x₀ := by
      rw [tsum_eq_single ⟨x₀, hmem⟩]
      · simp [ha]
      · intro γ hγ
        have : (γ : ℝ) ≠ x₀ := fun h' ↦ hγ (Subtype.ext h')
        simp [ha, this]
    have hfin : ∑' γ : phaseLevel φ (φ x₀), orthWeight E γ * ‖a γ‖ₑ ^ 2 < ⊤ := by
      rw [hsum, hw]; exact ENNReal.ofReal_lt_top
    obtain ⟨f, hfH, hfa⟩ := hTE.2 a hfin
    have hf := (hset f).mp hfH
    have h1 : heNormSq E f = orthWeight E x₀ := by
      rw [hTE.1 f hfH, ← hsum]
      refine tsum_congr fun γ ↦ ?_
      rw [hfa γ γ.2]
    have hpt := pw_norm_sq_le hPW hf x₀
    have hfx : f x₀ = 1 := by have := hfa x₀ hmem; simpa [ha] using this
    rw [hfx] at hpt
    simp only [Complex.ofReal_im, abs_zero, mul_zero, Real.exp_zero, one_mul, norm_one,
      one_pow] at hpt
    have hpw1 : (1 : ℝ≥0∞) ≤ pwNormSq f := by
      have := pwNormSq_ne_top hf
      rw [← ENNReal.ofReal_toReal this]
      simpa using ENNReal.ofReal_le_ofReal hpt
    have h2 : (c₁ : ℝ≥0∞) ≤ orthWeight E x₀ := by
      calc (c₁ : ℝ≥0∞) = c₁ * 1 := (mul_one _).symm
        _ ≤ c₁ * pwNormSq f := by gcongr
        _ ≤ heNormSq E f := (hnorm f hf).1
        _ = _ := h1
    rw [hw, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff (by have := hκpos x₀; positivity)] at h2
    have hk := hκpos x₀
    have hc : (0 : ℝ) < c₁ := hc₁
    rw [le_div_iff₀ hk] at h2
    rw [le_div_iff₀ hc]
    linarith
  have hclosed : IsClosed {x : ℝ | κ x ≤ Real.pi / c₁} :=
    isClosed_le hκc continuous_const
  refine ⟨Real.pi / c₁, fun x ↦ ?_⟩
  have : closure {x : ℝ | ¬ MemHE E (sAlpha E (φ x))} ⊆ {x : ℝ | κ x ≤ Real.pi / c₁} :=
    closure_minimal hgood hclosed
  rw [hdense.closure_eq] at this
  exact this (mem_univ x)

end FF
