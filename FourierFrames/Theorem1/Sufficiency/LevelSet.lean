import FourierFrames.HB.DeBranges
import FourierFrames.PW.PlancherelPolya

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF
namespace Suff

/-- The termwise bound in `levelSet_ineq`. -/
theorem orth_term_le {pE pG nE nG c1 : ℝ} (hc1 : 0 < c1) (hnG : 0 < nG) (hnE : 0 < nE)
    (hpG : 0 ≤ pG) (h : c1 ≤ pE * nE ^ 2) :
    Real.pi / ((pE + pG) * (nE * nG) ^ 2) * nG ^ 2 ≤ Real.pi / c1 := by
  have hπ := Real.pi_pos
  have hd : c1 * nG ^ 2 ≤ (pE + pG) * (nE * nG) ^ 2 := by
    have h1 : 0 ≤ pG * nE ^ 2 * nG ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg nG)]
  have hpos : 0 < c1 * nG ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (lt_of_lt_of_le hpos hd) hc1]
  have : Real.pi * nG ^ 2 * c1 ≤ Real.pi * ((pE + pG) * (nE * nG) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hd hπ.le]
  exact this


theorem levelSet_ineq_aux (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) :
    ∃ C₀ : ℝ≥0, 0 < C₀ ∧ ∀ G : ℂ → ℂ, IsHB G → (∀ x : ℝ, G x ≠ 0) → ∀ ψ : ℝ → ℝ,
      IsPhaseFunction (fun z ↦ E z * G z) ψ → ∀ α : ℝ,
        ¬ MemHE (fun z ↦ E z * G z) (sAlpha (fun z ↦ E z * G z) α) → ∀ f : ℂ → ℂ, MemPW f →
          pwNormSq f ≤ C₀ * sampleSum (phaseLevel ψ α) f := by
  have hπ := Real.pi_pos
  have hstrict : IsStrictHB E := HEEqPW.isStrictHB hEHB hEPW
  have hE0 : ∀ x : ℝ, E x ≠ 0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  obtain ⟨c, C, hc, hcC⟩ := hEPW.2
  obtain ⟨c1, hc1, hc1le⟩ := HEEqPW.phaseDeriv_mul_sq_ge hPW hE hEHB hEPW
  have hc0 : (c : ℝ≥0) ≠ 0 := hc.ne'
  refine ⟨c⁻¹ * Real.toNNReal (Real.pi / c1), ?_, ?_⟩
  · exact mul_pos (inv_pos.mpr hc) (Real.toNNReal_pos.mpr (div_pos hπ hc1))
  intro G hGHB hG0 ψ hψ α hα f hf
  have hstrict' : IsStrictHB (fun z ↦ E z * G z) := hstrict.mul_isHB hGHB
  have hE'0 : ∀ x : ℝ, E x * G x ≠ 0 := fun x ↦ mul_ne_zero (hE0 x) (hG0 x)
  have hfHE : MemHE E f := (hEPW.1 f).mpr hf
  have hg : MemHE (fun z ↦ E z * G z) (fun z ↦ G z * f z) := MemHE.mul_isHB hGHB hfHE
  have hnorm : heNormSq (fun z ↦ E z * G z) (fun z ↦ G z * f z) = heNormSq E f :=
    heNormSq_mul hGHB
  have hTE := (hE _ hstrict' hE'0 ψ hψ α hα).1 _ hg
  -- termwise bound
  have hterm : ∀ γ : phaseLevel ψ α, orthWeight (fun z ↦ E z * G z) γ * ‖(G (γ : ℝ) * f (γ : ℝ))‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.pi / c1) * ‖f ((γ : ℝ) : ℂ)‖ₑ ^ 2 := by
    intro γ
    set x : ℝ := (γ : ℝ)
    have hpd : phaseDeriv (fun z ↦ E z * G z) x = phaseDeriv E x + phaseDeriv G x :=
      phaseDeriv_mul hEHB.1 hGHB.1 (hE0 x) (hG0 x)
    have hpG : 0 ≤ phaseDeriv G x := hGHB.phaseDeriv_nonneg (hG0 x)
    have hnE : 0 < ‖E x‖ := norm_pos_iff.mpr (hE0 x)
    have hnG : 0 < ‖G x‖ := norm_pos_iff.mpr (hG0 x)
    have hle := orth_term_le (pE := phaseDeriv E x) (pG := phaseDeriv G x) hc1 hnG hnE hpG
      (hc1le x)
    unfold orthWeight
    rw [hpd, norm_mul]
    have e1 : ‖(G x * f x : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (‖G x‖ ^ 2) * ‖f x‖ₑ ^ 2 := by
      rw [enorm_mul, mul_pow, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    have hpE : 0 < phaseDeriv E x := by
      have := hc1le x
      by_contra h
      rw [not_lt] at h
      nlinarith [sq_nonneg ‖E x‖]
    rw [e1, ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hπ.le
      (mul_nonneg (add_nonneg hpE.le hpG) (sq_nonneg _)))]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hle) le_rfl
  have hsum : heNormSq E f ≤ ENNReal.ofReal (Real.pi / c1) * sampleSum (phaseLevel ψ α) f := by
    rw [← hnorm, hTE, sampleSum, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hterm
  have hlow : (c : ℝ≥0∞) * pwNormSq f ≤ heNormSq E f := (hcC f hf).1
  have hcinv : (c : ℝ≥0∞)⁻¹ * (c * pwNormSq f) = pwNormSq f := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hc0) ENNReal.coe_ne_top, one_mul]
  calc pwNormSq f = (c : ℝ≥0∞)⁻¹ * (c * pwNormSq f) := hcinv.symm
    _ ≤ (c : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (Real.pi / c1) * sampleSum (phaseLevel ψ α) f) :=
        mul_le_mul' le_rfl (hlow.trans hsum)
    _ = ((c⁻¹ * Real.toNNReal (Real.pi / c1) : ℝ≥0) : ℝ≥0∞) * sampleSum (phaseLevel ψ α) f := by
        rw [ENNReal.coe_mul, ENNReal.coe_inv hc0, mul_assoc]
        rfl


theorem orthWeight_le {E : ℂ → ℂ} {c1 : ℝ} (hc1 : 0 < c1)
    (h : ∀ x : ℝ, c1 ≤ phaseDeriv E x * ‖E x‖ ^ 2) (x : ℝ) :
    orthWeight E x ≤ ENNReal.ofReal (Real.pi / c1) := by
  unfold orthWeight
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_left Real.pi_pos.le hc1 (h x)

/-- The Theorem E set-up for `H(E) = PW`: the bounds on the data of the orthogonal sampling
formula. -/
theorem levelSet_data_aux (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {α : ℝ}
    (hα : ¬ MemHE E (sAlpha E α)) :
    ∃ K : ℝ, ∀ γ ∈ phaseLevel φ α, ∃ f : ℂ → ℂ, MemPW f ∧ f γ = 1 ∧
      (∀ γ' ∈ phaseLevel φ α, γ' ≠ γ → f γ' = 0) ∧ (pwNormSq f).toReal ≤ K := by
  classical
  have hπ := Real.pi_pos
  have hstrict : IsStrictHB E := HEEqPW.isStrictHB hEHB hEPW
  have hE0 : ∀ x : ℝ, E x ≠ 0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  obtain ⟨c, C, hc, hcC⟩ := hEPW.2
  obtain ⟨c1, hc1, hc1le⟩ := HEEqPW.phaseDeriv_mul_sq_ge hPW hE hEHB hEPW
  have hTE := hE E hstrict hE0 φ hφ α hα
  refine ⟨Real.pi / (c1 * c), fun γ hγ ↦ ?_⟩
  let a : ℝ → ℂ := fun x ↦ if x = γ then 1 else 0
  have hsum : ∑' x : phaseLevel φ α, orthWeight E x * ‖a x‖ₑ ^ 2 = orthWeight E γ := by
    rw [tsum_eq_single (⟨γ, hγ⟩ : phaseLevel φ α)]
    · simp [a]
    · intro b hb
      have : (b : ℝ) ≠ γ := fun h ↦ hb (Subtype.ext h)
      simp [a, this]
  have hfin : orthWeight E γ ≤ ENNReal.ofReal (Real.pi / c1) := orthWeight_le hc1 hc1le γ
  obtain ⟨f, hfHE, hfa⟩ := hTE.2 a (by rw [hsum]; exact lt_of_le_of_lt hfin ENNReal.ofReal_lt_top)
  have hnorm := hTE.1 f hfHE
  have hnorm' : heNormSq E f = orthWeight E γ := by
    rw [hnorm]
    have : ∀ x : phaseLevel φ α, orthWeight E x * ‖f x‖ₑ ^ 2 = orthWeight E x * ‖a x‖ₑ ^ 2 := by
      intro x; rw [hfa x x.2]
    rw [tsum_congr this, hsum]
  have hfPW : MemPW f := (hEPW.1 f).mp hfHE
  refine ⟨f, hfPW, ?_, ?_, ?_⟩
  · rw [hfa γ hγ]; simp [a]
  · intro γ' hγ' hne
    rw [hfa γ' hγ']; simp [a, hne]
  · have hlow : (c : ℝ≥0∞) * pwNormSq f ≤ ENNReal.ofReal (Real.pi / c1) :=
      ((hcC f hfPW).1.trans hnorm'.le).trans hfin
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlow
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_pos hπ hc1).le] at this
    simp only [ENNReal.coe_toReal] at this
    have hcR : (0 : ℝ) < c := hc
    have h2 : (pwNormSq f).toReal * (c1 * c) ≤ Real.pi := by
      have h3 := mul_le_mul_of_nonneg_left this hc1.le
      rw [mul_div_cancel₀ _ hc1.ne'] at h3
      nlinarith
    exact (le_div_iff₀ (mul_pos hc1 hcR)).mpr h2


theorem levelSet_separated_aux (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {α : ℝ}
    (hα : ¬ MemHE E (sAlpha E α)) : IsSeparated (phaseLevel φ α) := by
  obtain ⟨K, hK⟩ := levelSet_data_aux hPW hE hEHB hEPW hφ hα
  set Θ : ℝ := Real.sqrt ((Real.pi * Real.exp 1) ^ 2 * max K 0) with hΘ
  have hΘ0 : 0 ≤ Θ := Real.sqrt_nonneg _
  refine ⟨1 / (Θ + 1), by positivity, ?_⟩
  intro γ hγ γ' hγ' hne
  obtain ⟨f, hf, hf1, hf0, hfK⟩ := hK γ hγ
  have hf0' := hf0 γ' hγ' (Ne.symm hne)
  have hder : ∀ t : ℝ, ‖deriv f t‖ ≤ Θ := by
    intro t
    have h1 := pw_deriv_bound hPW hf t
    have h2 : ‖deriv f t‖ ^ 2 ≤ (Real.pi * Real.exp 1) ^ 2 * max K 0 :=
      h1.trans (mul_le_mul_of_nonneg_left (hfK.trans (le_max_left _ _)) (sq_nonneg _))
    have := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hd : ∀ t : ℝ, HasDerivAt (fun y : ℝ ↦ f (y : ℂ)) (deriv f t) t := fun t ↦
    ((hf.1 (t : ℂ)).hasDerivAt).comp_ofReal
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := Set.univ)
    (f := fun y : ℝ ↦ f (y : ℂ)) (f' := fun t ↦ deriv f t) (C := Θ)
    (fun t _ ↦ (hd t).hasDerivWithinAt) (fun t _ ↦ hder t) convex_univ (Set.mem_univ γ)
    (Set.mem_univ γ')
  simp only [hf1, hf0', zero_sub, norm_neg, norm_one, Real.norm_eq_abs] at hmvt
  have h3 : 1 ≤ (Θ + 1) * |γ - γ'| := by
    rw [abs_sub_comm]
    nlinarith [abs_nonneg (γ' - γ)]
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem levelSet_cis_aux (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {α : ℝ}
    (hα : ¬ MemHE E (sAlpha E α)) : IsCompleteInterpolating (phaseLevel φ α) := by
  have hπ := Real.pi_pos
  have hstrict : IsStrictHB E := HEEqPW.isStrictHB hEHB hEPW
  have hE0 : ∀ x : ℝ, E x ≠ 0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  obtain ⟨c, C, hc, hcC⟩ := hEPW.2
  obtain ⟨c1, hc1, hc1le⟩ := HEEqPW.phaseDeriv_mul_sq_ge hPW hE hEHB hEPW
  have hTE := hE E hstrict hE0 φ hφ α hα
  intro a ha
  have hlt : ∑' x : phaseLevel φ α, orthWeight E x * ‖a x‖ₑ ^ 2 < ∞ := by
    calc ∑' x : phaseLevel φ α, orthWeight E x * ‖a x‖ₑ ^ 2
        ≤ ∑' x : phaseLevel φ α, ENNReal.ofReal (Real.pi / c1) * ‖a x‖ₑ ^ 2 :=
          ENNReal.tsum_le_tsum fun x ↦ mul_le_mul' (orthWeight_le hc1 hc1le x) le_rfl
      _ = ENNReal.ofReal (Real.pi / c1) * ∑' x : phaseLevel φ α, ‖a x‖ₑ ^ 2 :=
          ENNReal.tsum_mul_left
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ha
  obtain ⟨f, hfHE, hfa⟩ := hTE.2 a hlt
  refine ⟨f, ⟨(hEPW.1 f).mp hfHE, hfa⟩, ?_⟩
  rintro g ⟨hg, hga⟩
  -- uniqueness: `g - f` vanishes on `Γ`
  have hgf : MemPW (g - f) := MemPW.sub hg ((hEPW.1 f).mp hfHE)
  have hHE : MemHE E (g - f) := (hEPW.1 _).mpr hgf
  have hzero : heNormSq E (g - f) = 0 := by
    rw [hTE.1 _ hHE]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    have : (g - f) (x : ℝ) = 0 := by
      simp only [Pi.sub_apply]
      rw [hga x x.2, hfa x x.2, sub_self]
    rw [this]; simp
  have hp : pwNormSq (g - f) = 0 := by
    have := (hcC _ hgf).1
    rw [hzero, nonpos_iff_eq_zero, mul_eq_zero] at this
    rcases this with h | h
    · exact absurd (by exact_mod_cast h) hc.ne'
    · exact h
  have := MemPW.eq_zero_of_pwNormSq_eq_zero hgf hp
  funext z
  have := congrFun this z
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

end Suff
end FF
