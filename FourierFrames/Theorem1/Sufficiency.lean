import FourierFrames.HB.DeBranges
import FourierFrames.PW.PlancherelPolya
import FourierFrames.Theorem1.Sufficiency.Interlace
import FourierFrames.Theorem1.Sufficiency.Limit
import FourierFrames.Theorem1.Sufficiency.LevelSet
import FourierFrames.Theorem1.Sufficiency.Phase
import FourierFrames.Theorem1.Sufficiency.RealFactor.Main

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF

/-!
# M04 — Theorem 1, sufficiency (pp. 795–797)

See `blueprint/M04_Sufficiency.md`.
-/

/-! ## Helpers on separation, sampling sums and exceptional levels -/

namespace Suff

/-- `α` is *exceptional* for `E`: `e^{iα}E - e^{-iα}E^* ∈ H(E)` (the hypothesis of Theorem E fails). -/
def Exceptional (E : ℂ → ℂ) (α : ℝ) : Prop :=
  MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z)

/-- Splitting a sampling sum into a bounded and an unbounded part. -/
theorem sampleSum_split (Λ : Set ℝ) (f : ℂ → ℂ) (R : ℝ) :
    sampleSum Λ f =
      sampleSum (Λ ∩ {x : ℝ | |x| < R}) f + sampleSum (Λ ∩ {x : ℝ | R ≤ |x|}) f := by
  rw [sampleSum_eq_tsum_indicator, sampleSum_eq_tsum_indicator, sampleSum_eq_tsum_indicator,
    ← ENNReal.tsum_add]
  congr 1
  ext x
  by_cases hΛ : x ∈ Λ <;> by_cases hR : |x| < R <;>
    simp [Set.indicator, hΛ, hR, not_le.mpr, not_lt.mp]

theorem phaseLevel_add_pi (φ : ℝ → ℝ) (α : ℝ) :
    phaseLevel φ (α + Real.pi) = phaseLevel φ α := by
  ext x
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rw [hk]; push_cast; ring⟩
  · rintro ⟨k, hk⟩
    exact ⟨k - 1, by rw [hk]; push_cast; ring⟩

/-- **Interlacing** (p. 796): if the level set `Λ = {φ ∈ π/2 + πℤ}` of a continuous strictly
increasing `φ` is `δ`-separated, then `{φ ∈ π/2 + ε + πℤ}` (`0 < ε < π`) is a union of two
`δ`-separated sets (even and odd index). -/
theorem phaseLevel_sepBy_two {φ : ℝ → ℝ} (hc : Continuous φ) (hφ : StrictMono φ) {δ : ℝ}
    (hsep : IsSepBy δ (phaseLevel φ (Real.pi / 2))) {ε : ℝ} (hε0 : 0 < ε) (hεπ : ε < Real.pi) :
    ∃ A B : Set ℝ, phaseLevel φ (Real.pi / 2 + ε) = A ∪ B ∧ IsSepBy δ A ∧ IsSepBy δ B :=
  phaseLevel_sepBy_two_aux hc hφ hsep hε0 hεπ

/-- At most one `n` has `π/2 + π/(n+2)` exceptional, so eventually none has. -/
theorem eventually_not_exceptional {E : ℂ → ℂ} (hE : IsStrictHB E) :
    ∀ᶠ n : ℕ in atTop, ¬ Exceptional E (Real.pi / 2 + Real.pi / (n + 2)) := by
  have hπ := Real.pi_pos
  have hsub : {n : ℕ | Exceptional E (Real.pi / 2 + Real.pi / (n + 2))}.Subsingleton := by
    intro n hn m hm
    obtain ⟨k, hk⟩ := memHE_sAlpha_unique hE.1 hn hm
    have hn2 : (0 : ℝ) < n + 2 := by positivity
    have hm2 : (0 : ℝ) < m + 2 := by positivity
    have h1 : 1 / ((m : ℝ) + 2) - 1 / ((n : ℝ) + 2) = k := by
      have : Real.pi * (1 / ((m : ℝ) + 2) - 1 / ((n : ℝ) + 2)) = Real.pi * k := by
        rw [mul_comm Real.pi (k : ℝ), ← hk]; field_simp; ring
      exact mul_left_cancel₀ hπ.ne' this
    have hb1 : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
    have hb2 : 1 / ((m : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hb3 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hb4 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hk0 : k = 0 := by
      have h5 : (k : ℝ) < 1 := by linarith
      have h6 : (-1 : ℝ) < k := by linarith
      have h5' : k < 1 := by exact_mod_cast h5
      have h6' : -1 < k := by exact_mod_cast h6
      omega
    rw [hk0] at h1
    simp only [Int.cast_zero] at h1
    have : (n : ℝ) + 2 = m + 2 := by
      have := sub_eq_zero.mp h1
      field_simp at this; linarith
    exact_mod_cast (by linarith : (n : ℝ) = m)
  have hfin := hsub.finite
  rw [← Nat.cofinite_eq_atTop]
  exact hfin.eventually_cofinite_notMem

theorem exists_not_exceptional {E : ℂ → ℂ} (hE : IsStrictHB E) :
    ∃ α : ℝ, ¬ MemHE E (sAlpha E α) := by
  obtain ⟨n, hn⟩ := (eventually_not_exceptional hE).exists
  exact ⟨_, hn⟩

/-- `ψ_G = φ_E + φ_F` is a phase function of `EF`. -/
theorem isPhaseFunction_mul {E F : ℂ → ℂ} {φ ψ : ℝ → ℝ} (hφ : IsPhaseFunction E φ)
    (hψ : IsPhaseFunction F ψ) :
    IsPhaseFunction (fun z ↦ E z * F z) (fun x ↦ φ x + ψ x) := by
  refine ⟨hφ.1.add hψ.1, fun x ↦ ?_⟩
  have h1 := hφ.2 x
  have h2 := hψ.2 x
  calc E x * F x = ((‖E x‖ : ℂ) * Complex.exp (-(I * φ x))) *
        ((‖F x‖ : ℂ) * Complex.exp (-(I * ψ x))) := by rw [← h1, ← h2]
    _ = ((‖E x * F x‖ : ℝ) : ℂ) * Complex.exp (-(I * ((φ x + ψ x : ℝ) : ℂ))) := by
      rw [norm_mul]
      push_cast
      rw [mul_add, neg_add, Complex.exp_add]
      ring

/-! ## The limit `α → π/2` (p. 797) -/

/-- **The limit argument** (README §3.5): if `{φ ∈ π/2 + πℤ}` is `δ`-separated, `φ` is a
continuous increasing bijection of `ℝ`, and `‖f‖² ≤ C₀ ∑_{Λ_{α_n}} |f|²` for all `f ∈ PW` and
all `n` large, with `α_n = π/2 + ε_n`, `0 < ε_n < π`, `ε_n → 0`, then the same inequality holds for
`Λ = Λ_{π/2}`. -/
theorem levelSet_limit (hPW : PaleyWienerThm) {ψ : ℝ → ℝ} (hψc : Continuous ψ)
    (hψm : StrictMono ψ) (hψs : Function.Surjective ψ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : IsSepBy δ (phaseLevel ψ (Real.pi / 2))) {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hεπ : ∀ n, ε n < Real.pi)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hlev : ∀ᶠ n in atTop, ∀ f : ℂ → ℂ, MemPW f →
      pwNormSq f ≤ C₀ * sampleSum (phaseLevel ψ (Real.pi / 2 + ε n)) f) :
    ∀ f : ℂ → ℂ, MemPW f → pwNormSq f ≤ C₀ * sampleSum (phaseLevel ψ (Real.pi / 2)) f :=
  levelSet_limit_aux hPW hψc hψm hψs hδ hsep hC₀ hε0 hεπ hεlim hlev

/-! ## Removing the real zeros of `F` (p. 795) -/

/-- **Weierstrass factorisation of the real zeros** (new lemma, `S` of the paper): an entire
`F ∈ \overline{HB}`, `F ≢ 0`, factors as `F = S G` with `S` real entire (`S^* = S`) whose zeros are
exactly the real zeros of `F` (with multiplicity), and `G ∈ \overline{HB}` without real zeros.
Needs Weierstrass products of non-constant genus (not in Mathlib); see the blueprint. -/
theorem exists_realFactor {F : ℂ → ℂ} (hF : IsHB F) (hF0 : ∃ z, F z ≠ 0) :
    ∃ S G : ℂ → ℂ, Differentiable ℂ S ∧ IsHB G ∧ (∀ z, F z = S z * G z) ∧
      (∀ z, fstar S z = S z) ∧ (∀ z, S z = 0 → z.im = 0) ∧ (∀ x : ℝ, G x ≠ 0) :=
  exists_realFactor_aux hF hF0

/-- The reduction of p. 795: `F` can be replaced by `G` without real zeros, at the price of
shrinking `Λ`. -/
theorem exists_noRealZero_hb {E F : ℂ → ℂ} {Λ : Set ℝ} (hEHB : IsHB E) (hFHB : IsHB F)
    (hzero : ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ)) :
    ∃ G : ℂ → ℂ, IsHB G ∧ (∀ x : ℝ, G x ≠ 0) ∧
      ∀ z : ℂ, E z * G z + fstar E z * fstar G z = 0 → ∃ x ∈ Λ, z = (x : ℂ) := by
  have _ := hEHB -- (not needed: `S` and `G` come from `F` alone)
  have hF0 : ∃ z, F z ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : E I * F I + fstar E I * fstar F I = 0 := by
      have : fstar F I = 0 := by simp [fstar, h]
      simp [h]
    obtain ⟨x, -, hx⟩ := (hzero I).mp h0
    have := congrArg Complex.im hx
    simp at this
  obtain ⟨S, G, -, hGHB, hFSG, hS, -, hG0⟩ := exists_realFactor hFHB hF0
  refine ⟨G, hGHB, hG0, fun z hz ↦ (hzero z).mp ?_⟩
  have h1 : fstar F z = S z * fstar G z := by
    have : fstar F = fun z ↦ fstar S z * fstar G z := by
      rw [← fstar_mul]; congr 1; funext w; exact hFSG w
    rw [this]; simp only [hS z]
  rw [hFSG z, h1]
  linear_combination S z * hz

end Suff

open Suff

/-! ## Consequences of `H(E) = PW` through Theorem E -/

/-- Theorem E gives the uniform inequality `‖f‖² ≤ C₀ ∑_{Λ_α} |f|²` for `EG`, `G ∈ \overline{HB}`
without real zeros, for every non-exceptional `α`, with `C₀` depending only on `E`. -/
theorem HEEqPW.levelSet_ineq (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) :
    ∃ C₀ : ℝ≥0, 0 < C₀ ∧ ∀ G : ℂ → ℂ, IsHB G → (∀ x : ℝ, G x ≠ 0) → ∀ ψ : ℝ → ℝ,
      IsPhaseFunction (fun z ↦ E z * G z) ψ → ∀ α : ℝ,
        ¬ Exceptional (fun z ↦ E z * G z) α → ∀ f : ℂ → ℂ, MemPW f →
          pwNormSq f ≤ C₀ * sampleSum (phaseLevel ψ α) f :=
  levelSet_ineq_aux hPW hE hEHB hEPW

/-- For `H(E) = PW` and `α` non-exceptional for `E`, `Γ_α = {φ_E ∈ α + πℤ}` is separated
(README §3.8). -/
theorem HEEqPW.levelSet_separated (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {α : ℝ}
    (hα : ¬ Exceptional E α) : IsSeparated (phaseLevel φ α) :=
  levelSet_separated_aux hPW hE hEHB hEPW hφ hα

/-- For `H(E) = PW` and `α` non-exceptional, `Γ_α` is a complete interpolating sequence. -/
theorem HEEqPW.levelSet_cis (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {α : ℝ}
    (hα : ¬ Exceptional E α) : IsCompleteInterpolating (phaseLevel φ α) :=
  levelSet_cis_aux hPW hE hEHB hEPW hφ hα

/-- If `H(E) = PW`, the phase of `E` is unbounded in both directions (so `Γ_α` is infinite on both
sides). -/
theorem HEEqPW.phase_tendsto (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ)
    (hφ' : ∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x) :
    Tendsto φ atTop atTop ∧ Tendsto φ atBot atBot :=
  phase_tendsto_aux hPW hE hEHB hEPW hφ hφ'
    (exists_not_exceptional (HEEqPW.isStrictHB hEHB hEPW))

/-- The phase `ψ = φ_E + φ_G` of `EG` is a continuous increasing bijection of `ℝ`
(`G ∈ \overline{HB}` without real zeros, `H(E) = PW`). -/
theorem HEEqPW.phase_mul_bijective (hPW : PaleyWienerThm) (hE : TheoremE) {E G : ℂ → ℂ}
    (hEHB : IsHB E) (hGHB : IsHB G) (hEPW : HEEqPW E) (hG0 : ∀ x : ℝ, G x ≠ 0)
    {φE φG : ℝ → ℝ} (hφE : IsPhaseFunction E φE) (hφE' : ∀ x : ℝ, HasDerivAt φE (phaseDeriv E x) x)
    (hφG : IsPhaseFunction G φG) (hφG' : ∀ x : ℝ, HasDerivAt φG (phaseDeriv G x) x) :
    StrictMono (fun x ↦ φE x + φG x) ∧ Function.Surjective (fun x ↦ φE x + φG x) :=
  phase_mul_bijective_aux hPW hE hEHB hGHB hEPW hG0 hφE hφE' hφG hφG'
    (exists_not_exceptional (HEEqPW.isStrictHB hEHB hEPW))

/-! ## Theorem 1, sufficiency (p. 795–797) -/

/-- **Theorem 1** (p. 795), sufficiency. -/
theorem theorem1_sufficiency (hPW : PaleyWienerThm) (hE : TheoremE)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) {E F : ℂ → ℂ} (hEHB : IsHB E) (hFHB : IsHB F)
    (hEPW : HEEqPW E) (hzero : ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ)) :
    IsSampling Λ := by
  have hπ := Real.pi_pos
  have hstrict : IsStrictHB E := HEEqPW.isStrictHB hEHB hEPW
  have hE0 : ∀ x : ℝ, E x ≠ 0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  obtain ⟨G, hGHB, hG0, hGΛ⟩ := exists_noRealZero_hb hEHB hFHB hzero
  obtain ⟨φE, hφE, hφE'⟩ := exists_isPhaseFunction hEHB.1 hE0
  obtain ⟨φG, hφG, hφG'⟩ := exists_isPhaseFunction hGHB.1 hG0
  have hψ : IsPhaseFunction (fun z ↦ E z * G z) (fun x ↦ φE x + φG x) :=
    isPhaseFunction_mul hφE hφG
  obtain ⟨hψm, hψs⟩ := HEEqPW.phase_mul_bijective hPW hE hEHB hGHB hEPW hG0 hφE hφE' hφG hφG'
  obtain ⟨δ, hδ, hsep⟩ := hΛ
  have hsub : phaseLevel (fun x ↦ φE x + φG x) (Real.pi / 2) ⊆ Λ := by
    intro x hx
    have h1 : (x : ℂ) ∈ Complex.ofReal '' phaseLevel (fun t ↦ φE t + φG t) (Real.pi / 2) :=
      ⟨x, hx, rfl⟩
    have h2 := (zero_set_eq_phaseLevel hstrict hGHB hE0 hG0 hφE hφG (x : ℂ)).mpr h1
    obtain ⟨y, hy, hxy⟩ := hGΛ _ h2
    have : x = y := by exact_mod_cast hxy
    rwa [this]
  have hsep1 : IsSepBy δ (phaseLevel (fun x ↦ φE x + φG x) (Real.pi / 2)) :=
    IsSepBy.mono hsep le_rfl hsub
  obtain ⟨C₀, hC₀pos, hC₀⟩ := HEEqPW.levelSet_ineq hPW hE hEHB hEPW
  have hstrict' : IsStrictHB (fun z ↦ E z * G z) := hstrict.mul_isHB hGHB
  have hlev := eventually_not_exceptional hstrict'
  have hlim := levelSet_limit hPW hψ.1 hψm hψs hδ hsep1 (C₀ := (C₀ : ℝ≥0∞)) ENNReal.coe_ne_top
    (ε := fun n : ℕ ↦ Real.pi / (n + 2))
    (fun n ↦ by positivity)
    (fun n ↦ by
      rw [div_lt_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith)
    (tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
    (hlev.mono fun n hn f hf ↦ hC₀ G hGHB hG0 _ hψ _ hn f hf)
  obtain ⟨B, hB⟩ := plancherelPolya hPW hδ
  refine ⟨C₀⁻¹, B, inv_pos.mpr hC₀pos, fun f hf ↦ ⟨?_, hB Λ hsep f hf⟩⟩
  have hC0 : (C₀ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC₀pos.ne'
  calc ((C₀⁻¹ : ℝ≥0) : ℝ≥0∞) * pwNormSq f
      ≤ ((C₀⁻¹ : ℝ≥0) : ℝ≥0∞) * ((C₀ : ℝ≥0∞) *
          sampleSum (phaseLevel (fun x ↦ φE x + φG x) (Real.pi / 2)) f) :=
        mul_le_mul' le_rfl (hlim f hf)
    _ = sampleSum (phaseLevel (fun x ↦ φE x + φG x) (Real.pi / 2)) f := by
        rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hC₀pos.ne']
        simp
    _ ≤ sampleSum Λ f := sampleSum_mono hsub f

end FF
