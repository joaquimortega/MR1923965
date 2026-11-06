import FourierFrames.Defs

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF

/-!
# M04 — Theorem 1, sufficiency (pp. 795–797)

See `blueprint/M04_Sufficiency.md`.
-/

/-! ## Upstream interface (temporary, replaced by imports at assembly) -/

/-! ### M01 (Paley–Wiener toolkit) -/

theorem pwNormSq_ne_top {f : ℂ → ℂ} (hf : MemPW f) : pwNormSq f ≠ ∞ := by
  sorry

theorem pw_norm_sq_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (z : ℂ) :
    ‖f z‖ ^ 2 ≤ Real.exp (2 * Real.pi * |z.im|) * (pwNormSq f).toReal := by
  sorry

theorem MemPW.sub {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) : MemPW (fun z ↦ f z - g z) := by
  sorry

theorem MemPW.comp_sub_ofReal {f : ℂ → ℂ} (hf : MemPW f) (a : ℝ) :
    MemPW (fun z ↦ f (z - a)) := by
  sorry

theorem pwNormSq_comp_sub_ofReal (f : ℂ → ℂ) (a : ℝ) :
    pwNormSq (fun z ↦ f (z - a)) = pwNormSq f := by
  sorry

theorem exists_memPW_eval_ne_zero : ∃ g : ℂ → ℂ, MemPW g ∧ g 0 = 1 := by
  sorry

theorem plancherelPolya (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ Λ : Set ℝ, (∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ |a - b|) →
      ∀ f : ℂ → ℂ, MemPW f → sampleSum Λ f ≤ C * pwNormSq f := by
  sorry

/-- Uniform tails: for `f ∈ PW` and `δ > 0` the tails of the sampling sums over `δ`-separated sets
are small, uniformly over all such sets. -/
theorem plancherelPolya_tail (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) {f : ℂ → ℂ}
    (hf : MemPW f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ Λ : Set ℝ, (∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ |a - b|) →
      sampleSum (Λ ∩ {x : ℝ | R ≤ |x|}) f ≤ ε := by
  sorry

theorem pw_deriv_bound (hPW : PaleyWienerThm) :
    ∃ C : ℝ, ∀ f : ℂ → ℂ, MemPW f → ∀ x : ℝ, ‖deriv f x‖ ^ 2 ≤ C * (pwNormSq f).toReal := by
  sorry

/-! ### M02 (Hermite–Biehler class, phases, `H(E)`) -/

theorem IsHB.mul {E F : ℂ → ℂ} (hE : IsHB E) (hF : IsHB F) : IsHB (fun z ↦ E z * F z) := by
  sorry

theorem IsStrictHB.mul_isHB {E F : ℂ → ℂ} (hE : IsStrictHB E) (hF : IsHB F) :
    IsStrictHB (fun z ↦ E z * F z) := by
  sorry

theorem IsHB.phaseDeriv_nonneg {E : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (x : ℝ) :
    0 ≤ phaseDeriv E x := by
  sorry

theorem IsStrictHB.phaseDeriv_pos {E : ℂ → ℂ} (hE : IsStrictHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (x : ℝ) : 0 < phaseDeriv E x := by
  sorry

theorem phaseDeriv_mul {E F : ℂ → ℂ} (hE : Differentiable ℂ E) (hF : Differentiable ℂ F)
    (hE0 : ∀ x : ℝ, E x ≠ 0) (hF0 : ∀ x : ℝ, F x ≠ 0) (x : ℝ) :
    phaseDeriv (fun z ↦ E z * F z) x = phaseDeriv E x + phaseDeriv F x := by
  sorry

theorem exists_isPhaseFunction {E : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0) :
    ∃ φ : ℝ → ℝ, IsPhaseFunction E φ ∧ ∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x := by
  sorry

/-- For `E` strict and `F ∈ \overline{HB}`, both without real zeros: the zeros of `EF + E^*F^*`
are the real points of the level set `{φ_E + φ_F ∈ π/2 + πℤ}`. -/
theorem zero_set_eq_phaseLevel {E F : ℂ → ℂ} (hE : IsStrictHB E) (hF : IsHB F)
    (hE0 : ∀ x : ℝ, E x ≠ 0) (hF0 : ∀ x : ℝ, F x ≠ 0) {φE φF : ℝ → ℝ}
    (hφE : IsPhaseFunction E φE) (hφF : IsPhaseFunction F φF) (z : ℂ) :
    E z * F z + fstar E z * fstar F z = 0 ↔
      ∃ x ∈ phaseLevel (fun t ↦ φE t + φF t) (Real.pi / 2), z = (x : ℂ) := by
  sorry

theorem MemHE.mul_isHB {E F f : ℂ → ℂ} (hE : IsHB E) (hF : IsHB F) (hF0 : ∀ x : ℝ, F x ≠ 0)
    (hf : MemHE E f) : MemHE (fun z ↦ E z * F z) (fun z ↦ F z * f z) := by
  sorry

theorem heNormSq_mul {E F : ℂ → ℂ} (f : ℂ → ℂ) (hF0 : ∀ x : ℝ, F x ≠ 0) :
    heNormSq (fun z ↦ E z * F z) (fun z ↦ F z * f z) = heNormSq E f := by
  sorry

theorem HEEqPW.isStrictHB (hPW : PaleyWienerThm) {E : ℂ → ℂ} (hE : IsHB E) (h : HEEqPW E) :
    IsStrictHB E := by
  sorry

theorem HEEqPW.ne_zero_ofReal (hPW : PaleyWienerThm) {E : ℂ → ℂ} (hE : IsHB E) (h : HEEqPW E)
    (x : ℝ) : E x ≠ 0 := by
  sorry

/-- `φ_E'(x) |E(x)|² ≥ c > 0` when `H(E) = PW` (the `≲` half of `φ_E'|E|² ≃ 1`). -/
theorem HEEqPW.phaseDeriv_mul_sq_ge (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (h : HEEqPW E) : ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, c ≤ phaseDeriv E x * ‖E x‖ ^ 2 := by
  sorry

/-- At most one `α` modulo `π` has `e^{iα}E - e^{-iα}E^* ∈ H(E)` (`E` strict). -/
theorem memHE_sAlpha_unique {E : ℂ → ℂ} (hE : IsStrictHB E) {α β : ℝ}
    (h1 : MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z))
    (h2 : MemHE E (fun z ↦ Complex.exp (I * β) * E z - Complex.exp (-(I * β)) * fstar E z)) :
    ∃ k : ℤ, β - α = k * Real.pi := by
  sorry

/-! ## Helpers on separation, sampling sums and exceptional levels -/

namespace Suff

/-- `Λ` is `δ`-separated. -/
def SepBy (δ : ℝ) (Λ : Set ℝ) : Prop :=
  ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ |a - b|

theorem isSeparated_iff {Λ : Set ℝ} : IsSeparated Λ ↔ ∃ δ : ℝ, 0 < δ ∧ SepBy δ Λ := Iff.rfl

/-- `α` is *exceptional* for `E`: `e^{iα}E - e^{-iα}E^* ∈ H(E)` (the hypothesis of Theorem E fails). -/
def Exceptional (E : ℂ → ℂ) (α : ℝ) : Prop :=
  MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z)

theorem sepBy_subset {δ : ℝ} {Λ Λ' : Set ℝ} (h : Λ' ⊆ Λ) (hΛ : SepBy δ Λ) : SepBy δ Λ' :=
  fun a ha b hb hab ↦ hΛ a (h ha) b (h hb) hab

theorem sampleSum_eq_tsum_indicator (Λ : Set ℝ) (f : ℂ → ℂ) :
    sampleSum Λ f = ∑' x : ℝ, Λ.indicator (fun x : ℝ ↦ ‖f (x : ℂ)‖ₑ ^ 2) x := by
  unfold sampleSum
  exact tsum_subtype Λ (fun x : ℝ ↦ ‖f (x : ℂ)‖ₑ ^ 2)

theorem sampleSum_mono {Λ Λ' : Set ℝ} (h : Λ ⊆ Λ') (f : ℂ → ℂ) :
    sampleSum Λ f ≤ sampleSum Λ' f := by
  rw [sampleSum_eq_tsum_indicator, sampleSum_eq_tsum_indicator]
  exact ENNReal.tsum_le_tsum fun x ↦ Set.indicator_le_indicator_of_subset h (by intro; positivity) x

theorem sampleSum_union_le (Λ Λ' : Set ℝ) (f : ℂ → ℂ) :
    sampleSum (Λ ∪ Λ') f ≤ sampleSum Λ f + sampleSum Λ' f :=
  ENNReal.tsum_union_le (fun x : ℝ ↦ ‖f (x : ℂ)‖ₑ ^ 2) Λ Λ'

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

theorem sepBy_mono {δ δ' : ℝ} (h : δ' ≤ δ) {Λ : Set ℝ} (hΛ : SepBy δ Λ) : SepBy δ' Λ :=
  fun a ha b hb hab ↦ h.trans (hΛ a ha b hb hab)

/-- **Interlacing** (p. 796): if the level set `Λ = {φ ∈ π/2 + πℤ}` of a continuous strictly
increasing `φ` is `δ`-separated, then `{φ ∈ π/2 + ε + πℤ}` (`0 < ε < π`) is a union of two
`δ`-separated sets (even and odd index). -/
theorem phaseLevel_sepBy_two {φ : ℝ → ℝ} (hc : Continuous φ) (hφ : StrictMono φ) {δ : ℝ}
    (hsep : SepBy δ (phaseLevel φ (Real.pi / 2))) {ε : ℝ} (hε0 : 0 < ε) (hεπ : ε < Real.pi) :
    ∃ A B : Set ℝ, phaseLevel φ (Real.pi / 2 + ε) = A ∪ B ∧ SepBy δ A ∧ SepBy δ B := by
  sorry

/-- At most one `n` has `π/2 + π/(n+2)` exceptional, so eventually none has. -/
theorem eventually_not_exceptional {E : ℂ → ℂ} (hE : IsStrictHB E) :
    ∀ᶠ n : ℕ in atTop, ¬ Exceptional E (Real.pi / 2 + Real.pi / (n + 2)) := by
  sorry

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
    (hsep : SepBy δ (phaseLevel ψ (Real.pi / 2))) {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hεπ : ∀ n, ε n < Real.pi)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hlev : ∀ᶠ n in atTop, ∀ f : ℂ → ℂ, MemPW f →
      pwNormSq f ≤ C₀ * sampleSum (phaseLevel ψ (Real.pi / 2 + ε n)) f) :
    ∀ f : ℂ → ℂ, MemPW f → pwNormSq f ≤ C₀ * sampleSum (phaseLevel ψ (Real.pi / 2)) f := by
  sorry

/-! ## Removing the real zeros of `F` (p. 795) -/

/-- **Weierstrass factorisation of the real zeros** (new lemma, `S` of the paper): an entire
`F ∈ \overline{HB}`, `F ≢ 0`, factors as `F = S G` with `S` real entire (`S^* = S`) whose zeros are
exactly the real zeros of `F` (with multiplicity), and `G ∈ \overline{HB}` without real zeros.
Needs Weierstrass products of non-constant genus (not in Mathlib); see the blueprint. -/
theorem exists_realFactor {F : ℂ → ℂ} (hF : IsHB F) (hF0 : ∃ z, F z ≠ 0) :
    ∃ S G : ℂ → ℂ, Differentiable ℂ S ∧ IsHB G ∧ (∀ z, F z = S z * G z) ∧
      (∀ z, fstar S z = S z) ∧ (∀ z, S z = 0 → z.im = 0) ∧ (∀ x : ℝ, G x ≠ 0) := by
  sorry

/-- The reduction of p. 795: `F` can be replaced by `G` without real zeros, at the price of
shrinking `Λ`. -/
theorem exists_noRealZero_hb {E F : ℂ → ℂ} {Λ : Set ℝ} (hEHB : IsHB E) (hFHB : IsHB F)
    (hzero : ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ)) :
    ∃ G : ℂ → ℂ, IsHB G ∧ (∀ x : ℝ, G x ≠ 0) ∧
      ∀ z : ℂ, E z * G z + fstar E z * fstar G z = 0 → ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry

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
          pwNormSq f ≤ C₀ * sampleSum (phaseLevel ψ α) f := by
  sorry

/-- For `H(E) = PW` and `α` non-exceptional for `E`, `Γ_α = {φ_E ∈ α + πℤ}` is separated
(README §3.8). -/
theorem HEEqPW.levelSet_separated (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {α : ℝ}
    (hα : ¬ Exceptional E α) : IsSeparated (phaseLevel φ α) := by
  sorry

/-- For `H(E) = PW` and `α` non-exceptional, `Γ_α` is a complete interpolating sequence. -/
theorem HEEqPW.levelSet_cis (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {α : ℝ}
    (hα : ¬ Exceptional E α) : IsCompleteInterpolating (phaseLevel φ α) := by
  sorry

/-- If `H(E) = PW`, the phase of `E` is unbounded in both directions (so `Γ_α` is infinite on both
sides). -/
theorem HEEqPW.phase_tendsto (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ)
    (hφ' : ∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x) :
    Tendsto φ atTop atTop ∧ Tendsto φ atBot atBot := by
  sorry

/-- The phase `ψ = φ_E + φ_G` of `EG` is a continuous increasing bijection of `ℝ`
(`G ∈ \overline{HB}` without real zeros, `H(E) = PW`). -/
theorem HEEqPW.phase_mul_bijective (hPW : PaleyWienerThm) (hE : TheoremE) {E G : ℂ → ℂ}
    (hEHB : IsHB E) (hGHB : IsHB G) (hEPW : HEEqPW E) (hG0 : ∀ x : ℝ, G x ≠ 0)
    {φE φG : ℝ → ℝ} (hφE : IsPhaseFunction E φE) (hφE' : ∀ x : ℝ, HasDerivAt φE (phaseDeriv E x) x)
    (hφG : IsPhaseFunction G φG) (hφG' : ∀ x : ℝ, HasDerivAt φG (phaseDeriv G x) x) :
    StrictMono (fun x ↦ φE x + φG x) ∧ Function.Surjective (fun x ↦ φE x + φG x) := by
  sorry

/-! ## Theorem 1, sufficiency (p. 795–797) -/

/-- **Theorem 1** (p. 795), sufficiency. -/
theorem theorem1_sufficiency (hPW : PaleyWienerThm) (hE : TheoremE)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) {E F : ℂ → ℂ} (hEHB : IsHB E) (hFHB : IsHB F)
    (hEPW : HEEqPW E) (hzero : ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ)) :
    IsSampling Λ := by
  sorry

end FF
