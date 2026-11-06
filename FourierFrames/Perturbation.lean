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
  sorry

/-- A separated set is closed (and discrete). -/
theorem IsSeparated.isClosed {Λ : Set ℝ} (h : IsSeparated Λ) : IsClosed Λ := by
  sorry

/-- Adding one point to a separated set keeps it separated. -/
theorem IsSeparated.insert {Λ : Set ℝ} (h : IsSeparated Λ) {b : ℝ} (hb : b ∉ Λ) :
    IsSeparated (insert b Λ) := by
  sorry

/-- Union of a separated set and a finite set is separated. -/
theorem IsSeparated.union_finite {Λ G : Set ℝ} (h : IsSeparated Λ) (hG : G.Finite) :
    IsSeparated (Λ ∪ G) := by
  sorry

/-! ## Replacing finitely many points -/

/-- **Replacing one point.**  If `Γ` is a separated sampling set, `a ∈ Γ` and `b ∉ Γ`, then
`(Γ \ {a}) ∪ {b}` is a (separated) sampling set. -/
theorem isSampling_replace_point (hPW : PaleyWienerThm) {Γ : Set ℝ} (hsep : IsSeparated Γ)
    (hs : IsSampling Γ) {a b : ℝ} (ha : a ∈ Γ) (hb : b ∉ Γ) :
    IsSampling (insert b (Γ \ {a})) := by
  sorry

/-- **Replacing finitely many points by the same number of new points.**  (The "elementary fact"
of p. 800.) -/
theorem isSampling_of_replace_finite (hPW : PaleyWienerThm) {Γ Γ' : Set ℝ}
    (hsep : IsSeparated Γ) (hs : IsSampling Γ) (hsep' : IsSeparated Γ')
    (hD : (Γ \ Γ').Finite) (hD' : (Γ' \ Γ).Finite) (hcard : (Γ \ Γ').ncard = (Γ' \ Γ).ncard) :
    IsSampling Γ' := by
  sorry

/-! ## The perturbation lemma -/

/-- **Perturbation lemma** (p. 800; Duffin–Schaeffer + finite modification).  Let `Γ` be a separated
sampling set and `δ : ℝ → ℝ` such that `γ ↦ γ + δ(γ)` is injective on `Γ` and `δ(γ) → 0` as
`|γ| → ∞` in `Γ`.  Then `{γ + δ(γ) : γ ∈ Γ}` is a sampling set. -/
theorem IsSampling.of_perturbation (hPW : PaleyWienerThm) (hDS : DSPerturbation) {Γ : Set ℝ}
    (hsep : IsSeparated Γ) (hs : IsSampling Γ) {δ : ℝ → ℝ}
    (hinj : InjOn (fun x ↦ x + δ x) Γ)
    (hδ : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x ∈ Γ, R ≤ |x| → |δ x| ≤ ε) :
    IsSampling ((fun x ↦ x + δ x) '' Γ) := by
  sorry

end FF
