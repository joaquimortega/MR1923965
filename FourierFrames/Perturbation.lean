import FourierFrames.Defs

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

/-! ## Upstream interface (temporary, replaced by imports at assembly) -/

section Upstream

/-- (M01, `PW/Basic.lean`) `f ∈ PW`, `f(a) = 0` ⇒ `f(z)(z - b)/(z - a) ∈ PW`. -/
theorem MemPW.mul_div_sub {f : ℂ → ℂ} (hf : MemPW f) {a : ℂ} (ha : f a = 0) (b : ℂ) :
    MemPW (fun z ↦ dslope f a z * (z - b)) := by
  sorry

/-- (M01, `PW/Basic.lean`) -/
theorem pwNormSq_ne_top {f : ℂ → ℂ} (hf : MemPW f) : pwNormSq f ≠ ⊤ := by
  sorry

/-- (M01, `PW/Basic.lean`) -/
def IsSepBy (δ : ℝ) (Λ : Set ℝ) : Prop :=
  ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ |a - b|

/-- (M01, `PW/PlancherelPolya.lean`) -/
theorem plancherelPolya (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ Λ : Set ℝ, IsSepBy δ Λ → ∀ f : ℂ → ℂ, MemPW f →
      sampleSum Λ f ≤ C * pwNormSq f := by
  sorry

/-- (M01, `PW/PlancherelPolya.lean`) -/
theorem sampleSum_union_le (Λ₁ Λ₂ : Set ℝ) (f : ℂ → ℂ) :
    sampleSum (Λ₁ ∪ Λ₂) f ≤ sampleSum Λ₁ f + sampleSum Λ₂ f := by
  sorry

/-- (M01, `PW/Complete.lean`) normal families in `PW`. -/
theorem pw_normal_family (hPW : PaleyWienerThm) {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemPW (f n))
    {M : ℝ} (hM : ∀ n, pwNormSq (f n) ≤ ENNReal.ofReal M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, MemPW g ∧
      TendstoLocallyUniformly (fun n ↦ f (φ n)) g atTop ∧
      pwNormSq g ≤ liminf (fun n ↦ pwNormSq (f n)) atTop := by
  sorry

end Upstream

/-! ## Elementary facts on sampling sums and separated sets -/

/-- `sampleSum` is monotone in the set. -/
theorem sampleSum_mono {Λ₁ Λ₂ : Set ℝ} (h : Λ₁ ⊆ Λ₂) (f : ℂ → ℂ) :
    sampleSum Λ₁ f ≤ sampleSum Λ₂ f := by
  sorry

/-- `sampleSum {a} f = |f(a)|²`. -/
theorem sampleSum_singleton (a : ℝ) (f : ℂ → ℂ) : sampleSum {a} f = ‖f (a : ℂ)‖ₑ ^ 2 := by
  sorry

/-- A separated set is closed (and discrete). -/
theorem IsSeparated.isClosed {Λ : Set ℝ} (h : IsSeparated Λ) : IsClosed Λ := by
  sorry

/-- A separated set meets bounded sets in finite sets. -/
theorem IsSeparated.finite_inter_Icc {Λ : Set ℝ} (h : IsSeparated Λ) (R : ℝ) :
    (Λ ∩ Icc (-R) R).Finite := by
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
