import FourierFrames.Cited.DeBrangesDE.Orthogonal
import FourierFrames.Cited.DeBrangesDE.EntireHerglotz

/-!
# P3 — Theorem E, part 2: completeness, the norm identity, interpolation

See `blueprint/P3_DeBrangesDE.md`, §7–§8.  Key proposition (`eq_zero_of_level_zero`): if
`S_α ∉ H(E)` and `f ∈ H(E)` vanishes on `Γ`, then `f = 0`.  Proof: the entire Pick function
`h = D/S` is linear (`entire_pick_linear`), `h = p z + q`; `p > 0` would put `S` in `H(E)` (the
defect kernel is `(p/π) S(z) conj S(w)` and is a limit in `H(E)` of partial sums); so `p = 0`,
the defect kernel vanishes, `K_w` is the norm limit of its partial orthogonal expansions, and
`f(w) = ⟨f, K_w⟩ = 0`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {E : ℂ → ℂ} {φ : ℝ → ℝ} {α : ℝ}

/-- Partial sum `s_F = Σ_{γ ∈ F} a_γ wt(γ) K_γ`. -/
def partialSum (E : ℂ → ℂ) (φ : ℝ → ℝ) (α : ℝ) (a : ℝ → ℂ) (F : Finset (phaseLevel φ α)) :
    ℂ → ℂ :=
  fun z ↦ ∑ γ ∈ F, a γ * (wt E γ : ℂ) * deBrangesKernel E (γ : ℂ) z

/-! ## 7.1 Exhaustion and convergence of partial sums -/

/-- `Γ` is exhausted by the finite sets `Γ ∩ [-n, n]`. -/
theorem exists_exhaustion (D : DBData E φ) (α : ℝ) :
    ∃ F : ℕ → Finset (phaseLevel φ α), Monotone F ∧ ∀ γ : phaseLevel φ α, ∃ n, γ ∈ F n := by
  sorry

/-- If `Σ wt |a|² < ∞` the partial sums along an exhaustion are Cauchy in `H(E)`
(Pythagoras `heNormSq_partialSum` on the difference of two finite sets). -/
theorem cauchy_partialSum (D : DBData E φ) {a : ℝ → ℂ}
    (ha : Summable fun γ : phaseLevel φ α ↦ wt E γ * ‖a γ‖ ^ 2)
    {F : ℕ → Finset (phaseLevel φ α)} (hF : Monotone F) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      heNormSq E (fun z ↦ partialSum E φ α a (F m) z - partialSum E φ α a (F n) z) ≤
        ENNReal.ofReal ε := by
  sorry

/-- **Series limit** (completeness of `H(E)` + orthogonality): for `Σ wt|a|² < ∞` there is
`g ∈ H(E)` with `g(γ) = a_γ` on `Γ` and `‖g‖² = Σ wt |a_γ|²`; `⟨f, g⟩ = Σ conj(a_γ) wt(γ) f(γ)`. -/
theorem exists_series_limit (D : DBData E φ) {a : ℝ → ℂ}
    (ha : Summable fun γ : phaseLevel φ α ↦ wt E γ * ‖a γ‖ ^ 2) :
    ∃ g : ℂ → ℂ, MemHE E g ∧ (∀ γ ∈ phaseLevel φ α, g γ = a γ) ∧
      (heNormSq E g).toReal = ∑' γ : phaseLevel φ α, wt E γ * ‖a γ‖ ^ 2 ∧
      ∀ f : ℂ → ℂ, MemHE E f →
        HasSum (fun γ : phaseLevel φ α ↦ conj (a γ) * (wt E γ : ℂ) * f γ) (heInner E f g) := by
  sorry

/-! ## 7.2 `h = D/S` is linear, and `S ∈ H(E)` if `p > 0` -/

/-- `h` is `p z + q` with `p ≥ 0` (apply `entire_pick_linear` to `h` of `exists_hFun`). -/
theorem hFun_linear (D : DBData E φ) {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) (hreal : ∀ z, h (conj z) = conj (h z)) :
    ∃ p q : ℝ, 0 ≤ p ∧ ∀ z, h z = p * z + q := by
  sorry

/-- For linear `h = p z + q`: `Q(w, z) = (p/π) S(z) conj S(w)` for all `w, z`. -/
theorem defectKer_eq_of_linear (D : DBData E φ) {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) {p q : ℝ} (hlin : ∀ z, h z = p * z + q)
    (w z : ℂ) :
    defectKer E φ α w z = (p / Real.pi : ℝ) * sFun E α z * conj (sFun E α w) := by
  sorry

/-- The defect kernel is an element of `H(E)`: `Q_w = K_w - lim s_{F_n}` with
`a_γ = K(w, γ)` (series limit); evaluating pointwise gives `Q(w, ·)`. -/
theorem memHE_defectKer (D : DBData E φ) (w : ℂ) :
    MemHE E (fun z ↦ defectKer E φ α w z) := by
  sorry

/-- `‖Q_w‖² = Q(w,w)` (norm of `K_w` minus the squared norm of its expansion). -/
theorem heNormSq_defectKer (D : DBData E φ) (w : ℂ) :
    (heNormSq E (fun z ↦ defectKer E φ α w z)).toReal = (defectKer E φ α w w).re := by
  sorry

/-- If `p > 0`, then `S ∈ H(E)`. -/
theorem memHE_sFun_of_pos (D : DBData E φ) {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) {p q : ℝ} (hp : 0 < p)
    (hlin : ∀ z, h z = p * z + q) : MemHE E (sFun E α) := by
  sorry

/-! ## 7.3 The key proposition and the norm identity -/

/-- **Key proposition**: if `S_α ∉ H(E)`, no nonzero `f ∈ H(E)` vanishes on `Γ`. -/
theorem eq_zero_of_level_zero (D : DBData E φ)
    (hα : ¬ MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z))
    {f : ℂ → ℂ} (hf : MemHE E f) (hz : ∀ γ ∈ phaseLevel φ α, f γ = 0) : ∀ z, f z = 0 := by
  sorry

/-- Norm identity (real form): `‖f‖²_E = Σ_γ wt(γ) |f(γ)|²`. -/
theorem heNormSq_eq_tsum (D : DBData E φ)
    (hα : ¬ MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z))
    {f : ℂ → ℂ} (hf : MemHE E f) :
    Summable (fun γ : phaseLevel φ α ↦ wt E γ * ‖f γ‖ ^ 2) ∧
      (heNormSq E f).toReal = ∑' γ : phaseLevel φ α, wt E γ * ‖f γ‖ ^ 2 := by
  sorry

/-- **Theorem E, part 1** in the form of `TheoremE`. -/
theorem theoremE_norm (D : DBData E φ)
    (hα : ¬ MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z))
    {f : ℂ → ℂ} (hf : MemHE E f) :
    heNormSq E f = ∑' γ : phaseLevel φ α, orthWeight E γ * ‖f γ‖ₑ ^ 2 := by
  sorry

/-- **Theorem E, part 2** (interpolation; needs neither completeness nor `S_α ∉ H(E)`). -/
theorem theoremE_interp (D : DBData E φ) (a : ℝ → ℂ)
    (ha : ∑' γ : phaseLevel φ α, orthWeight E γ * ‖a γ‖ₑ ^ 2 < ∞) :
    ∃ f : ℂ → ℂ, MemHE E f ∧ ∀ γ ∈ phaseLevel φ α, f γ = a γ := by
  sorry

end FF
