import FourierFrames.Cited.DeBrangesDE.Orthogonal
import FourierFrames.Cited.DeBrangesDE.EntireHerglotz

/-!
# P3 — Theorem E, part 2: completeness, the norm identity, interpolation

See `blueprint/P3_DeBrangesDE.md`, §7–§8.  Key proposition (`eq_zero_of_level_zero`): if
`S_α ∉ H(E)` and `f ∈ H(E)` vanishes on `Γ`, then `f = 0`.  Proof: the entire Pick function
`h = D/S` is linear (`entire_pick_linear`), `h = p z + q`; `p > 0` would put `S` in `H(E)` (the
defect kernel `Q_i` is an element of `H(E)` and equals `(p/π) conj S(i) · S`); so `p = 0`, the
defect kernel vanishes on the diagonal, `‖Q_w‖ = 0`, `K_w` is the norm limit of its orthogonal
expansion, and `f(w) = ⟨f, K_w⟩ = 0`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {E : ℂ → ℂ} {φ : ℝ → ℝ} {α : ℝ}

/-! ## 7.1 Exhaustion and convergence of partial sums -/

/-- `Γ` is exhausted by the finite sets `Γ ∩ [-n, n]`. -/
theorem exists_exhaustion (D : DBData E φ) (α : ℝ) :
    ∃ F : ℕ → Finset (phaseLevel φ α), Monotone F ∧ ∀ γ : phaseLevel φ α, ∃ n, γ ∈ F n := by
  sorry

/-- If `Σ wt |a|² < ∞` the partial sums along an exhaustion are Cauchy in `H(E)`
(Pythagoras `heNormSq_partialSum` on the difference `s_{F m} - s_{F n} = s_{F m \ F n}`). -/
theorem cauchy_partialSum (D : DBData E φ) {a : ℝ → ℂ}
    (ha : Summable fun γ : phaseLevel φ α ↦ wt E γ * ‖a γ‖ ^ 2)
    {F : ℕ → Finset (phaseLevel φ α)} (hF : Monotone F) (hex : ∀ γ, ∃ n, γ ∈ F n) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      heNormSq E (fun z ↦ partialSum E φ α a (F m) z - partialSum E φ α a (F n) z) ≤
        ENNReal.ofReal ε := by
  sorry

/-- **Series limit** (completeness of `H(E)` + orthogonality): for `Σ wt|a|² < ∞` there is
`g ∈ H(E)` with `g(z) = Σ_γ a_γ wt(γ) K(γ, z)` for every `z`, `g(γ) = a_γ` on `Γ`,
`‖g‖² = Σ wt |a_γ|²`, and `⟨f, g⟩ = Σ conj(a_γ) wt(γ) f(γ)` for `f ∈ H(E)`. -/
theorem exists_series_limit (D : DBData E φ) {a : ℝ → ℂ}
    (ha : Summable fun γ : phaseLevel φ α ↦ wt E γ * ‖a γ‖ ^ 2) :
    ∃ g : ℂ → ℂ, MemHE E g ∧
      (∀ z : ℂ, HasSum (fun γ : phaseLevel φ α ↦
        a γ * ((wt E γ : ℝ) : ℂ) * deBrangesKernel E (γ : ℂ) z) (g z)) ∧
      (∀ γ ∈ phaseLevel φ α, g γ = a γ) ∧
      (heNormSq E g).toReal = ∑' γ : phaseLevel φ α, wt E γ * ‖a γ‖ ^ 2 ∧
      ∀ f : ℂ → ℂ, MemHE E f →
        HasSum (fun γ : phaseLevel φ α ↦ conj (a γ) * (wt E γ : ℂ) * f γ) (heInner E f g) := by
  sorry

/-! ## 7.2 The defect kernel as an element of `H(E)`; `h` is linear; `S ∈ H(E)` if `p > 0` -/

/-- The defect kernel is an element of `H(E)`: `Q_w = K_w - g_w` with `g_w` the series limit for
`a_γ = K(w, γ)` (`Σ wt |K(w,γ)|² < ∞` by Bessel), and `‖Q_w‖² = Q(w, w)`. -/
theorem memHE_defectKer (D : DBData E φ) (w : ℂ) :
    MemHE E (fun z ↦ defectKer E φ α w z) ∧
      (heNormSq E (fun z ↦ defectKer E φ α w z)).toReal = (defectKer E φ α w w).re := by
  sorry

/-- `⟨f, Q_w⟩ = f(w)` for every `f ∈ H(E)` vanishing on `Γ` (`⟨f, g_w⟩ = Σ ... f(γ) = 0`). -/
theorem heInner_defectKer_of_level_zero (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f)
    (hz : ∀ γ ∈ phaseLevel φ α, f γ = 0) (w : ℂ) :
    heInner E f (fun z ↦ defectKer E φ α w z) = f w := by
  sorry

/-- `h` is `p z + q` with `p ≥ 0` (apply `entire_pick_linear` to `h` of `exists_hFun`, using
`im_hFun_nonneg`). -/
theorem hFun_linear (D : DBData E φ) {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) (hreal : ∀ z, h (conj z) = conj (h z)) :
    ∃ p q : ℝ, 0 ≤ p ∧ ∀ z, h z = p * z + q := by
  sorry

/-- For linear `h = p z + q`: `Q(w, z) = (p/π) S(z) conj S(w)` for `z ≠ w̄`
(divide `defectKer_mul` by `π (z - w̄)`). -/
theorem defectKer_eq_of_linear (D : DBData E φ) {h : ℂ → ℂ}
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) {p q : ℝ} (hlin : ∀ z, h z = p * z + q)
    {w z : ℂ} (hz : z ≠ conj w) :
    defectKer E φ α w z = (p / Real.pi : ℝ) * sFun E α z * conj (sFun E α w) := by
  sorry

/-- If `p > 0`, then `S ∈ H(E)`: `S = (π / (p conj S(i))) Q_i` off `z = -i`, hence everywhere by
continuity, and `Q_i ∈ H(E)`. -/
theorem memHE_sFun_of_pos (D : DBData E φ) {h : ℂ → ℂ}
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

/-- **Theorem E, part 2** (interpolation; needs neither the key proposition nor `S_α ∉ H(E)`). -/
theorem theoremE_interp (D : DBData E φ) (a : ℝ → ℂ)
    (ha : ∑' γ : phaseLevel φ α, orthWeight E γ * ‖a γ‖ₑ ^ 2 < ∞) :
    ∃ f : ℂ → ℂ, MemHE E f ∧ ∀ γ ∈ phaseLevel φ α, f γ = a γ := by
  sorry

end FF
