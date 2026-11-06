import FourierFrames.Defs

/-!
# M01 — Paley–Wiener space toolkit: basic facts

See `blueprint/M01_PW.md`.  Everything is derived from `hPW : PaleyWienerThm`; the lemmas that do
not need it (algebra of `PW`, translations, `f^*`, `mul_div_sub`) do not take it.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Notation for `L²(-π, π)` and the Fourier–Laplace transform -/

/-- `g ∈ L²(-π, π)`. -/
def MemL2pi (g : ℝ → ℂ) : Prop :=
  MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))

/-- `‖g‖²_{L²(-π,π)}`, in `ℝ≥0∞`. -/
def l2piSq (g : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2

/-- The transform `z ↦ ∫_{-π}^{π} g(t) e^{izt} dt` of the Paley–Wiener theorem. -/
def pwFT (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)

/-- `Λ` is `δ`-separated: distinct points are at distance `≥ δ`. -/
def IsSepBy (δ : ℝ) (Λ : Set ℝ) : Prop :=
  ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ |a - b|

theorem isSeparated_iff_exists_isSepBy {Λ : Set ℝ} :
    IsSeparated Λ ↔ ∃ δ : ℝ, 0 < δ ∧ IsSepBy δ Λ := Iff.rfl

theorem IsSepBy.mono {δ δ' : ℝ} {Λ Λ' : Set ℝ} (h : IsSepBy δ Λ) (hδ : δ' ≤ δ) (hΛ : Λ' ⊆ Λ) :
    IsSepBy δ' Λ' :=
  fun a ha b hb hab ↦ hδ.trans (h a (hΛ ha) b (hΛ hb) hab)

theorem MemL2pi.integrableOn {g : ℝ → ℂ} (hg : MemL2pi g) :
    IntegrableOn g (Ioc (-Real.pi) Real.pi) := by
  sorry

theorem MemL2pi.integrableOn_mul_exp {g : ℝ → ℂ} (hg : MemL2pi g) (z : ℂ) :
    IntegrableOn (fun t : ℝ ↦ g t * Complex.exp (I * z * t)) (Ioc (-Real.pi) Real.pi) := by
  sorry

theorem l2piSq_ne_top {g : ℝ → ℂ} (hg : MemL2pi g) : l2piSq g ≠ ⊤ := by
  sorry

/-- `g ↦ g(-·)`. -/
def reflect (g : ℝ → ℂ) : ℝ → ℂ := fun t ↦ g (-t)

theorem memL2pi_reflect {g : ℝ → ℂ} (hg : MemL2pi g) : MemL2pi (reflect g) := by
  sorry

theorem l2piSq_reflect (g : ℝ → ℂ) : l2piSq (reflect g) = l2piSq g := by
  sorry

theorem pwFT_reflect (g : ℝ → ℂ) (z : ℂ) :
    pwFT (reflect g) z = ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (-(I * z * t)) := by
  sorry

/-! ## Linearity, bounds and Parseval for `pwFT` (no `hPW`) -/

theorem pwFT_sub {g h : ℝ → ℂ} (hg : MemL2pi g) (hh : MemL2pi h) (z : ℂ) :
    pwFT (fun t ↦ g t - h t) z = pwFT g z - pwFT h z := by
  sorry

/-- `|pwFT g (z)| ≤ e^{π|Im z|} √(2π) ‖g‖_{L²(-π,π)}`. -/
theorem norm_pwFT_le {g : ℝ → ℂ} (hg : MemL2pi g) (z : ℂ) :
    ‖pwFT g z‖ ≤ Real.exp (Real.pi * |z.im|) * Real.sqrt (2 * Real.pi * (l2piSq g).toReal) := by
  sorry

/-- **Parseval at the integers** (Mathlib: `AddCircle.hasSum_sq_fourierCoeffOn`, period `2π`):
`∑_{k ∈ ℤ} |pwFT g k|² = 2π ‖g‖²`. -/
theorem tsum_enorm_sq_pwFT_int {g : ℝ → ℂ} (hg : MemL2pi g) :
    ∑' k : ℤ, ‖pwFT g (k : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (2 * Real.pi) * l2piSq g := by
  sorry

/-- **Uniqueness**: `pwFT g = pwFT h` on `ℤ` forces `g = h` a.e. on `(-π, π]`; in particular the
norms agree. -/
theorem l2piSq_eq_of_pwFT_eq {g h : ℝ → ℂ} (hg : MemL2pi g) (hh : MemL2pi h)
    (hgh : ∀ k : ℤ, pwFT g (k : ℂ) = pwFT h (k : ℂ)) : l2piSq g = l2piSq h := by
  sorry

/-- Locally uniform limits (along any filter) of functions of `PW` with a uniform bound
`|F_i(z)| ≤ K e^{π|Im z|}` and bounded norms lie in `PW`, and `‖f‖² ≤ liminf ‖F_i‖²` (Fatou). -/
theorem memPW_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, MemPW (F i)) {K : ℝ} (hK : ∀ i z, ‖F i z‖ ≤ K * Real.exp (Real.pi * |z.im|))
    (hd : Differentiable ℂ f) (hlim : ∀ z, Tendsto (fun i ↦ F i z) l (nhds (f z)))
    {M : ℝ≥0∞} (hM' : M ≠ ⊤) (hM : ∀ i, pwNormSq (F i) ≤ M) :
    MemPW f ∧ pwNormSq f ≤ liminf (fun i ↦ pwNormSq (F i)) l := by
  sorry

/-! ## Paley–Wiener, both directions, with the norm identity -/

/-- Easy half of `hPW`: every `f ∈ PW` is `pwFT g` for some `g ∈ L²(-π,π)`, with
`‖f‖² = 2π ‖g‖²`. -/
theorem exists_pwFT (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) :
    ∃ g : ℝ → ℂ, MemL2pi g ∧ f = pwFT g ∧ pwNormSq f = ENNReal.ofReal (2 * Real.pi) * l2piSq g := by
  sorry

/-- **Strong form of the Paley–Wiener theorem** (see blueprint §0: `PaleyWienerThm` as stated
only gives `⇐` for `g` for which the norm identity is already known; this lemma derives the
unconditional `⇐`). For every `g ∈ L²(-π,π)`, `pwFT g ∈ PW` and `‖pwFT g‖² = 2π‖g‖²`. -/
theorem memPW_pwFT (hPW : PaleyWienerThm) {g : ℝ → ℂ} (hg : MemL2pi g) :
    MemPW (pwFT g) ∧ pwNormSq (pwFT g) = ENNReal.ofReal (2 * Real.pi) * l2piSq g := by
  sorry

/-! ## `pwNormSq` is finite; algebra of `PW` -/

theorem pwNormSq_ne_top {f : ℂ → ℂ} (hf : MemPW f) : pwNormSq f ≠ ⊤ := by
  sorry

theorem memPW_zero : MemPW (fun _ : ℂ ↦ (0 : ℂ)) := by
  sorry

theorem MemPW.add {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) : MemPW (f + g) := by
  sorry

theorem MemPW.sub {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) : MemPW (f - g) := by
  sorry

theorem MemPW.const_mul {f : ℂ → ℂ} (hf : MemPW f) (c : ℂ) : MemPW (fun z ↦ c * f z) := by
  sorry

/-! ## Real translation and `f^*` -/

theorem MemPW.comp_sub_ofReal {f : ℂ → ℂ} (hf : MemPW f) (a : ℝ) :
    MemPW (fun z ↦ f (z - a)) := by
  sorry

theorem pwNormSq_comp_sub_ofReal (f : ℂ → ℂ) (a : ℝ) :
    pwNormSq (fun z ↦ f (z - a)) = pwNormSq f := by
  sorry

theorem MemPW.fstar {f : ℂ → ℂ} (hf : MemPW f) : MemPW (FF.fstar f) := by
  sorry

theorem pwNormSq_fstar (f : ℂ → ℂ) : pwNormSq (FF.fstar f) = pwNormSq f := by
  sorry

/-! ## Division by a zero -/

/-- If `f ∈ PW` vanishes at `a`, then `z ↦ f(z)(z - b)/(z - a)`, extended at `a` by `dslope`,
is in `PW`. -/
theorem MemPW.mul_div_sub {f : ℂ → ℂ} (hf : MemPW f) {a : ℂ} (ha : f a = 0) (b : ℂ) :
    MemPW (fun z ↦ dslope f a z * (z - b)) := by
  sorry

/-- (H1): for nonreal `a`, the multiplier `(z - ā)/(z - a)` is unimodular on `ℝ`, so the norm is
preserved. -/
theorem pwNormSq_mul_div_sub_conj (f : ℂ → ℂ) {a : ℂ} (ha : a.im ≠ 0) (ha0 : f a = 0) :
    pwNormSq (fun z ↦ dslope f a z * (z - conj a)) = pwNormSq f := by
  sorry

end FF
