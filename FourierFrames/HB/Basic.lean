import FourierFrames.Defs

/-!
# M02 — `f^*`, the Hermite–Biehler class

See `blueprint/M02_HB.md`, §2–§3.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Algebra of `f^*` -/

@[simp] theorem fstar_apply (f : ℂ → ℂ) (z : ℂ) : fstar f z = conj (f (conj z)) := rfl

@[simp] theorem fstar_fstar (f : ℂ → ℂ) : fstar (fstar f) = f := by
  funext z; simp [fstar]

theorem fstar_mul (f g : ℂ → ℂ) :
    fstar (fun z ↦ f z * g z) = fun z ↦ fstar f z * fstar g z := by
  funext z; simp [fstar]

theorem fstar_add (f g : ℂ → ℂ) :
    fstar (fun z ↦ f z + g z) = fun z ↦ fstar f z + fstar g z := by
  funext z; simp [fstar]

theorem fstar_sub (f g : ℂ → ℂ) :
    fstar (fun z ↦ f z - g z) = fun z ↦ fstar f z - fstar g z := by
  funext z; simp [fstar]

theorem fstar_const_mul (c : ℂ) (f : ℂ → ℂ) :
    fstar (fun z ↦ c * f z) = fun z ↦ conj c * fstar f z := by
  funext z; simp [fstar]

theorem fstar_div (f g : ℂ → ℂ) :
    fstar (fun z ↦ f z / g z) = fun z ↦ fstar f z / fstar g z := by
  funext z; simp [fstar]

/-- `f^*(x) = conj (f x)` for real `x`. -/
theorem fstar_ofReal (f : ℂ → ℂ) (x : ℝ) : fstar f (x : ℂ) = conj (f (x : ℂ)) := by
  simp [fstar]

theorem norm_fstar (f : ℂ → ℂ) (z : ℂ) : ‖fstar f z‖ = ‖f (conj z)‖ := by
  simp [fstar]

theorem Differentiable.fstar {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (FF.fstar f) := by
  intro z
  have h := (hf (conj z)).conj_conj
  rw [Complex.conj_conj] at h
  exact h

/-- `(f^*)'(z) = conj (f'(z̄))`. -/
theorem deriv_fstar (f : ℂ → ℂ) (z : ℂ) :
    deriv (fstar f) z = conj (deriv f (conj z)) := by
  have h := congrFun (deriv_conj_conj (𝕜 := ℂ) (f := f)) z
  exact h

/-- For real `x`: `(f^*)'(x) = conj (f'(x))`. -/
theorem deriv_fstar_ofReal (f : ℂ → ℂ) (x : ℝ) :
    deriv (fstar f) (x : ℂ) = conj (deriv f (x : ℂ)) := by
  simp [deriv_fstar]

/-! ## The class `\overline{HB}` -/

theorem isHB_one : IsHB (fun _ : ℂ ↦ (1 : ℂ)) := by
  refine ⟨differentiable_const _, fun _ _ ↦ one_ne_zero, fun _ _ ↦ le_rfl⟩

theorem IsHB.mul {E F : ℂ → ℂ} (hE : IsHB E) (hF : IsHB F) : IsHB (fun z ↦ E z * F z) := by
  obtain ⟨hEd, hE0, hE1⟩ := hE
  obtain ⟨hFd, hF0, hF1⟩ := hF
  refine ⟨hEd.mul hFd, fun z hz ↦ mul_ne_zero (hE0 z hz) (hF0 z hz), fun z hz ↦ ?_⟩
  simp only [norm_mul]
  exact mul_le_mul (hE1 z hz) (hF1 z hz) (norm_nonneg _) (norm_nonneg _)

/-- The zeros of `E ∈ \overline{HB}` lie in `Im z ≤ 0`, and `|E^*(z)| ≤ |E(z)|` on `Im z > 0`. -/
theorem IsHB.norm_fstar_le {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : 0 < z.im) :
    ‖fstar E z‖ ≤ ‖E z‖ := by
  rw [norm_fstar]; exact hE.2.2 z hz

/-- **Dichotomy** for `E ∈ \overline{HB}`: either `|E(z̄)| < |E(z)|` on `Im z > 0` (`E` strict) or
`E^* = c E` with `|c| = 1`.  (Maximum modulus for `E^*/E`, then the identity theorem.) -/
theorem IsHB.isStrictHB_or_fstar_eq {E : ℂ → ℂ} (hE : IsHB E) :
    IsStrictHB E ∨ ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z : ℂ, fstar E z = c * E z := by
  sorry

/-- If `E ∈ \overline{HB}` is strict at one point of `Im z > 0`, it is strict everywhere. -/
theorem IsHB.isStrictHB_of_exists_lt {E : ℂ → ℂ} (hE : IsHB E)
    (h : ∃ z : ℂ, 0 < z.im ∧ ‖E (conj z)‖ < ‖E z‖) : IsStrictHB E := by
  sorry

/-- **Hurwitz-type closure.**  A locally uniform limit of functions of `\overline{HB}` is in
`\overline{HB}` unless it vanishes identically. -/
theorem IsHB.of_tendstoLocallyUniformly {ι : Type*} {p : Filter ι} [p.NeBot]
    {E : ι → ℂ → ℂ} {E₀ : ℂ → ℂ} (hE : ∀ i, IsHB (E i))
    (hlim : TendstoLocallyUniformly E E₀ p) (hne : ∃ z, E₀ z ≠ 0) : IsHB E₀ := by
  sorry

/-- Added at assembly (requested by M04): `E` strict, `F ∈ \overline{HB}` ⇒ `E F` strict.
(`|E F (z̄)| ≤ |E(z̄)| |F(z)| < |E(z)| |F(z)|`, using `F(z) ≠ 0` for `Im z > 0`.) -/
theorem IsStrictHB.mul_isHB {E F : ℂ → ℂ} (hE : IsStrictHB E) (hF : IsHB F) :
    IsStrictHB (fun z ↦ E z * F z) := by
  sorry

/-- Added at assembly (moved from `Corollary1.lean` / `Corollary2.lean`): a unimodular constant
factor preserves `\overline{HB}`. -/
theorem IsHB.rotate {E : ℂ → ℂ} (hE : IsHB E) (θ : ℝ) :
    IsHB (fun z ↦ Complex.exp (I * θ) * E z) := by
  sorry

end FF
