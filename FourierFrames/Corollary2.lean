import FourierFrames.Construction
import FourierFrames.Perturbation
import FourierFrames.Theorem1.Sufficiency
import FourierFrames.HB.Comparable

/-!
# M07 — Corollary 2 (p. 800)

See `blueprint/M07_Corollary2.md`, §3.

`Λ(ψ)` is sampling if there is `f ∈ \overline{HB}` with `φ_f' → 0` and `U_ψ - log|f| = O(1)` on
`Im z ≥ 0`.  Proof: with `ω' = 1 + ψ' - φ_f'/π` (modified on a compact set to be `≃ 1`), the
construction of `Construction.lean` gives `E ∈ \overline{HB}` with `|E| ≃ e^{π Im z}` and
`φ_E + φ_f = π(x + ψ(x)) + c + o(1)`; the zero set of `E f + E^* f^*` is sampling by
`theorem1_sufficiency` and is a perturbation (`IsSampling.of_perturbation`) of `Λ(ψ)`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Rotating `E` by a unimodular constant -/

section Rotation

theorem phaseDeriv_rotate (E : ℂ → ℂ) (β : ℝ) (x : ℝ) :
    phaseDeriv (fun z ↦ Complex.exp (Complex.I * β) * E z) x = phaseDeriv E x := by
  sorry

end Rotation

/-! ## The potentials `U_g = OCS.multU g 0` of bounded densities -/

section Potentials

/-- `U_ψ` is the potential `OCS.multU` of the density `ψ'` (same integrand, constant `0`). -/
theorem UPsi_eq_multU (ψ : ℝ → ℝ) (z : ℂ) : UPsi ψ z = OCS.multU (deriv ψ) 0 z := by
  sorry

/-- The integrand of `multU` is integrable for every bounded measurable density (for weights this is
`OCS.integrable_multUIntegrand`; a bounded `g` is `(g + K) - K` with `g + K ≥ 1`). -/
theorem integrable_multU_integrand_of_bdd {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ t, |g t| ≤ M) (z : ℂ) :
    Integrable fun t : ℝ ↦
      (Real.log ‖1 - z / t‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).re) * g t := by
  sorry

theorem multU_add {g h : ℝ → ℝ} (hg : Measurable g) (hh : Measurable h) {M : ℝ}
    (hgM : ∀ t, |g t| ≤ M) (hhM : ∀ t, |h t| ≤ M) (z : ℂ) :
    OCS.multU (fun t ↦ g t + h t) 0 z = OCS.multU g 0 z + OCS.multU h 0 z := by
  sorry

theorem multU_const_mul {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) (c : ℝ)
    (z : ℂ) : OCS.multU (fun t ↦ c * g t) 0 z = c * OCS.multU g 0 z := by
  sorry

/-- The potential of Lebesgue measure: `U_1(z) = π |Im z|`.  (Compute
`∫_{-T}^{T} log|1 - z/t| dt` with the antiderivative of `½ log(u² + y²)` and let `T → ∞`;
the odd term `Re(z/t)` integrates to `0` over `[-T, T] ∖ [-1, 1]`.) -/
theorem multU_one (z : ℂ) : OCS.multU (fun _ ↦ (1 : ℝ)) 0 z = Real.pi * |z.im| := by
  sorry

/-- Growth of potentials of bounded densities. -/
theorem abs_multU_le_of_bdd {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    ∃ K : ℝ, ∀ z : ℂ, |OCS.multU g 0 z| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
  sorry

/-- Potential of a compactly supported bounded density of total mass `0`: bounded up to the linear
term `(∫_{|t| > 1} h(t)/t dt) Re z` coming from the `Re(z/t)` normalisation. -/
theorem multU_compact_sub_linear {h : ℝ → ℝ} (hh : Measurable h) {M R : ℝ}
    (hM : ∀ t, |h t| ≤ M) (hR : ∀ t, R < |t| → h t = 0) (h0 : ∫ t, h t = 0) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU h 0 z - (∫ t, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (h t / t)) * z.re| ≤ C := by
  sorry

end Potentials

/-! ## `log|f|` is the potential of `φ_f'/π` up to an affine function -/

section LogPotential

/-- Continuity of the potential of a bounded density. -/
theorem continuous_multU_of_bdd {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    Continuous (OCS.multU g 0) := by
  sorry

/-- The boundary-continuous argument: for `t < 0` the number `1 - z/t` has `Im ≥ 0` when
`Im z ≥ 0` and we take `arg ∈ [0, π]`; for `t > 0` it has `Im ≤ 0` and we take
`-arg (conj (1 - z/t)) ∈ [-π, 0]`.  This is the branch of `Im Log(1 - z/t)` continuous on
`Im z ≥ 0`, `z ≠ t`. -/
def argUp (z : ℂ) (t : ℝ) : ℝ :=
  if t < 0 then Complex.arg (1 - z / t) else -Complex.arg (conj (1 - z / t))

/-- The complex potential `Q_g(z) = ∫ [log|1 - z/t| + i argUp z t + 1_{|t|>1} z/t] g(t) dt`
(`= ∫ [Log(1 - z/t) + 1_{|t|>1} z/t] g(t) dt` on `Im z > 0`; `π P = Q_g`). -/
def potC (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (((Real.log ‖1 - z / t‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).re : ℝ) : ℂ) +
    Complex.I * ((argUp z t + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).im : ℝ) : ℂ)) *
      (g t : ℂ)

theorem potC_re {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) (z : ℂ) :
    (potC g z).re = OCS.multU g 0 z := by
  sorry

theorem differentiableOn_potC {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    DifferentiableOn ℂ (potC g) {z : ℂ | 0 < z.im} := by
  sorry

theorem continuousOn_potC {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    ContinuousOn (potC g) {z : ℂ | 0 ≤ z.im} := by
  sorry

/-- On the real axis `Im Q_g(x) = -π (φ(x) - φ(0))` when `φ' = g`
(`argUp x t = -π` for `0 < t < x` or `x < t < 0` with sign `±`, and `0` otherwise). -/
theorem potC_im_ofReal {g φ : ℝ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ t, |g t| ≤ M)
    (hφ : ∀ x, HasDerivAt φ (g x) x) (x : ℝ) :
    (potC g (x : ℂ)).im = -Real.pi * (φ x - φ 0) := by
  sorry

/-- **Schwarz reflection** (via Morera on discs and the rectangle theorem for functions continuous
on a closed half-disc): `H` continuous on `Im z ≥ 0`, holomorphic on `Im z > 0`, with `Im H = c`
on `ℝ`, extends to an entire function with `H(z̄) = conj H(z) + 2ic`... precisely
`H^ext(z) = conj (H (conj z)) + 2 i c` for `Im z < 0`. -/
theorem exists_entire_reflection {H : ℂ → ℂ} (hc : ContinuousOn H {z : ℂ | 0 ≤ z.im})
    (hd : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) {c : ℝ} (him : ∀ x : ℝ, (H x).im = c) :
    ∃ Ĥ : ℂ → ℂ, Differentiable ℂ Ĥ ∧ (∀ z : ℂ, 0 ≤ z.im → Ĥ z = H z) ∧
      ∀ z : ℂ, Ĥ (conj z) = conj (Ĥ z) + 2 * Complex.I * c := by
  sorry

/-- An entire function whose real part grows like `|z|^{3/2}` is affine
(Borel–Carathéodory, then Cauchy's estimate for `H''`). -/
theorem entire_affine_of_re_growth {H : ℂ → ℂ} (hH : Differentiable ℂ H) {K : ℝ}
    (hK : ∀ z : ℂ, |(H z).re| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ)) :
    ∃ α β : ℂ, ∀ z : ℂ, H z = α + β * z := by
  sorry

/-- **Key identity** (the harmonic correction is affine).  Let `f` be entire without zeros on
`Im z ≥ 0` with phase function `φ`, `φ' = g` continuous and bounded, and `|log|f|| ≲ (1+|z|)^{3/2}`
on `Im z ≥ 0`.  Then `log|f| = U_g/π + b Re z + c` on `Im z ≥ 0` for real `b, c`.

Proof (blueprint §3.2): `P(z) = (1/π) ∫ [Log(1 - z/t) + 1_{|t|>1} z/t] g(t) dt` is holomorphic on
`Im z > 0`, continuous on `Im z ≥ 0`, `Re P = U_g/π`, `Im P(x) = -(φ(x) - φ(0))`; a holomorphic
logarithm `L` of `f` on `Im z ≥ 0` has `Im L(x) = -φ(x) + const`; so `H = L - P` has constant
imaginary part on `ℝ`, extends by Schwarz reflection to an entire function with
`|Re H| ≲ (1 + |z|)^{3/2}`; Borel–Carathéodory and Cauchy's estimates give `H(z) = α + β z`,
`β` real. -/
theorem log_norm_eq_multU_add_affine {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : ∀ z : ℂ, 0 ≤ z.im → f z ≠ 0) {φ g : ℝ → ℝ} (hφ : IsPhaseFunction f φ)
    (hφ' : ∀ x, HasDerivAt φ (g x) x) (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    (hgrow : ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |Real.log ‖f z‖| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ)) :
    ∃ b c : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.log ‖f z‖ = OCS.multU g 0 z / Real.pi + b * z.re + c := by
  sorry

end LogPotential

/-! ## The density `m` and the phase comparison -/

section Density

/-- **Modification on a compact set.**  Given a continuous `w → 0` and `β ∈ ℝ`, there are `R > 0`
and a measurable `m` with `a ≤ m ≤ b`, `m = 1 + w` for `|t| > R`, `∫ (m - 1 - w) = 0` and
`∫_{|t|>1} (m - 1 - w)(t)/t dt = -β`.  (Take `m = c + s sgn(t) 1_{1<|t|<R}` on `[-R, R]` with
`c = (2R)⁻¹ ∫_{-R}^{R} (1 + w)`, `s = (-β + ∫_{1<|t|<R} (1+w)/t) / (2 log R)`.) -/
theorem exists_modified_density {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : Tendsto w (cocompact ℝ) (𝓝 0)) (β : ℝ) :
    ∃ (R : ℝ) (m : ℝ → ℝ) (a b : ℝ), 0 < R ∧ 0 < a ∧ Measurable m ∧ (∀ t, a ≤ m t) ∧
      (∀ t, m t ≤ b) ∧ (∀ t, R < |t| → m t = 1 + w t) ∧
      (∫ t, (m t - (1 + w t)) = 0) ∧
      (∫ t, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((m t - (1 + w t)) / t)) = -β := by
  sorry

/-- **Good density.**  Under the hypotheses of Corollary 2 and for a phase function `φ_f`, there
are a density `m` (`a ≤ m ≤ b`, `m → 1`) with `U_m - π Im z = O(1)` on `Im z ≥ 0` and a constant `κ`
with `π M(x) + φ_f(x) = π (x + ψ(x)) + κ` for `|x| ≥ R` (`M = OCS.multPrim m`). -/
theorem exists_good_density {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {f : ℂ → ℂ} (hf : IsHB f)
    (hφ : Tendsto (phaseDeriv f) (cocompact ℝ) (𝓝 0))
    (happ : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.exp (UPsi ψ z - C) ≤ ‖f z‖ ∧ ‖f z‖ ≤ Real.exp (UPsi ψ z + C))
    {φf : ℝ → ℝ} (hφf : IsPhaseFunction f φf) (hφf' : ∀ x, HasDerivAt φf (phaseDeriv f x) x) :
    ∃ (m : ℝ → ℝ) (a b κ R : ℝ), Measurable m ∧ 0 < a ∧ (∀ t, a ≤ m t) ∧ (∀ t, m t ≤ b) ∧
      Tendsto m (cocompact ℝ) (𝓝 1) ∧
      (∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → |OCS.multU m 0 z - Real.pi * z.im| ≤ C) ∧
      ∀ x : ℝ, R ≤ |x| → Real.pi * OCS.multPrim m x + φf x = Real.pi * (x + ψ x) + κ := by
  sorry

end Density

/-! ## From the phase to a perturbation of `Λ(ψ)` -/

section PhasePerturbation

/-- `x ↦ x + ψ(x)` is a strictly increasing, `1`-expanding bijection of `ℝ`. -/
theorem strictMono_add_psi {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) :
    StrictMono (fun x ↦ x + ψ x) ∧ Function.Surjective (fun x ↦ x + ψ x) ∧
      ∀ x y : ℝ, x ≤ y → y - x ≤ (y + ψ y) - (x + ψ x) := by
  sorry

/-- **Matching the zero set with `Λ(ψ)`.**  Let `Θ` be a continuous strictly increasing bijection
of `ℝ` with `Θ(x)/π - (x + ψ(x)) → 0` as `|x| → ∞`.  Then `Λ(ψ) = {x + δ(x) : Θ(x) ∈ π ℤ}` for a
`δ` that is injective on `{Θ ∈ π ℤ}` and tends to `0` at infinity (`δ(x) = Ψ⁻¹(Θ(x)/π) - x`,
`Ψ(x) = x + ψ(x)`, with `|δ(x)| ≤ |Θ(x)/π - Ψ(x)|`). -/
theorem exists_perturbation_of_phase {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {Θ : ℝ → ℝ}
    (hΘ : StrictMono Θ) (hΘs : Function.Surjective Θ)
    (hlim : Tendsto (fun x ↦ Θ x / Real.pi - (x + ψ x)) (cocompact ℝ) (𝓝 0)) :
    ∃ δ : ℝ → ℝ, InjOn (fun x ↦ x + δ x) {x | ∃ k : ℤ, Θ x = k * Real.pi} ∧
      (fun x ↦ x + δ x) '' {x | ∃ k : ℤ, Θ x = k * Real.pi} = LambdaPsi ψ ∧
      Tendsto δ (cocompact ℝ) (𝓝 0) := by
  sorry

/-- If `Θ` is strictly increasing with `Θ(y) - Θ(x) ≤ C (y - x)` for `x ≤ y`, then `{Θ ∈ π ℤ}`
is separated (by `π / C`). -/
theorem isSeparated_levelSet {Θ : ℝ → ℝ} (hΘ : StrictMono Θ) {C : ℝ} (hC : 0 < C)
    (hlip : ∀ x y : ℝ, x ≤ y → Θ y - Θ x ≤ C * (y - x)) :
    IsSeparated {x | ∃ k : ℤ, Θ x = k * Real.pi} := by
  sorry

/-- A derivative bound gives the Lipschitz bound (`image_sub_le_mul_sub_of_deriv_le`). -/
theorem sub_le_mul_sub_of_hasDerivAt {Θ d : ℝ → ℝ} (hΘ : ∀ x, HasDerivAt Θ (d x) x) {C : ℝ}
    (hd : ∀ x, d x ≤ C) {x y : ℝ} (hxy : x ≤ y) : Θ y - Θ x ≤ C * (y - x) := by
  sorry

end PhasePerturbation

/-! ## Corollary 2 -/

/-- **Corollary 2** (p. 800): `Λ(ψ)` is sampling for `PW` if there is `f ∈ \overline{HB}` with
`φ_f'(x) → 0` as `|x| → ∞` and `|U_ψ(z) - log|f(z)|| ≲ 1` for `Im z ≥ 0`. -/
theorem corollary2 (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {f : ℂ → ℂ} (hf : IsHB f)
    (hφ : Tendsto (phaseDeriv f) (cocompact ℝ) (𝓝 0))
    (happ : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.exp (UPsi ψ z - C) ≤ ‖f z‖ ∧ ‖f z‖ ≤ Real.exp (UPsi ψ z + C)) :
    IsSampling (LambdaPsi ψ) := by
  sorry

end FF
