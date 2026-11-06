module

public import Mathlib

/-!
# Statement-level definitions

J. Ortega-Cerdà and K. Seip, *Fourier frames*, Ann. of Math. (2) **155** (2002), 789–806,
MR1923965.

This file imports only `Mathlib` and contains every definition that appears in the statements of
the main theorems, including the cited results that enter the statements as explicit `Prop`
hypotheses.  It is copied verbatim into `FFChallenge.lean` (the self-contained file checked by
`comparator`), so it must stay free of project imports.

Conventions (see `blueprint/M00_Defs.md`):

* A sequence `Λ` of distinct real numbers is a `Set ℝ`.  Theorem 1 concerns separated sequences,
  whose points are automatically distinct, so no enumeration is needed.
* Sums, integrals and norms that may be infinite are `ℝ≥0∞`-valued (`∑'`, `∫⁻`), so that infinite
  quantities never silently become `0`.
* `f^*(z) = conj (f (conj z))` (`fstar`).
* The Hermite–Biehler class is the paper's closed class `\overline{HB}`: entire `E` with no zeros
  in the upper half-plane and `|E(z̄)| ≤ |E(z)|` for `Im z > 0` (`IsHB`).
* The phase function `φ_E` of `E` (with `E(x) = |E(x)| e^{-iφ_E(x)}` on `ℝ`) enters only through
  its derivative, which for `E` without real zeros is `φ_E'(x) = -Im (E'(x)/E(x))`
  (`phaseDeriv`), and through the level sets `{φ_E ∈ α + πℤ}` (`IsPhaseFunction`).
* Cited results of the literature (de Branges' Theorems C, E, F, the Paley–Wiener theorem,
  Pavlov's Theorem A, the John–Nirenberg theorem, Lemma III of Duffin–Schaeffer) are `Prop`s,
  never axioms.  Each is stated in the weakest form the paper uses; see `blueprint/M00_Defs.md`
  for the reasons each one is true.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

@[expose] public noncomputable section

namespace FF

/-! ## Entire functions of exponential type and the Paley–Wiener space -/

/-- `f` has *exponential type at most `τ`*: for every `ε > 0`, `|f(z)| ≤ C_ε e^{(τ+ε)|z|}`. -/
def IsExpTypeLE (τ : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖)

/-- The *Paley–Wiener space* `PW` (p. 790): entire functions of exponential type at most `π`
whose restrictions to `ℝ` are square integrable. -/
def MemPW (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ IsExpTypeLE Real.pi f ∧ MemLp (fun x : ℝ ↦ f x) 2

/-- The squared norm of `PW`, `‖f‖²_{PW} = ∫_ℝ |f(x)|² dx`. -/
def pwNormSq (f : ℂ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ‖f x‖ₑ ^ 2

/-! ## Sampling, separated and complete interpolating sequences -/

/-- The sampling sum `∑_{λ ∈ Λ} |f(λ)|²`. -/
def sampleSum (Λ : Set ℝ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  ∑' x : Λ, ‖f ((x : ℝ) : ℂ)‖ₑ ^ 2

/-- `Λ` is *sampling* for `PW` (p. 790): `A ‖f‖² ≤ ∑_{λ ∈ Λ} |f(λ)|² ≤ B ‖f‖²` for all `f ∈ PW`,
with constants `0 < A`, `B < ∞`. -/
def IsSampling (Λ : Set ℝ) : Prop :=
  ∃ A B : ℝ≥0, 0 < A ∧ ∀ f : ℂ → ℂ, MemPW f →
    A * pwNormSq f ≤ sampleSum Λ f ∧ sampleSum Λ f ≤ B * pwNormSq f

/-- `Λ` is *separated* (p. 791): `inf_{λ ≠ λ'} |λ - λ'| > 0`. -/
def IsSeparated (Λ : Set ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ |a - b|

/-- `Λ` is a *complete interpolating sequence* for `PW` (p. 791): for every square-summable datum
`(a(λ))_{λ ∈ Λ}` the interpolation problem `f(λ) = a(λ)`, `λ ∈ Λ`, has a unique solution in `PW`.
Only the values of `a` on `Λ` matter. -/
def IsCompleteInterpolating (Λ : Set ℝ) : Prop :=
  ∀ a : ℝ → ℂ, (∑' x : Λ, ‖a x‖ₑ ^ 2) < ∞ →
    ∃! f : ℂ → ℂ, MemPW f ∧ ∀ x ∈ Λ, f x = a x

/-- `{e^{iλx}}_{λ ∈ Λ}` is a *Fourier frame* (p. 789):
`A ∫_{-π}^{π} |g|² ≤ ∑_{λ ∈ Λ} |∫_{-π}^{π} g(x) e^{-iλx} dx|² ≤ B ∫_{-π}^{π} |g|²` for all
`g ∈ L²(-π, π)`. -/
def IsFourierFrame (Λ : Set ℝ) : Prop :=
  ∃ A B : ℝ≥0, 0 < A ∧ ∀ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) →
    A * (∫⁻ x in Ioc (-Real.pi) Real.pi, ‖g x‖ₑ ^ 2) ≤
        ∑' l : Λ, ‖∫ x in (-Real.pi)..Real.pi, g x * Complex.exp (-(I * ((l : ℝ) : ℂ) * x))‖ₑ ^ 2 ∧
      ∑' l : Λ, ‖∫ x in (-Real.pi)..Real.pi, g x * Complex.exp (-(I * ((l : ℝ) : ℂ) * x))‖ₑ ^ 2 ≤
        B * (∫⁻ x in Ioc (-Real.pi) Real.pi, ‖g x‖ₑ ^ 2)

/-! ## Counting functions, densities and BMO -/

/-- The counting function `n_Λ` (p. 791): `n_Λ(b) - n_Λ(a) = #(Λ ∩ (a, b])`, normalised by
`n_Λ(0) = 0`.  (Real-valued; meaningful when `Λ` meets bounded intervals in finite sets.) -/
def countFn (Λ : Set ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then ((Λ ∩ Ioc 0 t).ncard : ℝ) else -((Λ ∩ Ioc t 0).ncard : ℝ)

/-- The mean of `h` over `[a, b]`. -/
def intervalMean (h : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a)⁻¹ * ∫ t in a..b, h t

/-- The mean oscillation of `h` over `[a, b]`, `|I|⁻¹ ∫_I |h - h_I|`. -/
def meanOsc (h : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a)⁻¹ * ∫ t in a..b, |h t - intervalMean h a b|

/-- `h ∈ BMO(ℝ)`: `h` is locally integrable and its mean oscillation over bounded intervals is
bounded. -/
def MemBMO (h : ℝ → ℝ) : Prop :=
  LocallyIntegrable h ∧ ∃ M : ℝ, ∀ a b : ℝ, a < b → meanOsc h a b ≤ M

/-! ## Hardy space, the Hermite–Biehler class and de Branges spaces (§2) -/

/-- `f^*(z) = conj (f (conj z))`. -/
def fstar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  conj (f (conj z))

/-- `g` belongs to the Hardy space `H²` of the upper half-plane: holomorphic there with
`sup_{y > 0} ∫ |g(x + iy)|² dx < ∞`. -/
def IsH2Upper (g : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ g {z : ℂ | 0 < z.im} ∧
    ∃ C : ℝ≥0, ∀ y : ℝ, 0 < y → ∫⁻ x : ℝ, ‖g ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ C

/-- The (closed) *Hermite–Biehler class* `\overline{HB}` (p. 793): entire functions with no zeros in
the upper half-plane and `|E(z̄)| ≤ |E(z)|` for `Im z > 0`. -/
def IsHB (E : ℂ → ℂ) : Prop :=
  Differentiable ℂ E ∧ (∀ z : ℂ, 0 < z.im → E z ≠ 0) ∧
    ∀ z : ℂ, 0 < z.im → ‖E (conj z)‖ ≤ ‖E z‖

/-- `E` satisfies the *strict* Hermite–Biehler inequality `|E(z̄)| < |E(z)|` for `Im z > 0`
(the class `HB` of de Branges). -/
def IsStrictHB (E : ℂ → ℂ) : Prop :=
  IsHB E ∧ ∀ z : ℂ, 0 < z.im → ‖E (conj z)‖ < ‖E z‖

/-- The de Branges space `H(E)` (p. 793): entire `f` with `f/E` and `f^*/E` in `H²` of the upper
half-plane. -/
def MemHE (E f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ IsH2Upper (fun z ↦ f z / E z) ∧ IsH2Upper (fun z ↦ fstar f z / E z)

/-- The squared norm of `H(E)`, `‖f‖²_E = ∫_ℝ |f(t)/E(t)|² dt`. -/
def heNormSq (E f : ℂ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, ‖f t / E t‖ₑ ^ 2

/-- `H(E) = PW` in the sense of the paper (p. 794): the two spaces coincide as sets and their norms
are equivalent. -/
def HEEqPW (E : ℂ → ℂ) : Prop :=
  (∀ f : ℂ → ℂ, MemHE E f ↔ MemPW f) ∧
    ∃ c C : ℝ≥0, 0 < c ∧ ∀ f : ℂ → ℂ, MemPW f →
      c * pwNormSq f ≤ heNormSq E f ∧ heNormSq E f ≤ C * pwNormSq f

/-- `φ` is a *phase function* of `E` (p. 794): `φ` is continuous and `E(x) = |E(x)| e^{-iφ(x)}`
for real `x`. -/
def IsPhaseFunction (E : ℂ → ℂ) (φ : ℝ → ℝ) : Prop :=
  Continuous φ ∧ ∀ x : ℝ, E x = (‖E x‖ : ℂ) * Complex.exp (-(I * φ x))

/-- The derivative of the phase function, `φ_E'(x) = -Im (E'(x)/E(x))`, for `E` without real
zeros. -/
def phaseDeriv (E : ℂ → ℂ) (x : ℝ) : ℝ :=
  -(deriv E x / E x).im

/-- The level set `{x ∈ ℝ : φ(x) ∈ α + πℤ}` of a phase function. -/
def phaseLevel (φ : ℝ → ℝ) (α : ℝ) : Set ℝ :=
  {x : ℝ | ∃ k : ℤ, φ x = α + k * Real.pi}

/-- The weight `π / (φ_E'(x) |E(x)|²)` of the orthogonal sampling formula (Theorem E); it is
`1 / K_E(x, x)`. -/
def orthWeight (E : ℂ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.pi / (phaseDeriv E x * ‖E x‖ ^ 2))

/-- The Poisson integral `(y/π) ∫ dμ(t) / ((t - x)² + y²)` of a positive measure on `ℝ`. -/
def poissonInt (μ : Measure ℝ) (z : ℂ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, ENNReal.ofReal (z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2))) ∂μ

/-! ## Cited results

The paper quotes the following results without proof.  They enter the formal statements as
explicit hypotheses, never as axioms.  Each `Prop` is implied by the statement in the source
(see `blueprint/M00_Defs.md`). -/

/-- **The Paley–Wiener theorem**, with Plancherel's identity (p. 790): `f ∈ PW` if and only if
`f(z) = ∫_{-π}^{π} g(t) e^{izt} dt` for some `g ∈ L²(-π, π)`, and then
`‖f‖²_{L²(ℝ)} = 2π ‖g‖²_{L²(-π, π)}`. -/
def PaleyWienerThm : Prop :=
  ∀ f : ℂ → ℂ, MemPW f ↔
    ∃ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) ∧
      (∀ z : ℂ, f z = ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)) ∧
      pwNormSq f = ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2

/-- **Theorem C** (de Branges [dB68, Theorem 23], p. 793).  A Hilbert space `H` of entire
functions (given by an injective linear map `ι`) satisfying the axioms
* (H1) if `f ∈ H` has a nonreal zero `ζ`, then `f(z)(z - ζ̄)/(z - ζ) ∈ H` with the same norm,
* (H2) evaluation at every nonreal point is continuous,
* (H3) `f ∈ H ⇒ f^* ∈ H` with the same norm,
and containing a nonzero element, is equal isometrically to some `H(E)`. -/
def TheoremC : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ι : H →ₗ[ℂ] (ℂ → ℂ)), Function.Injective ι → (∀ h : H, Differentiable ℂ (ι h)) →
    (∀ h : H, ∀ ζ : ℂ, ζ.im ≠ 0 → ι h ζ = 0 →
      ∃ g : H, ‖g‖ = ‖h‖ ∧ ∀ z : ℂ, z ≠ ζ → ι g z = ι h z * (z - conj ζ) / (z - ζ)) →
    (∀ ζ : ℂ, ζ.im ≠ 0 → Continuous fun h : H ↦ ι h ζ) →
    (∀ h : H, ∃ g : H, ‖g‖ = ‖h‖ ∧ ι g = fstar (ι h)) →
    (∃ h : H, h ≠ 0) →
    ∃ E : ℂ → ℂ, IsHB E ∧ (∀ f : ℂ → ℂ, MemHE E f ↔ f ∈ Set.range ι) ∧
      ∀ h : H, ENNReal.ofReal (‖h‖ ^ 2) = heNormSq E (ι h)

/-- The reproducing kernel of `H(E)` given by formula (1) (p. 793),
`K_E(w, z) = (i/2) (E(z) conj E(w) - E^*(z) conj E^*(w)) / (π (z - w̄))`, extended to `z = w̄` by
its limit `(i/2π) (E'(w̄) conj E(w) - (E^*)'(w̄) conj E^*(w))`. -/
def deBrangesKernel (E : ℂ → ℂ) (w z : ℂ) : ℂ :=
  if z = conj w then
    (I / (2 * Real.pi)) * (deriv E z * conj (E w) - deriv (fstar E) z * conj (fstar E w))
  else (I / 2) * (E z * conj (E w) - fstar E z * conj (fstar E w)) / (Real.pi * (z - conj w))

/-- **Theorem D** (de Branges [dB68, Theorem 19], p. 793), for `E` in the strict class without
real zeros: `K_E(w, ·) ∈ H(E)` and `⟨f, K_E(w, ·)⟩_E = f(w)` for every `f ∈ H(E)` and `w ∈ ℂ`. -/
def TheoremD : Prop :=
  ∀ E : ℂ → ℂ, IsStrictHB E → (∀ x : ℝ, E x ≠ 0) → ∀ w : ℂ, MemHE E (deBrangesKernel E w) ∧
    ∀ f : ℂ → ℂ, MemHE E f →
      ∫ t : ℝ, f t * conj (deBrangesKernel E w t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) = f w

/-- **Theorem E** (de Branges [dB68, Theorem 22], p. 794), for `E` in the strict class without
real zeros.  Let `φ` be a phase function of `E` and `α ∈ ℝ` with
`e^{iα} E - e^{-iα} E^* ∉ H(E)`, and let `Γ = {φ ∈ α + πℤ}`.  Then the normalized reproducing
kernels at `Γ` form an orthonormal basis of `H(E)`; in the form used:
* `‖f‖²_E = ∑_{γ ∈ Γ} π |f(γ)|² / (φ'(γ) |E(γ)|²)` for all `f ∈ H(E)`, and
* every datum with `∑_{γ ∈ Γ} π |a(γ)|² / (φ'(γ) |E(γ)|²) < ∞` is interpolated on `Γ` by some
  `f ∈ H(E)`. -/
def TheoremE : Prop :=
  ∀ E : ℂ → ℂ, IsStrictHB E → (∀ x : ℝ, E x ≠ 0) → ∀ φ : ℝ → ℝ, IsPhaseFunction E φ →
    ∀ α : ℝ, ¬ MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z) →
      (∀ f : ℂ → ℂ, MemHE E f →
          heNormSq E f = ∑' γ : phaseLevel φ α, orthWeight E γ * ‖f γ‖ₑ ^ 2) ∧
        ∀ a : ℝ → ℂ, ∑' γ : phaseLevel φ α, orthWeight E γ * ‖a γ‖ₑ ^ 2 < ∞ →
          ∃ f : ℂ → ℂ, MemHE E f ∧ ∀ γ ∈ phaseLevel φ α, f γ = a γ

/-- **Theorem F** (de Branges [dB60], p. 794), the implication used in the paper, for `E` in the
strict class without real zeros.  If `H(E)` is contained isometrically in `L²(μ/|E|²)`, then there
is a holomorphic `A` on the upper half-plane with `|A| ≤ 1` such that
`(y/π) ∫ dμ(t)/((t-x)² + y²) + p y = Re ((E + E^* A)/(E - E^* A))` for some `p ≥ 0`.  (The paper
states this with `p = 0`; allowing `p ≥ 0` weakens the hypothesis, and the proof of Theorem 1
works verbatim.) -/
def TheoremF : Prop :=
  ∀ (μ : Measure ℝ) (E : ℂ → ℂ), IsStrictHB E → (∀ x : ℝ, E x ≠ 0) →
    (∀ f : ℂ → ℂ, MemHE E f → ∫⁻ t, ‖f t / E t‖ₑ ^ 2 ∂μ = heNormSq E f) →
    ∃ A : ℂ → ℂ, DifferentiableOn ℂ A {z : ℂ | 0 < z.im} ∧ (∀ z : ℂ, 0 < z.im → ‖A z‖ ≤ 1) ∧
      ∃ p : ℝ, 0 ≤ p ∧ ∀ z : ℂ, 0 < z.im → poissonInt μ z ≠ ∞ ∧
        (poissonInt μ z).toReal + p * z.im =
          ((E z + fstar E z * A z) / (E z - fstar E z * A z)).re

/-- **Theorem A** (Pavlov; Hruščev–Nikol'skiĭ–Pavlov, p. 791), the necessity half in the form
used: if a separated sequence `Γ` is a complete interpolating sequence for `PW`, then
`h(t) = n_Γ(t) - t` belongs to `BMO(ℝ)`. -/
def PavlovBMO : Prop :=
  ∀ Γ : Set ℝ, IsSeparated Γ → IsCompleteInterpolating Γ → MemBMO (fun t ↦ countFn Γ t - t)

/-- **The John–Nirenberg theorem** ([JN61], [Ga81, p. 230], p. 799): there are absolute constants
`C, c > 0` such that, if `h` has mean oscillation at most `M` on every bounded interval, then
`|{t ∈ I : |h(t) - h_I| ≥ s}| ≤ C e^{-cs/M} |I|` for every bounded interval `I` and `s > 0`. -/
def JohnNirenberg : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ h : ℝ → ℝ, LocallyIntegrable h → ∀ M : ℝ, 0 < M →
    (∀ a b : ℝ, a < b → meanOsc h a b ≤ M) → ∀ a b : ℝ, a < b → ∀ s : ℝ, 0 < s →
      volume {t ∈ Icc a b | s ≤ |h t - intervalMean h a b|} ≤
        ENNReal.ofReal (C * Real.exp (-(c * s / M)) * (b - a))

/-- **Lemma III of Duffin–Schaeffer** [DS52] (p. 800), in the form used: a separated sampling
sequence stays sampling under perturbations of sufficiently small size. -/
def DSPerturbation : Prop :=
  ∀ Γ : Set ℝ, IsSeparated Γ → IsSampling Γ → ∃ L : ℝ, 0 < L ∧
    ∀ δ : ℝ → ℝ, (∀ x ∈ Γ, |δ x| ≤ L) → InjOn (fun x ↦ x + δ x) Γ →
      IsSampling ((fun x ↦ x + δ x) '' Γ)

/-! ## Section 4: Landau's inequality and its sharpness -/

/-- The sequence `{k + log⁺|k|}_{k ∈ ℤ}` of p. 798, which shows that Landau's inequality is
best possible. -/
def logExample : Set ℝ :=
  Set.range fun k : ℤ ↦ (k : ℝ) + Real.posLog |(k : ℝ)|

/-! ## Section 5: the sequences `Λ(ψ)` -/

/-- The standing assumptions of §5 (p. 800): `ψ ∈ C¹(ℝ)` is nondecreasing,
`ψ(∞) - ψ(-∞) = ∞`, and `ψ'(x) → 0` as `|x| → ∞`. -/
def IsAdmissiblePsi (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 ψ ∧ Monotone ψ ∧ (Tendsto ψ atTop atTop ∨ Tendsto ψ atBot atBot) ∧
    Tendsto (deriv ψ) (cocompact ℝ) (𝓝 0)

/-- The sequence `Λ(ψ) = {λ_k}` defined by `λ_k + ψ(λ_k) = k`, `k ∈ ℤ` (p. 800). -/
def LambdaPsi (ψ : ℝ → ℝ) : Set ℝ :=
  {x : ℝ | ∃ k : ℤ, x + ψ x = k}

/-- The potential `U_ψ(z) = ∫ [log|1 - z/t| + Re (z/t)] dψ(t)` of p. 800.  The paper takes the
integral in the principal value sense; that principal value need not exist for `ψ ∈ C¹`
(NOTEBOOK), so the term `Re (z/t)` is only kept for `|t| > 1`.  The two potentials differ by a
real linear function `c · Re z` whenever the principal value exists. -/
def UPsi (ψ : ℝ → ℝ) (z : ℂ) : ℝ :=
  ∫ t : ℝ, (Real.log ‖1 - z / t‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).re) * deriv ψ t

/-- `ψ` (with `ψ = 0` on `(-∞, 0]`) *induces a logarithmically regular partition* (p. 801): with
`t₀ = 0`, `ψ(t_n) = n` (`n ≥ 1`) and `d_n = t_n - t_{n-1}`, one has `d_n ≃ d_{n+1}` and
`sup_{x > 0} ∑_{x/2 < t_n < 2x} d_n² / ((x - t_n)² + d_n²) < ∞`. -/
def IsLogRegularPartition (ψ : ℝ → ℝ) : Prop :=
  ∃ t : ℕ → ℝ, t 0 = 0 ∧ StrictMono t ∧ (∀ n : ℕ, 1 ≤ n → ψ (t n) = n) ∧
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      t (n + 1) - t n ≤ C * (t n - t (n - 1)) ∧ t n - t (n - 1) ≤ C * (t (n + 1) - t n)) ∧
    ∃ M : ℝ, ∀ x : ℝ, 0 < x →
      ∑' n : {n : ℕ | 1 ≤ n ∧ x / 2 < t n ∧ t n < 2 * x},
          ENNReal.ofReal ((t n - t (n - 1)) ^ 2 / ((x - t n) ^ 2 + (t n - t (n - 1)) ^ 2)) ≤
        ENNReal.ofReal M

end FF
