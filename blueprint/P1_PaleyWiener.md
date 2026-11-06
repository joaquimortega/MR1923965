# P1 — The Paley–Wiener theorem (`FF.PaleyWienerThm`)

**Lean files** (all compile with `lake env lean`; only `sorry` warnings):
`FourierFrames/Cited/PaleyWiener.lean` (ends with `theorem paleyWiener_holds : PaleyWienerThm`,
already fully proved from the two parts below), and under `FourierFrames/Cited/PaleyWiener/`:
`Part1.lean` (§1), `L2Fourier.lean` (§2), `Spectrum.lean` (§3), `Part2.lean` (§4).
Dependency order: `L2Fourier` → `Spectrum`; `Part1` independent; `Part2` imports `Part1`,
`Spectrum` and `OrtegaCerdaSeip.Bernstein.PhragmenLindelof`; `PaleyWiener.lean` imports `Part1`,`Part2`.
Namespace of the lemmas: `FF.PW1`.

**Paper**: the paper only cites it (p. 790: "the Paley–Wiener theorem", `PW = {f = ĝ : g ∈ L²(-π,π)}`);
the proof here is classical, not from the paper.

**Depends on**: Mathlib, `FF.IsExpTypeLE`, `FF.MemPW`, `FF.pwNormSq` (`Defs.lean`) and
`OCS.norm_le_mul_exp_abs_im` (vendored Phragmén–Lindelöf, `IsExpTypeLE` of `OCS` and `FF` are the same
formula, so `he : FF.IsExpTypeLE π f` is accepted verbatim as `OCS.IsExpTypeLE π f`).
**No** `FourierFrames/PW/*`, `HB/*` lemma is used (they take `hPW`); no import cycle.
**Used by**: `theorem1_unconditional` etc. (`paleyWiener_holds`).

## 0. Route chosen and why

Notation: `ft g z = ∫_{-π}^{π} g(t) e^{izt} dt`.

* **Part (1)** (`g ∈ L²(-π,π)` ⇒ `ft g ∈ PW`, `‖ft g‖² = 2π‖g‖²`): *Fourier series route*, no Fourier
  transform on `ℝ`. For each real `x`, `f(x+k) = ∫ (g e^{ix·}) e^{ik·} = 2π · (Fourier coefficient of g e^{ix·} at -k)`,
  so Parseval on `[-π,π]` (`hasSum_sq_fourierCoeffOn`) gives `∑_{k∈ℤ} |f(x+k)|² = 2π ∫|g|²` for **every** `x`
  (|g e^{ix·}| = |g|). Integrating over `x ∈ [0,1)` and using `ℝ = ⊔ [k,k+1)` gives `∫_ℝ|f|² = 2π∫|g|²`.
  This is much cheaper than going through the `L²` transform (it needs the missing `L¹∩L²` agreement lemma and
  a rescaling by `2π`).
* **Part (2)** (`f ∈ PW` ⇒ `f = ft g`): *Gaussian regularisation + `L²` Plancherel + Phragmén–Lindelöf*:
  1. (§3) If `f` is entire, `f|ℝ ∈ L²`, `|f(x+iy)| ≤ C e^{a|x|+b|y|}`, then the `L²` Fourier transform of `f|ℝ`
     vanishes a.e. on `{2π|w| > a+b}`.  (Contour shift of `∫ f(x)e^{-ηx²}e^{-iξx}dx`, then `η → 0`.)
  2. (§4) Crude bound `a = b = π+1` ⇒ spectrum in a compact ⇒ by `L²` inversion `f` is bounded on `ℝ`.
  3. Phragmén–Lindelöf (`OCS.norm_le_mul_exp_abs_im`): `|f(z)| ≤ M e^{π|Im z|}` ⇒ `a = 0, b = π`
     ⇒ spectrum in `[-1/2,1/2]` (in Mathlib's normalisation `𝐞(-xw)`).
  4. Inversion ⇒ `f(x) = ∫_{-π}^{π} g(t)e^{ixt}dt` on `ℝ`, `g(t) = Φ(t/2π)/2π`; identity theorem extends to `ℂ`.
* **Rejected**: (i) the sampling route (`g := ∑ f(k)e^{-ik·}/2π`, then uniqueness of `PW` functions vanishing on `ℤ`
  via `F/sin πz` and Liouville): it needs `∑|f(k)|² < ∞` (Plancherel–Pólya), whose elementary proofs need an `L²`
  bound of `f` on horizontal lines, i.e. the same difficulty as boundedness (the repo's `PW/PlancherelPolya.lean`
  derives it from `hPW`, so it is not usable). The two-pass trick of §4 (crude spectrum ⇒ bounded ⇒ PL ⇒ sharp
  spectrum) circumvents exactly this. (ii) the Fejér/`sinc²` regularisation: also needs `L¹` Plancherel–Pólya.
  (iii) log-convexity of `y ↦ ∫|f(x+iy)|²dx` (second derivative under the integral): much heavier than §3.

Mathlib facts: the `L²` transform `Lp.fourierTransformₗᵢ ℝ ℂ` (Plancherel, `inner_fourier_eq`), Schwartz agreement
(`SchwartzMap.toLp_fourier_eq`, `toLp_fourierInv_eq`) exist; the agreement with the integral on `L¹ ∩ L²` does **not**
(grep of `Mathlib/Analysis/Fourier`, `Distribution` finds nothing), hence §2.

Size estimate (Lean lines, proofs only): Part1 ≈ 350, L2Fourier ≈ 200, Spectrum ≈ 450, Part2 ≈ 300; total
≈ 1300 lines. Hardest pieces: `integral_line_shift`/`norm_integral_gauss_mul_le` (§3), `F2_toLp_ae_eq` (§2).

Conventions. `𝓕 φ w = ∫ x, 𝐞(-x w) • φ x = ∫ x, exp(-2πi x w) φ x` (Mathlib; `Real.fourier_real_eq_integral_exp_smul`
is the unfolding lemma), `𝓕⁻ φ x = 𝓕 φ (-x) = ∫ w, exp(2πi x w) φ w` (`Real.fourierInv_eq_fourier_neg`,
file `Analysis/Fourier/FourierTransform.lean` l. 463; named `fourierInv_eq_fourier_neg` in root namespace there).
`F2 := Lp.fourierTransformₗᵢ ℝ ℂ : Lp ℂ 2 ≃ₗᵢ[ℂ] Lp ℂ 2` (abbrev in `L2Fourier.lean`).
`L2pi g := MemLp g 2 (volume.restrict (Ioc (-π) π))` (abbrev).

---

## 1. Part (1) — `Cited/PaleyWiener/Part1.lean`

```lean
def ft (g : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)
theorem L2pi.integrable {g} (hg : L2pi g) : IntegrableOn g (Ioc (-Real.pi) Real.pi)
theorem differentiable_ft {g} (hg : L2pi g) : Differentiable ℂ (ft g)
theorem norm_ft_le {g} (hg : L2pi g) (z : ℂ) :
    ‖ft g z‖ ≤ (∫ t in Ioc (-Real.pi) Real.pi, ‖g t‖) * Real.exp (Real.pi * ‖z‖)
theorem isExpTypeLE_ft {g} (hg : L2pi g) : IsExpTypeLE Real.pi (ft g)
theorem L2pi.mul_cexp {g} (hg : L2pi g) (x : ℝ) : L2pi (fun t ↦ g t * Complex.exp (I * x * t))
theorem ft_add_intCast {g} (x : ℝ) (k : ℤ) :
    ft g ((x : ℂ) + k) = ft (fun t ↦ g t * Complex.exp (I * x * t)) k
theorem ft_intCast_eq_fourierCoeffOn {g} (n : ℤ) :
    ft g (n : ℂ) = (2 * Real.pi : ℂ) * fourierCoeffOn (by linarith [Real.pi_pos] : -Real.pi < Real.pi) g (-n)
theorem hasSum_sq_ft_add_intCast {g} (hg : L2pi g) (x : ℝ) :
    HasSum (fun k : ℤ ↦ ‖ft g ((x : ℂ) + k)‖ ^ 2) (2 * Real.pi * ∫ t in (-Real.pi)..Real.pi, ‖g t‖ ^ 2)
theorem tsum_enorm_sq_ft_add_intCast {g} (hg : L2pi g) (x : ℝ) :
    ∑' k : ℤ, ‖ft g ((x : ℂ) + k)‖ₑ ^ 2 =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2
theorem lintegral_enorm_sq_eq_lintegral_tsum {F : ℝ → ℂ} (hF : Measurable F) :
    ∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 = ∫⁻ x in Ico (0 : ℝ) 1, ∑' k : ℤ, ‖F (x + k)‖ₑ ^ 2
theorem pwNormSq_ft {g} (hg : L2pi g) :
    ∫⁻ x : ℝ, ‖ft g x‖ₑ ^ 2 = ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2
theorem memLp_ft_real {g} (hg : L2pi g) : MemLp (fun x : ℝ ↦ ft g x) 2
theorem paleyWiener_part1 : ∀ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) →
    MemPW (fun z ↦ ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)) ∧
    pwNormSq (fun z ↦ ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2
```
(In the file `g` carries its type `ℝ → ℂ`.)

**`L2pi.integrable`.** `IsFiniteMeasure (volume.restrict (Ioc a b))` is an instance
(`isFiniteMeasure_restrict_Ioc`), so `hg.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)` (`MemLp.integrable`).

**`differentiable_ft`.** Fix `z₀`. Use `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(`Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`, l. 96) with
`F z t = g t * cexp (I*z*t)`, `F' z t = g t * (I*t) * cexp (I*z*t)`, `ε = 1`, `bound t = ‖g t‖ * π * exp (π*(‖z₀‖+1))`.
For `t ∈ Ι (-π) π` (so `|t| ≤ π`) and `z ∈ ball z₀ 1`: `‖cexp (I*z*t)‖ = exp (-(z.im) * t) ≤ exp (π‖z‖)`
(`Complex.norm_exp`, `|z.im| ≤ ‖z‖`, `|t| ≤ π`), `‖I*t‖ ≤ π`. The derivative of `z ↦ cexp(I*z*t)` is
`I*t*cexp(...)` (`HasDerivAt.cexp`, `hasDerivAt_id`). Measurability: `hg.1` (strongly measurable on the restrict)
times a continuous function. `bound` is interval integrable by `L2pi.integrable` (`.norm.mul_const`).
Hence `HasDerivAt (ft g) _ z₀` for every `z₀`, i.e. `Differentiable ℂ`.

**`norm_ft_le`.** `intervalIntegral.integral_of_le` to pass to `Ioc`; `norm_integral_le_of_norm_le` (or
`norm_integral_le_integral_norm` then `integral_mono`) with the pointwise bound
`‖g t * cexp (I*z*t)‖ = ‖g t‖ * exp(-z.im * t) ≤ ‖g t‖ * exp(π‖z‖)` for `t ∈ Ioc (-π) π`
(use `-z.im * t ≤ |z.im| |t| ≤ ‖z‖ π`, `Complex.abs_im_le_norm`/`abs_im_le_norm`).

**`isExpTypeLE_ft`.** Given `ε>0` take `C = ∫ ‖g‖ ≥ 0`; `exp (π‖z‖) ≤ exp ((π+ε)‖z‖)` (`Real.exp_le_exp`,
`mul_le_mul_of_nonneg_right`).

**`L2pi.mul_cexp`.** `MemLp.congr_norm (hg) (hmeas) (h : ∀ᵐ t, ‖g t‖ = ‖g t * cexp (I*x*t)‖)`
(`Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean` l. 603); `‖cexp (I*x*t)‖ = 1` for real `x`:
`Complex.norm_exp_ofReal_mul_I` after rewriting `I*x*t = ((x*t : ℝ) : ℂ) * I` (`ring`+`push_cast`);
measurability `hg.1.mul (continuous_const.mul ...).cexp ...aestronglyMeasurable`.

**`ft_add_intCast`.** Pointwise `I*((x:ℂ)+k)*t = I*x*t + I*k*t` so `cexp(...) = cexp(I*x*t) * cexp(I*k*t)`
(`Complex.exp_add`), and `mul_assoc`; `intervalIntegral.integral_congr` (the integrands agree everywhere).

**`ft_intCast_eq_fourierCoeffOn`.** `fourierCoeffOn_eq_integral g m hab`
(`Analysis/Fourier/AddCircle.lean` l. 357): `fourierCoeffOn hab g m = (1/(b-a)) • ∫ x in a..b, fourier (-m) (x : AddCircle (b-a)) • g x`.
Here `b-a = π - -π = 2π` (rewrite with `by ring`; *beware*: `AddCircle (π - -π)` is not syntactically `AddCircle (2π)`, do
not rewrite the type, instead rewrite the value of `fourier (-(-n)) ↑t` using `fourier_coe_apply`
(`fourier n (x : AddCircle T) = cexp (2π I n x / T)`, l. 132) giving `cexp (2π I (-(-n)) t/(π - -π)) = cexp (I n t)`).
So `fourierCoeffOn g (-n) = (1/(2π)) ∫ g t * cexp (I n t)`; multiply by `2π ≠ 0`.

**`hasSum_sq_ft_add_intCast`.**
1. `hasSum_sq_fourierCoeffOn hab (hg.mul_cexp x)` (`AddCircle.lean` l. 459):
   `HasSum (fun i ↦ ‖fourierCoeffOn hab g_x i‖^2) ((π - -π)⁻¹ • ∫ t in -π..π, ‖g_x t‖^2)`, `g_x := g e^{ix·}`.
2. Pointwise `‖g_x t‖ = ‖g t‖` (unimodular), so the integral is `∫‖g‖²` and `(2π)⁻¹ • ` = `(2π)⁻¹ *`.
3. `‖ft g (x+k)‖² = ‖ft g_x k‖² = (2π)² ‖fourierCoeffOn g_x (-k)‖²` (`ft_add_intCast`,
   `ft_intCast_eq_fourierCoeffOn`, `norm_mul`, `mul_pow`, `Complex.norm_real`/`norm_ofReal`).
4. Re-index `i = -k`: `(Equiv.neg ℤ).hasSum_iff` (`Equiv.hasSum_iff`), then `HasSum.mul_left ((2π)^2)`;
   `(2π)² · (2π)⁻¹ = 2π` by `field_simp`.

**`tsum_enorm_sq_ft_add_intCast`.** From `hasSum_sq_ft_add_intCast` (nonnegative real terms, summable):
`ENNReal.ofReal_tsum_of_nonneg` (`ofReal (∑' f) = ∑' ofReal f`) and `ENNReal.ofReal_pow`,
`ofReal_norm_eq_enorm` to turn `ofReal (‖·‖^2)` into `‖·‖ₑ^2`. Right side: `∫⁻ t in Ioc, ‖g t‖ₑ^2 = ofReal (∫ t in Ioc, ‖g t‖^2)` by
`ofReal_integral_eq_lintegral_ofReal` (`Bochner/Basic.lean` l. 739) with integrability of `‖g‖²` on `Ioc`
from `memLp_two_iff_integrable_sq_norm hg.1` (`L2Space.lean` l. 45); `intervalIntegral.integral_of_le`;
`ENNReal.ofReal_mul (by positivity)`.

**`lintegral_enorm_sq_eq_lintegral_tsum`** (`F` measurable). Put `G x = ‖F x‖ₑ^2`.
(a) `Set.iUnion_Ico_intCast ℝ : ⋃ n:ℤ, Ico (n:ℝ) (n+1) = univ` (`Algebra/Order/ToIntervalMod.lean` l. 1466),
disjointness `pairwise_disjoint_Ico_intCast` (`Algebra/Order/Interval/Set/Group.lean` l. 228), so
`∫⁻ x, G = ∑' k:ℤ, ∫⁻ x in Ico k (k+1), G` by `lintegral_iUnion` (`Lebesgue/Basic.lean` l. 597; measurable sets `measurableSet_Ico`).
(b) each term equals `∫⁻ x in Ico 0 1, G (x + k)`: `(measurePreserving_add_right volume (k:ℝ))` is a measure preserving map with
measurable embedding `measurableEmbedding_addRight`, so `MeasurePreserving.setLIntegral_comp_emb` gives
`∫⁻ x in Ico 0 1, G (x+k) = ∫⁻ y in (·+k) '' Ico 0 1, G y`, and `Set.image_add_const_Ico` : image `= Ico (0+k) (1+k)`.
(c) `lintegral_tsum` (`Lebesgue/Add.lean` l. 362; each `x ↦ G (x+k)` is `AEMeasurable`) swaps `∑'` and `∫⁻`
(over `volume.restrict (Ico 0 1)`).

**`pwNormSq_ft`.** `F := fun x:ℝ ↦ ft g x` is continuous (`(differentiable_ft hg).continuous.comp Complex.continuous_ofReal`),
hence measurable. By the previous lemma the integral is `∫⁻ x in Ico 0 1, ∑' k, ‖ft g ((x+k : ℝ):ℂ)‖ₑ^2`;
`push_cast` turns `((x + k : ℝ) : ℂ)` into `(x:ℂ) + (k:ℂ)`; `tsum_enorm_sq_ft_add_intCast` makes the integrand the
constant `ofReal(2π) * ‖g‖²_{L²}`; `lintegral_const`, `Measure.restrict_apply MeasurableSet.univ`, `Real.volume_Ico`
(`= ofReal (1-0) = 1`).

**`memLp_ft_real`.** `AEStronglyMeasurable` from continuity. `eLpNorm F 2 volume < ⊤`: `eLpNorm_eq_lintegral_rpow_enorm`
(`p = 2`, `1/2`-th power of `∫⁻‖F‖ₑ^2`) and `pwNormSq_ft` plus finiteness of `∫⁻ ‖g‖ₑ^2` on `Ioc`
(`lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top`, `LpSeminorm/Basic.lean` l. 51, from `hg.2`).
(Alternatively `memLp_two_iff_integrable_sq_norm` + `lintegral_ofReal`.)

**`paleyWiener_part1`.** `ft g` is *definitionally* `fun z ↦ ∫ t in -π..π, g t * cexp (I*z*t)`, so `show`/`change` and
`⟨⟨differentiable_ft hg, isExpTypeLE_ft hg, memLp_ft_real hg⟩, pwNormSq_ft hg⟩` (`pwNormSq f = ∫⁻ x:ℝ, ‖f x‖ₑ^2` unfolds
to the left side of `pwNormSq_ft`).

---

## 2. The `L²` transform agrees with the integral on `L¹ ∩ L²` — `Cited/PaleyWiener/L2Fourier.lean`

```lean
abbrev F2 : Lp (α := ℝ) ℂ 2 ≃ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 := Lp.fourierTransformₗᵢ ℝ ℂ
theorem F2_toLp_ae_eq {φ : ℝ → ℂ} (h1 : Integrable φ) (h2 : MemLp φ 2) :
    (F2 (h2.toLp φ) : ℝ → ℂ) =ᵐ[volume] 𝓕 φ
theorem F2_symm_ae_eq (Φ : Lp (α := ℝ) ℂ 2) :
    ((F2.symm Φ : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) =ᵐ[volume] fun x ↦ (F2 Φ : ℝ → ℂ) (-x)
theorem F2_symm_toLp_ae_eq {φ : ℝ → ℂ} (h1 : Integrable φ) (h2 : MemLp φ 2) :
    ((F2.symm (h2.toLp φ) : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ φ
```
(`open scoped FourierTransform` for `𝓕`, `𝓕⁻`.)

**`F2_toLp_ae_eq`.** Write `Φ = h2.toLp φ`, `u = ⇑(F2 Φ)`, `v = 𝓕 φ`. `u` is locally integrable (`L²`: `(Lp.memLp _).locallyIntegrable`
via `MemLp.locallyIntegrable`), `v` is continuous (`VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
(innerSL ℝ).continuous₂ h1`, as in `Real.Lp.fourierTransform` in `FourierTransform.lean` l. 508) hence locally integrable.
By `ae_eq_of_integral_contDiff_smul_eq` (`Analysis/Distribution/AEEqOfIntegralContDiff.lean` l. 195) it suffices to show, for
every `g : ℝ → ℝ` smooth with compact support, `∫ g x • u x = ∫ g x • v x`.
Fix such `g`; `ψ : 𝓢(ℝ,ℂ) := (HasCompactSupport.toSchwartzMap (f := fun x ↦ (g x : ℂ)) hcs hsmooth)`
(`Distribution/SchwartzSpace/Basic.lean` l. 546); `ψ` is real-valued: `conj (ψ x) = ψ x`.
Let `χ := 𝓕⁻ ψ ∈ 𝓢` (`SchwartzMap.fourierTransformCLM` etc.), so `ψ = 𝓕 χ` (`fourier_fourierInv_eq`, Schwartz version in
`Analysis/Fourier/Inversion.lean`/`SchwartzSpace`).
* L²-side: `ψ.toLp 2 = 𝓕 (χ.toLp 2)` (`SchwartzMap.toLp_fourier_eq`, `LpSpace.lean` l. 100). Then by `inner_fourier_eq`
  (`LpSpace.lean` l. 94) and `MeasureTheory.L2.inner_def` (`L2Space.lean` l. 136):
  `∫ conj (ψ x) * u x = ⟪ψ.toLp, 𝓕 Φ⟫ = ⟪𝓕 (χ.toLp), 𝓕 Φ⟫ = ⟪χ.toLp, Φ⟫ = ∫ conj (χ x) * φ x`
  (use `ψ.coeFn_toLp`, `Lp.coeFn`-a.e. rewriting: `integral_congr_ae`, `h2.coeFn_toLp`).
  Since `ψ` is real, `conj (ψ x) = g x`.
* `L¹`-side: `integral_fourierIntegral_smul_eq_flip` (`VectorFourier`, `FourierTransform.lean` l. 241) with `e = 𝐞`,
  `L = innerSL ℝ`, `f = φ`, `g = ψ`: `∫ (𝓕 φ ξ) • ψ ξ = ∫ φ x • (𝓕 ψ x)`.
* Compare `conj (χ x)` and `𝓕 ψ x`: `conj (𝓕⁻ ψ x) = conj ∫ exp(2πi x ξ) ψ ξ = ∫ exp(-2πi x ξ) conj (ψ ξ) = 𝓕 ψ x`
  (`integral_conj` (`Bochner/ContinuousLinearMap.lean` l. 174), `Complex.exp_conj`, reality of `ψ`).
Combine: `∫ g • u = ∫ conj χ * φ = ∫ φ * 𝓕 ψ = ∫ 𝓕 φ * g = ∫ g • v`.
(If the sesquilinear lemma `integral_sesq_fourierIntegral_eq_neg_flip` (l. 252) is preferred, it removes the reality
bookkeeping at the cost of the `-L.flip` kernel.)

**`F2_symm_ae_eq`.** Let `R : Lp ℂ 2 →ₗᵢ[ℂ] Lp ℂ 2` be the reflection `Lp.compMeasurePreservingₗᵢ ℂ (fun x ↦ -x) (Measure.measurePreserving_neg volume)`
(`LpSpace/Basic.lean`; look for the exact name `Lp.compMeasurePreservingₗᵢ`). Claim `F2.symm = R ∘ F2` as maps. Both are continuous
(isometries); they agree on the range of `SchwartzMap.toLpCLM` (dense: `SchwartzMap.denseRange_toLpCLM`, `Distribution/SchwartzSpace/Basic.lean` l. 1375):
for `ψ ∈ 𝓢`, `F2.symm (ψ.toLp) = (𝓕⁻ ψ).toLp` (`SchwartzMap.toLp_fourierInv_eq`), `R (F2 (ψ.toLp)) = R ((𝓕 ψ).toLp) = ((𝓕ψ)∘neg).toLp`, and
`𝓕⁻ ψ = (𝓕 ψ) ∘ neg` (`fourierInv_eq_fourier_neg`). Conclude with `DenseRange.equalizer` (or `Continuous.ext_on` / `closure` argument).
Then `Lp.coeFn_compMeasurePreserving`.

**`F2_symm_toLp_ae_eq`.** `F2_symm_ae_eq` with `Φ = h2.toLp φ`, then `F2_toLp_ae_eq` composed with `x ↦ -x`
(a.e. statements pull back along the measure preserving `neg`: `Measure.QuasiMeasurePreserving.ae_eq_comp`/`(measurePreserving_neg _).quasiMeasurePreserving.ae_eq_comp`),
and `𝓕⁻ φ x = 𝓕 φ (-x)` (`fourierInv_eq_fourier_neg`).

*Alternative*: prove `F2_symm_toLp_ae_eq` directly like `F2_toLp_ae_eq` (swap `F2` and `F2.symm`, `𝓕` and `𝓕⁻`); equivalent effort.

---

## 3. Spectrum of an entire function of exponential type — `Cited/PaleyWiener/Spectrum.lean`

```lean
theorem integral_line_shift {H : ℂ → ℂ} (hH : Differentiable ℂ H) (y : ℝ)
    (hint0 : Integrable (fun x : ℝ ↦ H x)) (hinty : Integrable (fun x : ℝ ↦ H (x + y * I)))
    (hR  : Tendsto (fun R : ℝ ↦ ∫ s in (0 : ℝ)..y, ‖H (R + s * I)‖) atTop (𝓝 0))
    (hR' : Tendsto (fun R : ℝ ↦ ∫ s in (0 : ℝ)..y, ‖H (-R + s * I)‖) atTop (𝓝 0)) :
    ∫ x : ℝ, H x = ∫ x : ℝ, H (x + y * I)

theorem integral_exp_abs_sub_sq_le {a : ℝ} (ha : 0 ≤ a) {η : ℝ} (hη : 0 < η) :
    ∫ x : ℝ, Real.exp (a * |x| - η * x ^ 2) ≤ 2 * Real.sqrt (Real.pi / η) * Real.exp (a ^ 2 / (4 * η))
theorem integrable_exp_abs_sub_sq {a η : ℝ} (hη : 0 < η) :
    Integrable (fun x : ℝ ↦ Real.exp (a * |x| - η * x ^ 2))

theorem norm_integral_gauss_mul_le {f : ℂ → ℂ} (hd : Differentiable ℂ f) {C a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (a * |z.re| + b * |z.im|))
    {η : ℝ} (hη : 0 < η) {ξ : ℝ} (hξ : b ≤ |ξ|) :
    ‖∫ x : ℝ, f x * Complex.exp (-(η : ℂ) * (x : ℂ) ^ 2) * Complex.exp (-I * ξ * x)‖ ≤
      2 * |C| * Real.sqrt (Real.pi / η) * Real.exp ((a ^ 2 - (|ξ| - b) ^ 2) / (4 * η))

theorem tendsto_gauss_bound {a κ : ℝ} (ha : 0 ≤ a) (hκ : a < κ) (C : ℝ) :
    Tendsto (fun η : ℝ ↦ 2 * |C| * Real.sqrt (Real.pi / η) * Real.exp ((a ^ 2 - κ ^ 2) / (4 * η)))
      (𝓝[>] 0) (𝓝 0)

theorem memLp_mul_gauss {f : ℝ → ℂ} (hf : MemLp f 2) {η : ℝ} (hη : 0 < η) :
    MemLp (fun x : ℝ ↦ f x * ((Real.exp (-η * x ^ 2) : ℝ) : ℂ)) 2 ∧
    Integrable (fun x : ℝ ↦ f x * ((Real.exp (-η * x ^ 2) : ℝ) : ℂ))
theorem tendsto_eLpNorm_mul_gauss {f : ℝ → ℂ} (hf : MemLp f 2) :
    Tendsto (fun n : ℕ ↦ eLpNorm (fun x : ℝ ↦ f x * ((Real.exp (-(1 / ((n : ℝ) + 1)) * x ^ 2) : ℝ) : ℂ) - f x) 2 volume)
      atTop (𝓝 0)

theorem spectrum_vanish {f : ℂ → ℂ} (hd : Differentiable ℂ f) (hL2 : MemLp (fun x : ℝ ↦ f x) 2)
    {C a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (a * |z.re| + b * |z.im|)) :
    ∀ᵐ w : ℝ, a + b < 2 * Real.pi * |w| → (F2 (hL2.toLp (fun x : ℝ ↦ f x)) : ℝ → ℂ) w = 0
```

**`integral_line_shift`.** For `R > 0` apply `Complex.integral_boundary_rect_eq_zero_of_differentiableOn H (-R) (R + y*I)`
(`Analysis/Complex/CauchyIntegral.lean` l. 292; `H.differentiableOn`); note `(-R:ℂ).re = -R`, `(-R:ℂ).im = 0`, `(R + yI).im = y`; the statement (with `z = -R`, `w = R + y I`):
`∫_{-R}^{R} H(x + 0 I) - ∫_{-R}^{R} H(x + y I) + I•∫_0^y H(R + s I) ds - I•∫_0^y H(-R + s I) ds = 0`. (Careful: `simp` the `z.im*I = 0`;
the `(↑x + ↑0 * I)` must become `↑x`.) Let `R → ∞`: the horizontal integrals converge to the full integrals by
`MeasureTheory.intervalIntegral_tendsto_integral` (`IntegralEqImproper.lean` l. 609, with `tendsto_neg_atTop_atBot`,
`tendsto_id`) using `hint0`, `hinty`; the vertical ones have norm `≤ ∫_0^y ‖H(±R + s I)‖` (`intervalIntegral.norm_integral_le_integral_norm`,
for `y ≥ 0`; for `y < 0` use `intervalIntegral.integral_symm`/`norm_integral_le_abs_integral_norm`, i.e. work with `|∫|`; simplest is to
first treat `y ≥ 0` and obtain `y<0` by applying the result to `z ↦ H(conj ...)`, or directly bound by `|∫_0^y ‖·‖|`; adjust `hR` statement accordingly
if implementation prefers `|∫|`) tending to `0` by `hR`, `hR'`. Conclude by uniqueness of limits (`tendsto_nhds_unique`) in
`ℂ` after `sub_eq_zero`.

**`integral_exp_abs_sub_sq_le`.** `exp (a|x|) ≤ exp (a x) + exp (-a x)`; `∫ exp (a x - η x²) = exp (a²/(4η)) √(π/η)`:
`a x - η x² = a²/(4η) - η (x - a/(2η))²`, `integral_sub_right_eq_self` and `integral_gaussian` (`GaussianIntegral.lean` l. 210);
`x ↦ -x` (`integral_neg_eq_self`/`MeasurePreserving`) for the other term. (Or `integral_cexp_quadratic`, `Gaussian/FourierTransform.lean` l. 174, with `b = -η`.)
`integrable_exp_abs_sub_sq`: `exp (a|x| - ηx²) ≤ exp (ax - ηx²) + exp (-ax - ηx²)` and each is integrable (`integrable_exp_neg_mul_sq` + shift;
`integrable_cexp_quadratic`-type lemma in `Gaussian/FourierTransform.lean`), `Integrable.mono'`.
(For `a < 0` the statement is still true with `|a|`; the scaffold only needs `a ≥ 0` for the first.)

**`norm_integral_gauss_mul_le`.** `H z := f z * cexp (-η z²) * cexp (-I ξ z)` is entire. Put `κ = |ξ| - b ≥ 0`, `Y = κ/(2η) ≥ 0`,
`y = -Y` if `ξ ≥ 0`, `y = Y` if `ξ < 0`; thus `ξ y = -|ξ| Y`.
Moduli (`z = x + s I`): `‖cexp (-η z²)‖ = exp (-η (x² - s²))` (`Complex.norm_exp`, `re (z²) = x² - s²`), `‖cexp (-I ξ z)‖ = exp (ξ s)`,
so `‖H (x + s I)‖ ≤ |C| exp (a|x| - η x² + (η s² + b|s| + ξ s))`.
* `hint0`, `hinty`: dominated by `|C| exp(..)` times a constant, integrable by `integrable_exp_abs_sub_sq`
  (`Integrable.mono'`, with measurability from continuity of `H`).
* `hR`, `hR'`: for `s ∈ [0,y]` (or `[y,0]`), `|s| ≤ Y`, so `‖H(±R + s I)‖ ≤ K exp (aR - ηR²)` with
  `K = |C| exp (ηY² + (b+|ξ|)Y)` independent of `R`; the integral over `s` is `≤ Y K exp(aR - ηR²)`; and `exp(aR - ηR²) → 0`
  as `R → ∞` (`Real.tendsto_exp_atBot.comp`, `tendsto_atBot` of `aR - ηR²`, e.g. `-ηR² + aR ≤ -ηR²/2` for `R ≥ 2a/η`),
  `squeeze_zero`.
* Then `∫ H = ∫ H(x + yI)` and `‖∫ H(x + yI)‖ ≤ ∫ ‖H(x+yI)‖ ≤ |C| exp (η Y² + (b-|ξ|) Y) ∫ exp (a|x| - ηx²)`
  (`norm_integral_le_integral_norm`, `integral_mono`) and `η Y² + (b - |ξ|) Y = κ²/(4η) - κ²/(2η) = -κ²/(4η)`; finally
  `integral_exp_abs_sub_sq_le` gives `2√(π/η) exp (a²/(4η))`. Product: `2|C| √(π/η) exp ((a² - κ²)/(4η))`.
Remark: `C` may be negative only if `f = 0`; `|C|` avoids a case split (`C * e ≤ |C| * e`).

**`tendsto_gauss_bound`.** `t = 1/η → +∞` as `η → 0⁺` (`tendsto_inv_nhdsGT_zero`). Expression `= 2|C|√π · t^{1/2} exp (-c t)`,
`c = (κ² - a²)/4 > 0` (`κ > a ≥ 0`). `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/2) c hc`
(`Analysis/SpecialFunctions/Gamma/Basic.lean`/`Pow`), `Real.sqrt_eq_rpow`, `Real.sqrt_div`, `Tendsto.const_mul`.

**`memLp_mul_gauss`.** `gη(x) = exp (-η x²)` is real, `0 < gη ≤ 1`: `MemLp (f * gη) 2` by `MemLp.of_le_mul`/`MemLp.mono` with `‖f x * gη x‖ ≤ ‖f x‖`.
`gη ∈ L²`: `memLp_two_iff_integrable_sq_norm` and `gη² = exp (-(2η) x²)` integrable (`integrable_exp_neg_mul_sq`).
`Integrable (f * gη)` by Cauchy–Schwarz: `MemLp.integrable_mul` (`L1Space/Integrable.lean` l. 1081, `p = q = 2`, `HolderTriple`).

**`tendsto_eLpNorm_mul_gauss`.** Dominated convergence (`tendsto_lintegral_of_dominated_convergence`) for
`∫⁻ ‖f (gη - 1)‖ₑ^2` with bound `‖f‖ₑ^2` (integrable: `hf`), pointwise limit `0` since `exp (-η x²) → 1` as `η = 1/(n+1) → 0`;
then `eLpNorm = (∫⁻ ‖·‖ₑ²)^{1/2}` continuous at `0` (`ENNReal.continuousAt_rpow_const`/`Tendsto.ennrpow_const`). Or use
`tendsto_Lp_of_tendsto_ae` (`UnifTight.lean` l. 269; hypothesis: `UnifIntegrable` — not easier).

**`spectrum_vanish`.** Notation `f_n x = f x * exp (-(1/(n+1)) x²)` (on `ℝ`), `η_n = 1/(n+1)`, `Φ = F2 (hL2.toLp f|ℝ)`.
1. `f_n ∈ L¹ ∩ L²` (`memLp_mul_gauss`), and `toLp f_n → toLp f` in `Lp` (`tendsto_eLpNorm_mul_gauss`, `Lp.tendsto_Lp_iff_tendsto_eLpNorm'`),
   so `F2 (toLp f_n) → Φ` in `Lp` (continuity of `F2`, `F2.continuous`, or `‖F2 x‖ = ‖x‖`).
2. Convergence in `L²` ⇒ in measure (`tendstoInMeasure_of_tendsto_eLpNorm` on the coercions, `Lp.tendsto_Lp_iff_tendsto_eLpNorm'`)
   ⇒ a subsequence `ns` with a.e. pointwise convergence: `TendstoInMeasure.exists_seq_tendsto_ae` (`ConvergenceInMeasure.lean` l. 273).
3. `F2_toLp_ae_eq`: `F2 (toLp f_n) =ᵐ 𝓕 f_n`; countable intersection of a.e. sets (`ae_all_iff`): for a.e. `w`,
   `𝓕 f_{ns k} w → Φ w` as `k → ∞`.
4. For *every* `w` with `a + b < 2π|w|`: with `ξ = 2π w`, `𝓕 f_n w = ∫ f x e^{-η x²} e^{-2πi x w}dx`
   (`fourier_real_eq_integral_exp_smul` and `Complex.ofReal`-casts; `exp(-2πi x w) = exp(-I ξ x)`), so by
   `norm_integral_gauss_mul_le` (hypothesis `b ≤ |ξ|` holds) `‖𝓕 f_n w‖ ≤ B(η_n)`, with `B` the function of
   `tendsto_gauss_bound` for `κ = |ξ| - b > a`. Since `η_{ns k} → 0⁺` (strictly increasing `ns`, `tendsto_one_div_add_atTop_nhds_zero_nat`,
   `tendsto_nhdsWithin_iff`), `𝓕 f_{ns k} w → 0` (`squeeze_zero_norm`). By uniqueness of limits `Φ w = 0` (a.e.).
   Note: the hypothesis `hC` of `norm_integral_gauss_mul_le` is exactly the hypothesis of this lemma (applied with `f` entire).

---

## 4. Part (2) — `Cited/PaleyWiener/Part2.lean`

```lean
def specOf {f : ℂ → ℂ} (hL2 : MemLp (fun x : ℝ ↦ f x) 2) : ℝ → ℂ := (F2 (hL2.toLp (fun x : ℝ ↦ f x)) : ℝ → ℂ)
theorem memLp_specOf {f} (hL2 : MemLp (fun x : ℝ ↦ f x) 2) : MemLp (specOf hL2) 2
theorem eq_integral_of_spectrum {f : ℂ → ℂ} (hd : Differentiable ℂ f) (hL2 : MemLp (fun x : ℝ ↦ f x) 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hsp : ∀ᵐ w : ℝ, ρ < |w| → specOf hL2 w = 0) (x : ℝ) :
    f x = ∫ w in (-ρ)..ρ, specOf hL2 w * Complex.exp (2 * Real.pi * I * w * x)
theorem bounded_of_spectrum  (same hypotheses) : ∃ M : ℝ, ∀ x : ℝ, ‖f x‖ ≤ M
theorem pw_bounded {f} (hd : Differentiable ℂ f) (he : IsExpTypeLE Real.pi f) (hL2 : MemLp (fun x : ℝ ↦ f x) 2) :
    ∃ M : ℝ, ∀ x : ℝ, ‖f x‖ ≤ M
theorem pw_spectrum {f} (hd) (he) (hL2) : ∀ᵐ w : ℝ, (1 / 2 : ℝ) < |w| → specOf hL2 w = 0
theorem pw_representation_real {f} (hd) (he) (hL2) : ∃ g : ℝ → ℂ, L2pi g ∧ ∀ x : ℝ, f x = ft g x
theorem eq_of_eq_on_real {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h : ∀ x : ℝ, F x = G x) : ∀ z : ℂ, F z = G z
theorem paleyWiener_part2 : ∀ f : ℂ → ℂ, MemPW f → ∃ g : ℝ → ℂ,
    MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) ∧
    ∀ z : ℂ, f z = ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)
```

**`memLp_specOf`.** `Lp.memLp (F2 _)`.

**`eq_integral_of_spectrum`.** Let `u = hL2.toLp f|ℝ`, `Φ = F2 u`, `Φ₀ := (Icc (-ρ) ρ).indicator (specOf hL2)`.
* `Φ₀ =ᵐ specOf hL2` (from `hsp`: for a.e. `w`, `w ∉ Icc` ⇒ `ρ < |w|` ⇒ `specOf w = 0`).
* `Φ₀ ∈ L²` (`MemLp.indicator`, `memLp_specOf`) and `Φ₀ ∈ L¹` (`MemLp.restrict` to the finite-measure set `Icc (-ρ) ρ` then `.integrable`,
  `integrable_indicator_iff`).
* `Φ = (hΦ₀.toLp Φ₀)` as `Lp` elements (`Lp.ext`, `MemLp.coeFn_toLp`, a.e. equality).
* `u = F2.symm Φ` (`F2.symm_apply_apply`); by `F2_symm_toLp_ae_eq`, `u =ᵐ 𝓕⁻ Φ₀`, and `u =ᵐ f|ℝ` (`MemLp.coeFn_toLp`). So `f x = 𝓕⁻ Φ₀ x` for a.e. `x`.
* Both sides are continuous: `f` is (differentiable composed with `ofReal`), `𝓕⁻ Φ₀ = fun x ↦ 𝓕 Φ₀ (-x)` is continuous by
  `VectorFourier.fourierIntegral_continuous` (`Φ₀` integrable). `Continuous.ae_eq_iff_eq` (`Measure/OpenPos.lean` l. 141, `volume` is `IsOpenPosMeasure`)
  upgrades a.e. to everywhere.
* Unfold `𝓕⁻ Φ₀ x = ∫ w, exp (2πi w x) • Φ₀ w` (`Real.fourierInv_eq` / `fourierInv_eq`, `Real.fourierChar_apply`) and
  `∫ w, indicator = ∫ w in Icc, specOf …` (`integral_indicator measurableSet_Icc`), `integral_Icc_eq_integral_Ioc`, `intervalIntegral.integral_of_le`.

**`bounded_of_spectrum`.** `M = ∫ w in (-ρ)..ρ, ‖specOf hL2 w‖` (finite by integrability above); from `eq_integral_of_spectrum`:
`‖f x‖ ≤ ∫ ‖specOf w * exp(2πi w x)‖ = M` (`intervalIntegral.norm_integral_le_integral_norm`, `‖exp (2π I w x)‖ = 1`: `Complex.norm_exp_ofReal_mul_I` after
`2π I w x = ((2π w x : ℝ) : ℂ) * I`).

**`pw_bounded`.** `he 1 one_pos` gives `C₁` with `‖f z‖ ≤ C₁ exp ((π+1)‖z‖)`; `‖z‖ ≤ |z.re| + |z.im|` (`Complex.norm_le_abs_re_add_abs_im`) ⇒
hypothesis `hC` of `spectrum_vanish` with `C = C₁`, `a = b = π+1`. Then a.e. `w` with `ρ < |w|` where `ρ := 1 + 1/π`
satisfies `2(π+1) = 2πρ < 2π|w|`, so `hsp` of `bounded_of_spectrum` holds (`hρ : 0 < ρ`). Finish with `bounded_of_spectrum`.

**`pw_spectrum`.** `M` from `pw_bounded`; `OCS.norm_le_mul_exp_abs_im hd he (Real.pi_pos.le) hM z : ‖f z‖ ≤ M * exp (π |z.im|)`
(`OrtegaCerdaSeip/Bernstein/PhragmenLindelof.lean` l. 107; its `IsExpTypeLE` is `OCS.IsExpTypeLE`, the same formula — pass `he` directly, or
`fun ε hε ↦ he ε hε`). This is `hC` for `spectrum_vanish` with `a = 0, b = π, C = M` (`simp` the `0 * |z.re|`). The condition `π < 2π|w|` is `1/2 < |w|`
(`Real.pi_pos`, `div_lt_iff`).

**`pw_representation_real`.** Take `ρ = 1/2`: by `pw_spectrum` and `eq_integral_of_spectrum`,
`f x = ∫ w in (-1/2)..(1/2), Φ w * exp (2π I w x)` (`Φ = specOf hL2`). Define `g t = Φ (t/(2π)) / (2π)`.
* *`L2pi g`*: `t ↦ Φ (t/(2π))` is `MemLp 2` on `ℝ` since `volume.map (· * (2π)⁻¹)` is a constant multiple of `volume`
  (`Real.map_volume_mul_right`, `Measure/Lebesgue/Basic.lean`; `MemLp.comp_measurePreserving` (`LpSeminorm/Basic.lean` l. 1049) after `memLp_map_measure_iff`
  and `MemLp.smul_measure`/`MemLp.of_measure_le_smul`); then `.const_mul`/`.div_const` and `MemLp.restrict`.
  (Alternatively use `MemLp.comp_quasiMeasurePreserving` with `Real.quasiMeasurePreserving_mul_right`/`quasiMeasurePreserving_smul`, `EqHaar.lean` l. 345, if available.)
* *Identity*: `ft g x = ∫ t in -π..π, Φ (t/(2π))/(2π) * exp (I x t)`; `intervalIntegral.integral_comp_div` (`Basic.lean` l. 944: `∫ x in a..b, f (x / c) = c • ∫ x in a/c..b/c, f x`)
  applied to `w ↦ Φ w * exp (2π I w x)` (note `2π I (t/(2π)) x = I x t`, `field_simp`) with `c = 2π`, `π/(2π) = 1/2`.
  So `ft g x = (2π)⁻¹ • (2π) • ∫_{-1/2}^{1/2} ... = f x`.

**`eq_of_eq_on_real`.** `H = F - G` is entire, hence analytic (`Differentiable.analyticAt` / `DifferentiableOn.analyticOnNhd`,
`Complex.differentiableOn.analyticOnNhd`); `H = 0` on `ℝ`, in particular `∃ᶠ z in 𝓝[≠] 0, H z = 0` (points `1/(n+1)`), so
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` (`Analysis/Analytic/Uniqueness.lean`, with `isPreconnected_univ`) gives `H ≡ 0`.

**`paleyWiener_part2`.** `⟨hd, he, hL2⟩ := hf`; `pw_representation_real` gives `g`, `L2pi g`, `f x = ft g x` on `ℝ`; `eq_of_eq_on_real hd (differentiable_ft hg)` gives
`f z = ft g z` for all `z`, which is the statement (`ft` unfolds to the integral).

**Top file** `Cited/PaleyWiener.lean`: `theorem paleyWiener_holds : PaleyWienerThm := ⟨PW1.paleyWiener_part1, PW1.paleyWiener_part2⟩`
(already checks: the two statements are literally the two conjuncts of `PaleyWienerThm`).

---

## 5. Checked Mathlib names (all grep-confirmed in `.lake/packages/mathlib/Mathlib`)

`MeasureTheory.Lp.fourierTransformₗᵢ`, `Lp.norm_fourier_eq`, `Lp.inner_fourier_eq`, `SchwartzMap.toLp_fourier_eq`, `SchwartzMap.toLp_fourierInv_eq`
(`Analysis/Fourier/LpSpace.lean`); `fourierInv_eq_fourier_neg`, `fourier_real_eq_integral_exp_smul`, `VectorFourier.integral_fourierIntegral_smul_eq_flip`,
`integral_sesq_fourierIntegral_eq_neg_flip`, `fourierIntegral_continuous` (`FourierTransform.lean`); `SchwartzMap.denseRange_toLpCLM`, `HasCompactSupport.toSchwartzMap`;
`ae_eq_of_integral_contDiff_smul_eq`; `hasSum_sq_fourierCoeffOn`, `fourierCoeffOn_eq_integral`, `fourier_coe_apply` (`AddCircle.lean`);
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`; `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`;
`MeasureTheory.intervalIntegral_tendsto_integral`; `integral_gaussian`, `integral_cexp_quadratic`, `integrable_cexp_neg_mul_sq`;
`TendstoInMeasure.exists_seq_tendsto_ae`, `tendstoInMeasure_of_tendsto_eLpNorm`; `MemLp.integrable_mul`, `MemLp.congr_norm`, `MemLp.comp_measurePreserving`,
`MemLp.smul_measure`, `memLp_two_iff_integrable_sq_norm`, `lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top`, `ofReal_integral_eq_lintegral_ofReal`;
`lintegral_iUnion`, `lintegral_tsum`, `iUnion_Ico_intCast`, `pairwise_disjoint_Ico_intCast`, `Real.volume_Ico`;
`Continuous.ae_eq_iff_eq`; `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`;
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, `tendsto_inv_nhdsGT_zero`, `Complex.norm_le_abs_re_add_abs_im`, `intervalIntegral.integral_comp_div`;
`Lp.compMeasurePreservingₗᵢ`; and in the vendored library `OCS.norm_le_mul_exp_abs_im`.
Names marked "look for" in §2/§4 (`Lp.compMeasurePreservingₗᵢ` exact signature, `MemLp.indicator`/`restrict` variants,
`Real.map_volume_mul_right` use) were located but their exact argument order was not tested; adapt.

## 6. Risks

* *Lean plumbing in `F2_toLp_ae_eq`* (Schwartz coercions, `Lp`-valued `inner`, `𝓕` on `Lp` vs on functions): medium. Fallback: prove the
  a.e. equality by density of `C_c^∞` in `L¹ ∩ L²` (heavier).
* *`integral_line_shift`*: orientation/sign bookkeeping of the rectangle formula, `y<0`: medium. A cleaner variant is to prove the lemma
  for `y ≥ 0` and obtain `y ≤ 0` via `H̃(z) = H(conj z)‑conj`, or to apply the rectangle with `(z,w) = (-R + yI, R)`; either is routine.
* *Gaussian estimates* (`integral_exp_abs_sub_sq_le`, `tendsto_gauss_bound`): routine but long.
* `F2_symm_ae_eq` (density argument): small/medium. Mathlib may by now (later versions) contain `Lp.fourierTransform` ↔ integral agreement; if so §2 shrinks.
* No statement in `PaleyWienerThm` is unprovable as written: part (1) (`MemPW`, norm identity with `ofReal(2π)`) and part (2) (exponent `e^{izt}`,
  all `z ∈ ℂ`, `g ∈ L²(Ioc(-π,π))`) are exactly the classical theorem. Edge cases checked: the `IsExpTypeLE` formulation (`∀ ε, ∃ C`) is what the
  Phragmén–Lindelöf lemma and `isExpTypeLE_ft` use; `pwNormSq` is an `ℝ≥0∞` integral so finiteness is part of the statement and is proved by `memLp_ft_real`.

## Issues in the source

None specific to the paper (the theorem is only cited). Remarks:
* (certain) The paper's `PW` is defined with `ĝ(z) = ∫ g(t)e^{izt}dt` and "‖f‖² = 2π‖g‖²" is implicit (p. 790); the Lean statement
  matches this normalisation exactly, no `2π` is hidden.
* (certain) The theorem needs `f|ℝ ∈ L²` *and* exponential type only; boundedness on `ℝ` (used later via Bernstein) is a consequence, proved here as
  `pw_bounded`, so the repo's `PW/Bounds` lemmas could be re-derived from `paleyWiener_holds` (this is what phase 1 does).

## Requested changes to M00

None.
