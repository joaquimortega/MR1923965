# P2 — Two classical lemmas: Duffin–Schaeffer perturbation and John–Nirenberg

**Lean files.** `FourierFrames/Cited/DSPerturbation.lean` (Part A), `FourierFrames/Cited/JohnNirenberg.lean`
(Part B); both compile with `lake env lean` (only `sorry` warnings).
**Paper.** p. 799 (John–Nirenberg, [JN61], [Ga81, p. 230]) and p. 800 (Lemma III of [DS52]).
**Depends on.**
- A: `hPW : PaleyWienerThm` and the toolkit `FourierFrames/PW/Basic.lean` (`MemL2pi`, `l2piSq`,
  `pwFT`, `exists_pwFT`, `memPW_pwFT`, `MemL2pi.integrableOn_mul_exp`, `norm_exp_I_mul_le`,
  `pwNormSq_ne_top`, `IsSepBy`), `PW/Bounds.lean` (`pw_norm_sq_le`), `sampleSum`.
  It does **not** need `plancherelPolya` or `pw_deriv_bound` (see Part A route).
  Imports: `FourierFrames.PW.PlancherelPolya` (only to pull in `Basic`; may be reduced to `PW.Basic`).
- B: nothing from the project except `Defs` (`meanOsc`, `intervalMean`, `JohnNirenberg`).
**Used by.** Theorem 2(i)/Corollary 2 (`hDS`), Theorem 2(ii) (`hJN`). Final theorems:
`dsPerturbation_of_paleyWiener : PaleyWienerThm → DSPerturbation`, `johnNirenberg_holds : JohnNirenberg`
(unconditional).

Both `Prop`s in `Defs.lean` are true as stated (checked below); no change to M00 requested.

---------------------------------------------------------------------------------------------------
# Part A. `DSPerturbation`

```lean
def DSPerturbation : Prop :=
  ∀ Γ : Set ℝ, IsSeparated Γ → IsSampling Γ → ∃ L : ℝ, 0 < L ∧
    ∀ δ : ℝ → ℝ, (∀ x ∈ Γ, |δ x| ≤ L) → InjOn (fun x ↦ x + δ x) Γ →
      IsSampling ((fun x ↦ x + δ x) '' Γ)
```

## A.0 Route (deviation from the classical proof, and why)

The classical proof expands `f(γ+δ) - f(γ) = ∑_{n≥1} f^{(n)}(γ) δⁿ/n!` and uses Bernstein for
every `f^{(n)}` plus Plancherel–Pólya for each, giving `(e^{πL}-1)√B`. That needs an induction on
`n` (each `f^{(n)} ∈ PW`), a Taylor series in `ℓ²`, and a Minkowski inequality for `tsum` in `ℝ≥0∞`.
We use a cheaper route that gives an explicit but slightly worse smallness condition
(`ε² = π² L (2L/d + 1)` instead of `(e^{πL}-1)² B`), which is all that is needed:

1. **Bernstein in `L²`** (once): `f ∈ PW ⇒ f' ∈ PW`, `‖f'‖² ≤ π² ‖f‖²`.
2. **FTC + Cauchy–Schwarz**: `|f(γ+δ) - f(γ)|² ≤ |δ| ∫_{γ-|δ|}^{γ+|δ|} |f'|²`.
3. **Finite overlap**: for `d`-separated `Γ`, every `x` lies in at most `2L/d + 1` of the intervals
   `[γ-L, γ+L]`, so `∑_γ ∫_{γ-L}^{γ+L} |f'|² ≤ (2L/d+1) ‖f'‖²`.
   Combined: `∑_γ |f(γ+δ_γ) - f(γ)|² ≤ π² L (2L/d + 1) ‖f‖²` whenever `|δ_γ| ≤ L`.
4. **Transfer** with `(a+b)² ≤ 2a² + 2b²` (no Minkowski needed, works verbatim in `ℝ≥0∞`).

This does not use Plancherel–Pólya and is independent of `Γ`'s upper sampling constant; the upper
sampling bound for the perturbed set follows from the same estimate (the point flagged in the
task: the perturbed set must be checked to be sampling for the *upper* bound as well; it is, with
`B' = 2B + A/2`, no separation of `Γ'` required, only injectivity of `x ↦ x + δ x` so that the sum
over `Γ'` is the sum over `Γ`).

## A.1 Bernstein's inequality in `L²`

```lean
theorem memL2pi_mul_t {g : ℝ → ℂ} (hg : MemL2pi g) :
    MemL2pi (fun t ↦ I * (t : ℂ) * g t) ∧
      l2piSq (fun t ↦ I * (t : ℂ) * g t) ≤ ENNReal.ofReal (Real.pi ^ 2) * l2piSq g
```
Proof. `MemL2pi g` is `MemLp g 2 (volume.restrict (Ioc (-π) π))`. The function `t ↦ I * t` is
continuous and bounded by `π` on `Ioc (-π) π`, so `MemLp.of_le_mul`/`MemLp.mul_of_top_left`-type
lemma (grep `MemLp.of_le_mul`, `MemLp.of_bound`, `memLp_of_bounded`) or directly
`memLp_two_of_lintegral` (project, `PW/Basic.lean:59`) with
`∫⁻_{Ioc} ‖I t g t‖ₑ² ≤ ofReal(π²) ∫⁻_{Ioc} ‖g‖ₑ²`
via `lintegral_mono_ae` on `Ioc`: for `t ∈ Ioc (-π) π`, `‖I*t*g t‖ₑ² = ofReal(t²)·‖g t‖ₑ²` and
`t² ≤ π²` (`abs_le`, `sq_le_sq'`). Measurability is handled by `hg.aestronglyMeasurable`.
Second part is exactly that inequality (`ENNReal.ofReal_mul`, `enorm_mul`, `Complex.enorm_real`).
Use `lintegral_enorm_sq_lt_top_of_memLp` (`Basic.lean:54`) for finiteness.

```lean
theorem hasDerivAt_pwFT {g : ℝ → ℂ} (hg : MemL2pi g) (z : ℂ) :
    HasDerivAt (pwFT g) (pwFT (fun t ↦ I * (t : ℂ) * g t) z) z
```
Proof. `pwFT g z = ∫ t in -π..π, g t * exp (I z t)`. Apply
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(`Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean:96`; exact signature to be read: it has
`(ε_pos) (hF_meas) (hF_int) (hF'_meas) (h_bound : ∀ᵐ t, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, ‖F' x t‖ ≤ bound t)
(bound_integrable) (h_diff : ∀ᵐ t, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, HasDerivAt (F · t) (F' x t) x)`)
with `F z t = g t * exp (I * z * t)`, `F' z t = I * t * g t * exp (I * z * t)`, `ε = 1`,
`bound t = π * ‖g t‖ * exp(π (‖z‖ + 1))`. The pointwise bound is `norm_exp_I_mul_le`
(`Basic.lean:108`: `‖exp (I z t)‖ ≤ exp (π ‖z‖)` for `t ∈ Ioc (-π) π`, applied at `x ∈ ball z 1`,
`‖x‖ ≤ ‖z‖+1`) and `|t| ≤ π`. Integrability of `g` on `Ioc (-π) π`: `MemL2pi.integrableOn`
(`Basic.lean:42`); of `F x`, `F' x`: `MemL2pi.integrableOn_mul_exp` / `intervalIntegrable_mul_exp`
(`Basic.lean:46, 97`) (for `F'` apply with `memL2pi_mul_t`). `h_diff`: `hasDerivAt_exp` composed with
`(hasDerivAt_id x).const_mul (I * t)`.

```lean
theorem pw_bernstein (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) :
    MemPW (deriv f) ∧ pwNormSq (deriv f) ≤ ENNReal.ofReal (Real.pi ^ 2) * pwNormSq f
```
Proof. `obtain ⟨g, hg, hfg⟩ := exists_pwFT hPW hf` (so `f = pwFT g`, check exact form of
`exists_pwFT` at `Basic.lean:277`). Then `deriv f = pwFT g₁` with `g₁ t = I t g t`, by
`funext z; rw [hfg]; exact (hasDerivAt_pwFT hg z).deriv`. By `memL2pi_mul_t`, `g₁ ∈ L²`, so
`memPW_pwFT hPW` gives `MemPW (pwFT g₁)`. For the norms use `hPW.1 g`/`hPW.1 g₁` (the second
conjunct): `pwNormSq (pwFT g₁) = ofReal(2π) · l2piSq g₁ ≤ ofReal(2π) · ofReal(π²) · l2piSq g
= ofReal(π²) · pwNormSq f`. (`l2piSq` unfolds to the `∫⁻` in `hPW`.)

Nothing else about the Fourier side is needed. (An alternative, `f' ∈ PW` through Cauchy estimates
and `IsExpTypeLE`, is not shorter: it needs `‖f'‖₂` anyway.)

## A.2 Increments

```lean
theorem enorm_sq_sub_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (γ δ : ℝ) :
    ‖f ((γ + δ : ℝ) : ℂ) - f (γ : ℂ)‖ₑ ^ 2 ≤
      ENNReal.ofReal |δ| * ∫⁻ x in Icc (γ - |δ|) (γ + |δ|), ‖deriv f (x : ℂ)‖ₑ ^ 2
```
Proof. Let `F : ℝ → ℂ := fun x ↦ f x`; it is `ContDiff`/`HasDerivAt F (deriv f x) x` for all real
`x` (`hf.1.differentiableAt.hasDerivAt.comp_ofReal`, i.e. `HasDerivAt.comp_ofReal`). `deriv f` is
continuous (`hf.1.contDiff`, `Differentiable.contDiff`), hence interval integrable. FTC:
`intervalIntegral.integral_eq_sub_of_hasDerivAt : f(γ+δ) - f γ = ∫ x in γ..γ+δ, deriv f x`.
Let `J := uIcc γ (γ+δ) ⊆ Icc (γ-|δ|) (γ+|δ|)`, `|J| = |δ|`. Then
`‖∫_γ^{γ+δ} φ‖ ≤ ∫_J ‖φ‖` (`intervalIntegral.norm_integral_le_integral_norm` /
`MeasureTheory.norm_integral_le_lintegral_norm`). Work in `ℝ≥0∞`:
`‖f(γ+δ)-fγ‖ₑ ≤ ∫⁻_J ‖φ‖ₑ`, then Cauchy–Schwarz in the form
`(∫⁻_J u)² ≤ |J| · ∫⁻_J u²`, which follows from Jensen/Hölder in `ℝ≥0∞`:
`ENNReal.lintegral_mul_le_Lp_mul_Lq` (`μ`, `p = q = 2`, `f = u`, `g = 1`) or
`ENNReal.lintegral_rpow_le_...`; if awkward, go through reals: `u` is bounded and continuous on
the compact `J`, so use `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` (`Bochner/Basic.lean:1237`)
with `p = q = 2`, or the elementary `∫ (u - c)² ≥ 0` trick with `c = (1/|J|)∫u` (then
`(∫u)² ≤ |J| ∫u²` is `|J|∫(u-c)² = |J|∫u² - (∫u)² ≥ 0`). Finally monotonicity
`lintegral_mono_set (J ⊆ Icc …)`. The case `δ = 0` is trivial (both sides `0`); `volume J = ofReal |δ|`
by `Real.volume_interval` / `Real.volume_Icc`. This lemma does not use `hPW` except through
`pw_bernstein` elsewhere; the hypothesis `hPW` can be dropped (keep scaffold signature, or drop it
at implementation: then remove it from the call site).

## A.3 Finite overlap

```lean
theorem IsSepBy.ncard_Icc_le {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ) (x L : ℝ)
    (hL : 0 ≤ L) : ((Γ ∩ Icc (x - L) (x + L)).ncard : ℝ) ≤ 2 * L / d + 1
```
Proof. The set `T = Γ ∩ Icc (x-L)(x+L)` is finite (`IsSeparated.finite_inter_Icc`,
`Basic.lean:505`). If `T = ∅`, trivial. Otherwise let `n = #T`, list its elements increasingly
`t₀ < … < t_{n-1}` (`Finset.orderEmbOfFin`, or induction); consecutive gaps are `≥ d`, so
`(n-1) d ≤ t_{n-1} - t₀ ≤ 2L`. Cleaner (no sorting): by induction on `n` prove
"a finite `d`-separated set `T` has `(#T - 1) d ≤ sSup T - sInf T`" using `Finset.exists_max_image`,
remove the maximum `m`; the new max `m'` satisfies `m - m' ≥ d`; or use the pigeonhole version:
the intervals `Ico (t - d/2) (t + d/2)`, `t ∈ T`, are pairwise disjoint, contained in
`Icc (x-L-d/2) (x+L+d/2)` of length `2L + d`, so `n d ≤ 2L + d` by `measure_biUnion_finset` +
`Real.volume_Ico` + `measure_mono` — this gives exactly `n ≤ 2L/d + 1` and is the recommended route
(the disjointness is from `hΓ`).

```lean
theorem tsum_lintegral_Icc_le {d : ℝ} (hd : 0 < d) {Γ : Set ℝ} (hΓ : IsSepBy d Γ) {L : ℝ}
    (hL : 0 ≤ L) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∑' γ : Γ, ∫⁻ x in Icc ((γ : ℝ) - L) ((γ : ℝ) + L), φ x ≤
      ENNReal.ofReal (2 * L / d + 1) * ∫⁻ x, φ x
```
Proof. `Γ` is countable (separated: `IsSeparated.finite_inter_Icc` plus `Set.countable_iUnion` over
`Icc (-n) n`; or `Set.Countable` via `IsSepBy` ⇒ discrete second countable, check
`Set.PairwiseDisjoint.countable_of_Ioo`/`countable_setOf_isolated`). Rewrite
`∫⁻ x in Icc (γ-L)(γ+L), φ = ∫⁻ x, (Icc (γ-L) (γ+L)).indicator φ x` (`lintegral_indicator`), swap
`tsum` and `lintegral` with `lintegral_tsum` (`Lebesgue/Add.lean:362`, needs `Countable Γ`,
`AEMeasurable`), then pointwise
`∑'_γ indicator (Icc (γ-L)(γ+L)) φ x = φ x · #{γ ∈ Γ : |x-γ| ≤ L} ≤ ofReal(2L/d+1) φ x`
(the count is `(Γ ∩ Icc (x-L)(x+L)).ncard`; to convert `∑'` over `Γ` of indicators of `1` to a
cardinal use `tsum_eq_sum` over the finite set + `Finset.sum_const`, `Finset.card_eq`;
`ENNReal.tsum_const_smul`). Then `lintegral_const_mul'` / `lintegral_mono`.

```lean
theorem tsum_sub_le (hPW) (hd) (hΓ : IsSepBy d Γ) (hL : 0 ≤ L) (hδ : ∀ x ∈ Γ, |δ x| ≤ L) (hf : MemPW f) :
    ∑' γ : Γ, ‖f (((γ : ℝ) + δ γ : ℝ) : ℂ) - f ((γ : ℝ) : ℂ)‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.pi ^ 2 * L * (2 * L / d + 1)) * pwNormSq f
```
Proof. By `enorm_sq_sub_le` and `|δ γ| ≤ L`, each term is `≤ ofReal L · ∫⁻_{Icc (γ-L)(γ+L)} ‖f'‖ₑ²`
(`lintegral_mono_set`, `ENNReal.ofReal_le_ofReal`). `ENNReal.tsum_mul_left`, then
`tsum_lintegral_Icc_le` with `φ = ‖deriv f ·‖ₑ²` (measurable: `deriv f` continuous),
then `∫⁻ φ = pwNormSq (deriv f) ≤ ofReal(π²) pwNormSq f` by `pw_bernstein`. Combine
`ofReal` products with `ENNReal.ofReal_mul`.

## A.4 Transfer to sampling

```lean
theorem sampleSum_image {φ : ℝ → ℝ} {Γ : Set ℝ} (hφ : InjOn φ Γ) (f : ℂ → ℂ) :
    sampleSum (φ '' Γ) f = ∑' γ : Γ, ‖f ((φ γ : ℝ) : ℂ)‖ₑ ^ 2
```
Proof. `Equiv.Set.imageOfInjOn φ Γ hφ : Γ ≃ φ '' Γ` (grep `Set.BijOn.equiv`/`Equiv.Set.imageOfInjOn`;
else `Set.InjOn.bijOn_image.equiv`) and `Equiv.tsum_eq`. Unfold `sampleSum`.

```lean
theorem tsum_enorm_sq_add_le (a b : ι → ℂ) :
    ∑' i, ‖a i + b i‖ₑ ^ 2 ≤ 2 * ∑' i, ‖a i‖ₑ ^ 2 + 2 * ∑' i, ‖b i‖ₑ ^ 2
```
Pointwise: `‖x+y‖ₑ² ≤ 2‖x‖ₑ² + 2‖y‖ₑ²` — go through `NNReal` or `ofReal`: `‖x+y‖² ≤ 2‖x‖²+2‖y‖²`
real (`add_sq_le`/`nlinarith [sq_nonneg (‖x‖-‖y‖)]` with `norm_add_le`), then
`enorm_eq_ofReal`/`ofReal_pow`/`ENNReal.ofReal_add`. Then `ENNReal.tsum_add`, `ENNReal.tsum_mul_left`,
`ENNReal.tsum_le_tsum`.

## A.5 Main theorem

```lean
theorem dsPerturbation_of_paleyWiener (hPW : PaleyWienerThm) : DSPerturbation
```
Proof. Given `Γ` separated (`⟨d, hd, hsep⟩` – `IsSeparated` is definitionally `IsSepBy d`, use
`isSeparated_iff_exists_isSepBy`) and sampling `⟨A, B, hA, h⟩` (`A B : ℝ≥0`). Put
`L := min d (A / (12 π²))` (positive; `A` is the real number `(A : ℝ)`). Then `L ≤ d` so
`2L/d + 1 ≤ 3`, and `ε² := π² L (2L/d+1) ≤ 3π² L ≤ A/4`.
Fix `δ`, `|δ x| ≤ L` on `Γ`, injectivity, and `f ∈ PW`, `N := pwNormSq f`.
Write `S' = sampleSum Γ' f`, `S = sampleSum Γ f`, `D = ∑' γ : Γ, ‖f(γ+δ γ) - f γ‖ₑ²`.
By `sampleSum_image` `S' = ∑' γ, ‖f (γ+δγ)‖ₑ²`; `tsum_sub_le` gives `D ≤ ofReal(ε²) N ≤ ofReal(A/4) N`.
* **Lower:** `f(γ) = f(γ+δγ) + (f γ - f(γ+δγ))` and `‖f γ - f(γ+δγ)‖ₑ = ‖f(γ+δγ)-fγ‖ₑ`
  (`enorm_sub_rev`), so by `tsum_enorm_sq_add_le`, `A N ≤ S ≤ 2 S' + 2 D ≤ 2S' + (A/2) N`, hence
  `(A/4)·N ≤ S'`: more precisely `A N ≤ 2 S' + (A/2) N`, and `N < ∞` (`pwNormSq_ne_top`) lets us
  subtract in `ℝ≥0∞` (`ENNReal.sub_le_of_le_add`/`ENNReal.le_sub_of_add_le_right` or go via
  `toReal`), giving `(A/2) N ≤ 2 S'`.
* **Upper:** `f(γ+δγ) = f γ + (f(γ+δγ) - f γ)`, so `S' ≤ 2S + 2D ≤ 2B N + (A/2) N`.
So `IsSampling Γ'` holds with `A' = A/4`, `B' = 2B + A/2`. Packaging: `⟨A/4, 2*B + A/2, _, fun f hf ↦ …⟩`
with `NNReal` coercions (`ENNReal.coe_div`-style: write `(A/4 : ℝ≥0)` as `A * (1/4)` to avoid
division in `ℝ≥0∞`; simpler: use `A' = A/4`, prove `((A/4 : ℝ≥0) : ℝ≥0∞) * N ≤ S'` by
multiplying the inequality by `1/2` carefully, or choose constants `A' = A/4` and prove
`4 * (A/4 : ℝ≥0) = A` with `NNReal.mul_div_cancel`).

Edge cases: `Γ = ∅`: then sampling forces `A‖f‖² ≤ 0` for all `f`, impossible since PW has a nonzero
element (`exists_memPW_eval_ne_zero`), so `Γ` nonempty; nothing in the proof needs this.
Non-injective `δ` is excluded by hypothesis. Separation of `Γ'` is not needed.

## A.6 Size and risks (Part A)
~350 lines of Lean. Hardest: `hasDerivAt_pwFT` (parametric derivative, ~60 lines; follow
`PW/Bounds.lean` style for the `exp` estimates), `tsum_lintegral_Icc_le` (counting/`tsum` interchange,
~80 lines), the `ℝ≥0∞` subtraction in the lower bound. Low conceptual risk.

---------------------------------------------------------------------------------------------------
# Part B. `JohnNirenberg`

```lean
def JohnNirenberg : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ h : ℝ → ℝ, LocallyIntegrable h → ∀ M : ℝ, 0 < M →
    (∀ a b : ℝ, a < b → meanOsc h a b ≤ M) → ∀ a b : ℝ, a < b → ∀ s : ℝ, 0 < s →
      volume {t ∈ Icc a b | s ≤ |h t - intervalMean h a b|} ≤
        ENNReal.ofReal (C * Real.exp (-(c * s / M)) * (b - a))
```
True as stated (it is the standard theorem; the `LocallyIntegrable` hypothesis makes `meanOsc` and
`intervalMean` the genuine integrals — for non-integrable `h` Lean's `∫ = 0` could make the statement
false; here it is excluded). We prove it with `C = 2`, `c = log 2 / 4`.

## B.0 Route
Dyadic stopping-time (Calderón–Zygmund) decomposition at level `λ = 2M` of `I₀ = [a,b]`, one step
(`cz_step`), then induction on `k` (`jn_iter`): `|{|h - h_I| > 4Mk}| ≤ 2^{-k}|I|` for *all*
intervals simultaneously, and a last rounding step. No covering lemma, no Vitali; Lebesgue
differentiation is used once, through Mathlib:
`IsUnifLocDoublingMeasure.ae_tendsto_average`
(`Mathlib/MeasureTheory/Covering/DensityTheorem.lean:159`):
`∀ᵐ x ∂μ, ∀ {ι l} (w : ι → α) (δ : ι → ℝ) (_ : Tendsto δ l (𝓝[>] 0)) (_ : ∀ᶠ j in l, x ∈ closedBall (w j) (K * δ j)), Tendsto (fun j => ⨍ y in closedBall (w j) (δ j), f y ∂μ) l (𝓝 (f x))`
for `LocallyIntegrable f μ`. On `ℝ` with `volume` the instance `IsUnifLocDoublingMeasure volume`
comes from `IsAddHaarMeasure` (check by `inferInstance`; the lemma sits in namespace
`IsUnifLocDoublingMeasure`). A dyadic interval `[c-r, c+r]` is `closedBall c r` and contains `x`,
so `K = 1`. This is exactly what is needed (cf. `VitaliFamily.ae_tendsto_average`, `Differentiation.lean:856`,
the general version). No Mathlib John–Nirenberg or dyadic CZ exists (grepped `John`, `Nirenberg`, `Calder`).

## B.1 Notation and conversions
Everything below fixes `h` locally integrable, `M > 0`, `hosc : ∀ a<b, meanOsc h a b ≤ M`.
For `a < b` the interval integrals are `∫ t in a..b = ∫ t in Ioc a b` (`intervalIntegral.integral_of_le`);
and `Ioc`, `Ico`, `Icc` integrals agree (`MeasureTheory.integral_Icc_eq_integral_Ioc`,
`integral_Ico_eq_integral_Ioo`, `integral_Ioc_eq_integral_Ioo`), likewise volumes
(`Real.volume_Ioc`, `Real.volume_Icc`, `Real.volume_Ico`). `h` is integrable on every bounded
interval (`LocallyIntegrable.integrableOn_isCompact`, `isCompact_Icc`; `IntervalIntegrable`).
Let `m = h_I := intervalMean h a b`, `g := |h - m|`. `meanOsc h a b ≤ M` reads
`∫_{Ioc a b} g ≤ M (b - a)` (multiply by `b - a > 0`).
Key elementary fact (A): for any `a'<b'`, `|intervalMean h a' b' - m| ≤ (b'-a')⁻¹ ∫_{Ioc a' b'} g`
(since `intervalMean h a' b' - m = (b'-a')⁻¹ ∫ (h - m)`, using `integral_sub`, `integral_const`,
and `norm_integral_le_integral_norm`).

```lean
def dyadic (a b : ℝ) (n k : ℕ) : Set ℝ :=
  Ico (a + k * (b - a) / 2 ^ n) (a + (k + 1) * (b - a) / 2 ^ n)
def dyadicIdx (a b : ℝ) (n : ℕ) (x : ℝ) : ℕ := ⌊(x - a) / (b - a) * 2 ^ n⌋₊
theorem mem_dyadic_dyadicIdx (hab : a < b) (n) (hx : x ∈ Ico a b) : x ∈ dyadic a b n (dyadicIdx a b n x)
theorem dyadic_parent (n k) : dyadic a b (n + 1) k ⊆ dyadic a b n (k / 2)
theorem volume_dyadic (a b) (n k) : volume (dyadic a b n k) = ENNReal.ofReal ((b - a) / 2 ^ n)
```
Proofs. `mem_dyadic_dyadicIdx`: with `y = (x-a)/(b-a)·2ⁿ ≥ 0`, `⌊y⌋₊ ≤ y < ⌊y⌋₊ + 1`
(`Nat.floor_le`, `Nat.lt_floor_add_one`); rearrange using `b - a > 0`. `dyadic_parent`:
`k/2` is nat division, `2(k/2) ≤ k`, `k+1 ≤ 2(k/2) + 2` (`Nat.div_add_mod`, `omega` after casting;
state via `(k/2 : ℕ)` casts: `Nat.cast_div_le`-free: set `k = 2q + r`, `r<2`), and
`a + k(b-a)/2^{n+1} = a + (k/2·…)`; use `pow_succ`, `field_simp`, `nlinarith`.
`volume_dyadic`: `Real.volume_Ico` and `ring`.
Also needed (not in scaffold; state as a local lemma, `dyadic_nested_or_disjoint`):
for `n ≤ n'`, either `k' / 2^(n'-n) = k` and `dyadic a b n' k' ⊆ dyadic a b n k`, or they are disjoint
(`Set.disjoint_left`, interval endpoint arithmetic; easiest by induction on `n' - n` with
`dyadic_parent` and the disjointness of the two children of a parent / of distinct generation-`n`
intervals: for `k ≠ k'`, `Ico` endpoints `(k+1)w ≤ k' w`).

## B.2 The Calderón–Zygmund step

```lean
theorem cz_step (hh : LocallyIntegrable h) (hM : 0 < M) (hosc : ∀ a b, a < b → meanOsc h a b ≤ M)
    (hab : a < b) :
    ∃ (ι : Type) (_ : Countable ι) (a' b' : ι → ℝ), (∀ i, a ≤ a' i ∧ a' i < b' i ∧ b' i ≤ b) ∧
      (Pairwise fun i j ↦ Disjoint (Ioc (a' i) (b' i)) (Ioc (a' j) (b' j))) ∧
      (∑' i, ENNReal.ofReal (b' i - a' i)) ≤ ENNReal.ofReal ((b - a) / 2) ∧
      (∀ i, |intervalMean h (a' i) (b' i) - intervalMean h a b| ≤ 4 * M) ∧
      ∀ᵐ t, t ∈ Ioc a b → t ∉ (⋃ i, Ioc (a' i) (b' i)) → |h t - intervalMean h a b| ≤ 2 * M
```
Proof. Put `m = intervalMean h a b`, `g = fun t ↦ |h t - m|`, `λ = 2M`, and for a dyadic cell
`(n,k)` the number `G n k = ∫ t in dyadic a b n k, g t ∈ ℝ`.
*Stopping predicate:* `Stop n k := 1 ≤ n ∧ λ * ((b-a)/2^n) < G n k`.
*Selected cells:* `Sel n k := k < 2^n ∧ Stop n k ∧ ∀ j, 1 ≤ j → j < n → ¬ Stop j (k / 2^(n-j))`
(first stopping ancestor; for `j = 0` we do not test: `I₀` itself is never selected).
Index type `ι := {p : ℕ × ℕ // Sel p.1 p.2}` (countable: `Subtype.countable`, `Prod.countable`).
`a' p = a + k (b-a)/2ⁿ`, `b' p = a + (k+1)(b-a)/2ⁿ`.

1. `a ≤ a' < b' ≤ b`: from `k < 2ⁿ` (`k+1 ≤ 2ⁿ`), arithmetic.
2. *Disjoint:* distinct selected `(n,k)`, `(n',k')`. If `n = n'` then `k ≠ k'`, disjoint cells.
   If `n < n'` and `dyadic n' k' ⊆ dyadic n k` (nested case of `dyadic_nested_or_disjoint`), then
   `j := n` is `< n'` with `1 ≤ n` and `k'/2^(n'-n) = k`, `Stop n k` holds: contradicts `Sel n' k'`.
   So they are disjoint cells; `Ioc` versions disjoint because `Ioc ⊆ ` interior-extension: use directly
   endpoint inequalities (`b'(p) ≤ a'(q)` or vice versa), i.e. prove disjointness of intervals from
   `Ico` disjointness plus nonempty interior: `Ioc x y ∩ Ioc x' y' = ∅` iff `y ≤ x' ∨ y' ≤ x`, and
   two disjoint nonempty `Ico` have exactly that property (`Set.Ico_disjoint_Ico`).
3. *Mean bound:* let `(n,k)` selected, parent `(n-1, k/2)` (`dyadic_parent`), `n ≥ 1`.
   If `n - 1 ≥ 1`, `¬ Stop (n-1) (k/2)` (from `Sel`, `j = n-1`, with `k / 2^(n-(n-1)) = k/2`) means
   `G (n-1) (k/2) ≤ λ (b-a)/2^{n-1}`. If `n = 1`, the parent is `[a,b)`, and
   `G 0 0 = ∫_{Ico a b} g ≤ M(b-a) ≤ λ (b-a)` by `hosc` and `M ≤ 2M`. In both cases,
   by `g ≥ 0` and `lintegral/integral_mono_set`, `G n k ≤ G (n-1) (k/2) ≤ λ (b-a)/2^{n-1} = 2λ |J|`
   where `|J| = (b-a)/2ⁿ`. With elementary fact (A): `|h_J - m| ≤ |J|⁻¹ G n k ≤ 2λ = 4M`.
   (`intervalMean h a' b'` uses `Ioc`, `G` uses `Ico`: equal by §B.1.)
4. *Total length:* `λ |J_p| < G p` for each selected `p`, so
   `λ ∑_p |J_p| ≤ ∑_p G_p = ∫_{⋃ J_p} g ≤ ∫_{Ico a b} g ≤ M(b-a)`. In Lean do this in `ℝ≥0∞` with
   `lintegral_iUnion` (`Lebesgue/Basic.lean:597`; cells measurable `measurableSet_Ico`, pairwise
   disjoint from step 2), `lintegral_mono_set` (union ⊆ `Ico a b`), `ofReal_integral_eq_lintegral_ofReal`
   (`g` integrable on `Ico a b`, nonnegative) to match with the Bochner integrals; and
   `ENNReal.tsum_mul_left`, `ENNReal.ofReal_mul`. Dividing by `λ = 2M`: `∑ |J_p| ≤ (b-a)/2`
   (`ENNReal.mul_le_iff_le_inv`/`ENNReal.le_div_iff_mul_le`, or move to `toReal` using summability
   from the bound). If `ι` is empty the sum is `0`.
5. *Good set:* we show: for a.e. `t ∈ Ioc a b` with `t ∉ ⋃ Ioc (a' p)(b' p)`, `g t ≤ λ`.
   Discard the null set `N₁` of `t` for which Lebesgue differentiation for `g` fails
   (`IsUnifLocDoublingMeasure.ae_tendsto_average` applied to `g`, `K = 1`; `g` is locally integrable
   as `h` is, `LocallyIntegrable.sub`, `.norm`; note `h t` constant `m` is integrable), the null set
   `N₂ = {a, b} ∪ {a' p : p} ∪ {b' p : p}` (countable, `Set.Countable.measure_zero`), so that
   `t ∈ Ioo a b` and `t` is not a left endpoint of a selected cell. For such `t` (not in any
   `Ioc(a',b')`, hence, not being an endpoint, not in any `Ico` selected cell): claim
   `∀ n ≥ 1, ¬ Stop n (dyadicIdx a b n t)`. Otherwise by `Nat.find` there is a least `n ≥ 1` with
   `Stop n (dyadicIdx a b n t)`; set `k = dyadicIdx a b n t`; then `Sel n k` (the ancestors of the
   cell of `t` of generation `j<n` have index `dyadicIdx a b j t = k / 2^(n-j)`: lemma, from
   `Nat.floor` identity `⌊⌊y⌋₊ / 2^i⌋... = ⌊y/2^i⌋₊`: `Nat.floor_div_nat`, `Nat.floor_div_eq_div`)
   and `t ∈ dyadic a b n k` (`mem_dyadic_dyadicIdx`), so `t` is in a selected `Ico` cell, hence in
   `Ioc (a' p)(b' p)` since `t ≠ a' p`: contradiction. Hence `G n k ≤ λ |J|` for all `n ≥ 1`
   with `k = dyadicIdx a b n t`. Now apply Lebesgue differentiation with `l = atTop`, `δ n = (b-a)/2^{n+1}`
   (`→ 0` within `𝓝[>] 0`: `tendsto_nhdsWithin_iff`, `tendsto_pow_atTop_nhds_zero_of_lt_one`), centre
   `w n = (a'(n,k) + b'(n,k))/2`; `t ∈ closedBall (w n) (1·δ n)` since `t ∈ Ico`-cell. We get
   `⨍ y in closedBall (w n) (δ n), g y → g t`. But `closedBall (w n) (δ n) = Icc a' b'` and
   `⨍ Icc = ⨍ Ico = G n k / |J| ≤ λ` (`MeasureTheory.setAverage_eq`, `Real.volume_Icc`,
   `integral_Icc_eq_integral_Ico`). Passing to the limit: `le_of_tendsto'`/`ge_of_tendsto`. So `g t ≤ λ`.
Return `⟨ι, inferInstance, a', b', …⟩`. 

## B.3 Iteration

```lean
theorem jn_iter (hh) (hM) (hosc) (k : ℕ) : ∀ a b, a < b →
    volume {t ∈ Ioc a b | 4 * M * k < |h t - intervalMean h a b|} ≤ ENNReal.ofReal ((1/2)^k * (b - a))
```
Proof by induction on `k`. `k = 0`: the set is contained in `Ioc a b`, `volume = ofReal (b-a)`
(`measure_mono`, `Real.volume_Ioc`). Step `k → k+1`: fix `a<b`, take `ι, a', b'` from `cz_step`,
`m = h_{[a,b]}`, `E = {t ∈ Ioc a b | 4M(k+1) < |h t - m|}`. Let
`F i = {t ∈ Ioc (a' i)(b' i) | 4M k < |h t - h_{[a' i,b' i]}|}` (hypothesis for `k`, at the interval
`a' i < b' i`). Claim: `E ⊆ Z ∪ ⋃ i, F i` with `Z` null (the exceptional set of the last clause of
`cz_step`). Indeed for `t ∈ E` outside `Z`: if `t ∉ ⋃ Ioc (a' i)(b' i)` then `|h t - m| ≤ 2M < 4M(k+1)`,
contradiction; so `t ∈ Ioc (a' i)(b' i)` for some `i`, and
`|h t - h_i| ≥ |h t - m| - |h_i - m| > 4M(k+1) - 4M = 4Mk`. Then
`volume E ≤ ∑' i, volume (F i) ≤ ∑' i, ofReal ((1/2)^k (b'i - a'i))` (`measure_iUnion_le`, `measure_union_le`,
`measure_mono_null` for `Z`) `= ofReal((1/2)^k) ∑' ofReal(b'i-a'i)` (`ENNReal.ofReal_mul`, `ENNReal.tsum_mul_left`)
`≤ ofReal((1/2)^k)·ofReal((b-a)/2) = ofReal((1/2)^{k+1}(b-a))`. 

## B.4 Conclusion

```lean
theorem johnNirenberg_holds : JohnNirenberg
```
Take `C = 2`, `c = Real.log 2 / 4`. Given `h, M, hosc, a<b, s>0`: let `k := ⌈s / (4M)⌉₊ - 1`
(natural, `s/(4M) > 0` so the ceiling is `≥ 1`); then `4Mk < s` (`k < s/(4M)`: `Nat.ceil_lt_add_one`,
`Nat.sub_one_lt`...) and `k + 1 ≥ s/(4M)` (`Nat.le_ceil`). The set `{t ∈ Icc a b | s ≤ |h t - h_I|}`
is contained in `{a} ∪ {t ∈ Ioc a b | 4Mk < |h t - h_I|}`; `{a}` is null. By `jn_iter`,
`volume ≤ ofReal((1/2)^k (b-a))`, and
`(1/2)^k = 2 · (1/2)^{k+1} ≤ 2 · (1/2)^{s/(4M)} = 2 exp(-(log 2/4) s/M)`
(`Real.rpow_natCast`, `Real.rpow_le_rpow_of_exponent_ge`, `Real.exp_neg`, `Real.rpow_def_of_pos`:
`(1/2)^x = exp (-x log 2)`), matching `C exp(-(c s/M))` with `c s/M = (log 2/4) s/M = (s/(4M)) log 2`.
Then `ENNReal.ofReal_le_ofReal` and `mul_assoc`.

## B.5 Size and risks (Part B)
~450–650 lines of Lean. The risk is concentrated in `cz_step` (step 2: nested-or-disjoint, step 5:
index bookkeeping with `Nat.floor`/`Nat.find` and the Lebesgue-differentiation call with the
dependent `∀ {ι l}` universe-polymorphic quantifier; instantiate with `ι := ℕ`, `l := atTop`).
Possible simplification of step 5/2: replace the stopping *tree* by a recursion on generations,
`S_n := {x ∈ [a,b) : n is the first generation with stopping}`, a finite union of cells, and sum
the lengths generation by generation (`measure_iUnion` over `n` of the measurable `S_n`), at the
cost of weakening `cz_step` to "∃ a family of sets `S_n`"; `jn_iter` then sums over `(n,k)` selected.
Both versions are fine; the current statement of `cz_step` (explicit interval family) is
the most convenient for the induction.
Fallback if `ae_tendsto_average` proves awkward: `VitaliFamily.ae_tendsto_average` with
`Besicovitch`/`IsUnifLocDoublingMeasure.vitaliFamily volume 1` and `tendsto_filterAt`, or prove
a.e. convergence of dyadic averages via `MeasureTheory.Martingale`/`ae_tendsto_condExp` (heavier).

## Issues in the source
1. (Part A, p. 800; confidence high) The paper cites [DS52, Lemma III] in the form "separated
   sampling `Γ` ⇒ `Γ' = {γ_k + δ_k}` sampling when `δ` small". DS's own formulation is for
   *frames of exponentials* with a Bernstein–Taylor argument, with constant `(e^{πL}-1)√B < √A`.
   The `Prop` in `Defs.lean` additionally requires `x ↦ x + δ x` injective so that `Γ'` as a *set*
   has the same sampling sum; without injectivity (two points merging) the upper bound fails to be
   comparable with multiplicity. Our statement is the right one and is proved. No separation of `Γ'`
   is needed.
2. (Part A) The task's classical route needs `f^{(n)}∈PW` and Taylor series; we avoid it with FTC and
   Cauchy–Schwarz (same Bernstein input); the smallness condition is `π²L(2L/d+1) ≤ A/4`.
3. (Part B, p. 799; high) The paper only invokes John–Nirenberg through `Defs.lean`'s form; the
   `LocallyIntegrable` hypothesis is necessary for faithfulness (Bochner integral of a
   non-integrable function is `0`). The constants `C = 2`, `c = log 2/4` are not sharp (not optimised;
   only existence is claimed). The statement uses the closed
   interval `Icc a b` while the proof works on `Ioc a b`; the difference is the null set `{a}`.
