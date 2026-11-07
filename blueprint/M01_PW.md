# M01 — Paley–Wiener space toolkit

**Lean files:** `FourierFrames/PW/Basic.lean`, `PW/Bounds.lean`, `PW/PlancherelPolya.lean`,
`PW/Complete.lean` (all proved, no `sorry`).
**Paper:** §1 (p. 790, definition of `PW`, the Paley–Wiener reduction); Plancherel–Pólya used on
p. 796 (display (4), "`C` independent of `α`") and in the limit `α → π/2`, p. 797; Bernstein-type
estimates used on p. 796–797; the "evident fact" p. 799 (M02).
**Depends on:** M00 (`MemPW`, `pwNormSq`, `sampleSum`, `IsSeparated`, `IsH2Upper`, `fstar`,
`PaleyWienerThm`), Mathlib, and from the vendored OCS library only `OCS.csinc` and its bounds
(`OrtegaCerdaSeip/Bernstein/Sinc.lean`: `csinc`, `differentiable_csinc`,
`norm_csinc_le_exp_abs_im`, `norm_csinc_le_div`, `norm_csinc_ofReal_le_one`) and
`OCS.exists_tendstoLocallyUniformlyOn_of_ultrafilter` (`Bernstein/NormalFamily.lean`).
**Used by:** M02 (`MemPW.fstar`, `pw_norm_sq_le`, `pw_line_integral_le`, `pw_eval_lower`,
`exists_memPW_eval_ne_zero`), M03 (Plancherel–Pólya, `pw_complete`, `mul_div_sub`, evaluation
continuity), M04 (`plancherelPolya`, `plancherelPolya_tail`, `plancherelPolya_tail_union`,
`pw_deriv_bound`, `pw_complete` in `Corollary1/ClosedGraph.lean`), M07 (`Perturbation.lean`:
`pw_normal_family`, `mul_div_sub`, `plancherelPolya`), M10, P2 (`DSPerturbation`).

**Status (final).** All statements below are proved. Lean blocks show the statements (docstrings
as in the code); where the implemented route differs from the text it is marked *Implemented:*
(source: `impl_notes/pw.md`). Proved but unused anywhere: `pwFT_sub`, `tsum_enorm_sq_pwFT_int`,
`l2piSq_eq_of_pwFT_eq`, `fourierCoeffOn_pwFT` (the obsolete §1.7 route), `MemPW.isH2Upper_mul_exp`,
`MemPW.lintegral_mul_exp_le`.

Throughout, `f ∈ PW` means `MemPW f`, `‖f‖² = pwNormSq f ∈ ℝ≥0∞` (finite for `f ∈ PW`), and
`hPW : PaleyWienerThm`. For `g : ℝ → ℂ` write `F_g := pwFT g`, `F_g(z) = ∫_{-π}^{π} g(t) e^{izt} dt`
and `‖g‖² = l2piSq g = ∫_{(-π,π]} |g|²`.

## 0. `PaleyWienerThm`

`PaleyWienerThm` (Defs) is the Paley–Wiener–Plancherel theorem. Part 1 gives `F_g ∈ PW` and
`‖F_g‖² = 2π‖g‖²` for every `g ∈ L²(−π,π)`. Part 2 represents every `f ∈ PW` as `F_g` (without a
norm identity, which follows from part 1). `memPW_pwFT` is `hPW.1`; `exists_pwFT` is `hPW.2` plus
`hPW.1`. (A first, `↔` form had a vacuous `⇐`; it was strengthened to the present form before the
freeze, option (A) of the original blueprint. `PaleyWienerThm` is now proved: `paleyWiener_holds`,
`Cited/PaleyWiener.lean`, P1.)

## 1. `PW/Basic.lean`

### 1.1 Definitions

```lean
/-- `g ∈ L²(-π, π)`. -/
def MemL2pi (g : ℝ → ℂ) : Prop :=
  MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))
```
```lean
/-- `‖g‖²_{L²(-π,π)}`, in `ℝ≥0∞`. -/
def l2piSq (g : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2
```
```lean
/-- The transform `z ↦ ∫_{-π}^{π} g(t) e^{izt} dt` of the Paley–Wiener theorem. -/
def pwFT (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)
```
```lean
/-- `Λ` is `δ`-separated: distinct points are at distance `≥ δ`. -/
def IsSepBy (δ : ℝ) (Λ : Set ℝ) : Prop :=
  ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ |a - b|
```
```lean
/-- `g ↦ g(-·)`. -/
def reflect (g : ℝ → ℂ) : ℝ → ℂ := fun t ↦ g (-t)
```

`IsSepBy δ Λ` is `IsSeparated` with an explicit constant (`IsSeparated Λ ↔ ∃ δ > 0, IsSepBy δ Λ`, by
`Iff.rfl`, lemma `isSeparated_iff_exists_isSepBy`). Constants in all later results depend on `δ`
only through this `δ`.

### 1.2 Elementary lemmas about `L²(-π,π)`

```lean
theorem MemL2pi.integrableOn {g : ℝ → ℂ} (hg : MemL2pi g) :
    IntegrableOn g (Ioc (-Real.pi) Real.pi)
```
```lean
theorem MemL2pi.integrableOn_mul_exp {g : ℝ → ℂ} (hg : MemL2pi g) (z : ℂ) :
    IntegrableOn (fun t : ℝ ↦ g t * Complex.exp (I * z * t)) (Ioc (-Real.pi) Real.pi)
```
```lean
theorem l2piSq_ne_top {g : ℝ → ℂ} (hg : MemL2pi g) : l2piSq g ≠ ⊤
```

*Proof.* `μ = volume.restrict (Ioc (-π) π)` is a finite measure (`μ univ = 2π`), so
`MemLp g 2 μ → MemLp g 1 μ` (`MemLp.mono_exponent` / `MemLp.integrable` with `1 ≤ 2`, needs
`IsFiniteMeasure μ`; instance `isFiniteMeasure_restrict_Ioc`-type, or
`Restrict.isFiniteMeasure` + `measure_Ioc_lt_top`); that is `integrableOn`. For the product,
`t ↦ exp(I z t)` is continuous and bounded on `Ioc (-π) π` (`‖exp(I z t)‖ = exp(-t Im z)
≤ exp(π|Im z|)`, `Complex.norm_exp`), hence `Integrable.mul_bdd` (`Integrable.bdd_mul`). For
`l2piSq_ne_top`: `MemLp.eLpNorm_lt_top` and `eLpNorm_eq_lintegral_rpow_enorm_toReal`.

### 1.3 Reflection

```lean
theorem memL2pi_reflect {g : ℝ → ℂ} (hg : MemL2pi g) : MemL2pi (reflect g)
```
```lean
theorem l2piSq_reflect (g : ℝ → ℂ) : l2piSq (reflect g) = l2piSq g
```
```lean
theorem pwFT_reflect (g : ℝ → ℂ) (z : ℂ) :
    pwFT (reflect g) z = ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (-(I * z * t))
```

*Proof.* `pwFT_reflect` is `intervalIntegral.integral_comp_neg` (checked: `∫ x in a..b, f (-x) =
∫ x in -b..-a, f x`) applied to `s ↦ g s * exp(-(I z s))` on `[-π, π]`: the substitution `t = -s`
maps `[-π,π]` to itself and `exp(I z t) = exp(-(I z s))`. For `memL2pi_reflect` and `l2piSq_reflect`:
`t ↦ -t` preserves Lebesgue measure (`Measure.map_neg_eq_self`; `MeasurePreserving` of `neg`,
`measurePreserving_neg`) and maps `Ioc (-π) π` onto `Ico (-π) π`, which differs from `Ioc (-π) π` by
the null set `{-π, π}` (`Ico_ae_eq_Ioc`, `Ioc_ae_eq_Icc`, `Ico_ae_eq_Icc`). Hence
`∫⁻_{Ioc} ‖g(-t)‖² = ∫⁻_{Ico} ‖g‖² = ∫⁻_{Ioc} ‖g‖²` (`setLIntegral_congr` with the ae-equality),
and likewise for `MemLp` (`MemLp.comp_measurePreserving`, then `MemLp.congr_set_ae`‑type, or
unfold `MemLp` into `eLpNorm` and use the same equality).

### 1.4 Linearity, bound and Parseval for `pwFT` (no `hPW`)

```lean
theorem pwFT_sub {g h : ℝ → ℂ} (hg : MemL2pi g) (hh : MemL2pi h) (z : ℂ) :
    pwFT (fun t ↦ g t - h t) z = pwFT g z - pwFT h z
```

*Proof.* Linearity of the interval integral (`intervalIntegral.integral_sub`, needs
`IntervalIntegrable` of both integrands: from 1.2 via `intervalIntegral.intervalIntegrable_iff_integrableOn_Ioc_of_le`).

```lean
/-- `|pwFT g (z)| ≤ e^{π|Im z|} √(2π) ‖g‖_{L²(-π,π)}`. -/
theorem norm_pwFT_le {g : ℝ → ℂ} (hg : MemL2pi g) (z : ℂ) :
    ‖pwFT g z‖ ≤ Real.exp (Real.pi * |z.im|) * Real.sqrt (2 * Real.pi * (l2piSq g).toReal)
```

*Proof.* `‖F_g(z)‖ ≤ ∫_{(-π,π]} ‖g(t)‖ ‖e^{izt}‖ dt` (`intervalIntegral.norm_integral_le_integral_norm`,
`integral_of_le`), and for `|t| ≤ π`: `‖e^{izt}‖ = e^{Re(izt)} = e^{-t Im z} ≤ e^{π|Im z|}` (`Complex.norm_exp`,
`abs_le`, `Real.exp_le_exp`). Then Cauchy–Schwarz on an interval of length `2π`:
`(∫_{Ioc} ‖g‖)² ≤ 2π ∫_{Ioc} ‖g‖²`
(use `inner_mul_le_norm_mul_norm` in `L²`, or `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`
with `p = q = 2`, or in `ℝ≥0∞`: `ENNReal.lintegral_mul_le_Lp_mul_Lq`; `volume (Ioc (-π) π) = 2π`).
So `‖F_g(z)‖ ≤ e^{π|y|} √(2π ‖g‖²)`. **Constant: exactly 1 in front of `e^{π|y|}√(2π)‖g‖`.**

```lean
/-- **Parseval at the integers** (Mathlib: `AddCircle.hasSum_sq_fourierCoeffOn`, period `2π`):
`∑_{k ∈ ℤ} |pwFT g k|² = 2π ‖g‖²`. -/
theorem tsum_enorm_sq_pwFT_int {g : ℝ → ℂ} (hg : MemL2pi g) :
    ∑' k : ℤ, ‖pwFT g (k : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (2 * Real.pi) * l2piSq g
```

*Proof.* Mathlib: `AddCircle.hasSum_sq_fourierCoeffOn {a b} (hab : a < b) (hL2 : MemLp f 2
(volume.restrict (Ioc a b))) : HasSum (fun i ↦ ‖fourierCoeffOn hab f i‖ ^ 2) ((b-a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2)`
with `a = -π`, `b = π`. By `fourierCoeffOn_eq_integral`,
`fourierCoeffOn hab g n = (1/2π) ∫_{-π}^{π} fourier (-n) (x : AddCircle (2π)) • g x dx`, and
`fourier_coe_apply : fourier n (x : AddCircle T) = exp(2π i n x / T)`; with `T = 2π` this is
`exp(i n x)`, so `fourierCoeffOn g n = (2π)⁻¹ F_g(-n)`. Reindex `n ↦ -n` (`Equiv.neg ℤ`,
`tsum_equiv`/`HasSum.comp_equiv`). Multiply by `(2π)²`: `∑_k |F_g(k)|² = 2π ∫|g|²`. Convert
`‖·‖^2` real sums to `ℝ≥0∞` with `ENNReal.ofReal_tsum_of_nonneg` and `‖z‖ₑ^2 = ofReal (‖z‖^2)`
(`enorm_eq_ofReal`, `ofReal_pow`), `l2piSq g = ofReal(∫ ‖g‖²)` via `ofReal_integral_eq_lintegral_ofReal`
(`MemLp` ⇒ `Integrable (‖g‖^2)`, `memLp_two_iff_integrable_sq_norm`).

```lean
/-- **Uniqueness**: `pwFT g = pwFT h` on `ℤ` forces `g = h` a.e. on `(-π, π]`; in particular the
norms agree. -/
theorem l2piSq_eq_of_pwFT_eq {g h : ℝ → ℂ} (hg : MemL2pi g) (hh : MemL2pi h)
    (hgh : ∀ k : ℤ, pwFT g (k : ℂ) = pwFT h (k : ℂ)) : l2piSq g = l2piSq h
```

*Proof.* Apply `tsum_enorm_sq_pwFT_int` to `h := g - g'` (`pwFT_sub`, `MemLp.sub`): all
terms vanish, so `l2piSq h = 0` (`ofReal (2π) ≠ 0`), i.e. `g = g'` a.e. on `Ioc (-π) π`
(`lintegral_eq_zero_iff`, `ae_restrict` form); then `lintegral_congr_ae` gives equality of the
`l2piSq`.

```lean
/-- Locally uniform limits (along any filter) of functions of `PW` with a uniform bound
`|F_i(z)| ≤ K e^{π|Im z|}` and bounded norms lie in `PW`, and `‖f‖² ≤ liminf ‖F_i‖²` (Fatou). -/
theorem memPW_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, MemPW (F i)) {K : ℝ} (hK : ∀ i z, ‖F i z‖ ≤ K * Real.exp (Real.pi * |z.im|))
    (hd : Differentiable ℂ f) (hlim : ∀ z, Tendsto (fun i ↦ F i z) l (nhds (f z)))
    {M : ℝ≥0∞} (hM' : M ≠ ⊤) (hM : ∀ i, pwNormSq (F i) ≤ M) :
    MemPW f ∧ pwNormSq f ≤ liminf (fun i ↦ pwNormSq (F i)) l
```

*Proof.* (This is the shared "limit stays in `PW`" lemma, used for completeness, normal families,
and in the (obsolete) closure step of the old §1.7; it does not need `hPW`.)
* *Entire:* hypothesis `hd`.
* *Type:* for `ε > 0`, `‖f z‖ = lim ‖F_i z‖ ≤ K e^{π|Im z|} ≤ |K| e^{(π+ε)‖z‖}`
  (`le_of_tendsto`, `Complex.abs_im_le_norm`, `Real.exp_le_exp`, `mul_le_mul_of_nonneg_left`).
* *`L²(ℝ)` and Fatou:* `‖F_i x‖ₑ² → ‖f x‖ₑ²` for every real `x` (continuity of `‖·‖ₑ^2`), so
  `∫⁻ ‖f x‖ₑ² = ∫⁻ liminf_i ‖F_i x‖ₑ² ≤ liminf_i ∫⁻ ‖F_i x‖ₑ²` by
  `MeasureTheory.lintegral_liminf_le` (needs measurability of each `x ↦ ‖F_i x‖ₑ²`: continuity
  of entire functions) (Fatou needs `l.IsCountablyGenerated`, which is therefore a hypothesis of the Lean statement; every use is `atTop` on `ℕ`. In particular it can *not* be applied along an ultrafilter: see §4, `pw_normal_family`, where it is applied only after extracting a subsequence.) The right side is
  `≤ M < ∞`, so `MemLp (f|ℝ) 2` (`memLp_two_iff_integrable_sq_norm`, `lintegral` finite;
  measurability: `f` continuous).

### 1.5 Algebra of `PW`

```lean
theorem memPW_zero : MemPW (fun _ : ℂ ↦ (0 : ℂ))
```
```lean
theorem MemPW.add {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) : MemPW (f + g)
```
```lean
theorem MemPW.sub {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) : MemPW (f - g)
```
```lean
theorem MemPW.const_mul {f : ℂ → ℂ} (hf : MemPW f) (c : ℂ) : MemPW (fun z ↦ c * f z)
```
```lean
theorem pwNormSq_ne_top {f : ℂ → ℂ} (hf : MemPW f) : pwNormSq f ≠ ⊤
```

*Proof.* Entireness: `Differentiable.add` etc. Type: given `ε`, `C_f, C_g` with
`‖f z‖ ≤ C_f e^{(π+ε)‖z‖}`; then `‖(f+g) z‖ ≤ (|C_f| + |C_g|) e^{(π+ε)‖z‖}` (`norm_add_le`); for
`c * f`: `‖c‖ C_f`. `L²`: `MemLp.add`, `MemLp.sub`, `MemLp.const_mul` (names `MemLp.add`,
`MemLp.sub`, `MemLp.const_smul`; `fun x ↦ (f+g) x` unfolds to `f x + g x`; `Pi.add_apply`).
`pwNormSq_ne_top`: `MemLp f 2 ⇒ eLpNorm f 2 < ⊤`, and `eLpNorm f 2 volume ^ 2 = ∫⁻ ‖f‖ₑ²`
(`eLpNorm_eq_lintegral_rpow_enorm_toReal`, `ENNReal.rpow_two`/`lintegral_rpow_enorm_lt_top`; or
`MemLp.integrable_sq`, `memLp_two_iff_integrable_sq_norm`).

### 1.6 Real translation and `f^*`

```lean
theorem MemPW.comp_sub_ofReal {f : ℂ → ℂ} (hf : MemPW f) (a : ℝ) :
    MemPW (fun z ↦ f (z - a))
```
```lean
theorem pwNormSq_comp_sub_ofReal (f : ℂ → ℂ) (a : ℝ) :
    pwNormSq (fun z ↦ f (z - a)) = pwNormSq f
```
```lean
theorem MemPW.fstar {f : ℂ → ℂ} (hf : MemPW f) : MemPW (FF.fstar f)
```
```lean
theorem pwNormSq_fstar (f : ℂ → ℂ) : pwNormSq (FF.fstar f) = pwNormSq f
```

*Proof.* **Translation** (no `hPW`; one can also see it as `g ↦ g e^{-iat}` in the representation).
`z ↦ f(z - a)` is entire (`Differentiable.comp`, `differentiable_id.sub_const`). Type: for each
`ε`, `‖f(z-a)‖ ≤ C e^{(π+ε)‖z-a‖} ≤ (C e^{(π+ε)|a|}) e^{(π+ε)‖z‖}` (`norm_sub_le`, `‖(a:ℂ)‖ = |a|`).
The restriction to `ℝ` is `x ↦ f(((x - a : ℝ)) : ℂ)` (push_cast `Complex.ofReal_sub`), a translate of the
`L²` function `f|ℝ`: `MemLp.comp_measurePreserving` with `measurePreserving_sub_right volume a`.
The norm identity is `MeasureTheory.lintegral_sub_right_eq_self` (to_additive version of
`lintegral_div_right_eq_self`; check the name: if absent, use `(measurePreserving_sub_right volume a).lintegral_comp`).

**`f^*`.** `fstar f z = conj (f (conj z))`. Entire: `f^*` is the composition of
`conj ∘ f ∘ conj`; the cleanest proof is via power series, or via
`HasDerivAt` conjugation: if `f` is complex differentiable at `conj z` with derivative `d`, then
`f^*` is complex differentiable at `z` with derivative `conj d`
(Mathlib has `HasDerivAt.star`/`DifferentiableAt.star`‑type lemmas only for real fields; for `ℂ`
write `fstar f = fun z ↦ starRingEnd ℂ (f (starRingEnd ℂ z))` and prove
`HasDerivAt` directly from `hasDerivAt_iff_tendsto_slope` and `Complex.continuous_conj`/`Complex.conj_conj`;
M02 owns `Differentiable.fstar` — if M02's lemma is available at assembly, use it and delete the
proof here). Type: `‖f^*(z)‖ = ‖f(conj z)‖ ≤ C e^{(π+ε)‖conj z‖} = C e^{(π+ε)‖z‖}`
(`Complex.norm_conj` / `RCLike.norm_conj`). On `ℝ`: `conj (x:ℂ) = x` (`Complex.conj_ofReal`), so
`fstar f x = conj (f x)`, with the same `‖·‖` (`Complex.norm_conj`/`RCLike.norm_conj`); hence the
`L²` property and `pwNormSq_fstar` (`lintegral_congr` with `enorm` of conjugate, `RCLike.enorm_conj`).

### 1.6b Division by a zero (axiom (H1))

```lean
/-- If `f ∈ PW` vanishes at `a`, then `z ↦ f(z)(z - b)/(z - a)`, extended at `a` by `dslope`,
is in `PW`. -/
theorem MemPW.mul_div_sub {f : ℂ → ℂ} (hf : MemPW f) {a : ℂ} (ha : f a = 0) (b : ℂ) :
    MemPW (fun z ↦ dslope f a z * (z - b))
```
```lean
/-- (H1): for nonreal `a`, the multiplier `(z - ā)/(z - a)` is unimodular on `ℝ`, so the norm is
preserved. -/
theorem pwNormSq_mul_div_sub_conj (f : ℂ → ℂ) {a : ℂ} (ha : a.im ≠ 0) (ha0 : f a = 0) :
    pwNormSq (fun z ↦ dslope f a z * (z - conj a)) = pwNormSq f
```

*Proof of `MemPW.mul_div_sub`.* Write `h z := dslope f a z * (z - b)`. Recall `dslope f a z = (f z - f a)/(z - a)` for `z ≠ a`
(`dslope_of_ne`, `slope_def_field`) and `dslope f a a = deriv f a` (`dslope_same`); with `f a = 0`: `dslope f a z = f z/(z-a)` for `z ≠ a`.
* *Entire.* `differentiableOn_dslope (hc : s ∈ 𝓝 c)` (Mathlib.Analysis.Complex.RemovableSingularity) with `s = univ`
  (`Filter.univ_mem`) gives `DifferentiableOn ℂ (dslope f a) univ` from `DifferentiableOn ℂ f univ`; `Differentiable` via
  `differentiableOn_univ`; then `.mul (differentiable_id.sub_const b)`.
* *Type `≤ π`.* Fix `ε > 0`, `C` with `‖f z‖ ≤ C e^{(π+ε/2)‖z‖}` (apply the definition with `ε/2`).
  (i) If `‖z - a‖ ≥ 1`: `‖dslope f a z‖ = ‖f z‖/‖z-a‖ ≤ ‖f z‖`. (ii) If `‖z - a‖ < 1`: `z` lies in `closedBall a 1`, a compact set on which the continuous
  `dslope f a` has a bound `M_a` (`IsCompact.exists_bound_of_continuousOn`; `M_a` depends on `f, a`). Hence for all `z`:
  `‖dslope f a z‖ ≤ max(C e^{(π+ε/2)‖z‖}, M_a) ≤ (|C| + M_a) e^{(π+ε/2)‖z‖}` (as `e^{·} ≥ 1`). Finally `‖z - b‖ ≤ ‖z‖ + ‖b‖ ≤ (1+‖b‖) e^{(ε/2)‖z‖}`
  (`‖z‖ ≤ e^{(ε/2)‖z‖}·(2/ε)`‑type, e.g. `Real.add_one_le_exp`: `(ε/2)‖z‖ + 1 ≤ e^{(ε/2)‖z‖}` so `‖z‖ ≤ (2/ε)e^{(ε/2)‖z‖}`). So
  `‖h z‖ ≤ C' e^{(π+ε)‖z‖}` with `C' = (|C| + M_a)(2/ε + ‖b‖)`.
* *`L²(ℝ)`.* `h|ℝ` is continuous. For real `x` with `|x - a| ≥ 1` (here `‖(x:ℂ) - a‖ ≥ 1`): `‖h x‖ = ‖f x‖ ‖x - b‖/‖x - a‖ ≤ ‖f x‖ (‖x-a‖ + ‖a-b‖)/‖x-a‖
  ≤ (1 + ‖a-b‖)‖f x‖`. For `‖(x:ℂ) - a‖ < 1` we have `|x - Re a| < 1`, `x ∈ Icc (Re a - 1) (Re a + 1)`, a compact interval on which the continuous `h` is bounded by some `M_h`.
  So `‖h x‖ ≤ (1+‖a-b‖)‖f x‖ + M_h · 1_{Icc (Re a - 1) (Re a + 1)}(x)` for every real `x`; the right side is in `L²(ℝ)`
  (`MemLp.const_mul` of `f|ℝ`, plus the `L²` indicator of a finite-measure set: `memLp_indicator_const`), hence `MemLp (h|ℝ) 2` by domination
  (`MemLp.of_le`, `MemLp.mono'`/`MemLp.of_le_mul`‑type; take the norm of the sum of two nonnegative `L²` functions, `MemLp.add`).

*Proof of `pwNormSq_mul_div_sub_conj`.* Hypotheses: `a.im ≠ 0` and `f a = 0`. For real `x`: `(x:ℂ) ≠ a` (since `a.im ≠ 0`), so
`dslope f a x = f x/(x - a)` and `dslope f a x * (x - conj a) = f x · (x - conj a)/(x - a)`. Now `x - conj a = conj (x - a)` (`Complex.conj_ofReal`,
`map_sub`) so `‖x - conj a‖ = ‖x - a‖` (`Complex.norm_conj`) and `‖x - a‖ ≠ 0`; hence `‖dslope f a x * (x - conj a)‖ = ‖f x‖`, pointwise on `ℝ`, and the
two `lintegral`s agree (`lintegral_congr`, `enorm` version: `enorm_mul`, `enorm_div`, `RCLike.enorm_conj`). **Without `f a = 0` the statement is false**
(`f ≡ 1`, `a = i`: `dslope f a ≡ 0`, left side `0`, right side `∞`); without `a.im ≠ 0`, for real `a` the unimodularity fails.
This is exactly axiom (H1) for `PW`: for `ζ = a` nonreal with `f(ζ) = 0`, `f(z)(z - ζ̄)/(z - ζ) ∈ PW` with the same norm (`b = conj ζ`).

### 1.7 `exists_pwFT`, `memPW_pwFT`: projections of `hPW`

```lean
/-- Easy half of `hPW`: every `f ∈ PW` is `pwFT g` for some `g ∈ L²(-π,π)`, with
`‖f‖² = 2π ‖g‖²`. -/
theorem exists_pwFT (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) :
    ∃ g : ℝ → ℂ, MemL2pi g ∧ f = pwFT g ∧ pwNormSq f = ENNReal.ofReal (2 * Real.pi) * l2piSq g
```

*Proof.* `obtain ⟨g, hg, hrep⟩ := hPW.2 f hf`; `f = pwFT g` by `funext hrep` (`pwFT g z` is by
definition the interval integral in `hrep`; `MemL2pi g` is the `MemLp` of `PaleyWienerThm`); norm
identity `(hPW.1 g hg).2` (`l2piSq g` is the `lintegral` there).

```lean
/-- **Strong form of the Paley–Wiener theorem** (see blueprint §0: `PaleyWienerThm` as stated
only gives `⇐` for `g` for which the norm identity is already known; this lemma derives the
unconditional `⇐`). For every `g ∈ L²(-π,π)`, `pwFT g ∈ PW` and `‖pwFT g‖² = 2π‖g‖²`. -/
theorem memPW_pwFT (hPW : PaleyWienerThm) {g : ℝ → ℂ} (hg : MemL2pi g) :
    MemPW (pwFT g) ∧ pwNormSq (pwFT g) = ENNReal.ofReal (2 * Real.pi) * l2piSq g
```

*Proof.* `hPW.1 g hg`. (The docstring is stale: it predates the strengthening of
`PaleyWienerThm`. The five-step Parseval/density derivation that stood here is obsolete; its helper
lemmas `pwFT_sub`, `tsum_enorm_sq_pwFT_int`, `l2piSq_eq_of_pwFT_eq`, `fourierCoeffOn_pwFT` of §1.4
are proved but unused.)

## 2. `PW/Bounds.lean`

### 2.1 Imaginary translates

```lean
/-- Imaginary translate of a transform: `pwFT g (z + i y) = pwFT (g e^{-y·}) z`. -/
theorem pwFT_add_mul_I (g : ℝ → ℂ) (y : ℝ) (z : ℂ) :
    pwFT g (z + y * I) = pwFT (fun t ↦ g t * ((Real.exp (-(y * t)) : ℝ) : ℂ)) z
```

*Proof.* `exp(I (z + yI) t) = exp(I z t) * exp(-y t)` (`mul_add`, `I * (y * I) * t = -y t`, `Complex.exp_add`,
`Complex.ofReal_exp`), inside the interval integral (`intervalIntegral.integral_congr`, `mul_assoc`).

```lean
/-- `g ∈ L²(-π,π)` implies `g e^{-y·} ∈ L²(-π,π)` with `‖g e^{-y·}‖² ≤ e^{2π|y|} ‖g‖²`. -/
theorem memL2pi_mul_exp {g : ℝ → ℂ} (hg : MemL2pi g) (y : ℝ) :
    MemL2pi (fun t ↦ g t * ((Real.exp (-(y * t)) : ℝ) : ℂ)) ∧
      l2piSq (fun t ↦ g t * ((Real.exp (-(y * t)) : ℝ) : ℂ)) ≤
        ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * l2piSq g
```

*Proof.* On `[-π, π]`: `0 < e^{-yt} ≤ e^{π|y|}` and `e^{-2yt} ≤ e^{2π|y|}`. `MemLp.mul_bdd`/`MemLp.of_le_mul`
(`MemLp.of_le_mul`: `‖h x‖ ≤ c ‖g x‖` ae ⇒ `MemLp h`) with `c = e^{π|y|}`; `lintegral_mono`
for the norm bound: `‖g(t)e^{-yt}‖ₑ² ≤ ofReal(e^{2π|y|}) ‖g(t)‖ₑ²`, `lintegral_const_mul`.

```lean
/-- Imaginary translates of `f ∈ PW` are in `PW` (`z ↦ f(z + i y)` corresponds to `g e^{-y t}`),
and `‖f(· + iy)‖² = 2π ∫ |g|² e^{-2yt}`. -/
theorem pw_translate_I (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (y : ℝ) :
    MemPW (fun z ↦ f (z + y * I))
```
```lean
/-- The exact norm of an imaginary translate: if `f = pwFT g` then
`‖f(· + iy)‖² = 2π ∫ e^{-2yt} |g(t)|² dt`. -/
theorem pwNormSq_translate_I (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (y : ℝ) :
    ∃ g : ℝ → ℂ, MemL2pi g ∧ f = pwFT g ∧
      pwNormSq f = ENNReal.ofReal (2 * Real.pi) * l2piSq g ∧
      pwNormSq (fun z ↦ f (z + y * I)) = ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ t in Set.Ioc (-Real.pi) Real.pi, ENNReal.ofReal (Real.exp (-(2 * y * t))) * ‖g t‖ₑ ^ 2
```

*Proof.* Let `g` from `exists_pwFT` (`f = pwFT g`, `‖f‖² = 2π‖g‖²`). By 2.1,
`f(z + iy) = F_{g_y}(z)` with `g_y := g e^{-y·}` ∈ `L²` (`memL2pi_mul_exp`). By `memPW_pwFT` (§1.7)
`F_{g_y} ∈ PW` and `‖F_{g_y}‖² = 2π ‖g_y‖² = 2π ∫_{(-π,π]} e^{-2yt}|g|²`
(`‖g(t) e^{-yt}‖ₑ² = ofReal(e^{-2yt}) ‖g(t)‖ₑ²`, `ofReal_exp`/`enorm_mul`, `ofReal_pow`).
`pw_translate_I` is the first assertion; `pwNormSq_translate_I` the identity (the function `fun z ↦ f (z + y*I)`
is `pwFT g_y` by `funext`). **Real translates** `f(z-a)` correspond to `g e^{-iat}`
(`pwFT_sub_ofReal`: not needed in Lean, see 1.6), with norm unchanged.

### 2.2 Pointwise bound and line integrals

```lean
/-- **Pointwise bound** `|f(z)|² ≤ e^{2π|Im z|} ‖f‖²` (constant exactly `1`). -/
theorem pw_norm_sq_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (z : ℂ) :
    ‖f z‖ ^ 2 ≤ Real.exp (2 * Real.pi * |z.im|) * (pwNormSq f).toReal
```

*Proof.* `exists_pwFT`: `f = F_g`, `‖f‖² = 2π ‖g‖²`. By `norm_pwFT_le`,
`‖f z‖² ≤ e^{2π|y|} · 2π (l2piSq g).toReal = e^{2π|y|} (pwNormSq f).toReal`
(`ENNReal.toReal_mul`, `ENNReal.toReal_ofReal`, `Real.sq_sqrt`, `Real.exp_mul`‑type rewriting `exp(π|y|)^2 = exp(2π|y|)`).
**Constant `1`, sharp only at `y = 0`** (the best constant is `sinh(2π|y|)/(2π|y|)`, from
Cauchy–Schwarz with `∫_{-π}^{π} e^{-2yt}dt`); **the exponent `2π|y|` is sharp** (R2-03).

```lean
/-- **Line integrals** `∫ |f(x + iy)|² dx ≤ e^{2π|y|} ‖f‖²`. -/
theorem pw_line_integral_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (y : ℝ) :
    ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * pwNormSq f
```

*Proof.* `∫⁻ ‖f(x+iy)‖ₑ² dx = pwNormSq (fun z ↦ f (z + y*I))` (definition, with
`((x:ℝ):ℂ) + (y:ℂ) * I`). By `pwNormSq_translate_I` it is `2π ∫_{Ioc} e^{-2yt}‖g‖ₑ²
≤ 2π e^{2π|y|} ∫_{Ioc} ‖g‖ₑ² = ofReal(e^{2π|y|}) ‖f‖²`. **Constant `e^{2π|y|}`, no other.**

### 2.3 `f e^{iπz} ∈ H²(ℂ₊)`

```lean
/-- `f(z) e^{iπz} ∈ H²(ℂ₊)`. -/
theorem MemPW.isH2Upper_mul_exp (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) :
    IsH2Upper (fun z ↦ f z * Complex.exp (I * Real.pi * z))
```
```lean
/-- The `H²` norm bound, with constant `1`: for `y > 0`,
`∫ |f(x+iy) e^{iπ(x+iy)}|² dx ≤ ‖f‖²_{PW}`. -/
theorem MemPW.lintegral_mul_exp_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) {y : ℝ}
    (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I) * Complex.exp (I * Real.pi * ((x : ℂ) + (y : ℂ) * I))‖ₑ ^ 2
      ≤ pwNormSq f
```

*Proof.* For `y > 0`, `|e^{iπ(x+iy)}| = e^{-πy}` (`Complex.norm_exp`: `Re(iπ(x+iy)) = -πy`), so
`∫⁻ ‖f(x+iy)e^{iπ(x+iy)}‖ₑ² dx = ofReal(e^{-2πy}) ∫⁻ ‖f(x+iy)‖ₑ² dx
= ofReal(e^{-2πy}) · 2π ∫_{Ioc} e^{-2yt}‖g‖ₑ² = 2π ∫_{Ioc} e^{-2y(t+π)} ‖g‖ₑ²` by `pwNormSq_translate_I`.
On `Ioc (-π) π`: `t + π ≥ 0` hence `e^{-2y(t+π)} ≤ 1` for `y > 0` (`Real.exp_le_one_iff`, `mul_nonneg`).
So the integral is `≤ 2π ‖g‖² = pwNormSq f`. **Constant `1`**, uniformly in `y > 0`. (Equivalently:
`f(z) e^{iπz} = ∫ g(t) e^{iz(t+π)} dt` with `t + π ∈ [0, 2π]`, the Fourier transform of a function supported in `[0,2π]`.)
For `IsH2Upper`: `DifferentiableOn` from entireness of `f` and of `exp`; the bound `C := (pwNormSq f).toNNReal`
(`pwNormSq_ne_top`; `ENNReal.coe_toNNReal`).

### 2.4 Derivative bound on `ℝ`

```lean
/-- **Derivative bound on `ℝ`**: `|f'(x)|² ≤ π² e² ‖f‖²` (Cauchy estimate on the circle of radius
`1/π`; the constant is absolute). -/
theorem pw_deriv_bound (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (x : ℝ) :
    ‖deriv f x‖ ^ 2 ≤ (Real.pi * Real.exp 1) ^ 2 * (pwNormSq f).toReal
```

*Proof.* Cauchy estimate `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (hR : 0 < R) (hd : DiffContOnCl ℂ f (ball c R))
(hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) : ‖deriv f c‖ ≤ C / R` with `c = x`, `R = 1/π`,
`DiffContOnCl` from `Differentiable.diffContOnCl`. For `w ∈ sphere x (1/π)`: `|Im w| ≤ |w - x| = 1/π`, so by
`pw_norm_sq_le`: `‖f w‖² ≤ e^{2π/π} ‖f‖² = e² ‖f‖²`, i.e. `‖f w‖ ≤ e ‖f‖` (`Real.sqrt`, or
`abs_le_of_sq_le_sq`/`pow_le_pow_left`). So `‖f'(x)‖ ≤ e ‖f‖/(1/π) = π e ‖f‖`; square. **Constant `C = π² e²`, absolute.**
(Any `R` works, optimal `R` minimises `e^{πR}/R`: `R = 1/π`.)

### 2.5 The fixed function with `g(0) = 1`; evaluation lower bound

```lean
/-- `((sin (π z / 2)) / (π z / 2))²`. -/
def pwBump (z : ℂ) : ℂ :=
  OCS.csinc (((Real.pi / 2 : ℝ) : ℂ) * z) ^ 2
```
```lean
theorem pwBump_zero : pwBump 0 = 1
```
```lean
theorem memPW_pwBump : MemPW pwBump
```

*Proof of `memPW_pwBump`.* `pwBump z = csinc(w)²` with `w = (π/2) z`; `csinc` entire
(`OCS.differentiable_csinc`) so `pwBump` is entire. Type `≤ π`: `‖csinc w‖ ≤ e^{|Im w|}`
(`OCS.norm_csinc_le_exp_abs_im`), `|Im((π/2) z)| = (π/2)|Im z| ≤ (π/2)‖z‖`; thus
`‖pwBump z‖ ≤ e^{π|Im z|} ≤ 1 · e^{(π+ε)‖z‖}` (`Complex.abs_im_le_norm`; `C = 1` works for every `ε`).
`L²(ℝ)`: for real `x ≠ 0`, `‖csinc((π/2)x)‖ ≤ e^0/‖(π/2)x‖ = 2/(π|x|)` (`OCS.norm_csinc_le_div`), and `≤ 1`
(`OCS.norm_csinc_ofReal_le_one`), so
`‖pwBump x‖² ≤ min(1, (2/(π|x|))⁴) ≤ 2/(1+x²)`:
for `|x| ≤ 1`: `1 ≤ 2/(1+x²)`; for `|x| ≥ 1`: `(2/π)⁴ x⁻⁴ ≤ x⁻² ≤ 2/(1+x²)` (as `1+x² ≤ 2x²`, and `(2/π)⁴ < 1`).
`x ↦ 2/(1+x²)` is integrable (`integrable_inv_one_add_sq`); `pwBump` is continuous, hence
`AEStronglyMeasurable`; `memLp_two_iff_integrable_sq_norm` finishes. (Mathematically:
`pwBump` is the Fourier transform of the triangle function supported in `[-π,π]`;
`(sin(πz/2)/(πz/2))²` has type `π/2 + π/2 = π`, and decays like `1/x²`.)

```lean
theorem pwNormSq_pwBump_pos : 0 < pwNormSq pwBump
```

*Proof.* `pwBump` is continuous with `pwBump 0 = 1`, so `‖pwBump x‖ₑ² > 1/4` for `|x| < η` (some `η`),
and `lintegral ≥ ∫⁻_{ball 0 η} (1/4) > 0` (`setLIntegral_mono`, `Real.volume_ball`; or `lintegral_pos_iff_support`).
*Implemented:* by contradiction through `MemPW.eq_zero_of_pwNormSq_eq_zero` (`pwBump 0 = 1 ≠ 0`).

```lean
theorem exists_memPW_eval_ne_zero : ∃ g : ℂ → ℂ, MemPW g ∧ g 0 = 1
```
```lean
/-- A uniform lower bound for point evaluations: for every real `x` there is `f ∈ PW`, namely a
translate of `pwBump`, with `0 < ‖f‖² < ∞` and `c ‖f‖² ≤ |f(x)|²`; the constant is
`c = ‖pwBump‖⁻²` (absolute), `‖pwBump‖² = pwNormSq pwBump`. -/
theorem pw_eval_lower : ∃ c : ℝ≥0, 0 < c ∧ ∀ x : ℝ, ∃ f : ℂ → ℂ, MemPW f ∧
    (c : ℝ≥0∞) * pwNormSq f ≤ ‖f (x : ℂ)‖ₑ ^ 2 ∧ pwNormSq f ≠ 0 ∧ pwNormSq f ≠ ⊤
```

*Proof.* `N := pwNormSq pwBump ∈ (0,∞)` (`pwNormSq_pwBump_pos`, `pwNormSq_ne_top`).
`c := N⁻¹.toNNReal`‑like, i.e. `c = (N.toNNReal)⁻¹ > 0`. For `x ∈ ℝ` let `f z := pwBump (z - x)`:
`MemPW` by `MemPW.comp_sub_ofReal`; `pwNormSq f = N` by `pwNormSq_comp_sub_ofReal`; `f x = pwBump 0 = 1` so
`‖f x‖ₑ² = 1`, and `c N = N.toNNReal⁻¹ * N = 1` (`ENNReal.coe_toNNReal`). **`c = ‖pwBump‖_{PW}^{-2}` is an absolute constant;**
`N = ∫ |csinc(πx/2)|⁴ dx = (2/π)·∫ sinc⁴ = (2/π)(2π/3) = 4/3` (the value is not needed).

## 3. `PW/PlancherelPolya.lean`

### 3.1 Sub-mean-value property

```lean
/-- **Sub-mean-value property** of `|f|²` for entire `f`:
`|f(c)|² ≤ (π r²)⁻¹ ∫_{D(c,r)} |f|² dA`. -/
theorem enorm_sq_le_lintegral_ball {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) {r : ℝ}
    (hr : 0 < r) :
    ‖f c‖ₑ ^ 2 ≤ ENNReal.ofReal (1 / (Real.pi * r ^ 2)) * ∫⁻ z in ball c r, ‖f z‖ₑ ^ 2
```

*Proof.* Fix `0 < ρ < r`. Mean value property (Mathlib: `DiffContOnCl.circleAverage : circleAverage f c R = f c`, hypothesis
`DiffContOnCl ℂ f (ball c |R|)`, from `Differentiable.diffContOnCl`):
`f(c) = (2π)⁻¹ ∫_{-π}^{π} f(c + ρ e^{iθ}) dθ` (`Real.circleAverage_eq_intervalAverage` gives the integral over `[0, 2π]`; periodicity: `Function.Periodic.intervalIntegral_add_eq` moves it to `[-π, π]`).
By Cauchy–Schwarz (Jensen) `‖f(c)‖² ≤ (2π)⁻¹ ∫_{-π}^{π} ‖f(c+ρe^{iθ})‖² dθ` (`ENNReal.lintegral_mul_le_Lp_mul_Lq`
with `p = q = 2`, or `ConvexOn.map_integral_le` for `x ↦ x²`, `convexOn_pow 2`).
Multiply by `ρ` and integrate `ρ ∈ (0, r)`: `(r²/2) ‖f(c)‖² ≤ (2π)⁻¹ ∫_0^r ∫_{-π}^{π} ‖f(c+ρe^{iθ})‖² dθ ρ dρ
= (2π)⁻¹ ∫_{D(c,r)} ‖f‖² dA` by `Complex.lintegral_comp_polarCoord_symm` (checked:
`∫⁻ p in polarCoord.target, ofReal p.1 • F (polarCoord.symm p) = ∫⁻ p, F p`; `polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π`
(`Complex.polarCoord_target`)) applied to `F z = indicator (ball 0 r) (‖f (c + z)‖ₑ²)` after
translation invariance (`lintegral_add_left_eq_self`). Thus `‖f(c)‖² ≤ (π r²)⁻¹ ∫_{D(c,r)} ‖f‖²`. **Constant `1/(π r²)`**
(equality for `f ≡ 1`). Work in `ℝ≥0∞` throughout (`ENNReal.ofReal (1 / (π r²))`).

### 3.2 The strip integral

```lean
/-- `∫∫_{|y| < r} |f(x+iy)|² dx dy ≤ (e^{2πr} - 1)/π · ‖f‖²`. -/
theorem lintegral_strip_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) {r : ℝ} (hr : 0 < r) :
    ∫⁻ z in {z : ℂ | |z.im| < r}, ‖f z‖ₑ ^ 2 ≤
      ENNReal.ofReal ((Real.exp (2 * Real.pi * r) - 1) / Real.pi) * pwNormSq f
```

*Proof.* Identify `ℂ ≃ ℝ × ℝ` (`Complex.volume_preserving_equiv_real_prod`, `measurableEquivRealProd`),
Tonelli (`lintegral_prod`, `lintegral_prod_symm`): `∫⁻_{|y|<r} ‖f‖² = ∫_{-r}^{r} (∫⁻_x ‖f(x+iy)‖ₑ² dx) dy
≤ ∫_{-r}^{r} ofReal(e^{2π|y|}) dy · ‖f‖²` by `pw_line_integral_le`
(`lintegral_mono`), and `∫_{-r}^{r} e^{2π|y|} dy = 2 (e^{2πr} - 1)/(2π) = (e^{2πr} - 1)/π`
(`integral_exp_mul_complex`‑free: `integral_exp_mul`, even symmetry `integral_comp_neg`, or split at `0`).

### 3.3 Plancherel–Pólya

```lean
/-- Subadditivity of the sampling sum (used for `Λ_α = Λ' ∪ Λ''`, p. 796). -/
theorem sampleSum_union_le (Λ₁ Λ₂ : Set ℝ) (f : ℂ → ℂ) :
    sampleSum (Λ₁ ∪ Λ₂) f ≤ sampleSum Λ₁ f + sampleSum Λ₂ f
```
```lean
/-- The Plancherel–Pólya constant `C(δ) = 4 (e^{πδ} - 1) / (π² δ²)`; it depends only on `δ`. -/
def ppConst (δ : ℝ) : ℝ := 4 * (Real.exp (Real.pi * δ) - 1) / (Real.pi ^ 2 * δ ^ 2)
```
```lean
/-- **Plancherel–Pólya**, explicit constant. -/
theorem plancherelPolya_explicit (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) {Λ : Set ℝ}
    (hΛ : IsSepBy δ Λ) {f : ℂ → ℂ} (hf : MemPW f) :
    sampleSum Λ f ≤ ENNReal.ofReal (ppConst δ) * pwNormSq f
```

*Proof.* Let `r = δ/2`. Since `sampleSum Λ f = ∑' x : Λ, ‖f x‖ₑ²` and `ENNReal.tsum_eq_iSup_sum`
(checked: `ENNReal.tsum_eq_iSup_sum : ∑' a, f a = ⨆ s : Finset α, ∑ a ∈ s, f a`), it suffices to
bound `∑_{x ∈ S} ‖f x‖ₑ²` for every finite `S ⊂ Λ` (no countability of `Λ` needed).
(i) For `x ∈ S`: by 3.1, `‖f x‖ₑ² ≤ ofReal(1/(π r²)) ∫⁻_{ball (x:ℂ) r} ‖f‖ₑ²`.
(ii) The balls `ball (x:ℂ) r`, `x ∈ S`, are pairwise disjoint: for `x ≠ x'` in `Λ`,
`dist (x:ℂ) (x':ℂ) = |x - x'| ≥ δ = r + r` (`Complex.dist_eq`, `Complex.abs_ofReal`/`Complex.dist_ofReal`‑type; `Metric.ball_disjoint_ball`).
(iii) `ball (x:ℂ) r ⊂ {z | |Im z| < r}` (`|Im z| = |Im (z - x)| ≤ |z - x| < r`, `Complex.abs_im_le_norm`).
Hence `∑_{x∈S} ∫⁻_{ball x r} = ∫⁻_{⋃ ball x r}` (`lintegral_biUnion_finset`; measurable balls; pairwise
disjoint) `≤ ∫⁻_{|Im z|<r}‖f‖ₑ²`. With 3.2:
`sampleSum Λ f ≤ (πr²)⁻¹ · (e^{2πr} - 1)/π · ‖f‖² = 4 (e^{πδ} - 1)/(π² δ²) · ‖f‖²`.
**`C(δ) = 4(e^{πδ} - 1)/(π²δ²)`: depends only on `δ`** (not on `Λ`, `f`); `C(δ) ~ 4/(πδ)` as `δ → 0` (sharp order:
`δ`-separated sets have density `1/δ`), `C(δ) ~ e^{πδ}` for large `δ`. `sampleSum_union_le`:
`ENNReal.tsum_union_le` after splitting the subtype (`tsum_union_le` exists for `ℝ≥0∞`-valued
functions on a set: `ENNReal.tsum_union_le`; alternatively through `Set.indicator`, `tsum_add`): the sum over `Λ₁ ∪ Λ₂` is
`≤` the sum of the two (each point is counted at least once on the right).
This is what is used for `Λ_α = Λ' ∪ Λ''` (p. 796): `sampleSum Λ_α f ≤ 2 C(δ) ‖f‖²`.

```lean
/-- **Plancherel–Pólya** (interface form): the constant depends only on `δ`. -/
theorem plancherelPolya (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ Λ : Set ℝ, IsSepBy δ Λ → ∀ f : ℂ → ℂ, MemPW f → sampleSum Λ f ≤ C * pwNormSq f
```

*Proof.* `⟨(ofReal (ppConst δ)).toNNReal, …⟩` from `plancherelPolya_explicit` (`ENNReal.coe_toNNReal`, `ofReal_ne_top`).

### 3.4 Uniform tails

```lean
/-- The strip-tail integral `∫∫_{|y|<r, |x| ≥ R} |f|²` tends to `0` as `R → ∞`. -/
theorem tendsto_strip_tail (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R : ℝ ↦ ∫⁻ z in {z : ℂ | |z.im| < r ∧ R ≤ |z.re|}, ‖f z‖ₑ ^ 2)
      atTop (nhds 0)
```

*Proof.* Dominated convergence on `ℂ` with the measure `volume.restrict {|Im z| < r}`
(`MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence`, `l = atTop` on `ℝ`; countably generated):
`F_R(z) = indicator {R ≤ |Re z|} ‖f z‖ₑ²`, measurable (`f` continuous); dominated by `‖f z‖ₑ²`
whose integral over the strip is `< ∞` by `lintegral_strip_le` and `pwNormSq_ne_top`; and `F_R(z) = 0`
as soon as `R > |Re z|`, i.e. `F_R(z) → 0` pointwise (`tendsto_atTop_of_eventually_const`).
(Without `hPW` the finiteness would fail; this is where the line bounds enter. In the paper's terms this
is "dominated convergence in `y` using the line bounds": the inner integrals `∫_{|x|≥R}|f(x+iy)|²dx → 0` for each `y`
and are dominated by `e^{2π|y|}‖f‖²`.)

```lean
/-- **Uniform tail version**: for fixed `δ` and `f ∈ PW`, `∑_{λ ∈ Λ, |λ| ≥ R} |f(λ)|² → 0` as
`R → ∞`, uniformly over all `δ`-separated `Λ`. Explicitly,
`sampleSum (Λ ∩ {|x| ≥ R}) f ≤ (π (δ/2)²)⁻¹ ∫∫_{|y|<δ/2, |x| ≥ R - δ/2} |f|²`. -/
theorem plancherelPolya_tail (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) {f : ℂ → ℂ}
    (hf : MemPW f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ R : ℝ, ∀ Λ : Set ℝ, IsSepBy δ Λ → sampleSum (Λ ∩ {x : ℝ | R ≤ |x|}) f ≤ ε
```

*Proof.* Let `r = δ/2`, `ε ≠ 0`. By `tendsto_strip_tail` choose `R'` with
`ofReal(1/(πr²)) · ∫⁻_{|Im|<r, R' ≤ |Re|} ‖f‖ₑ² ≤ ε` (the integral tends to `0`; `ENNReal.Tendsto.const_mul`
or `ENNReal.tendsto_const_mul`‑type lemma needs the constant `≠ ⊤`; then `Tendsto.eventually_le_const`/`eventually_lt_of_tendsto_lt` with `0 < ε`).
Put `R := R' + r`. For `Λ` `δ`-separated and finite `S ⊂ Λ ∩ {|x| ≥ R}`: repeat §3.3 (i)–(iii) with the extra
inclusion `ball (x:ℂ) r ⊂ {|Im z| < r, R' ≤ |Re z|}` — if `|z - x| < r` then `|Re z| ≥ |x| - |Re z - x| > R - r = R'`.
Hence `sampleSum (Λ ∩ {|x| ≥ R}) f ≤ ofReal(1/(πr²)) ∫⁻_{strip, |Re| ≥ R'} ‖f‖² ≤ ε`, *uniformly in `Λ`*:
`R` depends on `δ`, `f`, `ε` only (through the function `R' ↦ ∫∫_{strip, |x| ≥ R'} |f|²`), not on `Λ`.
Bound used for the `α → π/2` limit (README §3.5): `∑_{λ ∈ Λ, |λ| ≥ R} |f(λ)|² ≤ (4/(π δ²)) ∫_{|y|<δ/2} ∫_{|x| ≥ R-δ/2} |f(x+iy)|² dx dy`.

### 3.5 Added during assembly/implementation

```lean
/-- The tail bound of `plancherelPolya_tail`, uniformly over unions `A ∪ B` of two `δ`-separated
sets (I-01; consumed by `Theorem1/Sufficiency/Limit.lean`). -/
theorem plancherelPolya_tail_union (hPW : PaleyWienerThm) {δ : ℝ} (hδ : 0 < δ) {f : ℂ → ℂ}
    (hf : MemPW f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ R : ℝ, ∀ A B : Set ℝ, IsSepBy δ A → IsSepBy δ B →
      sampleSum ((A ∪ B) ∩ {x : ℝ | R ≤ |x|}) f ≤ ε
theorem sampleSum_eq_tsum_indicator (Λ : Set ℝ) (f : ℂ → ℂ) :
    sampleSum Λ f = ∑' x : ℝ, Λ.indicator (fun x : ℝ ↦ ‖f (x : ℂ)‖ₑ ^ 2) x
theorem sampleSum_mono {Λ₁ Λ₂ : Set ℝ} (h : Λ₁ ⊆ Λ₂) (f : ℂ → ℂ) :
    sampleSum Λ₁ f ≤ sampleSum Λ₂ f
-- PW/Basic.lean
theorem MemPW.eq_zero_of_pwNormSq_eq_zero {f : ℂ → ℂ} (hf : MemPW f) (h : pwNormSq f = 0) : f = 0
theorem IsSeparated.finite_inter_Icc {Λ : Set ℝ} (h : IsSeparated Λ) (R : ℝ) : (Λ ∩ Icc (-R) R).Finite
theorem IsSepBy.mono {δ δ' : ℝ} {Λ Λ' : Set ℝ} (h : IsSepBy δ Λ) (hδ : δ' ≤ δ) (hΛ : Λ' ⊆ Λ) :
    IsSepBy δ' Λ'
```
`plancherelPolya_tail_union`: apply `plancherelPolya_tail` with `ε/2` to `A` and to `B` and use
`sampleSum_union_le`. `MemPW.eq_zero_of_pwNormSq_eq_zero` needs no `hPW`: `f` is continuous with
`∫ ‖f‖² = 0`, so `f = 0` on `ℝ`, hence everywhere (identity theorem).

## 4. `PW/Complete.lean`

```lean
/-- **Completeness.** An `L²(ℝ)`-Cauchy sequence in `PW` converges in `L²` and locally uniformly
to some `g ∈ PW`. -/
theorem pw_complete (hPW : PaleyWienerThm) {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemPW (f n))
    (hc : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      pwNormSq (fun z ↦ f m z - f n z) < ε) :
    ∃ g : ℂ → ℂ, MemPW g ∧ TendstoLocallyUniformly f g atTop ∧
      Tendsto (fun n ↦ pwNormSq (fun z ↦ f n z - g z)) atTop (nhds 0)
```

*Proof.* Let `ε > 0` finite, `N = N(ε)`. For `m, n`, `f_m - f_n ∈ PW` (`MemPW.sub`) and by `pw_norm_sq_le`
`‖f_m z - f_n z‖² ≤ e^{2π|Im z|} (pwNormSq (f_m - f_n)).toReal`. Hence on every strip `|Im z| ≤ ρ`, and so on every compact set,
`(f_n)` is uniformly Cauchy (`UniformCauchySeqOn`); `ℂ` complete, so `f_n → g` locally uniformly
(`UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto` with the pointwise limit from `cauchySeq_tendsto_of_complete`;
then `tendstoLocallyUniformlyOn_iff_forall_isCompact` with `tendstoLocallyUniformlyOn_univ`); `g` entire (`TendstoLocallyUniformlyOn.differentiableOn`, `isOpen_univ`).
*`g ∈ PW` and `L²` convergence (Fatou twice, no triangle inequality needed):* fix `n ≥ N(ε)`. The family `F_m := f_m - f_n` (`m ≥ N`)
lies in `PW`, has `pwNormSq F_m < ε`, converges pointwise to `g - f_n` as `m → ∞`, and satisfies the uniform bound
`‖F_m z‖ ≤ K e^{π|Im z|}` with `K := √ε` (from `pw_norm_sq_le`: `‖F_m z‖² ≤ e^{2π|y|} ε`). So `memPW_of_tendsto`
(`ι = ℕ`, `l = atTop`, `M = ε`) gives `g - f_n ∈ PW` and `pwNormSq (g - f_n) ≤ liminf_m pwNormSq (f_m - f_n) ≤ ε`. Then
`g = f_n + (g - f_n) ∈ PW` (`MemPW.add`), and `pwNormSq (f_n - g) = pwNormSq (g - f_n)` (`norm_sub_rev`) `≤ ε` for all `n ≥ N(ε)`
(*Implemented:* the family is re-indexed as `k ↦ f(k+N) − f n`, R2-04):
convergence to `0`. (Locally uniform convergence is needed for `g` entire; the identity `f_n - g` vs `g - f_n`: use `‖a - b‖ₑ = ‖b - a‖ₑ`.)

```lean
/-- **Normal families.** A norm-bounded sequence in `PW` has a subsequence converging locally
uniformly to some `g ∈ PW`, and `‖g‖² ≤ liminf ‖f_n‖²` (even `≤ lim ‖f_{φ n}‖²` along the
subsequence, which may be chosen to realise the `liminf`). -/
theorem pw_normal_family (hPW : PaleyWienerThm) {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemPW (f n))
    {M : ℝ} (hM : ∀ n, pwNormSq (f n) ≤ ENNReal.ofReal M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, MemPW g ∧
      TendstoLocallyUniformly (fun n ↦ f (φ n)) g atTop ∧
      pwNormSq g ≤ liminf (fun n ↦ pwNormSq (f n)) atTop
```

*Proof.* Let `M' = √M`. By `pw_norm_sq_le`, `‖f_n z‖ ≤ M' e^{π|Im z|}` for all `n, z` (`ENNReal.toReal_mono`, `ENNReal.toReal_ofReal`),
a continuous majorant. (a) *Montel.* `OCS.exists_tendstoLocallyUniformlyOn_of_ultrafilter` (checked in `Bernstein/NormalFamily.lean`: for an ultrafilter `𝒰` on `ℕ`, `U = univ`, `F := f`,
`M z := M' e^{π|Im z|}`) gives an entire `H` with `f_n → H` locally uniformly along `𝒰`. Take `𝒰 ≥ atTop`
(`Ultrafilter.exists_le (atTop : Filter ℕ)`, `atTop` is `NeBot`). (b) *Subsequence* (this must come before any use of `memPW_of_tendsto`, which needs a countably generated filter; the ultrafilter of (a) is not). View `f_n` as elements `u n : C(ℂ, ℂ)` (continuity).
By `ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn`, `u → H` along `𝒰`, hence `H` is a cluster point of `u`
along `atTop` (`MapClusterPt H atTop u`, as `𝒰 ≤ atTop` and `map u 𝒰 ≤ 𝓝 H`). `C(ℂ,ℂ)` is first countable
(checked: `#synth FirstCountableTopology C(ℂ, ℂ)` succeeds, via `PseudoMetrizableSpace`, from `IsCountablyGenerated (𝓤 C(α,β))`),
so `MapClusterPt.tendsto_subseq` yields `φ` strictly monotone with `u ∘ φ → H` in `C(ℂ,ℂ)`, i.e. `f_{φ n} → H` locally uniformly
(`ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn`, `tendstoLocallyUniformlyOn_iff_forall_isCompact`, `tendstoLocallyUniformlyOn_univ`).
(c) *Norm bound with the full `liminf`.* Let `ℓ := liminf_n pwNormSq (f_n) ≤ ofReal M < ∞`. Before (a),
extract by `Filter.extraction_forall_of_frequently` a subsequence `ψ₀` with `pwNormSq (f_{ψ₀ k}) ≤ ℓ + 1/(k+1)` for all `k`
(the set `{n | pwNormSq (f_n) < ℓ + 1/(k+1)}` is frequently true: `Filter.frequently_lt_of_liminf_lt`; it is nonempty-frequent because `ℓ < ℓ + 1/(k+1)`),
and run (a), (b) for `f ∘ ψ₀`. Then `memPW_of_tendsto` (hypotheses: `hF` given, `hK` with `K = M'` from the bound above, `hd` from Montel, `hlim` pointwise from local uniform convergence,
`M := ofReal M`) shows `H ∈ PW` and `pwNormSq H ≤ liminf_k pwNormSq(f_{ψ₀ φ k}) ≤ limsup_k ≤ ℓ`
(since `pwNormSq (f_{ψ₀ (φ k)}) ≤ ℓ + 1/(φ k + 1)` and `φ k ≥ k`). Take `φ_final = ψ₀ ∘ φ`. (If only the bound `≤ ofReal M` is needed, skip (c).)

## 5. Dependence of constants (summary)

| statement | constant | depends on |
|---|---|---|
| `pw_norm_sq_le` | `1` · `e^{2π|Im z|}` (best: `sinh(2π|y|)/(2π|y|)`) | nothing |
| `pw_line_integral_le` | `e^{2π|y|}` | nothing |
| `MemPW.lintegral_mul_exp_le` | `1` | nothing |
| `pw_deriv_bound` | `π² e²` | nothing |
| `pw_eval_lower` | `c = ‖pwBump‖⁻²` | nothing (absolute) |
| `plancherelPolya` | `C(δ) = 4(e^{πδ}-1)/(π²δ²)` | `δ` only |
| `plancherelPolya_tail` | `R = R(δ, f, ε)` | `δ`, `f`, `ε`; not `Λ` |
| `pw_normal_family` | none | `M` enters only through the bound |
| `isFourierFrame_iff_isSampling` (M10) | `A_sampling = A_frame/(2π)`, `B_sampling = B_frame/(2π)` | absolute |

## 6. Issues in the source

1. **p. 790, "By the Paley–Wiener theorem, `Λ` is sampling for PW iff `{e^{iλ_k x}}` is a Fourier frame"
   (tex l. 135–137).** Correct, but (a) the constants change by the factor `2π` (the norm identity in
   the Paley–Wiener theorem is `‖f‖²_{L²(ℝ)} = 2π‖g‖²` for the transform `∫ g e^{izt}dt`, no normalisation is
   given in the paper), and (b) the paper's `Λ = {λ_k}_{k∈ℤ}` is a *sequence*, possibly with repeated points, whereas the
   formalisation uses sets. Statement (b) is harmless for Theorem 1 (separated ⇒ distinct) and the formal equivalence
   is exactly true for sets. The "only if" direction in the other sign convention (`e^{-iλx}` vs `e^{izt}`) is handled by `t ↦ -t` (M10). Sure.
2. **p. 796 (tex l. 483–488), "Plancherel–Pólya implies `∑_k |f(λ_{α,k})|² ≤ C‖f‖²_{PW}` with `C` independent of `α`".**
   Correct. Details left out in the paper: `Λ_α` is the union of two `δ`-separated sequences (the paper says this),
   so `C = 2 C(δ)` with `C(δ) = 4(e^{πδ} - 1)/(π² δ²)`; the constant in [Yo80] is for the version with unit separation and
   exponential type `π`. No error. Sure.
3. **p. 797, the limit `α → π/2`:** "dominated convergence by (4)" does not give domination (README §3.5). The fix is
   `plancherelPolya_tail` above. Sure.
4. **(Source of the formalization, not of the paper)** The first `PaleyWienerThm` made `⇐` vacuous.
   *Resolved before the freeze* (option A, part 2 without norm identity; §0).
5. The paper uses the bound `|f(z)| ≤ C e^{π|y|}‖f‖` and the Bernstein/Cauchy estimates freely (pp. 796–797, 801). The constants
   are made explicit here: `|f(z)|² ≤ e^{2π|y|}‖f‖²` (constant 1, sharp only at `y = 0`), `|f'(x)|² ≤ π²e²‖f‖²`.

## 7. Requested changes to M00

*Resolved before the freeze* (option A, with part 2 without the norm identity, which follows from
part 1; `Defs.lean`). The request is kept for the record.

1. **Strengthen `PaleyWienerThm`** (high priority). Replace by
```lean
def PaleyWienerThm : Prop :=
  (∀ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) →
      MemPW (fun z ↦ ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)) ∧
      pwNormSq (fun z ↦ ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)) =
        ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2) ∧
  (∀ f : ℂ → ℂ, MemPW f → ∃ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) ∧
      (∀ z : ℂ, f z = ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)) ∧
      pwNormSq f = ENNReal.ofReal (2 * Real.pi) * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2)
```
   This is the actual Paley–Wiener–Plancherel theorem; the current `↔` form has a vacuous `⇐`. With the
   current form the blueprint still works (§1.7), at the price of one extra paragraph of formalisation;
   if M00 changes, `memPW_pwFT` and `exists_pwFT` become projections. In `M00_Defs.md` the statement
   "`PaleyWienerThm`... to be proved in phase 2 from `Lp.fourierTransformₗᵢ`" is right, except that Mathlib (this version) has no lemma saying that the `L¹` and `L²`
   Fourier transforms agree on `L¹ ∩ L²`, which phase 2 will need.
2. No other change to `Defs.lean` is needed for M01 (`IsExpTypeLE` with `‖z‖`, `MemPW`, `pwNormSq`, `sampleSum` are all
   used as is; `sampleSum` is a `tsum` over a subtype `↥Λ`, handled by `ENNReal.tsum_eq_iSup_sum`).
