# M03 — Theorem 1, necessity

**Lean:** `FourierFrames/Theorem1/Necessity.lean` (namespace `FF`; main statement `theorem1_necessity`,
identical to `comparator/statements.lean`).
**Paper:** pp. 795–796, from "Proof. Let us assume first that Λ is a sampling sequence" to
"for all z ∈ ℂ" (the necessity half of Theorem 1).
**Depends on:**
- M00 (`Defs.lean`): `IsSampling`, `IsSeparated`, `MemPW`, `pwNormSq`, `sampleSum`, `IsHB`,
  `IsStrictHB`, `MemHE`, `heNormSq`, `HEEqPW`, `poissonInt`, `fstar`, `TheoremC`, `TheoremF`,
  `PaleyWienerThm`.
- M01 (PW toolkit): `memPW_zero`, `MemPW.add`, `MemPW.sub`, `MemPW.const_mul`, `MemPW.fstar`,
  `pwNormSq_fstar`, `MemPW.mul_div_sub`, `pwNormSq_ne_top`, `pw_norm_sq_le`,
  `exists_memPW_eval_ne_zero`, `pw_complete`, `MemPW.eq_zero_of_pwNormSq_eq_zero` (added to
  `PW/Basic.lean` at assembly), `IsSeparated.finite_inter_Icc` (moved to `PW/Basic.lean`).
- M02 (HB): `fstar_fstar`, `Differentiable.fstar`, `fstar_ofReal`, `HEEqPW.isStrictHB`,
  `HEEqPW.ne_zero_ofReal`.
- Vendored `OrtegaCerdaSeip/Products/Canonical.lean`: `OCS.canonicalProd`, `OCS.IsGenusOneData`,
  `OCS.differentiable_canonicalProd`, `OCS.canonicalProd_eq_zero_iff`, `OCS.canonicalProd_conj`.

**Used by:** M04 (`theorem1`, `corollary1` use `theorem1_necessity`; the remark
`completeInterpolating_zero_set` uses `hC, hD` but not `hF`, so it will rather reuse the Theorem C
step: **exported lemmas `exists_samplingHilbertSpace` (§3.6) and `exists_E` (§4)**, which give `E ∈
\overline{HB}` with `H(E) = PW` for any *sampling* `Λ`), M05 (via Corollary 1).

**Status (final).** All declarations proved, no `sorry`; helper file
`Theorem1/Necessity/Sep.lean` (bucketing for §2.2), plus `PWFun.mk`, `PWFun.val_mk`,
`IsSeparated.eventually_le_abs` in `Necessity.lean`. Lean blocks show the statements (some lemma
hypotheses were removed as unused in the lint pass, NOTEBOOK I-03). §13 is obsolete: the interface
block was replaced by imports (`IMPORTS.md`).

---

## 0. Overview, and what differs from the paper

Let `Λ` be separated and sampling, with sampling constants `0 < a ≤ ∑_{λ∈Λ}|f(λ)|²/‖f‖²_PW ≤ b`
(`IsSampling` gives `A, B : ℝ≥0`; I write `A, B`).

1. (§3–4) `PW` with `⟨f,g⟩ = ∑_λ conj f(λ) g(λ)` is a Hilbert space satisfying (H1)–(H3), so Theorem C
   gives `E ∈ \overline{HB}` with `H(E) = PW` isometrically for this norm. `HEEqPW E` follows from
   `A‖f‖² ≤ ∑|f(λ)|² ≤ B‖f‖²`. M02 then gives `E` strict without real zeros.
2. (§5) `μ = ∑_λ |E(λ)|² δ_λ` satisfies `∫|f/E|² dμ = ∑|f(λ)|² = ‖f‖²_E`; Theorem F gives `A` (a
   holomorphic function on `ℂ₊`, `|A| ≤ 1`) and `p ≥ 0` with
   `(y/π)∫dμ(t)/((t-x)²+y²) + p y = Re H(z)`, `H = (E + E^*A)/(E - E^*A)`.
3. (§6, §8) Herglotz: `H = M` on `ℂ₊`, where `M(z) = (-i/π) ∑ c_λ (1/(λ-z) - λ/(1+λ²)) - i p z + i a`,
   `c_λ = |E(λ)|²`.  The sign, the factor `1/π` and the convergence factor differ from the paper's (3)
   (see Issues 1–3).
4. (§7–8) `G` = genus-one product with zero set `Λ`, real (`G^* = G`). The *entire* functions
   `W = G·M`, `P = W - G = G(M-1)`, `Q = W + G = G(M+1)`: no meromorphic functions are used.
   `W^* = -W`, hence `P^* = -Q`.
5. (§9) `F` is built from `Φ = P/E^*` (= `QA/E` on `ℂ₊`), the removable-singularity gluing being done
   by an `if`-definition; then `E F = Q`, `E^*F^* = -P`, so `EF + E^*F^* = Q - P = 2G`
   **identically** (this replaces the paper's "real part on the real axis" argument), `F^* = -AF` on
   `ℂ₊`, and `F = 2G/(E - E^*A)` on `ℂ₊` has no zeros there. So `F ∈ \overline{HB}`, and the zero
   set of `EF + E^*F^* = 2G` is `Λ`.

Notation. `ℂ₊ = {z : 0 < Im z}`, `y = Im z`. `c_λ := ‖E λ‖²` (`λ ∈ Λ ⊂ ℝ`, cast to `ℂ` in `E λ`).
`hbQuot E A z := (E z + fstar E z * A z)/(E z - fstar E z * A z)` (the paper's `H`).
In Lean `E λ` for `λ : Λ` is written `E (((x : Λ) : ℝ) : ℂ)`.

**Lean-specific warning (found while compiling the assembly).** When applying lemmas that have an
implicit `c : ℝ → ℝ` (`differentiable_herglotzEnt`, `fstar_herglotzEnt`, ...) to hypotheses of the
form `Summable fun x : Λ ↦ |‖E ↑↑x‖^2| / ...`, give `c` explicitly
(`(c := fun x ↦ ‖E (x : ℂ)‖ ^ 2)`); higher-order unification with the coerced argument times out
(`whnf` heartbeat timeout).  Likewise do not `set`/`generalize` the large terms `G`, `W` in the main
proof; the scaffold uses `generalize genProd Λ = G at …` early and a `suffices key : ∀ W …`.

---

## 1. Generalities

### 1.1 `differentiableOn_tsum_of_cofinite_bound`
```lean
theorem differentiableOn_tsum_of_cofinite_bound {ι : Type*} {F : ι → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) {u : ι → ℝ} (hu : Summable u)
    (hb : ∀ᶠ i in cofinite, ∀ w ∈ U, ‖F i w‖ ≤ u i) :
    DifferentiableOn ℂ (fun w ↦ ∑' i, F i w) U := sorry
```

*Proof.* Let `s = {i | ¬ ∀ w ∈ U, ‖F i w‖ ≤ u i}`; it is finite by `hb`. For `w ∈ U`,
`∑' i, F i w = ∑_{i∈s} F i w + ∑' i : sᶜ, F i w` (`Summable.tsum_add_tsum_compl`, with
`Summable (F · w)` obtained from `Summable.of_norm_bounded_eventually`, and the finite part by
`Finset.tsum_subtype`/`tsum_eq_sum`). The finite sum is differentiable (`DifferentiableOn.fun_sum`). The tail
is differentiable by `differentiableOn_tsum_of_summable_norm` (Mathlib,
`Analysis/Complex/LocallyUniformLimit.lean`) with the summable majorant `u ∘ (↑) : sᶜ → ℝ`
(`hu.subtype`). `DifferentiableOn.congr` finishes. (Alternative: replace `F i` by `0` for `i ∈ s`.)

### 1.2 `Differentiable.eq_of_eqOn_upper`
```lean
theorem Differentiable.eq_of_eqOn_upper {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h : ∀ z : ℂ, 0 < z.im → f z = g z) : f = g := sorry
```

*Proof.* `hf.analyticOnNhd`, `hg.analyticOnNhd` (`Differentiable.analyticAt`, or
`DifferentiableOn.analyticOnNhd`) on `univ`; `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`
(`Analysis/Analytic/Uniqueness.lean`) with `U = univ`, `z₀ = I`, and `f =ᶠ[𝓝 I] g` because
`{z | 0 < z.im}` is open (`isOpen_lt continuous_const Complex.continuous_im`) and contains `I`.

### 1.3 `exists_const_of_re_eq_zero`
```lean
theorem exists_const_of_re_eq_zero {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D {z : ℂ | 0 < z.im})
    (hre : ∀ z : ℂ, 0 < z.im → (D z).re = 0) :
    ∃ a : ℝ, ∀ z : ℂ, 0 < z.im → D z = a * I := sorry
```

*Proof.* `U = {z | 0 < z.im}` is open and preconnected
(`(convex_halfSpace_im_gt 0).isPreconnected`). `hD.analyticOnNhd isOpen_upper`, then
`AnalyticOnNhd.is_constant_or_isOpen` (`Analysis/Complex/OpenMapping.lean`):
- *constant case*: `D z = w` on `U`; `w = D I`, `a := (D I).im`, `Re (D I) = 0` gives
  `D I = a * I` (`Complex.ext`).
- *open case*: `D '' U` is open (take `s = U`), nonempty, and contained in `{re = 0}`. Pick
  `D I ∈ D '' U` and a ball `ball (D I) r ⊆ D '' U`; the point `D I + (r/2 : ℝ)` lies in the ball but
  has real part `r/2 ≠ 0`: contradiction.

(Alternative: Cauchy–Riemann; the open mapping argument is shorter in Mathlib.)

---

## 2. Separated sets

`IsSeparated Λ` is `∃ δ > 0, ∀ a b ∈ Λ, a ≠ b → δ ≤ |a - b|`.

### 2.1 `IsSeparated.finite_inter_Icc`
```lean
theorem IsSeparated.finite_inter_Icc {Λ : Set ℝ} (h : IsSeparated Λ) (r : ℝ) :
    (Λ ∩ Icc (-r) r).Finite := sorry
```

(Moved to `PW/Basic.lean` at assembly, with the binder `R`.)

*Proof.* The map `x ↦ ⌊x/δ⌋ : ℤ` is injective on `Λ`: if `⌊x/δ⌋ = ⌊y/δ⌋` then `|x - y| < δ`
(`Int.abs_sub_lt_one_of_floor_eq_floor` applied to `x/δ, y/δ`), so `x = y`. It maps `Λ ∩ [-r, r]` into
`Finset.Icc ⌊-r/δ⌋ ⌊r/δ⌋` (monotonicity of `⌊·⌋`). Conclude with `Set.Finite.of_injOn` (or
`Set.Finite.of_finite_image`) and `Set.finite_Icc`.

### 2.2 `IsSeparated.summable_inv_one_add_sq`
```lean
theorem IsSeparated.summable_inv_one_add_sq {Λ : Set ℝ} (h : IsSeparated Λ) :
    Summable fun x : Λ ↦ 1 / (1 + (x : ℝ) ^ 2) := sorry
```

*Proof (bucketing).* Shrinking `δ` we may assume `0 < δ ≤ 1`. Put `N := ⌊1/δ⌋ + 1`.
(a) *At most `N` points per unit cell.* For `n ∈ ℤ` let `Λ_n = Λ ∩ [n, n+1)`. The map
`x ↦ ⌊(x - n)/δ⌋` is injective on `Λ_n` (as in 2.1) with values in `{0, …, ⌊1/δ⌋}`; so
`#Λ_n ≤ N`.
(b) *Weights.* For `x ∈ [n, n+1)`: `1/(1+x²) ≤ 5/(1+n²)` (*Implemented:* `≤ 3/(1+n²)`,
`one_add_sq_floor_le` in `Necessity/Sep.lean`; either constant works). If `n ≥ 0`, `x ≥ n` and the constant is 1.
If `n < 0`, `x ≤ n + 1 ≤ 0`, so `x² ≥ (|n|-1)²` and `1 + n² ≤ 5(1 + (|n|-1)²)` iff
`4m² - 10m + 9 ≥ 0` (`m = |n|`), true since the discriminant is negative.
(c) *Sum.* Use `summable_of_sum_le` (nonneg terms; all finite partial sums bounded). For a finite
`s ⊂ Λ`, `∑_{x∈s} 1/(1+x²) = ∑_{n ∈ s.image ⌊·⌋} ∑_{x∈s, ⌊x⌋=n} 1/(1+x²)`
(`Finset.sum_fiberwise_of_maps_to`) `≤ ∑_{n∈ℤ-finite} N · 5/(1+n²) ≤ 5 N ∑_{n∈ℤ} 1/(1+n²)`,
and `∑_{n∈ℤ} 1/(1+n²) < ∞` by comparison with `1/n²` off `n = 0`
(`Real.summable_one_div_int_pow`, `Summable.of_norm_bounded_eventually`).

(One could instead use the sampling upper bound with a translate of a fixed `g ∈ PW`, but no
lower bound `|g(x)|² ≳ 1/(1+x²)` is available from the M01 interface; bucketing is elementary.)

---

## 3. The sampling Hilbert space (Step 1)

### 3.1 The vector space `PWFun`
```lean
def PWSub : Submodule ℂ (ℂ → ℂ)        -- carrier {f | MemPW f}; add_mem' := MemPW.add,
                                       -- zero_mem' := memPW_zero, smul_mem' := MemPW.const_mul
def PWFun : Type := ↥PWSub             -- a `def`, so that TC does not inherit the (wrong) topology
instance : AddCommGroup PWFun := inferInstanceAs (AddCommGroup ↥PWSub)
instance : Module ℂ PWFun := inferInstanceAs (Module ℂ ↥PWSub)
def PWFun.val : PWFun →ₗ[ℂ] (ℂ → ℂ) := PWSub.subtype
theorem PWFun.memPW (h : PWFun) : MemPW (PWFun.val h)
theorem PWFun.val_injective : Function.Injective PWFun.val
```
(exact text in the scaffold). The reason for the `def PWFun`: a `Submodule` of `ℂ → ℂ` carries the
product topology/uniformity, which TC would pick up and which disagrees with the sampling norm.

### 3.2 The inner product
```lean
def sampInner (Λ : Set ℝ) (f g : ℂ → ℂ) : ℂ :=
  ∑' x : Λ, conj (f ((x : ℝ) : ℂ)) * g ((x : ℝ) : ℂ)
```

Convention: Mathlib's `inner` is conjugate-linear in the first slot, hence `conj (f λ) * g λ`.
In this section `hs : IsSampling Λ` with constants `A, B : ℝ≥0`, `0 < A`.

Signatures: the lemmas of this subsection live in the Lean section
```lean
section Sampling
variable {Λ : Set ℝ} (hs : IsSampling Λ) {f g : ℂ → ℂ}
include hs
```
so each has the explicit hypothesis `hs : IsSampling Λ` as first argument (the statements below show
the bodies only).  Exceptions (NOTEBOOK I-03): `sampInner_self`, `sampInner_conj_symm`,
`sampInner_smul_left` need neither `hs` nor `MemPW`; they are stated before the section with
explicit `Λ f g`.  `samp_H1` and `samp_H3` are preceded by `omit hs in` (no `hs` argument).

**`sampleSum_ne_top`.**
```lean
theorem sampleSum_ne_top (hf : MemPW f) : sampleSum Λ f ≠ ∞ := sorry
```
`sampleSum Λ f ≤ B * pwNormSq f < ∞` by `pwNormSq_ne_top`.

**`summable_sq_norm_samp`.**
```lean
theorem summable_sq_norm_samp (hf : MemPW f) :
    Summable fun x : Λ ↦ ‖f ((x : ℝ) : ℂ)‖ ^ 2 := sorry
```
`ENNReal.summable_toReal` (`Topology/Algebra/InfiniteSum/ENNReal.lean`) applied to
`x ↦ ‖f x‖ₑ ^ 2` with `tsum ≠ ∞` (previous lemma); `(‖a‖ₑ ^ 2).toReal = ‖a‖ ^ 2`
(`ENNReal.toReal_pow`, `toReal_enorm`).

**`sampleSum_eq_ofReal_tsum`.**
```lean
theorem sampleSum_eq_ofReal_tsum (hf : MemPW f) :
    sampleSum Λ f = ENNReal.ofReal (∑' x : Λ, ‖f ((x : ℝ) : ℂ)‖ ^ 2) := sorry
```
`ENNReal.ofReal_tsum_of_nonneg (hf_nonneg) (hf : Summable)` and
`ENNReal.ofReal (‖a‖^2) = ‖a‖ₑ^2` (`ENNReal.ofReal_pow`, `ofReal_norm`; formerly
`ofReal_norm_eq_enorm`, now deprecated).

**`summable_samp_inner`.**
```lean
theorem summable_samp_inner (hf : MemPW f) (hg : MemPW g) :
    Summable fun x : Λ ↦ conj (f ((x : ℝ) : ℂ)) * g ((x : ℝ) : ℂ) := sorry
```
`Summable.of_norm_bounded` with majorant `(‖f x‖² + ‖g x‖²)/2`: `‖conj a * b‖ = ‖a‖‖b‖` and
`2‖a‖‖b‖ ≤ ‖a‖² + ‖b‖²` (`two_mul_le_add_sq`).

**`sampInner_self`.**
```lean
theorem sampInner_self (Λ : Set ℝ) (f : ℂ → ℂ) :
    sampInner Λ f f = ((∑' x : Λ, ‖f ((x : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := sorry
```
`conj a * a = (‖a‖ ^ 2 : ℝ)` (`Complex.conj_mul'`), `Complex.ofReal_tsum`.

**`sampInner_conj_symm`.**
```lean
theorem sampInner_conj_symm (Λ : Set ℝ) (f g : ℂ → ℂ) :
    conj (sampInner Λ g f) = sampInner Λ f g := sorry
```
`tsum_star` / `Complex.conj_tsum`-like (`star = conj`): `conj (∑ conj g · f) = ∑ g · conj f`, and
the product commutes.

**`sampInner_add_left`, `sampInner_smul_left`.**
```lean
theorem sampInner_add_left {h : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) (hh : MemPW h) :
    sampInner Λ (f + g) h = sampInner Λ f h + sampInner Λ g h := sorry
```
```lean
theorem sampInner_smul_left (Λ : Set ℝ) (c : ℂ) (f g : ℂ → ℂ) :
    sampInner Λ (c • f) g = conj c * sampInner Λ f g := sorry
```
`(f+g) x = f x + g x`, `conj` additive, `add_mul`, `Summable.tsum_add` (summability from
`summable_samp_inner`); `(c • f) x = c * f x`, `conj (c * f x) = conj c * conj (f x)`,
`tsum_mul_left`.

**`sampInner_definite`.**
```lean
theorem sampInner_definite (hf : MemPW f) (h : sampInner Λ f f = 0) : f = 0 := sorry
```
`sampInner Λ f f = 0` gives, by `sampInner_self` and injectivity of `Complex.ofReal`,
`∑ ‖f λ‖² = 0`, so `sampleSum Λ f = ofReal 0 = 0` (`sampleSum_eq_ofReal_tsum`).
By `hs`, `A * pwNormSq f ≤ sampleSum Λ f = 0`, so `pwNormSq f = 0` (`A ≠ 0`: `mul_eq_zero`,
`ENNReal.coe_ne_zero`). Finish with `MemPW.eq_zero_of_pwNormSq_eq_zero`. (Proof of that M01
lemma: `∫⁻ ‖f x‖ₑ² = 0` ⟹ `f = 0` a.e. on `ℝ` (`lintegral_eq_zero_iff` with `f|ℝ` continuous,
hence measurable) ⟹ `f = 0` on `ℝ` (`Continuous.ae_eq_iff_eq`, `volume` is open-positive) ⟹
`f ≡ 0` by the identity theorem
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, the zeros `1/(n+1)` accumulating
at `0`.)

### 3.3 `sampCore`
```lean
abbrev sampCore : InnerProductSpace.Core ℂ PWFun where
  inner f g := sampInner Λ (PWFun.val f) (PWFun.val g)
  conj_inner_symm f g := sampInner_conj_symm Λ _ _
  re_inner_nonneg f := by
    have h := sampInner_self Λ (PWFun.val f)
    show 0 ≤ (sampInner Λ (PWFun.val f) (PWFun.val f)).re
    rw [h, Complex.ofReal_re]
    exact tsum_nonneg fun x ↦ by positivity
  add_left f g h := sampInner_add_left hs f.memPW g.memPW h.memPW
  smul_left f g c := sampInner_smul_left Λ c _ _
  definite f h := PWFun.val_injective (by simpa using sampInner_definite hs f.memPW h)
```

`conj_inner_symm`, `add_left`, `smul_left`, `definite` are the lemmas above applied to
`f.memPW`, ...; `re_inner_nonneg`: by `sampInner_self`, `re ⟪f,f⟫ = ∑ ‖f λ‖² ≥ 0`
(`tsum_nonneg`). (It is an `abbrev`: a `def` of class type must be reducible, NOTEBOOK I-03.)
This def has no `sorry` of its own; it only uses the lemmas.

Instances (verified to elaborate; this is the pattern to use in 3.6):
```lean
letI : NormedAddCommGroup PWFun := (sampCore hs).toNormedAddCommGroup
letI : InnerProductSpace ℂ PWFun := InnerProductSpace.ofCore (sampCore hs).toCore
```
The norm is then `‖h‖ = √(re ⟪h,h⟫)` (`InnerProductSpace.Core.toNormedAddCommGroup`), so
`‖h‖² = re ⟪h,h⟫ = ∑ ‖h λ‖²` (`Real.sq_sqrt`, `re_inner_nonneg`, `sampInner_self`), i.e.
`ENNReal.ofReal (‖h‖²) = sampleSum Λ (PWFun.val h)` (`sampleSum_eq_ofReal_tsum`).

### 3.4 Completeness
```lean
theorem samp_cauchy_converges (hPW : PaleyWienerThm) {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemPW (f n))
    (hc : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      sampleSum Λ (fun z ↦ f m z - f n z) < ε) :
    ∃ g : ℂ → ℂ, MemPW g ∧ Tendsto (fun n ↦ sampleSum Λ (fun z ↦ f n z - g z)) atTop (𝓝 0) :=
  sorry
```

*Proof.* Let `ε ≠ 0`. By `hs`, `A * pwNormSq (f m - f n) ≤ sampleSum Λ (f m - f n)`, so
`pwNormSq (f m - f n) ≤ A⁻¹ * sampleSum(...)` (`ENNReal` division by `A ≠ 0, ≠ ∞`;
`(f m - f n)` is in `PW` by `MemPW.sub`). Thus, given `ε`, apply `hc` to `A * ε` (nonzero) to get
`N` with `pwNormSq (f m - f n) < ε` for `m, n ≥ N`: the hypothesis of `pw_complete hPW hf`. It gives
`g ∈ PW` with `pwNormSq (f n - g) → 0`. The upper sampling bound gives
`sampleSum (f n - g) ≤ B * pwNormSq (f n - g)` (here `f n - g ∈ PW` by `MemPW.sub`), and
`B * pwNormSq(...) → 0` (`ENNReal.Tendsto.const_mul`, `B ≠ ∞`). Conclude with
`tendsto_of_tendsto_of_tendsto_of_le_of_le` / `squeeze_zero'`.

`CompleteSpace PWFun` (in 3.6): `Metric.complete_of_cauchySeq_tendsto`. A Cauchy sequence
`h_n` in the sampling norm has `ENNReal.ofReal (‖h_m - h_n‖²) = sampleSum Λ (h_m - h_n)` small, so the
hypothesis of `samp_cauchy_converges` holds; its `g` gives `h = ⟨g, _⟩ : PWFun` and
`‖h_n - h‖² = (sampleSum (h_n - g)).toReal → 0`, hence `h_n → h` (`tendsto_iff_dist_tendsto_zero`
and `dist = ‖·‖`, `Real.sqrt`).

### 3.5 (H1), (H2), (H3)
```lean
omit hs in
theorem samp_H1 (hf : MemPW f) {ζ : ℂ} (hζ : ζ.im ≠ 0) (hz : f ζ = 0) :
    MemPW (fun z ↦ dslope f ζ z * (z - conj ζ)) ∧
      sampleSum Λ (fun z ↦ dslope f ζ z * (z - conj ζ)) = sampleSum Λ f := sorry
```
*Proof.* `f ∈ PW`, `f ζ = 0`: `MemPW.mul_div_sub hf hz (conj ζ)` gives `MemPW`.  For real `x`:
`ζ ≠ x` (as `ζ.im ≠ 0`), so `dslope f ζ x = (f x - f ζ)/(x - ζ) = f x/(x - ζ)`
(`dslope_of_ne`, `slope_def_field`) and
`‖dslope f ζ x * (x - conj ζ)‖ = ‖f x‖ ‖x - conj ζ‖/‖x - ζ‖ = ‖f x‖`, since
`x - conj ζ = conj (x - ζ)` for real `x` (`Complex.norm_conj`). Hence the `tsum`s coincide termwise.

```lean
theorem samp_H2 (hPW : PaleyWienerThm) (ζ : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℂ → ℂ, MemPW f → ‖f ζ‖ ^ 2 ≤ C * (sampleSum Λ f).toReal := sorry
```
*Proof.* `C = e^{2π|Im ζ|}/A`: `pw_norm_sq_le hPW hf ζ` gives `‖f ζ‖² ≤ e^{2π|Im ζ|} (pwNormSq f).toReal`,
and `A * pwNormSq f ≤ sampleSum Λ f` with `sampleSum Λ f ≠ ∞` gives
`(pwNormSq f).toReal ≤ A⁻¹ (sampleSum Λ f).toReal` (`ENNReal.toReal_mono`, `ENNReal.toReal_mul`).
(`A ≠ 0`.)

```lean
omit hs in
theorem samp_H3 : sampleSum Λ (fstar f) = sampleSum Λ f := sorry
```
*Proof.* (No hypothesis on `f` is needed.) For real `x`, `fstar f x = conj (f x)` (`fstar_ofReal`), so
`‖fstar f x‖ₑ = ‖f x‖ₑ` termwise.

### 3.6 Packaging
```lean
theorem exists_samplingHilbertSpace (hPW : PaleyWienerThm) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ι : H →ₗ[ℂ] (ℂ → ℂ)), Function.Injective ι ∧ (∀ h : H, Differentiable ℂ (ι h)) ∧
      (∀ h : H, ∀ ζ : ℂ, ζ.im ≠ 0 → ι h ζ = 0 →
        ∃ g : H, ‖g‖ = ‖h‖ ∧ ∀ z : ℂ, z ≠ ζ → ι g z = ι h z * (z - conj ζ) / (z - ζ)) ∧
      (∀ ζ : ℂ, ζ.im ≠ 0 → Continuous fun h : H ↦ ι h ζ) ∧
      (∀ h : H, ∃ g : H, ‖g‖ = ‖h‖ ∧ ι g = fstar (ι h)) ∧ (∃ h : H, h ≠ 0) ∧
      (∀ f : ℂ → ℂ, f ∈ Set.range ι ↔ MemPW f) ∧
      ∀ h : H, ENNReal.ofReal (‖h‖ ^ 2) = sampleSum Λ (ι h) := sorry
```

*Proof.* Take `H := PWFun` with the instances of 3.3, `CompleteSpace` from 3.4,
`ι := PWFun.val`. Injective: `PWFun.val_injective`. Differentiable: `MemPW` includes
`Differentiable ℂ`. Range: `{f | MemPW f}`. Norm identity: end of 3.3. Nonzero: `g` from
`exists_memPW_eval_ne_zero` (`g 0 = 1`), as an element of `PWFun`; `g ≠ 0` as `g 0 ≠ 0`.
(H1): given `h` and `ζ` with `ι h ζ = 0`, put `g := ⟨fun z ↦ dslope (ι h) ζ z * (z - conj ζ), _⟩`
(`samp_H1`); `‖g‖ = ‖h‖` from the norm identity and `samp_H1` (`ENNReal.ofReal_injective`-type step:
`ofReal (‖g‖²) = ofReal (‖h‖²)`, both norms `≥ 0`); for `z ≠ ζ`,
`dslope f ζ z = f z/(z-ζ)` (`f ζ = 0`), so `ι g z = ι h z * (z - conj ζ)/(z - ζ)`
(`field_simp`/`ring`).
(H2): `ι` is linear and `‖ι h ζ‖ ≤ √C ‖h‖` from `samp_H2` and the norm identity, so `h ↦ ι h ζ` is
a bounded linear functional: `(LinearMap.mkContinuous …).continuous` or
`AddMonoidHomClass.continuous_of_bound`.
(H3): `g := ⟨fstar (ι h), MemPW.fstar _⟩`, `‖g‖ = ‖h‖` from `samp_H3`.

---

## 4. Theorem C: the function `E` (Steps 1–2 of the paper)

```lean
theorem exists_E (hPW : PaleyWienerThm) (hC : TheoremC) {Λ : Set ℝ} (hs : IsSampling Λ) :
    ∃ E : ℂ → ℂ, IsHB E ∧ HEEqPW E ∧ (∀ f : ℂ → ℂ, MemHE E f ↔ MemPW f) ∧
      ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Λ f := sorry
```

*Proof.* Get the data of `exists_samplingHilbertSpace hPW (hs := hs)`, apply `hC H ι` to its
conclusions (the premises of `TheoremC` are exactly (inj., diff., H1, H2, H3, nonzero)). It returns
`E` with `IsHB E`, `MemHE E f ↔ f ∈ range ι ↔ MemPW f` and `ofReal (‖h‖²) = heNormSq E (ι h)`.
Hence for `f ∈ PW`: `f = ι h` and `heNormSq E f = ofReal(‖h‖²) = sampleSum Λ f` (norm identity of
3.6). `HEEqPW E`: first component is `hmem`; for the constants take `c = A`, `C = B`:
`A * pwNormSq f ≤ sampleSum Λ f = heNormSq E f ≤ B * pwNormSq f` (the lower and upper sampling
bounds).

Then, in the main proof, `HEEqPW.isStrictHB hEHB hEPW : IsStrictHB E` and
`HEEqPW.ne_zero_ofReal hEHB hEPW : ∀ x : ℝ, E x ≠ 0` from M02. (These are essential: strictness gives
`E - E^*A ≠ 0` on `ℂ₊` and is a hypothesis of `TheoremF`; no real zeros is needed to divide by `E(λ)`
below, and for the zeros of `E^*` to lie in `ℂ₊` in §9. The paper uses "`E` has no zeros on the real
axis since PW = H(E)" only in the converse direction; here it is needed already.)

---

## 5. The measure `μ` and Theorem F (Step 3)

```lean
def sampMeasure (Λ : Set ℝ) (E : ℂ → ℂ) : Measure ℝ :=
  Measure.sum fun x : Λ ↦ ENNReal.ofReal (‖E ((x : ℝ) : ℂ)‖ ^ 2) • Measure.dirac (x : ℝ)
```

**`lintegral_sampMeasure`.**
```lean
theorem lintegral_sampMeasure (Λ : Set ℝ) (E : ℂ → ℂ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ t, g t ∂(sampMeasure Λ E) =
      ∑' x : Λ, ENNReal.ofReal (‖E ((x : ℝ) : ℂ)‖ ^ 2) * g (x : ℝ) := sorry
```
`lintegral_sum_measure` (`MeasureTheory/Integral/Lebesgue/Basic.lean`, no countability needed),
then `lintegral_smul_measure` (`c • ∫⁻`, with `c • x = c * x` in `ℝ≥0∞`), then `lintegral_dirac`
(`Integral/Lebesgue/Countable.lean`, valid for every function since `ℝ` has measurable singletons).

**`lintegral_sampMeasure_div`.**
```lean
theorem lintegral_sampMeasure_div {Λ : Set ℝ} {E : ℂ → ℂ} (hE0 : ∀ x : ℝ, E (x : ℂ) ≠ 0)
    (f : ℂ → ℂ) : ∫⁻ t : ℝ, ‖f t / E t‖ₑ ^ 2 ∂(sampMeasure Λ E) = sampleSum Λ f := sorry
```
By `lintegral_sampMeasure` the left side is `∑' λ, ofReal(‖E λ‖²) * ‖f λ / E λ‖ₑ²`. Termwise:
`ofReal (‖E λ‖²) = ‖E λ‖ₑ²` and `‖f λ / E λ‖ₑ = ‖f λ‖ₑ / ‖E λ‖ₑ` (`enorm_mul`, `enorm_inv`/`div_eq_mul_inv`; check the exact name for `NormedDivisionRing`), with
`‖E λ‖ₑ ≠ 0, ≠ ∞` since `E λ ≠ 0`; so the term is `‖f λ‖ₑ²` (`ENNReal.mul_div_cancel`).

**`poissonInt_sampMeasure`.**
```lean
theorem poissonInt_sampMeasure (Λ : Set ℝ) (E : ℂ → ℂ) (z : ℂ) :
    poissonInt (sampMeasure Λ E) z =
      ∑' x : Λ, ENNReal.ofReal (‖E ((x : ℝ) : ℂ)‖ ^ 2) *
        ENNReal.ofReal (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2))) := sorry
```
Unfold `poissonInt` (an `ℝ≥0∞` lintegral of `ofReal (z.im / (π((t - z.re)² + z.im²)))`) and apply
`lintegral_sampMeasure`.

**`hbQuot`, `denom_ne_zero`, `differentiableOn_hbQuot`.**
```lean
def hbQuot (E A : ℂ → ℂ) (z : ℂ) : ℂ :=
  (E z + fstar E z * A z) / (E z - fstar E z * A z)
```
```lean
theorem denom_ne_zero {E A : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ} (hz : 0 < z.im)
    (hA : ‖A z‖ ≤ 1) : E z - fstar E z * A z ≠ 0 := sorry
```
*Proof.* `z ∈ ℂ₊`. `‖fstar E z‖ = ‖E (conj z)‖ < ‖E z‖` (strictness), so
`‖fstar E z * A z‖ ≤ ‖fstar E z‖ < ‖E z‖`, hence `E z ≠ fstar E z * A z`
(`norm_sub_norm_le`/`ne_of_apply_ne norm`). [Uses `E z ≠ 0` only through the strict inequality.]
```lean
theorem differentiableOn_hbQuot {E A : ℂ → ℂ} (hE : IsStrictHB E)
    (hA : DifferentiableOn ℂ A {z : ℂ | 0 < z.im}) (hA1 : ∀ z : ℂ, 0 < z.im → ‖A z‖ ≤ 1) :
    DifferentiableOn ℂ (hbQuot E A) {z : ℂ | 0 < z.im} := sorry
```
*Proof.* `E`, `fstar E` (`Differentiable.fstar`) differentiable, `A` on `ℂ₊`, division by
the nonvanishing denominator (`DifferentiableOn.div`).

**`exists_herglotz_data`.**
```lean
theorem exists_herglotz_data (hF : TheoremF) (Λ : Set ℝ) {E : ℂ → ℂ} (hE : IsStrictHB E)
    (hE0 : ∀ x : ℝ, E (x : ℂ) ≠ 0)
    (hnorm : ∀ f : ℂ → ℂ, MemHE E f → heNormSq E f = sampleSum Λ f) :
    ∃ A : ℂ → ℂ, DifferentiableOn ℂ A {z : ℂ | 0 < z.im} ∧ (∀ z : ℂ, 0 < z.im → ‖A z‖ ≤ 1) ∧
      ∃ p : ℝ, 0 ≤ p ∧
        Summable (fun x : Λ ↦ ‖E ((x : ℝ) : ℂ)‖ ^ 2 / (1 + (x : ℝ) ^ 2)) ∧
        ∀ z : ℂ, 0 < z.im →
          Summable (fun x : Λ ↦ ‖E ((x : ℝ) : ℂ)‖ ^ 2 *
            (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2)))) ∧
          (∑' x : Λ, ‖E ((x : ℝ) : ℂ)‖ ^ 2 *
            (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2)))) + p * z.im =
            (hbQuot E A z).re := sorry
```

*Proof.* Apply `hF (sampMeasure Λ E) E hE hE0 _`. The hypothesis of `TheoremF`:
for `f` with `MemHE E f`, `∫⁻ ‖f t/E t‖ₑ² ∂μ = sampleSum Λ f` (`lintegral_sampMeasure_div hE0`)
`= heNormSq E f` (hypothesis `hnorm`). This yields `A`, holomorphic on `ℂ₊` with `‖A‖ ≤ 1`, `p ≥ 0`,
and for `z ∈ ℂ₊`: `poissonInt μ z ≠ ∞` and `(poissonInt μ z).toReal + p y = Re (hbQuot E A z)`.
Real reformulation: by `poissonInt_sampMeasure`, `poissonInt μ z = ∑' λ, ofReal(c_λ) * ofReal(t_λ(z))`
with `t_λ(z) = y/(π((λ-x)²+y²)) ≥ 0`, which equals `∑' λ, ofReal (c_λ * t_λ(z))`
(`ENNReal.ofReal_mul`, `c_λ ≥ 0`). Since the sum is `≠ ∞`, the real family `c_λ t_λ(z)` is summable
(`ENNReal.summable_toReal`) and `(∑' ofReal (c_λ t_λ)).toReal = ∑' c_λ t_λ`
(`ENNReal.tsum_toReal_eq`, `ENNReal.toReal_ofReal`). *Summability of `c_λ/(1+λ²)`:* take `z = I`:
`t_λ(I) = 1/(π(λ²+1))`, so `∑ c_λ/(π(1+λ²)) < ∞`; multiply by `π`
(`Summable.mul_left`). Note that only `z = I` is needed for this, and that all later convergence
statements (§6) follow from it.

---

## 6. The Herglotz kernel with repaired normalisation (Step 4)

```lean
def hk (x : ℝ) (z : ℂ) : ℂ := 1 / ((x : ℂ) - z) - ((x / (1 + x ^ 2) : ℝ) : ℂ)
```

Remark: `hk λ z = 1/(λ - z) - λ/(1+λ²)`; it is *not* `1/(z-λ) + 1/λ`, see Issues 1–3.

```lean
theorem hk_eq {x : ℝ} {z : ℂ} (hz : z ≠ x) :
    hk x z = (1 + x * z) / (((x : ℂ) - z) * (1 + (x : ℂ) ^ 2)) := sorry
```
*Proof.* `1/(λ - z) - λ/(1+λ²) = ((1+λ²) - λ(λ - z))/((λ-z)(1+λ²)) = (1 + λ z)/((λ - z)(1+λ²))`
(`field_simp; ring`, with `(λ:ℂ) - z ≠ 0` and `1 + (λ:ℂ)² ≠ 0` because `1 + λ² > 0` for real `λ`;
`Complex.ofReal` casts via `push_cast`).

```lean
theorem norm_hk_le {R : ℝ} (hR : 1 / 2 ≤ R) {x : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) (hx : 2 * R ≤ |x|) :
    ‖hk x z‖ ≤ 2 * (1 + R) / (1 + x ^ 2) := sorry
```
*Proof.* `‖z‖ ≤ R`, `|λ| ≥ 2R ≥ 1`. So `z ≠ λ` (`‖z‖ ≤ R < |λ|`, as `R ≥ 1/2 > 0`) and
`‖λ - z‖ ≥ |λ| - R ≥ |λ|/2`. By `hk_eq`:
`‖hk λ z‖ ≤ (1 + |λ| R)/((|λ|/2)(1 + λ²)) = 2(1/|λ| + R)/(1+λ²) ≤ 2(1+R)/(1+λ²)` using `1/|λ| ≤ 1`.

```lean
theorem re_neg_I_mul_hk {x : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    (-I * hk x z).re = z.im / (((x : ℝ) - z.re) ^ 2 + z.im ^ 2) := sorry
```
*Proof.* Write `z = a + i b` with `b ≠ 0`. `1/(λ - z) = ((λ - a) + i b)/((λ-a)² + b²)`
(`Complex.inv_def`, `Complex.normSq_apply`), so `-i · 1/(λ - z) = (b - i(λ - a))/((λ-a)²+b²)`
with real part `b/((λ-a)²+b²)`. The second term of `hk` is real, so `-i ·` it is purely
imaginary (real part `0`). (Sign check: `z = i, λ = 0` gives `-i · (1/(-i)) = -i · i = 1 > 0`.)

```lean
def herglotzSum (Λ : Set ℝ) (c : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∑' x : Λ, (c x : ℂ) * hk (x : ℝ) z
```

```lean
theorem summable_norm_herglotz {Λ : Set ℝ} (hΛ : IsSeparated Λ) {c : ℝ → ℝ}
    (hcs : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2)) (z : ℂ) :
    Summable fun x : Λ ↦ ‖(c x : ℂ) * hk (x : ℝ) z‖ := sorry
```
*Proof.* (Valid for every `z`: only the `λ` with `|λ| ≥ 2R` matter.) Let `R := max ‖z‖ (1/2)`. By
`IsSeparated.finite_inter_Icc hΛ (2R)` the set of `λ ∈ Λ` with `|λ| < 2R` is finite, and for the
other `λ`, `‖c_λ hk λ z‖ ≤ |c_λ| · 2(1+R)/(1+λ²)` by `norm_hk_le`. `Summable.of_norm_bounded_eventually`
(cofinite filter on the subtype `Λ`, finiteness transferred from `Λ ∩ Icc` to the subtype) with
majorant `2(1+R)·|c_λ|/(1+λ²)` (`hcs.mul_left`).

```lean
theorem re_herglotzSum {Λ : Set ℝ} (hΛ : IsSeparated Λ) {c : ℝ → ℝ}
    (hcs : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2)) {z : ℂ} (hz : 0 < z.im) :
    ((-I / Real.pi) * herglotzSum Λ c z).re =
      ∑' x : Λ, c x * (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2))) := sorry
```
*Proof.* `((-I/π) * ∑' …).re = ∑' ((-I/π) * (c_λ hk λ z)).re` (`Complex.hasSum_re` applied to
`(summable_norm_herglotz …).of_norm.mul_left (-I/π)).hasSum`, `tsum_mul_left`). Termwise,
`(-I/π * (c_λ hk)).re = (c_λ/π) (-I * hk).re = c_λ y/(π((λ-x)²+y²))`, by `re_neg_I_mul_hk`
(`(c : ℂ)` real, `Complex.re_ofReal_mul`).  This equals the terms
`c_λ * (y/(π((λ-x)²+y²)))` of `exists_herglotz_data`.

### 6.1 The entire continuation `G · hk`

```lean
def entTerm (G : ℂ → ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  -dslope G (x : ℂ) z - ((x / (1 + x ^ 2) : ℝ) : ℂ) * G z
```
```lean
theorem differentiable_entTerm {G : ℂ → ℂ} (hG : Differentiable ℂ G) (x : ℝ) :
    Differentiable ℂ (entTerm G x) := sorry
```
*Proof.* `dslope G x` is differentiable on `univ` by `differentiableOn_dslope (univ_mem)`
(`Analysis/Complex/RemovableSingularity.lean`): `(differentiableOn_dslope Filter.univ_mem).2 hG.differentiableOn`.
```lean
theorem entTerm_eq {G : ℂ → ℂ} {x : ℝ} (hGx : G (x : ℂ) = 0) {z : ℂ} (hz : z ≠ (x : ℂ)) :
    entTerm G x z = G z * hk x z := sorry
```
*Proof.* `dslope_of_ne` and `slope_def_field`: `dslope G x z = (G z - G x)/(z - x) = G z/(z - x)`. So
`-dslope = G z/(x - z) = G z * (1/(x - z))` and `entTerm = G z (1/(x-z) - x/(1+x²))`.

```lean
def entSum (Λ : Set ℝ) (c : ℝ → ℝ) (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' x : Λ, (c x : ℂ) * entTerm G (x : ℝ) z
```
```lean
theorem differentiable_entSum {Λ : Set ℝ} (hΛ : IsSeparated Λ) {c : ℝ → ℝ}
    (hcs : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2)) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0) :
    Differentiable ℂ (entSum Λ c G) := sorry
```
*Proof.* Show `DifferentiableOn ℂ (entSum Λ c G) (ball 0 R)` for every `R ≥ 1/2` (then
`Differentiable` since the balls are open and cover `ℂ`: `differentiableOn_univ`/`DifferentiableOn.differentiableAt`
on `ball 0 (‖z‖+1)`). Use `differentiableOn_tsum_of_cofinite_bound` with `F λ = c_λ · entTerm G λ`
(entire by `differentiable_entTerm`) and `u λ = M_R · 2(1+R) · |c_λ|/(1+λ²)`, where
`M_R = sup_{‖w‖ ≤ R} ‖G w‖` (finite: continuous on a compact set,
`IsCompact.exists_bound_of_continuousOn`). Eventually (off the finite set `Λ ∩ [-2R, 2R]`,
`IsSeparated.finite_inter_Icc`): for `‖w‖ ≤ R`, `|λ| ≥ 2R` hence `w ≠ λ`, `entTerm_eq (hG0 λ _)` gives
`‖c_λ entTerm G λ w‖ = |c_λ| ‖G w‖ ‖hk λ w‖ ≤ |c_λ| M_R 2(1+R)/(1+λ²)`.

```lean
theorem entSum_eq {Λ : Set ℝ} {c : ℝ → ℝ} {G : ℂ → ℂ}
    (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0) {z : ℂ} (hz : z.im ≠ 0) :
    entSum Λ c G z = G z * herglotzSum Λ c z := sorry
```
*Proof.* For `z` nonreal, `z ≠ λ`; `entTerm_eq` termwise: `c_λ entTerm G λ z = G z * (c_λ hk λ z)`;
`tsum_mul_left`. (No summability needed in the field `ℂ`.)

```lean
theorem fstar_entSum {Λ : Set ℝ} (hΛ : IsSeparated Λ) {c : ℝ → ℝ}
    (hcs : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2)) {G : ℂ → ℂ}
    (hGd : Differentiable ℂ G) (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0) (hGs : fstar G = G) :
    fstar (entSum Λ c G) = entSum Λ c G := sorry
```
*Proof.* Both sides are entire (`differentiable_entSum`, `Differentiable.fstar`).
By `Differentiable.eq_of_eqOn_upper` it suffices to compare on `ℂ₊`. For `z ∈ ℂ₊`, `conj z ∈ ℂ₋`
is nonreal, `entSum (conj z) = G (conj z) * herglotzSum (conj z)` (`entSum_eq`), so
`fstar (entSum) z = conj (G (conj z)) * conj (herglotzSum Λ c (conj z)) = G z * conj(S(conj z))`
(`hGs`: `conj (G (conj z)) = fstar G z = G z`). And
`conj (S (conj z)) = ∑' conj (c_λ hk λ (conj z)) = ∑' c_λ hk λ z = S z`
(`tsum_star`; `conj (hk λ (conj z)) = hk λ z` since `λ` and `λ/(1+λ²)` are real: `map_sub`, `map_div₀`,
`Complex.conj_ofReal`). Then `entSum_eq` again at `z`.

---

## 7. The canonical product `G` (Step 5, first half)

```lean
def zeroSet (Λ : Set ℝ) : Set ℂ := Complex.ofReal '' (Λ \ {0})
```
```lean
def genProd (Λ : Set ℝ) (z : ℂ) : ℂ :=
  (if (0 : ℝ) ∈ Λ then z else 1) * OCS.canonicalProd (zeroSet Λ) (fun a ↦ a⁻¹) z
```

`G(z) = z^{[0 ∈ Λ]} ∏_{λ∈Λ∖{0}} (1 - z/λ) e^{z/λ}`; convergence factors `c_a = a⁻¹`
(the paper's `e^{z/λ_k}`, **undefined for `λ = 0`** — hence the factor `z` and the set `Λ ∖ {0}`).

```lean
theorem isGenusOneData_zeroSet {Λ : Set ℝ} (hΛ : IsSeparated Λ) :
    OCS.IsGenusOneData (zeroSet Λ) (fun a ↦ a⁻¹) := sorry
```
*Proof.* `IsGenusOneData Z c` (see the vendored file, line 38) has three fields: `0 ∉ Z`
(`λ ≠ 0` for `λ ∈ Λ∖{0}`, `Complex.ofReal_eq_zero`); `Summable (fun a : Z ↦ ‖a‖⁻¹ ^ 2)`; and
`Summable (fun a : Z ↦ ‖c a - a⁻¹‖)`, which is identically `0` for `c = (·)⁻¹`.
For the second: transfer along the equivalence `Λ∖{0} ≃ Z`, `x ↦ ↑x`
(`Equiv.Set.image Complex.ofReal _ Complex.ofReal_injective`, `Equiv.summable_iff`) to the real family
`1/x²` on `Λ∖{0}`; for `|x| ≥ 1`, `1/x² ≤ 2/(1+x²)`, and `Λ ∩ [-1,1]` is finite
(`IsSeparated.finite_inter_Icc`), so `Summable.of_norm_bounded_eventually` with the majorant
`2/(1+x²)` from `IsSeparated.summable_inv_one_add_sq` (restricted to the subtype `Λ ∖ {0}`,
`Summable.subtype`).

```lean
theorem differentiable_genProd {Λ : Set ℝ} (hΛ : IsSeparated Λ) :
    Differentiable ℂ (genProd Λ) := sorry
```
*Proof.* `OCS.differentiable_canonicalProd (isGenusOneData_zeroSet hΛ)`, times `z` or `1`
(`split_ifs`; `differentiable_id`, `differentiable_const`).

```lean
theorem genProd_eq_zero_iff {Λ : Set ℝ} (hΛ : IsSeparated Λ) (z : ℂ) :
    genProd Λ z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := sorry
```
*Proof.* `mul_eq_zero`; `OCS.canonicalProd_eq_zero_iff : P z = 0 ↔ z ∈ Z`. Case `0 ∈ Λ`: the zeros
are `{0} ∪ ofReal '' (Λ∖{0}) = ofReal '' Λ`; case `0 ∉ Λ`: `Λ∖{0} = Λ`.

```lean
theorem fstar_genProd {Λ : Set ℝ} (hΛ : IsSeparated Λ) : fstar (genProd Λ) = genProd Λ := sorry
```
*Proof.* `OCS.canonicalProd_conj h hZ hc z` (hypotheses: `Z` conjugation-symmetric because
`conj (↑x) = ↑x`; `c (conj a) = conj (c a)`, `map_inv₀`): `P (conj z) = conj (P z)`. The factor `z`
satisfies `conj (conj z) = z`. Thus `fstar G z = conj (G (conj z)) = conj (conj z) · conj (conj (P z))
= z · P z`.

```lean
theorem genProd_ne_zero_of_im_ne_zero {Λ : Set ℝ} (hΛ : IsSeparated Λ) {z : ℂ} (hz : z.im ≠ 0) :
    genProd Λ z ≠ 0 := sorry
```
*Proof.* By `genProd_eq_zero_iff`, a zero is a real number.

(Simplicity of the zeros of `G` is **not needed** in this approach; `deriv_canonicalProd_ne_zero` is
unused.)

---

## 8. The entire functions `W`, `P`, `Q` (Step 4–5)

```lean
def herglotzEnt (Λ : Set ℝ) (c : ℝ → ℝ) (G : ℂ → ℂ) (p a : ℝ) (z : ℂ) : ℂ :=
  (-I / Real.pi) * entSum Λ c G z - I * p * z * G z + I * a * G z
```

`W = G M` for `M(z) = (-i/π) S(z) - i p z + i a`, `S = herglotzSum`.

```lean
theorem differentiable_herglotzEnt {Λ : Set ℝ} (hΛ : IsSeparated Λ) {c : ℝ → ℝ}
    (hcs : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2)) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0) (p a : ℝ) :
    Differentiable ℂ (herglotzEnt Λ c G p a) := sorry
```
*Proof.* Sum of products of entire functions (`differentiable_entSum`, `hG`, identity, constants).

```lean
theorem fstar_herglotzEnt {Λ : Set ℝ} (hΛ : IsSeparated Λ) {c : ℝ → ℝ}
    (hcs : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2)) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0) (hGs : fstar G = G) (p a : ℝ) :
    fstar (herglotzEnt Λ c G p a) = fun z ↦ -herglotzEnt Λ c G p a z := sorry
```
*Proof.* Unfold `fstar`: `conj (W (conj z)) =
conj(-I/π) conj(entSum (conj z)) - conj(I p conj z G(conj z)) + conj(I a G (conj z))`
`= (I/π) (fstar entSum) z + I p z (fstar G) z - I a (fstar G) z`
`= (I/π) entSum z + I p z G z - I a G z = -W z` using `fstar_entSum`, `hGs`,
`conj (-I/π) = I/π`, `conj I = -I`, `conj (p:ℂ) = p`, `conj (a:ℂ) = a`, `Complex.conj_conj`.

### 8.1 Herglotz normalisation: `exists_herglotz_const`
```lean
theorem exists_herglotz_const {Λ : Set ℝ} (hΛ : IsSeparated Λ) {E A G : ℂ → ℂ} {p : ℝ}
    (hE : IsStrictHB E) (hA : DifferentiableOn ℂ A {z : ℂ | 0 < z.im})
    (hA1 : ∀ z : ℂ, 0 < z.im → ‖A z‖ ≤ 1)
    (hcs : Summable fun x : Λ ↦ ‖E ((x : ℝ) : ℂ)‖ ^ 2 / (1 + (x : ℝ) ^ 2))
    (hre : ∀ z : ℂ, 0 < z.im →
      (∑' x : Λ, ‖E ((x : ℝ) : ℂ)‖ ^ 2 *
            (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2)))) + p * z.im =
            (hbQuot E A z).re)
    (hG : Differentiable ℂ G) (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0) (hGne : ∀ z : ℂ, 0 < z.im → G z ≠ 0) :
    ∃ a : ℝ, ∀ z : ℂ, 0 < z.im →
      hbQuot E A z = (-I / Real.pi) * herglotzSum Λ (fun x ↦ ‖E (x : ℂ)‖ ^ 2) z
        - I * p * z + I * a := sorry
```

*Proof.* Put `c λ := ‖E λ‖²`, `S := herglotzSum Λ c`, `M₀ z := (-I/π) * S z - I * p * z`,
`W₀ z := (-I/π) * entSum Λ c G z - I * p * z * G z` (entire by `differentiable_entSum`).
Notation `hcs'`: `Summable |c λ|/(1+λ²)` from `hcs` since `c ≥ 0`.
1. *`M₀` is holomorphic on `ℂ₊`:* for `z ∈ ℂ₊`, `G z ≠ 0` and `W₀ z = G z * M₀ z`
   (by `entSum_eq`), so `M₀ = W₀/G` on `ℂ₊`, a quotient of differentiable functions with
   nonvanishing denominator (`DifferentiableOn.div`, `DifferentiableOn.congr`). (This avoids proving
   differentiability of the series `S` itself.)
2. *Real parts:* for `z ∈ ℂ₊`,
   `Re M₀ z = Re((-I/π) S z) + Re(-I p z) = ∑' c_λ y/(π((λ-x)²+y²)) + p y`
   (`re_herglotzSum`; `Re(-I p z) = p y` since `-I(x+iy) = y - ix`; `Complex.mul_re`). By `hre` this is
   `Re (hbQuot E A z)`.
3. *Difference:* `D := hbQuot E A - M₀` is holomorphic on `ℂ₊` (`differentiableOn_hbQuot`, step 1),
   with `Re D = 0`. `exists_const_of_re_eq_zero` gives `a : ℝ` with `D z = a * I` on `ℂ₊`; i.e.
   `hbQuot E A z = M₀ z + I a = (-I/π) S z - I p z + I a`.

Real part check for the sign (also used in Issue 1): `Re(-i/(λ - z)) = y/|λ-z|² ≥ 0` — positive, as
a Poisson integral and as `Re (1+w)/(1-w) ≥ 0` for `|w| ≤ 1` require; whereas the paper's
`-i/(z - λ)` has real part `-y/|z-λ|²`.

```lean
theorem herglotzEnt_eq {Λ : Set ℝ} {E A G : ℂ → ℂ} {p a : ℝ}
    (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0)
    (ha : ∀ z : ℂ, 0 < z.im → hbQuot E A z =
      (-I / Real.pi) * herglotzSum Λ (fun x ↦ ‖E (x : ℂ)‖ ^ 2) z - I * p * z + I * a)
    {z : ℂ} (hz : 0 < z.im) :
    herglotzEnt Λ (fun x ↦ ‖E (x : ℂ)‖ ^ 2) G p a z = G z * hbQuot E A z := sorry
```
*Proof.* For `z ∈ ℂ₊` (so `z ≠ λ`, nonreal): `entSum_eq`:
`W z = (-I/π) G z S z - I p z G z + I a G z = G z ((-I/π) S z - I p z + I a) = G z * hbQuot E A z`
by `ha`. (`ring` after rewriting.)

```lean
theorem PQ_relations {E A G W : ℂ → ℂ} (hE : IsStrictHB E)
    (hA1 : ∀ z : ℂ, 0 < z.im → ‖A z‖ ≤ 1) (hW : ∀ z : ℂ, 0 < z.im → W z = G z * hbQuot E A z)
    {z : ℂ} (hz : 0 < z.im) :
    (W z - G z) * E z = (W z + G z) * (fstar E z * A z) ∧
      (W z + G z) * (E z - fstar E z * A z) = 2 * G z * E z := sorry
```
*Proof.* Let `N = E + E^*A`, `D = E - E^*A ≠ 0` (`denom_ne_zero`), `H = N/D`, `W = G H`. Then
`W - G = G (N - D)/D = 2 G E^*A/D` and `W + G = G(N + D)/D = 2 G E/D`. Hence
`(W - G) E = 2 G E^*A E/D = (W + G) E^*A` and `(W + G) D = 2 G E`. (`field_simp; ring`.)

---

## 9. The function `F` (Step 5, second half)

```lean
theorem exists_F {E A P Q : ℂ → ℂ} (hE : IsHB E) (hE0 : ∀ x : ℝ, E (x : ℂ) ≠ 0)
    (hA : DifferentiableOn ℂ A {z : ℂ | 0 < z.im}) (hP : Differentiable ℂ P)
    (hQ : Differentiable ℂ Q) (hPQ : fstar P = fun z ↦ -Q z)
    (hrel : ∀ z : ℂ, 0 < z.im → P z * E z = Q z * (fstar E z * A z)) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ z : ℂ, E z * F z = Q z) ∧
      (∀ z : ℂ, fstar E z * fstar F z = -P z) ∧
      ∀ z : ℂ, 0 < z.im → fstar F z = -(A z * F z) := sorry
```

*Proof.* Notation: `ℂ₊`, `P`, `Q` entire, `P^* = -Q`, `hrel : P E = Q E^* A` on `ℂ₊`.
*Zeros of `E^*`.* `E^* z = conj (E (conj z))`. If `Im z ≤ 0`, then `Im (conj z) ≥ 0`: for `Im > 0` use
`IsHB` (no zeros in `ℂ₊`), for `Im = 0` use `hE0`. So **`E^* z ≠ 0` whenever `Im z ≤ 0`**, and
`E z ≠ 0` whenever `Im z > 0`.
*Definition.* `Φ z := if 0 < z.im then Q z * A z / E z else P z / fstar E z`.
*Claim `Φ` is entire.*
- At `z₀ ∈ ℂ₊` (open): `Φ =ᶠ[𝓝 z₀] Q A/E`, which is differentiable at `z₀` (`A` is differentiable on
  the open `ℂ₊`, `E z₀ ≠ 0`: `DifferentiableOn.differentiableAt`, `DifferentiableAt.div`).
- At `z₀` with `Im z₀ ≤ 0`: `V = {z | fstar E z ≠ 0}` is open (continuity of `fstar E`) and contains
  `z₀`. On `V`, `Φ = P/fstar E`: if `Im z ≤ 0` by definition; if `Im z > 0`, `Φ z = Q A/E` and
  `Q A/E = P/E^*` because `P E = Q E^* A` (hrel) with `E z ≠ 0`, `E^* z ≠ 0`
  (`div_eq_div_iff`). Hence `Φ =ᶠ[𝓝 z₀] P/fstar E`, differentiable at `z₀`
  (`DifferentiableAt.congr_of_eventuallyEq`).
*Key identity:* `E^* Φ = P` on `ℂ`: for `Im z > 0` it is `hrel` (as above), for `Im z ≤ 0`
`E^* z · (P z/E^* z) = P z`.
*Definition of `F`.* `F := fstar (fun z ↦ -Φ z)`, i.e. `F z = -conj (Φ (conj z))`. Then
`Differentiable ℂ F` (`Differentiable.fstar`, `Differentiable.neg`) and `fstar F = -Φ`
(`fstar_fstar`). Therefore
- `E^* F^* = -E^* Φ = -P` on `ℂ`.
- `E F = Q`: apply `fstar` to the key identity: `(E^*Φ)^* = E · Φ^*` (as `fstar (fstar E) = E`)
  and `P^* = -Q`, so `E Φ^* = -Q`, and `E F = -E Φ^* = Q` (note `F = -Φ^*`).
- On `ℂ₊`: `fstar F z = -Φ z = -Q z A z/E z = -A z F z`, using `F z = Q z/E z` (from `E F = Q`,
  `E z ≠ 0`).
(Concretely, with `fstar` unfolded: `fstar (fun z ↦ -Φ z) w = conj (-Φ (conj w))`; the three bullets
are `simp [fstar]` computations plus `conj_conj`.)

```lean
theorem isHB_F {E A F G Q : ℂ → ℂ} (hE : IsStrictHB E) (hF : Differentiable ℂ F)
    (hA1 : ∀ z : ℂ, 0 < z.im → ‖A z‖ ≤ 1) (hEF : ∀ z : ℂ, E z * F z = Q z)
    (hFA : ∀ z : ℂ, 0 < z.im → fstar F z = -(A z * F z))
    (hQ : ∀ z : ℂ, 0 < z.im → Q z * (E z - fstar E z * A z) = 2 * G z * E z)
    (hG : ∀ z : ℂ, 0 < z.im → G z ≠ 0) : IsHB F := sorry
```
*Proof.* Entire: `hF`. On `ℂ₊`: from `E F = Q` and `Q (E - E^*A) = 2 G E`,
`E (F (E - E^*A)) = E (2 G)`, so `F (E - E^*A) = 2G` (`E z ≠ 0`, cancel); `E - E^*A ≠ 0`
(`denom_ne_zero hE hz (hA1 z hz)`), and `G z ≠ 0`, hence `F z ≠ 0`. Finally
`‖F (conj z)‖ = ‖fstar F z‖ = ‖-(A z F z)‖ = ‖A z‖ ‖F z‖ ≤ ‖F z‖` (`norm_fstar`).

---

## 10. Assembly: `theorem1_necessity`

```lean
theorem theorem1_necessity (hPW : PaleyWienerThm) (hC : TheoremC) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  -- Steps 1-2: Theorem C
  obtain ⟨E, hEHB, hEPW, hmem, hnorm⟩ := exists_E hPW hC hs
  have hEs : IsStrictHB E := HEEqPW.isStrictHB hEHB hEPW
  have hE0 : ∀ x : ℝ, E (x : ℂ) ≠ 0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  -- Step 3: Theorem F
  obtain ⟨A, hAd, hA1, p, hp, hcs, hpo⟩ :=
    exists_herglotz_data hF Λ hEs hE0 (fun f hf ↦ hnorm f ((hmem f).1 hf))
  have hcs' : Summable fun x : Λ ↦ |‖E ((x : ℝ) : ℂ)‖ ^ 2| / (1 + (x : ℝ) ^ 2) := by
    refine hcs.congr fun x ↦ ?_
    rw [abs_of_nonneg (by positivity)]
  -- Step 5: the product G
  have hGd : Differentiable ℂ (genProd Λ) := differentiable_genProd hΛ
  have hGs : fstar (genProd Λ) = genProd Λ := fstar_genProd hΛ
  have hG0 : ∀ x ∈ Λ, genProd Λ (x : ℂ) = 0 := fun x hx ↦
    (genProd_eq_zero_iff hΛ _).2 ⟨x, hx, rfl⟩
  have hGne : ∀ z : ℂ, 0 < z.im → genProd Λ z ≠ 0 := fun z hz ↦
    genProd_ne_zero_of_im_ne_zero hΛ hz.ne'
  have hzero := genProd_eq_zero_iff hΛ
  generalize genProd Λ = G at hGd hGs hG0 hGne hzero
  -- Step 4: Herglotz normalisation
  obtain ⟨a, ha⟩ := exists_herglotz_const hΛ hEs hAd hA1 hcs (fun z hz ↦ (hpo z hz).2) hGd hG0
    hGne
  have hWd := differentiable_herglotzEnt (c := fun x ↦ ‖E (x : ℂ)‖ ^ 2) hΛ hcs' hGd hG0 p a
  have hWs := fstar_herglotzEnt (c := fun x ↦ ‖E (x : ℂ)‖ ^ 2) hΛ hcs' hGd hG0 hGs p a
  have hWeq : ∀ z : ℂ, 0 < z.im → herglotzEnt Λ (fun x ↦ ‖E (x : ℂ)‖ ^ 2) G p a z =
      G z * hbQuot E A z := fun z hz ↦ herglotzEnt_eq hG0 ha hz
  suffices key : ∀ W : ℂ → ℂ, Differentiable ℂ W → fstar W = (fun z ↦ -W z) →
      (∀ z : ℂ, 0 < z.im → W z = G z * hbQuot E A z) →
      ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
        ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) from
    key _ hWd hWs hWeq
  intro W hWd hWs hWeq
  have hPd : Differentiable ℂ (fun z ↦ W z - G z) := hWd.sub hGd
  have hQd : Differentiable ℂ (fun z ↦ W z + G z) := hWd.add hGd
  have hPQ : fstar (fun z ↦ W z - G z) = fun z ↦ -(W z + G z) := by
    funext z
    have h1 := congrFun hWs z
    have h2 := congrFun hGs z
    simp only [fstar] at h1 h2 ⊢
    rw [map_sub, h1, h2]
    ring
  have hrel : ∀ z : ℂ, 0 < z.im → (W z - G z) * E z = (W z + G z) * (fstar E z * A z) :=
    fun z hz ↦ (PQ_relations hEs hA1 hWeq hz).1
  obtain ⟨F, hFd, hEF, hEFs, hFA⟩ := exists_F hEHB hE0 hAd hPd hQd hPQ hrel
  refine ⟨E, F, hEHB, isHB_F hEs hFd hA1 hEF hFA
    (fun z hz ↦ (PQ_relations hEs hA1 hWeq hz).2) hGne, hEPW, fun z ↦ ?_⟩
  have h2G : E z * F z + fstar E z * fstar F z = 2 * G z := by
    rw [hEF, hEFs]; ring
  rw [h2G, mul_eq_zero, hzero]
  simp
```

The proof (`theorem1_necessity`, `Necessity.lean`) follows this logic.

1. `exists_E` (§4): `E`, `IsHB E`, `HEEqPW E`, `MemHE E f ↔ MemPW f`, `heNormSq E f = sampleSum Λ f`.
   M02: `IsStrictHB E`, `∀ x, E x ≠ 0`.
2. `exists_herglotz_data hF Λ hEs hE0 _` (§5): `A`, `p`, `hcs`, and the real-part identity.
3. `G := genProd Λ` (§7): entire, `G^* = G`, `G λ = 0` for `λ ∈ Λ`, `G z ≠ 0` for nonreal `z`.
4. `exists_herglotz_const` (§8.1): the real `a` with `hbQuot E A = M` on `ℂ₊`.
5. `W := herglotzEnt Λ c G p a`: entire, `W^* = -W`, `W = G · hbQuot E A` on `ℂ₊` (`herglotzEnt_eq`).
6. `P := W - G`, `Q := W + G`: entire; `P^* = -Q` (`fstar` of a difference; `W^* = -W`, `G^* = G`:
   `fstar P z = fstar W z - fstar G z = -W z - G z = -Q z`); relations from `PQ_relations`.
7. `exists_F` (§9): `F` entire, `E F = Q`, `E^* F^* = -P`, `F^* = -A F` on `ℂ₊`; `isHB_F`: `F ∈ \overline{HB}`.
8. `E F + E^* F^* = Q - P = 2 G` on `ℂ` (`ring`); and `2 G z = 0 ↔ G z = 0 ↔ ∃ x ∈ Λ, z = x`
   (`genProd_eq_zero_iff`).

Dependency graph of the lemmas:
`exists_samplingHilbertSpace → exists_E`; `lintegral_sampMeasure(_div), poissonInt_sampMeasure →
exists_herglotz_data`; `hk-lemmas → entSum-lemmas → exists_herglotz_const, herglotzEnt_*`;
`genProd-lemmas`; `PQ_relations, exists_F, isHB_F`; all → `theorem1_necessity`.

Where each hypothesis is used: `hPW` (completeness, H2); `hC` (E); `hF` (A, p); separation of `Λ`
(`G` exists, convergence of the kernel series); sampling (Hilbert space and `HEEqPW`).
Not used: Theorem E, D; simplicity of zeros of `G`; `plancherelPolya`.

---

## 11. Issues in the source

Each item: page/line in the printed version (journal p. 795–796) / `literature/ArxivOrtega.tex`
lines 417–465.

1. **Sign error in (3).** tex l. 429–432: `-i \sum_{k}|E(\lambda_k)|^2(\frac1{z-\lambda_k}+\frac1{\lambda_k}) + ia
   = \frac{E+E^*A}{E-E^*A}`. For `z = x+iy`, `Re(-i/(z-λ)) = -y/|z-λ|² ≤ 0`, whereas the right
   side has real part `≥ 0` on `ℂ₊` (`|E^*A| ≤ |E^*| < |E|`) and equals the Poisson integral of
   `μ` (≥ 0) by Theorem F. Concrete check: `λ = 0`, `z = i`: `-i/(z-λ) = -i/i = -1 < 0`, while
   `-i/(λ-z) = -i/(-i) = 1 > 0`. The correct term is `-i/(λ - z) = i/(z - λ)`, i.e. the sum in (3)
   should read `+i ∑ |E(λ_k)|² (1/(z-λ_k) - …)` (with the repaired convergence factor). *Sure.*
2. **Missing factor `1/π`.** Theorem F (tex l. 376–386) has `\frac y\pi\int d\mu/((t-x)^2+y^2) = Re(\ldots)`.
   `Re(-i/(λ-z)) = y/|λ-z|²` has no `1/π`; so (3) needs `(1/π)` in front of the sum (our `M` has
   `-i/π`). *Sure.* (Harmless for the structure of the proof since it only rescales the residues of `M`.)
3. **`1/λ_k` undefined if `0 ∈ Λ`**, both in (3) and in `G(z) = ∏(1 - z/λ_k)e^{z/λ_k}` (tex l. 444);
   moreover `∑|E(λ_k)|²/λ_k` need not converge, which is the reason for a convergence factor.
   Fix: kernel `1/(λ - z) - λ/(1+λ²)` (`hk`), whose convergence follows from
   `∑ |E(λ_k)|²/(1+λ_k²) < ∞` (the Poisson integral at `z = i` is finite); `G` = product over
   `Λ∖{0}` times `z` if `0 ∈ Λ`. The paper never mentions the convergence of the series
   (3); its absolute convergence needs this finite Poisson integral. *Sure.*
4. **Theorem F as quoted has no `p y` term**, but Herglotz' representation of a positive
   harmonic function on `ℂ₊` contains `p y`, `p ≥ 0` (the `TheoremF` in `Defs.lean` has it). With
   it `M` gains the entire term `-i p z` and `M^* = -M` still holds, so the proof is unchanged.
   Also Theorem F is stated for `E ∈ \overline{HB}`; it needs `E` strict without real zeros (cf.
   README 2.7). *Fairly sure.*
5. **"The function `M - 1` ... vanishes whenever `E^*` vanishes"** (tex l. 440–447): only meaningful
   after noting (a) the zeros of `E^*` lie in `ℂ₊` (needs: `E` has no real zeros, which the paper
   states only in the converse part), and (b) multiplicities: from `(M-1)E = (M+1)E^*A` on `ℂ₊` and
   `E ≠ 0`, `M + 1` holomorphic, the order of `M-1` at a zero of `E^*` is at least that of `E^*`.
   Also `M - 1` vanishes at the zeros of `A` (not mentioned; harmless). The construction in §9
   (the `if`-definition of `Φ`) makes this precise without meromorphic functions. *Sure.*
6. **"`M - 1 = -E^*F^*/G` with `F` entire"** (tex l. 448) tacitly uses that `G(M-1)` is entire
   (each pole of `M` at a `λ_k` is simple and cancelled by the zero of `G`), and that `G(M-1)/E^*` is
   entire (previous item). Here `G·M` is shown entire directly: `G M = (-i/π) ∑ c_λ G(z)(1/(λ-z) - …) + …`
   and each term is entire because `G(λ) = 0` (`entTerm`, `dslope`); no simplicity of zeros is
   needed. *Sure.*
7. **"`F` has no zeros in `Im z > 0`"** is asserted from `F^*/F = -A`; this is unjustified (the
   quotient `F^*/F` presupposes `F ≠ 0`). Correct argument: `F = 2G/(E - E^*A)` on `ℂ₊` (equivalently `M + 1 ≠ 0` because `Re M ≥ 0`). The same
   formula shows that the closed class `\overline{HB}` (and not `HB`) is the right one: `F^* = -AF`
   with `|A| ≤ 1` gives only `|F^*| ≤ |F|`. *Sure.*
8. **The real-part argument** (tex l. 457–460): "`G` is the real part of `EF` for real `z`".
   Correct but unnecessary and slightly imprecise: at `x ∈ Λ`, `M(x)` is a pole, and `M(x) G(x)` must
   be read as the value of the entire function `G M`. Simplification used here: `Q - P = 2G` identically
   as entire functions, where `EF = Q = G(M+1)`, `E^*F^* = -P = -G(M-1)`. *Sure.*
9. **`E(λ_k) ≠ 0`.** The measure `μ` and the identity `∫|f/E|²dμ = ∑|f(λ_k)|²` require `E(λ_k) ≠ 0`
   (otherwise the term `|E(λ_k)|² |f(λ_k)/E(λ_k)|²` is `0` and not `|f(λ_k)|²`). This follows
   from `H(E) = PW` (M02: `HEEqPW.ne_zero_ofReal`), not stated in the paper at this point. *Sure.*
10. **Theorem C hypotheses.** The paper's one sentence "the Paley–Wiener space equipped with the norm
    `√∑|f(λ_k)|²` is a de Branges space" hides: completeness (needs the Plancherel–Pólya inequality
    and completeness of `PW`), that `∑|f(λ_k)|² = 0` implies `f = 0` (lower sampling bound), and
    (H1)–(H3) (the multiplier `(z - w̄)/(z - w)` is unimodular on `ℝ`; `f^*` has the same values'
    moduli on `ℝ`), plus the identification `H(E) = PW` only with equivalent norms, from the
    sampling constants. All handled in §3–4. *Sure.*
11. Minor: "Setting `G(z) = …`" then "`G^* = G`": needs the zero set real (true: `Λ ⊂ ℝ`) and the
    product symmetric (`OCS.canonicalProd_conj`).

Possible simplification of the paper: the exponent/convergence normalisation can be bypassed
entirely by working with `W = G M` directly (§8).

## 12. Requested changes to M00

None required. Comments:
- `TheoremC` as formalised is what is needed (H1 pointwise off `ζ`; the conclusion
  `∀ h, ofReal (‖h‖²) = heNormSq E (ι h)`). The use of `IsHB` (closed class) in the conclusion is
  enough, given the M02 lemmas `HEEqPW.isStrictHB`, `HEEqPW.ne_zero_ofReal`.
- `TheoremF` with `p ≥ 0` and `poissonInt μ z ≠ ∞` is exactly what §5 uses. The hypothesis
  `IsStrictHB E` and no real zeros are used in `denom_ne_zero` and in `lintegral_sampMeasure_div`.

## 13. Notes for the integrator (upstream interface section of the scaffold)

*Obsolete:* the interface section was replaced by imports at assembly (`IMPORTS.md`);
`IsSeparated.finite_inter_Icc` moved to `PW/Basic.lean`. Kept for the record.

The scaffold declares, with README/M01/M02 names, the following (all `sorry`), to be replaced by
imports. Signatures already match the current `PW/Basic.lean`, `PW/Bounds.lean`, `PW/Complete.lean`,
`HB/Basic.lean`, `HB/DeBranges.lean` (checked at the time of writing; `MemPW.const_mul hf c` has the
function first):
`memPW_zero`, `MemPW.add`, `MemPW.sub`, `MemPW.const_mul`, `MemPW.fstar`, `pwNormSq_fstar`,
`MemPW.mul_div_sub`, `pwNormSq_ne_top`, `pw_norm_sq_le`, `exists_memPW_eval_ne_zero`, `pw_complete`,
`fstar_fstar`, `Differentiable.fstar`, `fstar_ofReal`, `HEEqPW.isStrictHB`, `HEEqPW.ne_zero_ofReal`.
**New (not in the README list):** `MemPW.eq_zero_of_pwNormSq_eq_zero` (M01).
Generic lemmas owned by this module (could be moved to a utilities file):
`differentiableOn_tsum_of_cofinite_bound`, `Differentiable.eq_of_eqOn_upper`,
`exists_const_of_re_eq_zero`, `IsSeparated.finite_inter_Icc`, `IsSeparated.summable_inv_one_add_sq`
(M04, M05 may also need the last two).
