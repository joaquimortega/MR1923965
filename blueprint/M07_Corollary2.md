# M07 — The phase construction, the perturbation lemma and Corollary 2

**Lean:** `FourierFrames/Perturbation.lean`, `FourierFrames/Construction.lean`,
`FourierFrames/Corollary2.lean` (namespace `FF`; the last imports the first two, so for a stand-alone
compilation the two oleans must exist: `lake build FourierFrames.Perturbation
FourierFrames.Construction`; `Perturbation` and `Construction` compile with `lake env lean` directly).
**Paper:** §5, pp. 799–801 (the proof of Corollary 2) and the perturbation sentence on p. 800.

**Depends on.**
- M00: `Defs.lean` (`IsHB`, `IsStrictHB`, `fstar`, `IsPhaseFunction`, `phaseDeriv`, `phaseLevel`,
  `HEEqPW`, `IsSampling`, `IsSeparated`, `DSPerturbation`, `UPsi`, `LambdaPsi`, `IsAdmissiblePsi`,
  `TheoremE`, `PaleyWienerThm`).
- M01: `MemPW.mul_div_sub`, `pw_normal_family`, `plancherelPolya`, `pwNormSq_ne_top`,
  `sampleSum_union_le`.
- M02: `IsHB.of_tendstoLocallyUniformly`, `IsHB.mul`, `exists_isPhaseFunction`,
  `IsHB.phaseDeriv_nonneg`, `continuous_phaseDeriv`, `IsStrictHB.phaseDeriv_pos`,
  `IsPhaseFunction.strictMono_of_isStrictHB`, `zero_set_eq_phaseLevel`, `heEqPW_of_comparable`,
  `HEEqPW.isStrictHB`, `HEEqPW.phaseDeriv_mul_sq_le`.
- M04: `theorem1_sufficiency`.
- Vendored: `OCS.multF`, `OCS.multU`, `OCS.multGamma`, `OCS.multBary`, `OCS.multPt`, `OCS.multPrim`,
  `OCS.multGammaC`, `OCS.IsMultWeight`, `OCS.multF_estimate_two`, `OCS.multF_estimate_three`,
  `OCS.exp_multL`, `OCS.multF_eq_zero_iff`, `OCS.multF_conj`, `OCS.differentiable_multF`,
  `OCS.multU_conj`, `OCS.strictMono_multBary`, `OCS.multPrim_multPt`, `OCS.multPt_succ_sub_bounds`,
  `OCS.integrable_multUIntegrand`, `OCS.hasProdLocallyUniformlyOn_canonicalProd`,
  `OCS.deriv_canonicalProd_ne_zero`, `OCS.MemBernstein.exists_subseq_tendstoLocallyUniformly`,
  `OCS.memBernstein_of_norm_le`.

**Used by.** M06 (`exists_hb_of_density`, `exists_hb_of_density_phase`), M08 (`corollary2`),
the comparator (`corollary2`).

---------------------------------------------------------------------------------------------------

## 0. Summary: what is different from the paper and from `README.md` §4

The proof of Corollary 2 on pp. 800–801 is a sketch with five real gaps. All are repaired below
(details in §4, **Issues in the source**).

1. **Meĭman's theorem is replaced** (README §3.6). `E = A - iB ∈ \overline{HB}` is proved from the
   polynomial Hermite–Biehler inequality `Im ∏ (z-b_k)/(z-a_k) > 0` for interlacing real zeros
   (a half-page argument with arguments of the factors) and Hurwitz closure (§2.4).
2. **The phase clause of the README's `exists_hb_of_density` is not provable for general `m → 1`**
   (README §4 lists `φ_E - π M → c₀` as a conclusion for every `m` with `a ≤ m ≤ b`, `m → 1`).
   The phase of `E = A - iB` is governed by the *amplitude* of `A` relative to its translate
   `A(· - 1/2)`: locally `A(s + τ) ≈ c e^{κ_s τ} sin π(τ - θ)` with `κ_s = ∂_x U(s)`, hence
   `B/A ≈ e^{-κ_s/2} tan`, which has the phase `π M + c₀ + o(1)` only if `κ_s → 0`. For `m → 1`
   alone, `∂_x U` (a Hilbert transform of `m - 1`) can be unbounded (take `m - 1 = (log log t)^{-1}`
   on sparse long intervals `[t_k, 2t_k]`; then `∂_x U(t_k + 1) ≈ log t_k / log log t_k`).
   *Fix:* the phase clause is proved under the drifted hypothesis
   `hU : ∃ κ C, ∀ z, 0 ≤ Im z → |U - π Im z - κ Re z| ≤ C` (`exists_hb_of_density_phase`; for
   `κ = 0` this says that `A` is bounded on `ℝ`, for `κ ≠ 0` that `A e^{-κ z}` is, see the
   paragraph "Generalisation to a linear drift" below); the first four clauses need only the
   weaker `hshift : |U(z - 1/2) - U(z)| ≤ C` (`exists_hb_of_density`). M06 needs
   `|E| ≃ e^{π Im z}`, which `exists_hb_of_density_phase` now delivers directly (after the
   normalisation `E ↦ e^{-κ z} E`), so M06 does not have to multiply by `e^{-κ z}` itself.

   **Generalisation to a linear drift (added at assembly).** The first version assumed
   `|U - π Im z| ≤ C`. M06 (`LogExample.lean`, §4) proves `U(z) = π Im z + κ Re z + O(1)` with
   `κ = ∫_{|t|>1} (m - 1)/t dt ≠ 0` in general, so the hypothesis is generalised to
   `∃ κ C, |U - π Im z - κ Re z| ≤ C`. Nothing else changes, because `κ` is absorbed by the
   *real entire* zero-free factor `e^{κ z}`: `A_κ := A e^{-κ z}` is real entire with the same simple
   zeros `Γ` and satisfies all estimates of 2.1 with `U` replaced by `U - κ Re z` (`|e^{-κ z}| =
   e^{-κ Re z}`). Concretely: (i) 2.1 under `hU` gives `|A| ≃ e^{π|Im z| + κ Re z} min(1, dist(z, Γ))`;
   (ii) the translates `e^{-κ s_k} A(· + s_k) = A_κ(· + s_k) e^{κ z}` lie in `𝓑_π` with a uniform bound,
   and the normal-family/Liouville argument of 2.7 (a) yields the limits `c e^{κ z} sin π(z - θ)`
   (`c ≠ 0` real); (iii) **`B` must be rescaled.** With `A_κ = e^{-κ z} A` and `B_κ(z) = A_κ(z - 1/2) P/Q`, one has
   `e^{-κ z} B = e^{-κ/2} B_κ`, so the plain twist `e^{-κ z}(A - iB) = A_κ - i e^{-κ/2} B_κ` has the
   right modulus but its translates tend to `c[sin π(x-θ) + i e^{-κ/2} cos π(x-θ)]`, whose phase is
   *not* `-πx + const` (for `λ ≠ 1`, `arg(sin πu + iλ cos πu) + πu` is non-constant and 1-periodic):
   the phase rigidity (2.7 (b)) fails. The right function is
   `E_κ := A_κ - i B_κ = e^{-κ z}(A - i e^{κ/2} B)` (`compEκ`). It is in `\overline{HB}`: `A - iλB ∈
   \overline{HB}` for every `λ > 0` (the proof of `isHB_compE` via `isHB_polyA_sub_polyB`, which already
   allows an arbitrary positive multiplier), and `e^{-κ z}` is a real entire factor (`IsHB.mul`,
   `isHB_cexp_real_linear`). It has no real zeros, `|E_κ| ≃ e^{U - κ Re z} ≃ e^{π Im z}`, and
   `E_κ + E_κ^* = 2 e^{-κ z} A` has zero set `Γ`. (iv) `e^{-κ x} > 0` on `ℝ`, and
   `E_κ(x + s_k) → c[sin π(x-θ) + i cos π(x-θ)] = i c e^{-iπ(x-θ)}`, so 2.7 (b)-(d) run verbatim
   for `E_κ` (`phase_rigidity`, `phase_levels` are stated for `compEκ m κ N`; for `κ = 0` they are the
   statements for `compE`). The theorem also returns `HasDerivAt φ (phaseDeriv E x) x` for all `x`
   (`exists_isPhaseFunction`), which Corollary 2's separation step uses. For `exists_hb_of_density` (no phase clause) `hshift`
   follows from the drifted `hU` with the constant `2C + |κ|/2`.
3. **"We may assume `ω' ≃ 1`" is the delicate step** (it conceals the potential identity of §3.2 and
   a *moment condition*). `ω' = 1 + ψ' - φ_f'/π` is continuous and `→ 1`, but may be `≤ 0` on a
   compact set. Modifying it there changes `U_ω` by a potential of a compactly supported function `h`,
   which is bounded *iff* `∫ h = 0`, up to the linear term `(∫_{|t|>1} h/t dt) Re z`; and
   `U_ω = π Im z + U_ψ - log|f| + (b Re z + c)` with a **non-zero `b` in general** (§3.2). `b` must be
   cancelled by the choice of `h` (§3.3, `exists_modified_density`); otherwise `|E|` is off by
   `e^{b Re z}` and the phase rigidity of (2) fails.
4. **Separation of the zero set** of `Ef + E^*f^*`, needed to apply Theorem 1 (stated for separated
   sequences), is not mentioned in the paper: it follows from `φ_E' |E|² ≲ 1` (M02) (§3.5).
5. **The perturbation step**: the "elementary fact" is only true for finitely many *replacements*
   (not deletions); the index bookkeeping (`γ_n ↔ λ_n` with the *same* integer `n` at both ends) is
   exactly where the single constant `c₀` of the phase clause (the same at `+∞` and `-∞`) is used (§3.4).

Other differences: `A` is `OCS.multF m 0` (contains the factor `e^{-κ z + β}`; the paper's symmetric
product need not converge); `ψ(∞) - ψ(-∞) = ∞` is not needed (§4); `P ↦ -P` is not needed (the sign is
forced, §2.4).

**Constants.** `a, b` are the bounds of `m`; `c₁, c₂, …` denote constants depending only on
`(m, a, b)` and on the constant of `hU`/`hshift`.

---------------------------------------------------------------------------------------------------

## 1. The perturbation lemma (`Perturbation.lean`)

### 1.0 Upstream interface (declared at the top of the file, identical to M01's)

`MemPW.mul_div_sub`, `pwNormSq_ne_top`, `IsSepBy`, `plancherelPolya`, `sampleSum_union_le`,
`pw_normal_family` (all with the statements of `FourierFrames/PW/*.lean`).

### 1.1 Elementary facts

```lean
theorem sampleSum_mono {Λ₁ Λ₂ : Set ℝ} (h : Λ₁ ⊆ Λ₂) (f : ℂ → ℂ) :
    sampleSum Λ₁ f ≤ sampleSum Λ₂ f := by
```
`sampleSum Λ f = ∑' x, Λ.indicator (fun x => ‖f x‖ₑ^2) x` (`tsum_subtype`), then
`ENNReal.tsum_le_tsum` with `Set.indicator_le_indicator_of_subset`.

```lean
theorem sampleSum_singleton (a : ℝ) (f : ℂ → ℂ) : sampleSum {a} f = ‖f (a : ℂ)‖ₑ ^ 2 := by
```
`tsum_unique` / `tsum_singleton` on the subtype `({a} : Set ℝ)` (a `Unique`).

```lean
theorem IsSeparated.isClosed {Λ : Set ℝ} (h : IsSeparated Λ) : IsClosed Λ := by
```
*Proof.* Let `δ` be the separation constant and `x ∈ closure Λ`. Pick `a ∈ Λ` with `|a - x| < δ/2`. If
`x ∉ Λ` then `r := |a - x| > 0`; pick `b ∈ Λ` with `|b - x| < min(δ/2, r)`; then `b ≠ a` and
`|a - b| < δ`, contradiction. So `x ∈ Λ`.

```lean
theorem IsSeparated.finite_inter_Icc {Λ : Set ℝ} (h : IsSeparated Λ) (R : ℝ) :
    (Λ ∩ Icc (-R) R).Finite := by
```
*Proof.* `x ↦ ⌊2x/δ⌋` is injective on `Λ` (two points with the same value differ by `< δ/2`, hence are
equal) and takes values in the finite set `ℤ ∩ [-2R/δ - 1, 2R/δ]` on `Λ ∩ [-R, R]`
(`Set.Finite.of_injOn`).

```lean
theorem IsSeparated.insert {Λ : Set ℝ} (h : IsSeparated Λ) {b : ℝ} (hb : b ∉ Λ) :
    IsSeparated (insert b Λ) := by
```
*Proof.* `Λ` is closed (1.1) and `b ∉ Λ`, so `d := infDist b Λ > 0` (`IsClosed.notMem_iff_infDist_pos`,
if `Λ = ∅` the claim is trivial); the new constant is `min δ d`.

```lean
theorem IsSeparated.union_finite {Λ G : Set ℝ} (h : IsSeparated Λ) (hG : G.Finite) :
    IsSeparated (Λ ∪ G) := by
```
*Proof.* Induction on `G` (`Set.Finite.induction_on`), using `insert` (inserting a point already in
the set changes nothing).

### 1.2 Replacing one point

```lean
theorem isSampling_replace_point (hPW : PaleyWienerThm) {Γ : Set ℝ} (hsep : IsSeparated Γ)
    (hs : IsSampling Γ) {a b : ℝ} (ha : a ∈ Γ) (hb : b ∉ Γ) :
    IsSampling (insert b (Γ \ {a})) := by
```

*Proof.* Put `Γ' = insert b (Γ \ {a})`. It is separated (`IsSepBy.mono` and `IsSeparated.insert`,
`b ∉ Γ \ {a}`), so by `plancherelPolya` the upper bound holds with a constant `B'` depending on its
separation constant. Let `A > 0` be the lower constant of `Γ`.

*Lower bound by contradiction.* Suppose `∀ n, ∃ f_n ∈ PW`, `sampleSum Γ' f_n < (n+1)⁻¹ pwNormSq f_n`.
Then `0 < pwNormSq f_n < ∞` (if it were `0`, `f_n = 0` on `ℝ`, so the strict inequality `0 < 0`
fails; `pwNormSq_ne_top`), and after multiplying by a constant (`MemPW.const_mul`) we may assume
`pwNormSq f_n = 1`, `sampleSum Γ' f_n → 0`. By `pw_normal_family` a subsequence converges locally
uniformly to some `g ∈ PW`. For each `p ∈ Γ'`, `|f_n(p)|² ≤ sampleSum Γ' f_n → 0`, so `g(p) = 0`.

*Case `g ≠ 0`.* Let `h(z) = dslope g b z · (z - a)`; since `g(b) = 0` (`b ∈ Γ'`), `h ∈ PW`
(`MemPW.mul_div_sub`). For `γ ∈ Γ \ {a}`: `γ ≠ b` (as `b ∉ Γ`), so `dslope g b γ = g(γ)/(γ - b) = 0`
and `h(γ) = 0`; and `h(a) = dslope g b a · 0 = 0`. So `h` vanishes on `Γ`, hence
`A · pwNormSq h ≤ sampleSum Γ h = 0`, `pwNormSq h = 0`, `h = 0` on `ℝ`, `h ≡ 0` (identity theorem), and
`g(z) = 0` for `z ∉ {a, b}`, `g ≡ 0`: contradiction.

*Case `g = 0`.* Then `f_n(a) → 0`. Since `Γ ⊆ (Γ \ {a}) ∪ {a}` and `Γ \ {a} ⊆ Γ'`,
`A = A · pwNormSq f_n ≤ sampleSum Γ f_n ≤ sampleSum Γ' f_n + |f_n(a)|² → 0` (`sampleSum_mono`,
`sampleSum_union_le`, `sampleSum_singleton`): contradiction. ∎

### 1.3 Replacing finitely many points

```lean
theorem isSampling_of_replace_finite (hPW : PaleyWienerThm) {Γ Γ' : Set ℝ}
    (hsep : IsSeparated Γ) (hs : IsSampling Γ)
    (hD : (Γ \ Γ').Finite) (hD' : (Γ' \ Γ).Finite) (hcard : (Γ \ Γ').ncard = (Γ' \ Γ).ncard) :
    IsSampling Γ' := by
```

*Proof.* Induction on `n = (Γ \ Γ').ncard`. If `n = 0` both difference sets are empty (equal
cardinalities, finite), so `Γ = Γ'`. Otherwise pick `a ∈ Γ \ Γ'`, `b ∈ Γ' \ Γ` and put
`Γ₁ = insert b (Γ \ {a})`: it is separated and sampling by 1.2 (`b ∉ Γ`), and
`Γ₁ \ Γ' = (Γ \ Γ') \ {a}`, `Γ' \ Γ₁ = (Γ' \ Γ) \ {b}` (use `a ∉ Γ'`, `b ∉ Γ`), both finite of
cardinality `n - 1`. Apply the induction hypothesis to `Γ₁`. ∎

*Remark.* The cardinality condition cannot be dropped: `ℤ \ {0}` is not sampling.

### 1.4 The perturbation lemma

```lean
theorem IsSampling.of_perturbation (hPW : PaleyWienerThm) (hDS : DSPerturbation) {Γ : Set ℝ}
    (hsep : IsSeparated Γ) (hs : IsSampling Γ) {δ : ℝ → ℝ}
    (hinj : InjOn (fun x ↦ x + δ x) Γ)
    (hδ : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x ∈ Γ, R ≤ |x| → |δ x| ≤ ε) :
    IsSampling ((fun x ↦ x + δ x) '' Γ) := by
```

*Proof.* Let `η > 0` be the separation constant of `Γ` and `L` the constant of `hDS` for `Γ`. Choose
`R₁` with `|δ x| ≤ min(L, η/4)` for `x ∈ Γ`, `|x| ≥ R₁` (hypothesis `hδ`). Put `N = Γ ∩ [-R₁, R₁]`
(finite, 1.1), `M = {y + δ y : y ∈ Γ, |y| > R₁}`, `G = {x + δ x : x ∈ N}` (finite, `|G| = |N|` by
`hinj`), and let `δ₁ x = 0` for `|x| ≤ R₁`, `δ₁ x = δ x` otherwise.

* `|δ₁| ≤ L` and `x ↦ x + δ₁ x` is injective on `Γ`: far–far by `hinj`; near–near trivial; if `x` is
  near and `y` far with `x = y + δ y`, then `|x - y| ≤ η/4 < η` and `x ≠ y` (`|x| ≤ R₁ < |y|`),
  contradicting separation.
* `Γ₁ := {x + δ₁ x} = N ∪ M` is `η/2`-separated (far–far: `η - 2·η/4`; near–far: `η - η/4`), and
  sampling by `hDS` (`hsep`, `hs`).
* `Γ' := {x + δ x : x ∈ Γ} = M ∪ G`. It is separated: `M` is `η/2`-separated, hence closed, `G` is
  finite and `G ∩ M = ∅` (injectivity), so `IsSeparated.union_finite`.
* `Γ₁ \ Γ' = N \ G` (as `N ∩ M = ∅`) and `Γ' \ Γ₁ = G \ N` (as `G ∩ M = ∅`), both finite, and
  `|N \ G| = |N| - |N ∩ G| = |G| - |N ∩ G| = |G \ N|`.

By `isSampling_of_replace_finite`, `Γ'` is sampling. ∎

(The three declared lemmas `isSampling_replace_point`, `isSampling_of_replace_finite` and the
separation lemmas are used only here.)

---------------------------------------------------------------------------------------------------

## 2. The construction `E = A - iB` (`Construction.lean`)

Throughout `hw : OCS.IsMultWeight m a b` (`m` measurable, `0 < a ≤ m ≤ b`), `γ_j = OCS.multBary m j`,
`x_j = OCS.multPt m j` (so `M(x_j) = j`, `M = OCS.multPrim m`, `I_j = [x_j, x_{j+1}]`, `∫_{I_j} m = 1`,
`γ_j = ∫_{I_j} t m`), `U = OCS.multU m 0`, `A = OCS.multF m 0` (`genA m`), `Γ = {γ_j}`
(`OCS.multGamma m`), `Γ_ℂ = OCS.multGammaC m`.

Facts about `A` from the vendored library (all proved there):
* `A` entire (`differentiable_multF`), `A(z̄) = conj A(z)` (`multF_conj`), zero set exactly `Γ`
  (`multF_eq_zero_iff`), zeros simple (`A = e^{-κz+β} · canonicalProd`, `deriv_canonicalProd_ne_zero`);
  `0 ∉ Γ`, `Γ` separated, `γ_j` strictly increasing (`strictMono_multBary`).
* Estimate (2): `c₁ dist(z, Γ) ≤ |A| e^{-U} ≤ c₂ dist(z, Γ)` for `|Im z| ≤ 1`.
* Estimate (3): for `Im z ≠ 0`, `A = e^{L}` with `|L - U - iV| ≤ π/(2a|Im z|)`; hence
  `e^{-π/(2a)} e^{U} ≤ |A| ≤ e^{π/(2a)} e^{U}` for `|Im z| ≥ 1` (`|A| = e^{Re L}`, `exp_multL`).
* `U(z̄) = U(z)` (`multU_conj`).

### 2.1 Comparability of `A` on all of ℂ

```lean
theorem norm_genA_comparable (hw : OCS.IsMultWeight m a b) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℂ,
      c₁ * Real.exp (OCS.multU m 0 z) * min 1 (infDist z (OCS.multGammaC m)) ≤ ‖genA m z‖ ∧
      ‖genA m z‖ ≤ c₂ * Real.exp (OCS.multU m 0 z) * min 1 (infDist z (OCS.multGammaC m)) := by
```

*Proof.* For `|Im z| ≥ 1`, `dist(z, Γ) ≥ 1`, so `min(1, ·) = 1` and the claim is (3). For `|Im z| ≤ 1`,
`dist(z, Γ) ≤ 1 + 1/a` (the gaps of `Γ` are `≤ 2/a`: `γ_{j+1} - γ_j ≤ |I_j| + |I_{j+1}|`,
`|I_j| ≤ 1/a` by `multPt_succ_sub_bounds`), hence `min(1, d) ≥ d/(1 + 1/a)` and `≤ d`; combine with (2). ∎

```lean
theorem norm_genA_comparable_of_hU (hw : OCS.IsMultWeight m a b) {κ : ℝ}
    (hU : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℂ,
      c₁ * Real.exp (Real.pi * |z.im| + κ * z.re) * min 1 (infDist z (OCS.multGammaC m)) ≤
        ‖genA m z‖ ∧
      ‖genA m z‖ ≤
        c₂ * Real.exp (Real.pi * |z.im| + κ * z.re) * min 1 (infDist z (OCS.multGammaC m)) := by
```

*Proof.* `hU` on `Im z ≥ 0` and `U(z̄) = U(z)` (`Re z̄ = Re z`) give `|U(z) - π|Im z| - κ Re z| ≤ C`
on ℂ; use `e^{U} ≃ e^{π|y| + κ Re z}` in 2.1. ∎

### 2.2 Gaps of `Γ`, position of the barycentre

Let `ε > 0`. Since `m → 1` there is `X` with `|m - 1| ≤ ε` on `|t| ≥ X`, and `|x_j| ≥ |j|/b → ∞`
(`abs_multPt_ge`), so for `|j|` large `I_j ⊂ {|t| ≥ X}` (`|I_j| ≤ 1/a`).

* Length: `1 = ∫_{I_j} m ∈ (1 ± ε)|I_j|`, so `|I_j| ∈ [(1+ε)^{-1}, (1-ε)^{-1}]`.
* Barycentre: `γ_j - x_j = ∫_{I_j} (t - x_j) m ∈ (1 ± ε)|I_j|²/2` (`multBary_sub_multPt`), so
  `|γ_j - x_j - 1/2| ≤ ε'(ε)` with `ε' → 0`.
* `M(γ_j) - j = ∫_{x_j}^{γ_j} m ∈ (1 ± ε)(γ_j - x_j)`, so `|M(γ_j) - j - 1/2| ≤ ε''`.
* `γ_{j+1} - γ_j = (γ_{j+1} - x_{j+1}) + |I_j| - (γ_j - x_j) → 1`.
* `M(x + τ) - M(x) = ∫_x^{x+τ} m → τ` uniformly for `|τ| ≤ T` as `|x| → ∞`.

```lean
theorem tendsto_multBary_sub_multPt (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    Tendsto (fun j : ℤ ↦ OCS.multBary m j - OCS.multPt m j) cofinite (𝓝 (1 / 2)) := by
```
```lean
theorem tendsto_multBary_succ_sub (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    Tendsto (fun j : ℤ ↦ OCS.multBary m (j + 1) - OCS.multBary m j) cofinite (𝓝 1) := by
```
```lean
theorem tendsto_multPrim_multBary (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    Tendsto (fun j : ℤ ↦ OCS.multPrim m (OCS.multBary m j) - (j + 1 / 2)) cofinite (𝓝 0) := by
```
```lean
theorem tendsto_multPrim_sub (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) (T : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ |x| → ∀ τ : ℝ, |τ| ≤ T →
      |OCS.multPrim m (x + τ) - OCS.multPrim m x - τ| ≤ ε := by
```
```lean
theorem exists_gap_index (hw : OCS.IsMultWeight m a b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    ∃ N : ℕ, ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j := by
```

(`exists_gap_index` from `tendsto_multBary_succ_sub`: eventually `> 1/2`; a cofinite set of `ℤ` is
`{|j| ≥ N}` up to a finite set.)

### 2.3 The companion `B`

Fix `N` as in `exists_gap_index`. For `|j| ≥ N`, `β_j := γ_j + 1/2 ∈ (γ_j, γ_{j+1})` (strictly: the gap
exceeds `1/2`); for `|j| < N`, `β_j := (γ_j + γ_{j+1})/2`. Thus

&nbsp;&nbsp;&nbsp;&nbsp;`γ_j < β_j < γ_{j+1}` for **all** `j ∈ ℤ`. (interlacing)

(In the file these definitions live in a `section` with `variable (m : ℝ → ℝ)`, so `m` is an explicit
argument.)

```lean
def compBeta (N : ℕ) (j : ℤ) : ℝ :=
  if |j| < N then (OCS.multBary m j + OCS.multBary m (j + 1)) / 2 else OCS.multBary m j + 1 / 2
```
```lean
def compRemoved (N : ℕ) : List ℂ :=
  ((Finset.Ioo (-(N : ℤ)) N).toList).map fun j ↦ ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)
```
```lean
abbrev genA (z : ℂ) : ℂ := OCS.multF m 0 z
```
```lean
def compB (N : ℕ) (z : ℂ) : ℂ :=
  divZeros (compRemoved m N) (fun w ↦ genA m (w - 1 / 2)) z *
    ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ))
```
```lean
def compE (N : ℕ) (z : ℂ) : ℂ :=
  genA m z - Complex.I * compB m N z
```

`divZeros`, `prodLin` (iterated `dslope`, the same device as M01's `MemPW.mul_div_sub`):

```lean
def prodLin (l : List ℂ) (z : ℂ) : ℂ :=
  (l.map fun t ↦ z - t).prod
```
```lean
def divZeros : List ℂ → (ℂ → ℂ) → ℂ → ℂ
  | [], F => F
  | a :: l, F => divZeros l (dslope F a)
```
```lean
theorem differentiable_divZeros (l : List ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (divZeros l F) := by
```
```lean
theorem divZeros_mul_prodLin {l : List ℂ} (hl : l.Nodup) {F : ℂ → ℂ} (hF : ∀ t ∈ l, F t = 0)
    (z : ℂ) : divZeros l F z * prodLin l z = F z := by
```
```lean
theorem divZeros_conj {l : List ℂ} (hl : ∀ t ∈ l, t.im = 0) {F : ℂ → ℂ}
    (hF : ∀ z, F (conj z) = conj (F z)) (z : ℂ) :
    divZeros l F (conj z) = conj (divZeros l F z) := by
```

*Proofs.* `differentiable_divZeros`: induction on `l`; `dslope F a` is entire when `F` is
(`differentiableOn_dslope` on `univ`). `divZeros_mul_prodLin`: induction; `dslope F a z · (z - a) = F z - F a
= F z` by `sub_smul_dslope` (`F a = 0`), and `dslope F a` vanishes at every other `t ∈ l`, since
`(t - a) dslope F a t = F t - F a = 0`, `t ≠ a`. `divZeros_conj`: `dslope` commutes with `conj`-symmetry
when `a` is real (`a.im = 0`): `dslope F a (z̄) = conj (dslope F a z)` for `z ≠ a`, by continuity at `a`.

Consequences (all about `B := compB m N`):

```lean
theorem differentiable_compB (hw : OCS.IsMultWeight m a b) (N : ℕ) :
    Differentiable ℂ (compB m N) := by
```
```lean
theorem compB_conj (hw : OCS.IsMultWeight m a b) (N : ℕ) (z : ℂ) :
    compB m N (conj z) = conj (compB m N z) := by
```
```lean
theorem compBeta_interlace (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) (j : ℤ) :
    OCS.multBary m j < compBeta m N j ∧ compBeta m N j < OCS.multBary m (j + 1) := by
```
```lean
theorem compB_eq_zero_iff (hw : OCS.IsMultWeight m a b) (N : ℕ) (z : ℂ) :
    compB m N z = 0 ↔ ∃ j : ℤ, z = (compBeta m N j : ℂ) := by
```
```lean
theorem compB_mul_Q (hw : OCS.IsMultWeight m a b) (N : ℕ) (z : ℂ) :
    compB m N z * ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)) =
      genA m (z - 1 / 2) * ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ)) := by
```

*Proofs.* `compB_mul_Q`: `divZeros_mul_prodLin` applied to `F(w) = A(w - 1/2)`, which vanishes at the
points of `compRemoved` (`γ_j + 1/2 - 1/2 = γ_j ∈ Γ`), and these points are pairwise distinct since
`j ↦ γ_j` is injective.

*Zero set of `B`.* `D := divZeros (compRemoved m N) (A(· - 1/2))` is entire with `D · Q = A(· - 1/2)`
(`Q = prodLin (compRemoved m N)`). The zeros of `A(· - 1/2)` are the simple zeros `γ_k + 1/2`; off the
roots of `Q`, `D(z) = 0 ↔ A(z - 1/2) = 0`; at a root `a_j = γ_j + 1/2` (`|j| < N`) the simple zero of
`A(· - 1/2)` is cancelled by `Q`, so `D(a_j) = A'(γ_j)/∏_{i ≠ j}(a_j - a_i) ≠ 0` (here the `a_i` are
distinct and `A'(γ_j) ≠ 0`). Thus the zero set of `D` is `{γ_k + 1/2 : |k| ≥ N}`, and the zero set of
`B = D · P` is `{γ_k + 1/2 : |k| ≥ N} ∪ {β_j : |j| < N} = {β_k : k ∈ ℤ}` (this holds even if some
`β_j = a_j`; no coincidence has to be excluded). All these zeros are simple (they lie in the disjoint
open intervals `(γ_k, γ_{k+1})`, one per interval, and each is a simple zero of one factor and not a zero
of the other: `P(γ_k + 1/2) ≠ 0` for `|k| ≥ N` because `γ_k + 1/2 ∈ (γ_k, γ_{k+1})` and `β_j ∈ (γ_j,
γ_{j+1})`, `j ≠ k`). `compBeta_interlace`: for `|j| ≥ N`, `β_j - γ_j = 1/2 > 0` and
`γ_{j+1} - β_j = (γ_{j+1} - γ_j) - 1/2 > 0`; for `|j| < N`, `β_j` is the midpoint of `γ_j < γ_{j+1}`.

### 2.4 `E = A - iB ∈ \overline{HB}` (replaces Meĭman's theorem)

**Lemma H (polynomial Hermite–Biehler).**

```lean
theorem im_prod_div_pos {n : ℕ} {a b : Fin (n + 1) → ℝ}
    (hab : ∀ k, a k < b k) (hba : ∀ k : Fin n, b k.castSucc < a k.succ) {z : ℂ} (hz : 0 < z.im) :
    0 < (∏ k, ((z - b k) / (z - a k))).im := by
```

*Proof.* For `z ∈ ℂ₊` and real `t` put `θ(t) = arg(z - t) ∈ (0, π)`; it is strictly *increasing* in `t`
(`z - t = (x - t) + iy`, `θ = arccot((x - t)/y)`). `arg((z - b_k)/(z - a_k)) = θ(b_k) - θ(a_k) ∈ (0,π)`
for each `k`, and, summing and using `a_0 < b_0 < a_1 < … < a_n < b_n`,

&nbsp;&nbsp;`S := ∑_k (θ(b_k) - θ(a_k)) = θ(b_n) - θ(a_0) - ∑_{k<n} (θ(a_{k+1}) - θ(b_k)) < θ(b_n) - θ(a_0) < π`,
and `S > 0` termwise. The product has argument `S ∈ (0, π)` (the arguments add exactly, no wrap-around,
since `S ∈ (0,π)`), so `Im > 0`. (In Lean: `Complex.arg_mul` iterated, or `Complex.arg` of a finite
product via induction with the invariant "partial sum of args in `(0, π)`", or directly:
`∏ w_k = |∏ w_k| e^{iS}`.) ∎

**The pair of real polynomials.** For `R ≥ N`:

```lean
def polyA (m : ℝ → ℝ) (R : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.Icc (-(R : ℤ)) R, (1 - z / (OCS.multBary m j : ℂ))
```
```lean
def polyB (m : ℝ → ℝ) (N R : ℕ) (z : ℂ) : ℂ :=
  (∏ j ∈ Finset.Ioo (-(N : ℤ)) N, ((-1 / (OCS.multBary m j : ℂ)) * (z - (compBeta m N j : ℂ)))) *
    ∏ j ∈ Finset.Icc (-(R : ℤ)) R \ Finset.Ioo (-(N : ℤ)) N,
      (1 - (z - 1 / 2) / (OCS.multBary m j : ℂ))
```
```lean
def polyExp (m : ℝ → ℝ) (R : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc (-(R : ℤ)) R, 1 / OCS.multBary m j) - OCS.multKappa m
```
```lean
theorem polyB_mul_Q (hw : OCS.IsMultWeight m a b) {N R : ℕ} (hNR : N ≤ R) (z : ℂ) :
    polyB m N R z * ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)) =
      polyA m R (z - 1 / 2) * ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ)) := by
```

`A_R = ∏_{|j| ≤ R} (1 - z/γ_j) = c_R ∏ (z - γ_j)` with `c_R = ∏ (-1/γ_j)`. For `R ≥ N`,
`B_R = c_R ∏_{|j| ≤ R} (z - β_j)` (for `|j| ≥ N`, `1 - (z - 1/2)/γ_j = (-1/γ_j)(z - γ_j - 1/2)`; for
`|j| < N` the factors `(-1/γ_j)(z - β_j)` are written explicitly). So

&nbsp;&nbsp;`B_R/A_R = ∏_{|j| ≤ R} (z - β_j)/(z - γ_j)`,

and the zeros `γ_{-R} < β_{-R} < γ_{-R+1} < … < γ_R < β_R` interlace as in Lemma H (`a_k = γ_{k-R}`,
`b_k = β_{k-R}`). Hence `Im (B_R/A_R) > 0` on ℂ₊, and for every `λ > 0`:

```lean
theorem isHB_polyA_sub_polyB (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) {R : ℕ}
    (hNR : N ≤ R) {lam : ℝ} (hlam : 0 < lam) :
    IsHB (fun z ↦ polyA m R z - Complex.I * lam * polyB m N R z) := by
```

*Proof.* `A_R, B_R` are real polynomials, so `(A_R - iλB_R)^*(z) = A_R(z) + iλB_R(z)` and
`|P(z)|² - |P^*(z)|² = 4|A_R(z)|² Im(λ B_R/A_R)(z)`, where `P = A_R - iλB_R`:
`|A - iB'|² - |A + iB'|² = -4 Im(A \bar{B'}) = 4|A|² Im(B'/A)` for real-symmetric `A`, `B'` — more
precisely `|A - iB'|² = |A|² + |B'|² - 2 Im(A \bar B')`, `|A + iB'|² = |A|²+|B'|² + 2 Im(A \bar B')`,
`Im(B'/A) = Im(B' \bar A)/|A|² = -Im(A \bar B')/|A|²`. `A_R ≠ 0` on ℂ₊ (real zeros), so
`|P(z̄)| = |A_R + iλB_R| < |P(z)|`; in particular `P(z) ≠ 0` for `Im z > 0` (else `|P(z̄)| < 0`). ∎

**The limit.**

```lean
theorem tendsto_polyA (hw : OCS.IsMultWeight m a b) :
    TendstoLocallyUniformly
      (fun (R : ℕ) (z : ℂ) ↦ Complex.exp (OCS.multBeta m 0 + polyExp m R * z) * polyA m R z)
      (genA m) atTop := by
```
```lean
theorem tendsto_polyB (hw : OCS.IsMultWeight m a b) (N : ℕ) :
    TendstoLocallyUniformly
      (fun (R : ℕ) (z : ℂ) ↦ Complex.exp (OCS.multBeta m 0 + polyExp m R * z) *
        Real.exp (-polyExp m R / 2) * polyB m N R z)
      (compB m N) atTop := by
```

*Proofs.* `A = e^{-κz + β} ∏_{γ ∈ Γ} (1 - z/γ) e^{z/γ}` (`multF`), and the product converges
locally uniformly along finsets (`hasProdLocallyUniformlyOn_canonicalProd`, applied through the
enumeration `multGammaEquiv`); along the cofinal sequence of finsets `Icc (-R) R`,
`∏_{|j| ≤ R} (1 - z/γ_j) e^{z/γ_j} = A_R(z) e^{S_R z}`, `S_R = ∑_{|j| ≤ R} 1/γ_j`. Hence
`e^{β + (S_R - κ) z} A_R(z) → A(z)`, i.e. `tendsto_polyA` (`polyExp = S_R - κ`). For `B`:
off the roots of `Q`, `e^{β + c_R z} e^{-c_R/2} B_R(z) = [e^{β + c_R(z - 1/2)} A_R(z - 1/2)] P(z)/Q(z)
→ A(z - 1/2) P/Q = B(z)` (use `polyB_mul_Q`, `compB_mul_Q`); the functions on the left are entire, and
`B` is entire; convergence near a root `a` of `Q` follows from uniform convergence on a small circle
about `a` (it avoids the roots) and the maximum principle
(`Complex.norm_le_of_forall_mem_frontier_norm_le` applied to the difference). ∎

**Theorem.**

```lean
theorem isHB_compE (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) :
    IsHB (compE m N) := by
```

*Proof.* `E_R(z) := e^{β + c_R z}(A_R - i e^{-c_R/2} B_R)(z)` is in `\overline{HB}`
(`isHB_polyA_sub_polyB` with `λ = e^{-c_R/2} > 0`, `isHB_cexp_real_linear`, `IsHB.mul`). By
`tendsto_polyA`, `tendsto_polyB`, `E_R → A - iB = E` locally uniformly. `E ≢ 0`: `E(x) = A(x) - iB(x) ≠ 0` at any real `x ∉ Γ` (`A(x)` is real and non-zero).
`IsHB.of_tendstoLocallyUniformly` (Hurwitz) gives `E ∈ \overline{HB}`. ∎

*Remark (the sign).* No sign choice (`P ↦ -P`) is needed: `B_R/A_R → 1` at `∞` and the zeros lie to the
right of the poles, which is exactly the arrangement of Lemma H with `Im > 0`. For the opposite
relative position (`β_j < γ_j`) one would take `E = A + iB`.

```lean
theorem fstar_compE (hw : OCS.IsMultWeight m a b) (N : ℕ) (z : ℂ) :
    fstar (compE m N) z = genA m z + Complex.I * compB m N z := by
```

(`E^*(z) = conj E(z̄) = conj A(z̄) + i conj B(z̄) = A(z) + iB(z)` because `A, B` are real-symmetric
(`multF_conj`, `compB_conj`).) In particular `E + E^* = 2A` and `E z + fstar E z = 0 ↔ A z = 0 ↔ z ∈ Γ`.

```lean
theorem norm_compE_sq_bounds {N : ℕ} (hE : IsHB (compE m N)) (hw : OCS.IsMultWeight m a b)
    {z : ℂ} (hz : 0 ≤ z.im) :
    ‖genA m z‖ ^ 2 + ‖compB m N z‖ ^ 2 ≤ ‖compE m N z‖ ^ 2 ∧
      ‖compE m N z‖ ^ 2 ≤ 2 * (‖genA m z‖ ^ 2 + ‖compB m N z‖ ^ 2) := by
```

*Proof.* On `Im z ≥ 0`, `|E^*(z)| ≤ |E(z)|` (`IsHB.norm_fstar_le`, trivial on `ℝ`), and
`|E|² + |E^*|² = 2(|A|² + |B|²)` (parallelogram law), hence `|A|²+|B|² ≤ |E|² ≤ 2(|A|²+|B|²)`. ∎

### 2.5 Comparability of `B`

```lean
theorem norm_compB_comparable (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℂ, 0 ≤ z.im →
      c₁ * Real.exp (OCS.multU m 0 (z - 1 / 2)) *
          min 1 (infDist z (Set.range fun j : ℤ ↦ ((compBeta m N j : ℝ) : ℂ))) ≤
        ‖compB m N z‖ ∧
      ‖compB m N z‖ ≤ c₂ * Real.exp (OCS.multU m 0 (z - 1 / 2)) *
          min 1 (infDist z (Set.range fun j : ℤ ↦ ((compBeta m N j : ℝ) : ℂ))) := by
```

*Proof.* `A_1(z) = A(z - 1/2)` satisfies 2.1 with `Γ + 1/2` and `U(· - 1/2)` (`Im (z - 1/2) = Im z`).
Let `Σ` be the finite set `{β_j, γ_j + 1/2 : |j| < N}` and `ρ₀` so large that `|z| ≥ ρ₀` implies
`dist(z, Σ) ≥ 1`, `|P/Q - 1| ≤ 1/2`. For `|z| ≥ ρ₀`: `|B| = |A_1| |P/Q| ≃ |A_1|`, and
`min(1, dist(z, Γ + 1/2)) = min(1, dist(z, Γ_B))` (the nearest points differ only inside `Σ`-balls of
radius `≥ 1`, where both minima are `1`). For `|z| ≤ ρ₀`, `Im z ≥ 0`: `B` is entire with simple zeros
`β_j` only, so `|B(z)|/dist(z, Γ_B)` is a positive continuous function on the compact set (limit
`|B'(β_j)| > 0` at the zeros), bounded above and below; and `e^{U(z - 1/2)}` is bounded above and
below there (`abs_multU_le_of_bdd`, §3.1). ∎

### 2.6 The main construction

```lean
theorem exists_hb_of_density (hm : Measurable m) (ha : 0 < a) (hlow : ∀ t, a ≤ m t)
    (hup : ∀ t, m t ≤ b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1))
    (hshift : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 (z - 1 / 2) - OCS.multU m 0 z| ≤ C) :
    ∃ E : ℂ → ℂ, IsHB E ∧ (∀ x : ℝ, E x ≠ 0) ∧
      (∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
        c * Real.exp (OCS.multU m 0 z) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (OCS.multU m 0 z)) ∧
      (∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ OCS.multGamma m, z = (γ : ℂ)) := by
```

*Proof.* Take `N` from `exists_gap_index`, `E = compE m N` (`isHB_compE`). Real zeros: `E(x) = A(x) -
iB(x)` with `A(x), B(x)` real, and `A`, `B` have disjoint zero sets (`β_j ∈ (γ_j, γ_{j+1})`), so `E(x) ≠ 0`.
Zero set of `E + E^*`: `2A`, zero set `Γ`.

*Upper bound.* By `norm_compE_sq_bounds`, `|E| ≤ |A| + |B|`; `|A| ≤ c₂ e^{U}` and
`|B| ≤ c₂' e^{U(z - 1/2)} ≤ c₂' e^{C} e^{U(z)}` (2.1, 2.5, `hshift`).

*Lower bound.* `|E|² ≥ |A|² + |B|² ≥ c e^{2U} (min(1, d_Γ)² + e^{-2C} min(1, d_B)²)`, where `d_Γ =
dist(z, Γ)`, `d_B = dist(z, Γ_B)`. By the triangle inequality `d_Γ + d_B ≥ η₀ := dist(Γ, Γ_B) =
inf_j min(β_j - γ_j, γ_{j+1} - β_j)`, and `η₀ > 0`: for `|j| ≥ N` these are `1/2` and `gap - 1/2 → 1/2`,
for `|j| < N` finitely many positive numbers. So `max(min(1, d_Γ), min(1, d_B)) ≥ min(1, η₀/2)`. ∎

### 2.7 Phase asymptotics (under `hU`)

From now on `hU : ∃ C, ∀ z, 0 ≤ Im z → |U z - π Im z - κ Re z| ≤ C` for a fixed real `κ` (so `hshift`
holds with `2C + |κ|/2`; `κ = 0` is the case of the first version), and
`E = compE m N`, `B = compB m N`, `R(z) = P(z)/Q(z) = B(z)/A(z - 1/2)`.

**(a) Limits of translates of `A`.**

```lean
theorem genA_translate_limit (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) {κ : ℝ}
    (hU : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C)
    {s : ℕ → ℝ} (hs : Tendsto (fun k ↦ |s k|) atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c θ : ℝ, c ≠ 0 ∧
      TendstoLocallyUniformly
        (fun k z ↦ genA m (z + s (φ k)) * Complex.exp (-((κ * s (φ k) : ℝ) : ℂ)))
        (fun z ↦ (c : ℂ) * Complex.exp ((κ : ℂ) * z) * Complex.sin (Real.pi * (z - θ))) atTop := by
```

*Proof.* Let `s_k → ±∞` (`|s_k| → ∞`).

*Compactness.* `F_k(z) = A(z + s_k) e^{-κ s_k}` (for `κ = 0`: `A(z + s_k)`) is entire, real on `ℝ`, with
`|F_k(z)| ≤ c₂ e^{π|Im z| + κ Re z}` (2.1 under `hU`, `min(1, ·) ≤ 1`; the factor `e^{κ (x + s_k)} e^{-κ s_k}
= e^{κ x}` is locally bounded, and `F_k(z) e^{-κ z}` is bounded by `c₂ e^{π|Im z|}`), hence
`G_k(z) := F_k(z) e^{-κ z} = A_κ(z + s_k)` is in `𝓑_π` with uniform bound `c₂` on `ℝ`
(`OCS.memBernstein_of_norm_le`). By `OCS.MemBernstein.exists_subseq_tendstoLocallyUniformly` a
subsequence converges locally uniformly to an entire `A_∞`, real on `ℝ`.

*The zero set of the limit.* Let `j_k = max{j : γ_j ≤ s_k}`, `t_k = γ_{j_k} - s_k ∈ (-(γ_{j_k+1} -
γ_{j_k}), 0]`; `|j_k| → ∞`, the gaps tend to `1` (2.2), so after passing to a subsequence
`t_k → θ ∈ [-1, 0]`, and for fixed `n ∈ ℤ`,
`γ_{j_k+n} - s_k = t_k + ∑_{i<n}(γ_{j_k+i+1} - γ_{j_k+i}) → θ + n`. Therefore, for every fixed `z`,
`dist(z, Γ - s_k) → dist(z, θ + ℤ) =: d_θ(z)` (locally uniformly in `z`).

*Two-sided estimate for the limit.* Pass to the limit in 2.1 (applied to `z + s_k`):

&nbsp;&nbsp;`c₁ e^{π|y|} min(1, d_θ(z)) ≤ |A_∞(z)| ≤ c₂ e^{π|y|} min(1, d_θ(z))` for all `z`. (★)

*Identification.* (We write the argument for `κ = 0`; for general `κ` apply it to `G_k = A_κ(· + s_k)`,
whose limit is `c sin π(z - θ)`, and then `F_k = G_k e^{κ z} → c e^{κ z} sin π(z - θ)`; (★) is stated
for `A_κ`, i.e. with `U - κ Re z`.) `|sin π w| ≥ c₀ e^{π|Im w|} min(1, dist(w, ℤ))` for all `w` with `c₀ > 0` explicit
(for `|Im w| ≥ 1/2`: `|sin π w| ≥ sinh(π|Im w|) ≥ (1 - e^{-π}) e^{π|Im w|}/2`; for `|Im w| < 1/2`:
`|sin π w|² = sin²πx + sinh²πy ≥ 4 dist(x,ℤ)² + π²y² ≥ 4 dist(w,ℤ)²`), and `|sin π w| ≤
e^{π|Im w|}`. Let `Q(z) = A_∞(z)/sin π(z - θ)` off `θ + ℤ`. By (★), `|A_∞(z)| ≤ c₂ e^{π|y|}|z - z₀|`
near each `z₀ ∈ θ + ℤ`, so `A_∞(z₀) = 0` and `Q` is bounded near `z₀` and extends holomorphically
(`Complex.differentiableOn_update_limUnder_of_bddAbove`). By (★) and the bound on `sin`:
`|Q| ≤ c₂/c₀` on ℂ. By Liouville (`Differentiable.apply_eq_apply_of_bounded`) `Q ≡ c`. `c ≠ 0` because
`|A_∞(θ + 1/2)| ≥ c₁ min(1, 1/2) > 0` by (★); `c` is real because `A_∞` and `sin π(x - θ)` are
real on `ℝ`. ∎

**(b) Limits of `E` and the rigidity of the phase.**

```lean
theorem phase_rigidity (hw : OCS.IsMultWeight m a b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) {κ : ℝ}
    (hU : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C) {N : ℕ}
    {φ : ℝ → ℝ} (hφ : IsPhaseFunction (compEκ m κ N) φ) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ s : ℝ, X ≤ |s| → ∀ τ : ℝ, |τ| ≤ 2 →
      |φ (s + τ) - φ s - Real.pi * τ| ≤ ε := by
```

*Proof.* Let `φ` be a phase function of `E`. Suppose the claim fails for some `ε > 0`: there are
`s_k` with `|s_k| → ∞` and `τ_k ∈ [-2, 2]` with `|φ(s_k + τ_k) - φ(s_k) - πτ_k| > ε`. Apply (a) to
`s_k` and pass to a subsequence with `A(z + s_k) → c sin π(z - θ)`. Since `R(z + s_k) → 1` locally
uniformly (`R` is a quotient of monic polynomials of the same degree), `B(z + s_k) = A(z + s_k - 1/2)
R(z + s_k) → c sin π(z - θ - 1/2) = -c cos π(z - θ)`. Hence, locally uniformly on `ℝ`,

&nbsp;&nbsp;`E(x + s_k) → c[sin π(x - θ) + i cos π(x - θ)] = i c e^{-iπ(x - θ)} =: E_∞(x)`, `|E_∞| = |c| ≥ c₁/2`.

So for large `k`, `|E(x + s_k)| ≥ |c|/2` on `[-2, 2]` and the unit vectors
`u_k(x) = E(x + s_k)/|E(x + s_k)|` converge uniformly on `[-2,2]` to `sgn(c) i e^{-iπ(x - θ)}`.
Since `E(x) = |E(x)| e^{-iφ(x)}`, `e^{-i(φ(s_k + x) - φ(s_k))} = u_k(x) \bar{u_k(0)} → e^{-iπx}`
uniformly on `[-2, 2]`. The functions `g_k(x) = φ(s_k + x) - φ(s_k) - πx` are continuous, `g_k(0) = 0`
and `e^{-i g_k} → 1` uniformly; so for large `k`, `|e^{-ig_k(x)} - 1| < 1` forces `g_k(x) ∈ 2πℤ +
(-π/3, π/3)`, and by connectedness and `g_k(0) = 0` (`g_k` stays in `(-π/3, π/3)`) one gets
`g_k → 0` uniformly on `[-2, 2]`. This contradicts the choice of `τ_k`. ∎

(Both `s_k → +∞` and `s_k → -∞` are covered: `(a)` only uses `|s_k| → ∞`.)

**(c) The levels of the phase.**

```lean
theorem phase_levels (hw : OCS.IsMultWeight m a b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) {κ : ℝ}
    (hU : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j)
    {φ : ℝ → ℝ} (hφ : IsPhaseFunction (compEκ m κ N) φ) :
    StrictMono φ ∧ ∃ k₀ : ℤ, ∀ j : ℤ, φ (OCS.multBary m j) = Real.pi / 2 + Real.pi * (j + k₀) := by
```

*Proof.* *Monotone:* `E ∈ \overline{HB}` without real zeros, so `φ' = phaseDeriv E ≥ 0`
(`IsHB.phaseDeriv_nonneg`, `exists_isPhaseFunction`), `φ` nondecreasing. *Strict:* if `φ ≡ α` on an
interval `J`, then on `J` `A = Re E = |E| cos α`, `B = -Im E = |E| sin α`, so
`sin α · A - cos α · B = 0` on `J`, hence on ℂ (identity theorem); `A ≢ 0`, `B ≢ 0` and `A`, `B`
have disjoint non-empty zero sets, so `(\sin α, \cos α) = (0,0)`: impossible. *Onto:* by (b),
`φ(s + 1) - φ(s) ≥ π/2` for `|s| ≥ X`, so `φ → ±∞` at `±∞`. *Levels:* `A(x) = Re E(x) = |E(x)| cos φ(x)`,
so `A(x) = 0 ↔ φ(x) ∈ π/2 + πℤ`. Thus `n ↦ φ^{-1}(π/2 + πn)` and `j ↦ γ_j` are strictly increasing
bijections of `ℤ` onto `Γ`; the composite `σ = γ^{-1}∘φ^{-1}(π/2 + π ·)` is a strictly increasing
bijection of `ℤ`, hence `σ(n+1) = σ(n) + 1` (surjectivity, no gaps) and `σ(n) = n - k₀`, i.e.
`φ(γ_j) = π/2 + π(j + k₀)`. ∎

**(d) The phase asymptotics.** Let `Δ = φ - πM`.
* `Δ(γ_j) = π/2 + π(j + k₀) - πM(γ_j) = πk₀ - π(M(γ_j) - j - 1/2) → πk₀` as `|j| → ∞` (2.2).
* Given `ε > 0`, for `|s| ≥ X` and `|τ| ≤ 2`: `|Δ(s + τ) - Δ(s)| ≤ |φ(s+τ) - φ(s) - πτ| +
  π|M(s + τ) - M(s) - τ| ≤ ε + πε` ((b), 2.2).
* Every `x` lies in some `[γ_j, γ_{j+1})`, with `|j| → ∞` as `|x| → ∞` and `0 ≤ x - γ_j ≤ γ_{j+1} - γ_j ≤ 2`
  for `|j|` large.

Hence `|Δ(x) - πk₀| ≤ |Δ(x) - Δ(γ_j)| + |Δ(γ_j) - πk₀| → 0`: **`φ_E - π M → c₀ := π k₀` at both
`+∞` and `-∞`** (a single `c₀`, essential for §3.4).

```lean
theorem exists_hb_of_density_phase (hm : Measurable m) (ha : 0 < a) (hlow : ∀ t, a ≤ m t)
    (hup : ∀ t, m t ≤ b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1))
    (hU : ∃ κ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C) :
    ∃ E : ℂ → ℂ, IsHB E ∧ (∀ x : ℝ, E x ≠ 0) ∧
      (∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
        c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) ∧
      (∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ OCS.multGamma m, z = (γ : ℂ)) ∧
      ∃ φ : ℝ → ℝ, IsPhaseFunction E φ ∧ (∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x) ∧
        StrictMono φ ∧ ∃ c₀ : ℝ,
        Tendsto (fun x ↦ φ x - Real.pi * OCS.multPrim m x) (cocompact ℝ) (𝓝 c₀) := by
```

*Proof.* Take `E = compEκ m κ N` (`isHB_compEκ`): `E(x) ≠ 0`, `|E| ≃ e^{U - κ Re z} ≃ e^{π Im z}`
by 2.1-2.6 for `A_κ, B_κ` and `hU`; `E + E^* = 2 e^{-κ z} A` has zero set `Γ` (`compEκ_add_fstar`). A phase
function with `φ' = phaseDeriv E` exists (`exists_isPhaseFunction`), is strictly increasing by (c), and
`φ - πM → c₀` by (d) applied to `E_κ`.

---------------------------------------------------------------------------------------------------

## 3. Corollary 2 (`Corollary2.lean`)

Notation. `ψ` admissible (`C¹`, nondecreasing, `ψ' → 0`); hence `ψ'` is continuous, `≥ 0`, bounded.
`f ∈ \overline{HB}`, `g := phaseDeriv f`, hypotheses `hφ : g → 0`, `happ`.

### 3.0 Preliminaries on `f`

* `f(z) ≠ 0` on `Im z ≥ 0`: `|f| ≥ e^{UPsi ψ z - C} > 0` (`happ`). In particular `f` has no real zeros
  and `g = phaseDeriv f` is continuous (`continuous_phaseDeriv`), `g ≥ 0` (`IsHB.phaseDeriv_nonneg`),
  bounded (`g → 0`, continuous), and there is a phase function `φ_f` with `φ_f' = g`
  (`exists_isPhaseFunction`).
* `log|f| = UPsi ψ + O(1)` on `Im z ≥ 0` (`happ`).

### 3.1 Potentials of bounded densities

`OCS.multU g 0` is the potential used throughout; `UPsi ψ = OCS.multU (deriv ψ) 0` (identical integrands).

```lean
theorem UPsi_eq_multU (ψ : ℝ → ℝ) (z : ℂ) : UPsi ψ z = OCS.multU (deriv ψ) 0 z := by
```

```lean
theorem integrable_multU_integrand_of_bdd {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ t, |g t| ≤ M) (z : ℂ) :
    Integrable fun t : ℝ ↦
      (Real.log ‖1 - z / t‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).re) * g t := by
```
*Proof.* For a weight `m' = g + K` with `K = M + 1` (`1 ≤ m' ≤ 2M + 1`, measurable)
`OCS.integrable_multUIntegrand` applies; the integrand for `g` is the integrand for `m'` minus
`K ·` (the integrand for the constant weight `1`).

```lean
theorem multU_add {g h : ℝ → ℝ} (hg : Measurable g) (hh : Measurable h) {M : ℝ}
    (hgM : ∀ t, |g t| ≤ M) (hhM : ∀ t, |h t| ≤ M) (z : ℂ) :
    OCS.multU (fun t ↦ g t + h t) 0 z = OCS.multU g 0 z + OCS.multU h 0 z := by
```
```lean
theorem multU_const_mul (g : ℝ → ℝ) (c : ℝ) (z : ℂ) :
    OCS.multU (fun t ↦ c * g t) 0 z = c * OCS.multU g 0 z := by
```
(`integral_const_mul`; no integrability needed)

```lean
theorem continuous_multU_of_bdd {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    Continuous (OCS.multU g 0) := by
```
*Proof.* `z ↦ ∫ k(z,t) g(t) dt` with `k(z, t) = log|1 - z/t| + 1_{|t|>1} Re(z/t)`: dominated convergence
on compact sets of `z`; the dominating function is `C(1 + |log|t - z_0|| + |log|t||)` for `|t| ≤ T`
(uniformly integrable) and `C|z|²/t²` for `|t| > T`.

```lean
theorem multU_one (z : ℂ) : OCS.multU (fun _ ↦ (1 : ℝ)) 0 z = Real.pi * |z.im| := by
```
*Proof.* Let `z = x + iy`. `U_1(z) = lim_{T→∞} ∫_{-T}^{T} (log|1 - z/t| + 1_{|t|>1}Re(z/t)) dt` (the
integrand is `O(1/t²)` at infinity) and the term `Re(z/t) 1_{|t|>1}` is odd, so it integrates to `0` over
`[-T, T]`. Hence `U_1(z) = lim [ ∫_{-T}^T ½ log((t - x)² + y²) dt - ∫_{-T}^T log|t| dt ]`. With
`∫ ½ log(u² + y²) du = (u/2) log(u² + y²) - u + y arctan(u/y)` (`y ≠ 0`; for `y = 0`
`∫ log|u| du = u log|u| - u`), and `∫_{-T}^T log|t| dt = 2T log T - 2T`:
`(T - x)/2 · log((T - x)² + y²) + (T + x)/2 · log((T+x)² + y²) - 2T + y(arctan((T-x)/y) + arctan((T+x)/y))
- 2T log T + 2T → π|y|` since `(T ∓ x) log|T ∓ x|`-terms cancel against `2T log T` up to `O(1/T)`
(`log(1 ∓ x/T) = ∓x/T + O(T^{-2})`) and `arctan → ±π/2`. For `y = 0` the same computation gives
`(T - x) log|T - x| + (T + x) log(T + x) - 2T log T → 0`. ∎

```lean
theorem abs_multU_le_of_bdd {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    ∃ K : ℝ, ∀ z : ℂ, |OCS.multU g 0 z| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
```
*Proof.* Let `T = 2|z| + 2`. For `|t| ≥ T`, `|z/t| ≤ 1/2` and `|log|1 - w| + Re w| ≤ |w|²` (`|w| ≤ 1/2`),
so the far part is `≤ M|z|² ∫_{|t| ≥ T} t^{-2} dt = 2M|z|²/T ≤ M|z|`. For `|t| < T`: `|log|1 - z/t|| ≤
|log|t - z|| + |log|t||` and `∫_{|t|<T} |log|t - z|| dt ≤ 2T(|log (3T)| + 1)` (substitute `u = t - x`,
`|t - z| ≥ |u|`), same for `log|t|`; and `∫_{1<|t|<T} |Re(z/t)| ≤ 2|z| log T`. Altogether
`|U_g(z)| ≤ C M (1 + |z|)(1 + log(1 + |z|)) ≤ K (1 + |z|)^{3/2}`.

```lean
theorem multU_compact_sub_linear {h : ℝ → ℝ} (hh : Measurable h) {M R : ℝ}
    (hM : ∀ t, |h t| ≤ M) (hR : ∀ t, R < |t| → h t = 0) (h0 : ∫ t, h t = 0) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU h 0 z - (∫ t, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (h t / t)) * z.re| ≤ C := by
```
*Proof.* Let `ℓ = ∫ (1 - 1_{[-1,1]}) h/t`; `U_h(z) - ℓ Re z = ∫ log|1 - z/t| h(t) dt`
(`Re(z/t) = Re z / t`). Write `log|1 - z/t| = log|t - z| - log|t|`; the part `∫ log|t| h` is a
constant. Case `|z| ≥ 2R + 2`: `log|t - z| = log|z| + log|1 - t/z|`, `∫ h = 0` kills `log|z|`, and
`|log|1 - t/z|| ≤ 2|t|/|z| ≤ 1`: bounded by `M·2R`. Case `|z| ≤ 2R + 2`: `∫_{|t|≤R} |log|t - z|| dt ≤
2R(|log(3R + 3)| + 1)`. ∎

### 3.2 The key identity: `log|f|` is the potential of `φ_f'/π` up to an affine function

**Claim.** `U_g/π - log|f|` is `-(b Re z + c)` on `Im z ≥ 0` for real `b, c` (in general `b ≠ 0`).

*Why a harmonic correction can appear and why it is affine.* `Δ log|f| = 0` near `ℝ` (no real zeros),
whereas `Δ U_g = 2π g(x) δ_{y=0}`; but `∂_y U_g(x + i0)/π = g(x) = φ_f'(x) = ∂_y log|f|(x + i0)`
(Cauchy–Riemann for `log f`, `Im log f(x) = -φ_f(x) + const`). So the difference has zero
Neumann data and extends by even reflection to a harmonic function on ℂ of growth `o(|z|²)`: affine.
To avoid harmonic reflection (absent from Mathlib) work with the holomorphic function `H = log f - P`.

Definitions (Lean).

```lean
def argUp (z : ℂ) (t : ℝ) : ℝ :=
  if t < 0 then Complex.arg (1 - z / t) else -Complex.arg (conj (1 - z / t))
```
```lean
def potC (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (((Real.log ‖1 - z / t‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).re : ℝ) : ℂ) +
    Complex.I * ((argUp z t + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).im : ℝ) : ℂ)) *
      (g t : ℂ)
```

`Q_g := potC g`. For `Im z > 0` it is `∫ [Log(1 - z/t) + 1_{|t|>1} z/t] g(t) dt` (principal `Log`;
`1 - z/t ∉ (-∞, 0]` as it is non-real), so `π P = Q_g` in the notation above.

```lean
theorem potC_re {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) (z : ℂ) :
    (potC g z).re = OCS.multU g 0 z := by
```
```lean
theorem differentiableOn_potC {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    DifferentiableOn ℂ (potC g) {z : ℂ | 0 < z.im} := by
```
```lean
theorem continuousOn_potC {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    ContinuousOn (potC g) {z : ℂ | 0 ≤ z.im} := by
```
```lean
theorem potC_im_ofReal {g φ : ℝ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ t, |g t| ≤ M)
    (hφ : ∀ x, HasDerivAt φ (g x) x) (x : ℝ) :
    (potC g (x : ℂ)).im = -Real.pi * (φ x - φ 0) := by
```

*Proofs.*
* `potC_re`: `Re Log w = log|w|`; the `Re` of the integrand is that of `multU`.
* `differentiableOn_potC`: for `Im z > 0` the integrand `t ↦ [Log(1 - z/t) + 1_{|t|>1} z/t] g(t)` is
  holomorphic in `z`; differentiate under the integral sign
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) on `{Im z > y₀, |z| < r}`:
  `∂_z [Log(1 - z/t) + z/t] = 1/(z - t) + 1/t = z/(t(z - t))`, bounded by `r/(|t| y₀)` for `|t| ≥ 1`
  and `1/|z - t| ≤ 1/y₀` for `|t| ≤ 1`; for `|t| ≥ 2r` it is `≤ 2r/t²`, integrable; `g` is bounded.
* `continuousOn_potC`: on `Im z ≥ 0` the real part is `multU` (continuous,
  `continuous_multU_of_bdd`). For the imaginary part, `z ↦ argUp z t` is continuous on
  `{Im z ≥ 0} \ {t}` (for `t < 0`, `1 - z/t` ranges in the closed upper half-plane minus `0`, where
  `arg ∈ [0, π]` is continuous; for `t > 0`, `conj(1 - z/t)` does); `|argUp| ≤ π`; and for `|t| ≥ 2|z|`,
  `|argUp z t + Im(z/t)| ≤ C|z|²/t²` (`Im Log(1 - w) + Im w = O(|w|²)`). Dominated convergence on
  compact sets of `z` (the point `z = t` is a single `t`, a null set).
* `potC_im_ofReal`: for real `x` and `t ∉ {0, x}`: `1 - x/t` is real. If `t < 0`: `argUp x t = arg(1 - x/t)
  = π` iff `1 - x/t < 0` iff `x/t > 1` iff `x < t < 0` (as `t < 0` flips) i.e. `t ∈ (x, 0)` when `x < 0`,
  and `0` otherwise. If `t > 0`: `argUp x t = -arg(1 - x/t) = -π` iff `1 - x/t < 0` iff `0 < t < x`,
  and `0` otherwise. So `∫ argUp(x, t) g(t) dt = -π ∫_0^x g` (for `x < 0`: `+π ∫_x^0 g = -π ∫_0^x g`).
  The terms `1_{|t|>1} Im(x/t) = 0`. `∫_0^x g = φ(x) - φ(0)` (FTC, `φ' = g` continuous).

Reflection and growth lemmas.

```lean
theorem exists_entire_reflection {H : ℂ → ℂ} (hc : ContinuousOn H {z : ℂ | 0 ≤ z.im})
    (hd : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) {c : ℝ} (him : ∀ x : ℝ, (H x).im = c) :
    ∃ Ĥ : ℂ → ℂ, Differentiable ℂ Ĥ ∧ (∀ z : ℂ, 0 ≤ z.im → Ĥ z = H z) ∧
      ∀ z : ℂ, Ĥ (conj z) = conj (Ĥ z) + 2 * Complex.I * c := by
```
```lean
theorem entire_affine_of_re_growth {H : ℂ → ℂ} (hH : Differentiable ℂ H) {K : ℝ}
    (hK : ∀ z : ℂ, |(H z).re| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ)) :
    ∃ α β : ℂ, ∀ z : ℂ, H z = α + β * z := by
```

*Proofs.* `exists_entire_reflection`: define `Ĥ(z) = H(z)` for `Im z ≥ 0`, `conj(H(z̄)) + 2ic` for
`Im z < 0`; continuous on ℂ (on `ℝ`: `conj H(x) + 2ic = Re H(x) - ic + 2ic = H(x)` as `Im H(x) = c`),
holomorphic off `ℝ`; by Morera on discs (`Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`):
for a rectangle meeting `ℝ` split it along `ℝ` into two rectangles, on each of which `Ĥ` is continuous
on the closed rectangle and holomorphic in the interior, so the rectangle integral vanishes
(`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`, off the countable set
`∅`, applied with `Hd` on the interior — the closed rectangle's boundary part on `ℝ` is only used
through continuity); the two integrals over the common edge cancel. `entire_affine_of_re_growth`:
`H - H(0)` has `|Re(H - H(0))| ≤ K'(1 + |z|)^{3/2}`; Borel–Carathéodory
(`Complex.borelCaratheodory`, with `M = K'(1+2r)^{3/2}`, radius `r → 2r`) gives
`sup_{|z| = r} |H(z) - H(0)| ≤ C r^{3/2}` for `r ≥ 1`; Cauchy's estimate for `H''`
(`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`): `|H''(z_0)| ≤ 2 C (2r)^{3/2}/r² → 0`; so
`H'' ≡ 0`.

```lean
theorem log_norm_eq_multU_add_affine {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : ∀ z : ℂ, 0 ≤ z.im → f z ≠ 0) {φ g : ℝ → ℝ} (hφ : IsPhaseFunction f φ)
    (hφ' : ∀ x, HasDerivAt φ (g x) x) (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    (hgrow : ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |Real.log ‖f z‖| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ)) :
    ∃ b c : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.log ‖f z‖ = OCS.multU g 0 z / Real.pi + b * z.re + c := by
```

*Proof.* Since `f ≠ 0` on the closed half-plane `{Im z ≥ 0}` (a convex set contained in the open set
`{f ≠ 0}`) the function `f'/f` has a primitive `L` there (integrate along segments; triangles in
`{Im z ≥ 0}` lie in `{f ≠ 0}`, so Cauchy–Goursat applies), `L` holomorphic on `Im z > 0`, continuous on
`Im z ≥ 0`, `e^{L} = f` (adding a constant), `Re L = log|f|`, and `e^{L(x)} = f(x) = |f(x)| e^{-iφ(x)}`
gives `Im L(x) = -φ(x) + 2πk` with `k` constant (continuity). Put `H = L - Q_g/π`. Then `H` is continuous
on `Im z ≥ 0`, holomorphic on `Im z > 0` (`differentiableOn_potC`, `continuousOn_potC`), and for real `x`
`Im H(x) = -φ(x) + 2πk + (φ(x) - φ(0)) = 2πk - φ(0) =: c` (`potC_im_ofReal`). By
`exists_entire_reflection`, `H` extends to an entire `Ĥ`. Real part: on `Im z ≥ 0`
`Re H = log|f| - U_g/π` (`potC_re`), so `|Re H| ≤ K(1+|z|)^{3/2} + K'(1+|z|)^{3/2}` by `hgrow` and
`abs_multU_le_of_bdd`; for `Im z < 0`, `Re Ĥ(z) = Re H(z̄)` has the same bound. By
`entire_affine_of_re_growth`, `Ĥ(z) = α + β z`; `Im Ĥ = c` on `ℝ` gives `Im(α + βx) = c` for all real
`x`, so `Im β = 0`, and `Re(α + βz) = Re α + β Re z`. So `log|f| = U_g/π + b Re z + c'` with
`b = β`, `c' = Re α`. ∎

### 3.3 The density `m`

```lean
theorem exists_modified_density {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : Tendsto w (cocompact ℝ) (𝓝 0)) (β : ℝ) :
    ∃ (R : ℝ) (m : ℝ → ℝ) (a b : ℝ), 0 < R ∧ 0 < a ∧ Measurable m ∧ (∀ t, a ≤ m t) ∧
      (∀ t, m t ≤ b) ∧ (∀ t, R < |t| → m t = 1 + w t) ∧
      (∫ t, (m t - (1 + w t)) = 0) ∧
      (∫ t, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((m t - (1 + w t)) / t)) = -β := by
```

*Proof.* Let `X` be such that `|w| ≤ 1/4` for `|t| ≥ X`; for `R ≥ X + 1` set
`S = ∫_{-R}^{R} (1 + w)`, `c = S/(2R)`, `L_R = ∫_{1<|t|<R} (1 + w(t))/t dt`, `s = (L_R - β)/(2 log R)`,
and
&nbsp;&nbsp;`m = c + s · sgn(t) · 1_{1<|t|<R}` on `[-R, R]`, `m = 1 + w` outside.
Then `m` is measurable, and:
* `∫_{-R}^{R} m = 2Rc = S = ∫_{-R}^R (1 + w)`: `∫ (m - 1 - w) = 0`.
* `∫_{1<|t|<R} m/t = c ∫ 1/t + s ∫ sgn(t)/t = 0 + 2 s log R = L_R - β`, hence
  `∫ (1 - 1_{[-1,1]}) (m - 1 - w)/t = (L_R - β) - L_R = -β`.
* Bounds. The `1/t` part of `1 + w` is odd, so `L_R = ∫_{1<|t|<R} w/t dt`. Given `ε > 0` let `X_ε`
  with `|w| ≤ ε` for `|t| ≥ X_ε`; then `|L_R| ≤ C_ε + 2ε log R` (`C_ε = 2 sup|w| log X_ε`), so
  `|s| ≤ (C_ε + |β|)/(2 log R) + ε ≤ 2ε` for `R` large. Also `|c - 1| ≤ (2R)^{-1} ∫_{-R}^{R} |w| → 0`
  (Cesàro, `w → 0`). Take `ε = 1/16` and `R` large: `c ≥ 3/4`, `|s| ≤ 1/8`, so `m ≥ 5/8` on
  `[-R, R]` (`m ∈ {c, c ± s}`), and `m = 1 + w ≥ 15/16` outside. Upper bound `m ≤ c + |s| ≤ 2 + sup|w|`.
  Take `a = 5/8`, `b = 2 + sup |w|`. ∎

```lean
theorem exists_good_density {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {f : ℂ → ℂ} (hf : IsHB f)
    (hφ : Tendsto (phaseDeriv f) (cocompact ℝ) (𝓝 0))
    (happ : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.exp (UPsi ψ z - C) ≤ ‖f z‖ ∧ ‖f z‖ ≤ Real.exp (UPsi ψ z + C))
    {φf : ℝ → ℝ} (hφf : IsPhaseFunction f φf) (hφf' : ∀ x, HasDerivAt φf (phaseDeriv f x) x) :
    ∃ (m : ℝ → ℝ) (a b κ R : ℝ), Measurable m ∧ 0 < a ∧ (∀ t, a ≤ m t) ∧ (∀ t, m t ≤ b) ∧
      Tendsto m (cocompact ℝ) (𝓝 1) ∧
      (∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → |OCS.multU m 0 z - Real.pi * z.im| ≤ C) ∧
      ∀ x : ℝ, R ≤ |x| → Real.pi * OCS.multPrim m x + φf x = Real.pi * (x + ψ x) + κ := by
```

*Proof.* Put `w = ψ' - g/π` (continuous, `→ 0`: `ψ' → 0` by admissibility, `g → 0` by `hφ`) and
`ω' = 1 + w`.
1. *Growth.* By `happ`, `|log|f| - UPsi ψ| ≤ C`; `UPsi ψ = U_{ψ'}` and `|U_{ψ'}| ≤ K(1+|z|)^{3/2}`
   (3.1), so `hgrow` holds. By 3.2 there are real `b₀, c₀` with
   `log|f| = U_g/π + b₀ Re z + c₀` on `Im z ≥ 0`.
2. *Choice of `m`.* `exists_modified_density` with `β = b₀` gives `R, m, a, b` and `h = m - (1 + w)`
   (bounded, measurable, supported in `[-R, R]`) with `∫ h = 0`, `ℓ := ∫(1 - 1_{[-1,1]}) h/t = -b₀`.
   `m → 1` since `m = 1 + w` outside `[-R, R]`.
3. *Potential.* `m = 1 + ψ' - g/π + h` pointwise, so by linearity (3.1)
   `U_m = U_1 + U_{ψ'} - U_g/π + U_h = π Im z + UPsi ψ - (log|f| - b₀ Re z - c₀) + (ℓ Re z + O(1))`
   (using `multU_one`, 3.2 and `multU_compact_sub_linear`), on `Im z ≥ 0`. With `ℓ = -b₀`
   the linear terms cancel and
   `U_m - π Im z = (UPsi ψ - log|f|) + c₀ + O(1)`, bounded by `happ`. This is `hU` for `m`.
4. *Phase comparison.* For `x ≥ R`: `M(x) = ∫_0^x m = ∫_0^x (1 + ψ' - g/π) + ∫_0^x h =
   x + ψ(x) - ψ(0) - (φ_f(x) - φ_f(0))/π + ∫_0^R h` (`ψ` is `C¹`, `φ_f' = g`; `h = 0` beyond `R`). For
   `x ≤ -R`: `∫_0^x h = -∫_{-R}^0 h = ∫_0^R h` since `∫_{-R}^R h = 0`. So in both cases
   `π M(x) + φ_f(x) = π(x + ψ(x)) + κ`, `κ = -πψ(0) + φ_f(0) + π∫_0^R h`. (This is why `∫ h = 0` is
   needed: the constants at `+∞` and `-∞` coincide.) ∎

### 3.4 Matching the zero set with `Λ(ψ)`

```lean
theorem strictMono_add_psi {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) :
    StrictMono (fun x ↦ x + ψ x) ∧ Function.Surjective (fun x ↦ x + ψ x) ∧
      ∀ x y : ℝ, x ≤ y → y - x ≤ (y + ψ y) - (x + ψ x) := by
```
*Proof.* `ψ` nondecreasing gives `Ψ(y) - Ψ(x) ≥ y - x` for `x ≤ y` (`Ψ(x) = x + ψ(x)`): strictly increasing,
`1`-expanding, `Ψ(x) → ±∞`, continuous, so onto.

```lean
theorem exists_perturbation_of_phase {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {Θ : ℝ → ℝ}
    (hΘ : StrictMono Θ) (hΘs : Function.Surjective Θ)
    (hlim : Tendsto (fun x ↦ Θ x / Real.pi - (x + ψ x)) (cocompact ℝ) (𝓝 0)) :
    ∃ δ : ℝ → ℝ, InjOn (fun x ↦ x + δ x) {x | ∃ k : ℤ, Θ x = k * Real.pi} ∧
      (fun x ↦ x + δ x) '' {x | ∃ k : ℤ, Θ x = k * Real.pi} = LambdaPsi ψ ∧
      Tendsto δ (cocompact ℝ) (𝓝 0) := by
```
*Proof.* `Ψ` is a bijection with `1`-Lipschitz inverse. Put `δ(x) := Ψ^{-1}(Θ(x)/π) - x`. For `x`
with `Θ(x) = kπ`: `x + δ(x) = Ψ^{-1}(k) ∈ Λ(ψ)`. `x ↦ Ψ^{-1}(Θ(x)/π)` is strictly increasing, so
injective, and maps `{Θ ∈ πℤ}` *onto* `{Ψ^{-1}(k)} = Λ(ψ)` (`Θ` onto: each `k` is `Θ(x)/π` for some `x`).
`|δ(x)| = |Ψ^{-1}(Θ(x)/π) - Ψ^{-1}(Ψ(x))| ≤ |Θ(x)/π - Ψ(x)| → 0`. ∎

(Both `{Θ ∈ πℤ} → ℤ` and `Λ(ψ) ↔ ℤ` are *the same integer index*, so no counting issue arises. This
uses that the constant in the asymptotics of `Θ` is the same at `+∞` and `-∞`.)

### 3.5 Separation

```lean
theorem sub_le_mul_sub_of_hasDerivAt {Θ d : ℝ → ℝ} (hΘ : ∀ x, HasDerivAt Θ (d x) x) {C : ℝ}
    (hd : ∀ x, d x ≤ C) {x y : ℝ} (hxy : x ≤ y) : Θ y - Θ x ≤ C * (y - x) := by
```
(Mathlib `image_sub_le_mul_sub_of_deriv_le`.)

```lean
theorem isSeparated_levelSet {Θ : ℝ → ℝ} (hΘ : StrictMono Θ) {C : ℝ} (hC : 0 < C)
    (hlip : ∀ x y : ℝ, x ≤ y → Θ y - Θ x ≤ C * (y - x)) :
    IsSeparated {x | ∃ k : ℤ, Θ x = k * Real.pi} := by
```
*Proof.* If `Θ(x) = kπ`, `Θ(y) = lπ`, `x < y`: strictly increasing gives `l > k`, so `(l - k)π ≥ π`;
`π ≤ Θ(y) - Θ(x) ≤ C(y - x)`: `y - x ≥ π/C`. ∎

### 3.6 Rotation lemmas

```lean
theorem IsHB.rotate {E : ℂ → ℂ} (hE : IsHB E) (β : ℝ) :
    IsHB (fun z ↦ Complex.exp (Complex.I * β) * E z) := by
```
```lean
theorem IsPhaseFunction.rotate {E : ℂ → ℂ} {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) (β : ℝ) :
    IsPhaseFunction (fun z ↦ Complex.exp (Complex.I * β) * E z) (fun x ↦ φ x - β) := by
```
```lean
theorem phaseDeriv_rotate (E : ℂ → ℂ) (β : ℝ) (x : ℝ) :
    phaseDeriv (fun z ↦ Complex.exp (Complex.I * β) * E z) x = phaseDeriv E x := by
```
(`|e^{iβ}E(z)| = |E(z)|`; `e^{iβ}E(x) = |E(x)| e^{-i(φ(x) - β)}`;
`(e^{iβ}E)'/(e^{iβ}E) = E'/E`.)

### 3.7 Proof of Corollary 2

```lean
theorem corollary2 (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {f : ℂ → ℂ} (hf : IsHB f)
    (hφ : Tendsto (phaseDeriv f) (cocompact ℝ) (𝓝 0))
    (happ : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.exp (UPsi ψ z - C) ≤ ‖f z‖ ∧ ‖f z‖ ≤ Real.exp (UPsi ψ z + C)) :
    IsSampling (LambdaPsi ψ) := by
```

*Proof.*

1. *`f`.* As in 3.0: `f ≠ 0` on `Im z ≥ 0`, `g = phaseDeriv f` continuous `≥ 0` bounded `→ 0`; phase
   function `φ_f` with `φ_f' = g`; `φ_f` nondecreasing.
2. *Density.* `exists_good_density`: `m, a, b, κ, R` with `hU` and `π M + φ_f = π(x + ψ) + κ` for `|x| ≥ R`.
3. *The function `E`.* `exists_hb_of_density_phase` for `m` gives `E ∈ \overline{HB}`, `E(x) ≠ 0`,
   `|E| ≃ e^{π Im z}` on `Im z ≥ 0`, strictly increasing phase `φ_E` with `φ_E - π M → c₀`.
   Hence for `|x| ≥ R`: `φ_E + φ_f = π(x + ψ(x)) + κ + c₀ + o(1)`.
4. *`H(E) = PW`.* `heEqPW_of_comparable hPW` (`|E| ≃ e^{π Im z}` on `Im z ≥ 0`): `HEEqPW E`; then
   `E` is strict (`HEEqPW.isStrictHB`).
5. *Rotation.* `β := κ + c₀ - π/2`, `E_β := e^{iβ}E`. `E_β ∈ \overline{HB}`, `|E_β| = |E|` (so `HEEqPW E_β`
   by 3.4 again, and strict), phase `φ_E - β` (3.6). Put `Θ := φ_E - β + φ_f - π/2`. Then
   `Θ(x) - π(x + ψ(x)) = (κ + c₀ - β - π/2) + o(1) = o(1)`.
6. *Zero set.* `zero_set_eq_phaseLevel` (`E_β` strict, `f ∈ \overline{HB}`, no real zeros, phases
   `φ_E - β`, `φ_f`): for all `z`,
   `E_β f + E_β^* f^* (z) = 0 ↔ z ∈ ofReal '' phaseLevel (φ_E - β + φ_f) (π/2)` and
   `phaseLevel (φ_E - β + φ_f)(π/2) = {x | ∃ k ∈ ℤ, Θ x = kπ} =: Γ'`.
7. *`Θ` is a homeomorphism-like map.* Strictly increasing (`φ_E` strictly increasing, `φ_f` nondecreasing),
   onto: for `x ≥ 0`, `Θ(x) ≥ φ_E(x) - β + φ_f(0) - π/2 ≥ πM(x) + c₀ - 1 - β + φ_f(0) - π/2 → ∞` (`M(x) ≥ ax`),
   similarly `Θ(x) → -∞` as `x → -∞`; `Θ` continuous.
8. *`Γ'` separated.* `Θ' = phaseDeriv E + g ≤ C` (`HEEqPW.phaseDeriv_mul_sq_le hPW hE` gives
   `phaseDeriv E · |E|² ≤ C_E` and `|E(x)| ≥ c` on `ℝ` by the comparability at `Im z = 0`; `g ≤ M_g`);
   `sub_le_mul_sub_of_hasDerivAt` + `isSeparated_levelSet`. (`HasDerivAt φ_E (phaseDeriv E x) x` from M02.)
9. *Sampling of `Γ'`.* `theorem1_sufficiency hPW hE` with `Λ = Γ'` separated (8), `E_β`, `f`, `HEEqPW E_β`,
   zero set (6): `IsSampling Γ'`.
10. *Perturbation.* `Θ(x)/π - (x + ψ x) → 0` (5). `exists_perturbation_of_phase` (`Θ` strictly increasing,
    onto) gives `δ` injective on `Γ'` with image `Λ(ψ)` and `δ → 0`.
    `IsSampling.of_perturbation hPW hDS` (separated `Γ'`, sampling `Γ'`) gives
    `IsSampling ((x ↦ x + δ x) '' Γ') = IsSampling (LambdaPsi ψ)`. ∎

---------------------------------------------------------------------------------------------------

## 4. Issues in the source

(Page/line refer to `literature/ArxivOrtega.tex`, the print agrees.)

1. **Meĭman's theorem (p. 801, tex l. 775–778; certain).** "Then according to a theorem of Meĭman
   (see [Le80, p. 314]), we have either `A - iB ∈ \overline{HB}` or `A + iB ∈ \overline{HB}`." As quoted
   (interlacing zeros of entire functions of exponential type) this is false: `A = cos πz`,
   `B = e^{az} sin πz`. The true statement needs an extra condition (e.g. genus/growth); here `A`, `B` are
   locally uniform limits of real polynomials with interlacing zeros, for which the claim is elementary
   (§2.4). Also, "`P` may be replaced by `-P`" is unnecessary: with the zeros of `B` to the right of those
   of `A` and `P/Q → 1`, `E = A - iB` is the right choice automatically (§2.4, Remark).
2. **"two monomials `P` and `Q`" (l. 771; certain).** They must be polynomials with real zeros (products of
   linear factors); monomials `z^k` have all zeros at `0`.
3. **`A(z) = lim_{R→∞} ∏_{|γ_k| < R} (1 - z/γ_k)` (l. 764; fairly sure).** The symmetric partial products
   `A_R` converge only if `∑_{|j| ≤ R} 1/γ_j` converges, which fails e.g. for
   `m = 1 + (log log t)^{-1}` on `t > t_0`, `m = 1` for `t < 0`; the multiplier of [OS99, Lemma 3] is
   `OCS.multF m 0 = e^{-κz+β} ∏ (1 - z/γ) e^{z/γ}`; its extra factor `e^{-κ z}` is *not* removable
   (it affects `|A|e^{-U}`, and `U` is fixed by the `Re(z/t)`-normalisation).
4. **"We may assume `ω' ≃ 1`" (l. 758; certain that it is a gap).** `ω' = 1 + ψ' - φ_f'/π` can be `≤ 0`
   on a compact set; a modification there must (i) preserve the integral (so `φ_E - πM` has the same
   limit at `±∞`; otherwise Corollary 2's zero-set matching has an index shift, which can destroy
   sampling) and (ii) kill the *linear* term created by the compensating `Re(z/t)` (§3.3); (ii) requires the
   knowledge of the affine correction `b Re z` in `log|f| - U_g/π` (§3.2), which the paper never states
   (it identifies `U_ω` with `π Im z + U_ψ - log|f|` implicitly: this is true only up to `b Re z + c`).
5. **The identity `U_{φ_f'/π} ≈ log|f|` is used without proof (l. 755–795; certain).** §3.2 proves it:
   `log|f| - U_{φ_f'}/π` is affine (Schwarz reflection + Liouville). Not true for general `f ∈ HB` without
   the growth hypothesis; here it comes from `happ`.
6. **Normal family step (l. 785–791; certain gap, fixable).** (a) "`A_k(z) = A(z - x_{2k})`": the translate
   moving `x_{2k}` to `0` is `A(z + x_{2k})`. (b) "`A_k(x) - c_k cos πx → 0`" with `c_k ≃ 1`: (i) it needs
   `A` bounded on `ℝ` and `|A| ≃ e^{π|y|}` away from `ℝ`, i.e. `U - π Im z = O(1)` — otherwise the
   envelope of `A` near `x_{2k}` is `e^{κ_k τ}` and the amplitudes of `A` and `B` differ by `e^{κ_k/2}`
   (§0.2, README §4's phase clause is false in general); (ii) the limit zero set is `1/2 + ℤ` because
   `γ_{2k} - x_{2k} → 1/2` and `x_{j+1} - x_j → 1`, which should be said; (iii) "similarly for `B_k`" needs
   `B(z) = A(z - 1/2)P/Q` with `P/Q → 1`; (iv) only `k → +∞` is treated; `k → -∞` is symmetric but the
   *same integer shift* `k₀` must be shown at both ends (§2.7(c): done through the exact level structure
   `φ(γ_j) = π/2 + π(j + k₀)`). (v) The conclusion "`E(x) = |E(x)| e^{i(π(x + ψ(x)) - φ_f + o(1))}`"
   has the wrong sign of the exponent: with `E = |E|e^{-iφ_E}` (p. 794) it should be
   `e^{-i(...)}` (tex l. 793; certain).
7. **Zero sequence of `Ef + E^*f^*` need not be separated a priori (p. 800; fixable).** Theorem 1 is stated for
   separated sequences (M04); the perturbation step is applied to the zero sequence. Separation follows from
   `φ_E' |E|² ≲ 1` (§3.5, M02). Not mentioned in the paper.
8. **"the elementary fact that `Γ` is sampling if `δ_k = 0` except for finitely many `k`" (p. 800; fixable).**
   Only true for replacements of finitely many points by the *same number* of new distinct points
   (`ℤ \ {0}` is not sampling). In Corollary 2 the matching is by the integer index, so this is the
   situation (§1.3, §3.4); but it requires that the index shift at `+∞` and `-∞` agree (the constant `c₀`).
9. **`ψ(∞) - ψ(-∞) = ∞` (p. 799) is not used** in Corollary 2 (nor `ψ → ∞`); the hypotheses of
   `IsAdmissiblePsi` are harmless but the conclusion holds for every `C¹` nondecreasing `ψ` with `ψ' → 0`
   (e.g. `ψ = 0`, `f = 1`, `Λ = ℤ`). (Certain.)
10. **Principal value `U_ψ` (p. 799).** Not used verbatim; with `UPsi` the `Re(z/t)` is kept only for
    `|t| > 1`, differing from the p.v. by `c Re z`. The Lean `corollary2` is stated with `UPsi`; the version
    with the p.v. follows by `f ↦ f e^{-cz}` (preserves `\overline{HB}` and the phase), but is not
    needed (README §2.5).
11. **The estimate `|A| e^{-U_ω} ≃ min(1, dist(z, Γ))` (l. 767) "by Lemma 3 in [OS99]" (certain it is fine
    for `|y| ≤ 1`, the case `|y| ≥ 1` is estimate (3) of [OS99]); the claim "`|E(z)| ≃ e^{π Im z}`"
    is never derived: `|E| ≃ e^{U_ω}` needs `|B| ≲ e^{U_ω}` i.e. `U(z - 1/2) - U(z) = O(1)` (`hshift`) and
    the lower bound `|E|² ≥ |A|² + |B|²` plus the uniform distance between the zeros of `A` and `B`
    (§2.6).

## 5. Requested changes to M00

None required. Remarks:
* `corollary2`'s statement is true as stated (the proof above). Note the edge case `UPsi` is the integral of
  an integrable function (3.1), so the junk value `0` for non-integrable integrands does not occur.
* `IsAdmissiblePsi` could drop the clause `Tendsto ψ atTop atTop ∨ Tendsto ψ atBot atBot` for Corollary 2
  (needed only for Theorem 2); no change requested.
* README §4 (M07 interface): done at assembly: the old `exists_hb_of_density` block was replaced by
  `exists_hb_of_density` + `exists_hb_of_density_phase` as in `Construction.lean`, the latter with
  the drifted hypothesis `∃ κ C, |U - π Im z - κ Re z| ≤ C` (M06 uses it with `κ = logKappa`).

## 6. Implementation notes and risks

* **Hardest pieces (in order):** (i) `log_norm_eq_multU_add_affine` (§3.2: parametric integrals, boundary
  argument, Morera reflection); (ii) `genA_translate_limit`/`phase_rigidity` (§2.7); (iii)
  `tendsto_polyA/B` (§2.4, locally uniform convergence of products + removable singularities);
  (iv) `multU_one` (§3.1, explicit limit); (v) `norm_compB_comparable`.
* The three files are independent of `FourierFrames.HB.*` except through the declared upstream lemmas.
* **Mathlib names checked to exist:** `dslope`, `sub_smul_dslope`, `differentiableOn_dslope`,
  `Complex.differentiableOn_update_limUnder_of_bddAbove`, `Complex.borelCaratheodory`,
  `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`, `Differentiable.apply_eq_apply_of_bounded`,
  `Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`,
  `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`,
  `Complex.norm_le_of_forall_mem_frontier_norm_le`, `image_sub_le_mul_sub_of_deriv_le`,
  `Complex.arg` / `Complex.arg_mul` (check exact names with `grep`).
* Compile status: `Perturbation.lean`, `Construction.lean`, `Corollary2.lean` compile with only
  `declaration uses 'sorry'` warnings.
