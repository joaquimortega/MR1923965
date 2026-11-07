# M04 — Theorem 1 (sufficiency and `theorem1`), Corollary 1, the remark of p. 797

**Lean files** (all proved, no `sorry`; namespace `FF`):
- `FourierFrames/Theorem1/Sufficiency.lean` — `theorem1_sufficiency` and its lemmas; helpers
  `Theorem1/Sufficiency/{Interlace,Limit,LevelSet,Phase}.lean` and the Weierstrass product
  `Theorem1/Sufficiency/RealFactor/{Elem,LUProd,Zeros,Product,Main}.lean`;
- `FourierFrames/Theorem1/Main.lean` — `theorem1` (from `theorem1_necessity`, M03, and
  `theorem1_sufficiency`);
- `FourierFrames/Corollary1.lean` — `corollary1`, `corollary1_strong`,
  `completeInterpolating_zero_set`; helpers `Corollary1/{Rotate,Kernel,ClosedGraph}.lean`.

**Status (final).** Lean blocks show the statements (some hypotheses were removed as unused in the
lint pass, NOTEBOOK I-03); all are proved. The routes actually implemented, where they differ from
the text, are marked *Implemented:* below (source: `impl_notes/sufficiency.md`,
`impl_notes/sufficiency_cor1_landau.md`).

**Paper:** §3 "Main theorem" (pp. 795–797, tex lines 396–470), the remark on p. 797 (tex 472–480),
§4 Corollary 1 (p. 798, tex 601–621).

**Cited `Prop`s used:** `PaleyWienerThm` (`hPW`), `TheoremC` (`hC`, only through M03 and for the remark),
`TheoremD` (`hD`, only for the remark), `TheoremE` (`hE`), `TheoremF` (`hF`, only through M03).

**Depends on** (imported, see `IMPORTS.md`):
- M01: `pwNormSq_ne_top`, `pw_norm_sq_le`, `MemPW.sub`, `MemPW.comp_sub_ofReal`,
  `pwNormSq_comp_sub_ofReal`, `exists_memPW_eval_ne_zero`, `plancherelPolya`, `plancherelPolya_tail`,
  `plancherelPolya_tail_union`, `sampleSum_mono`, `IsSepBy.mono`, `pw_deriv_bound` (README names), and, in the proof of `isSampling_of_isCompleteInterpolating`,
  `pw_complete`.
- M02: `IsHB.mul`, `IsStrictHB.mul_isHB` (new name: product of a strict and a closed-class function),
  `IsHB.phaseDeriv_nonneg`, `IsStrictHB.phaseDeriv_pos`, `phaseDeriv_mul`, `exists_isPhaseFunction`,
  `zero_set_eq_phaseLevel`, `MemHE.mul_isHB`, `heNormSq_mul`, `HEEqPW.isStrictHB`,
  `HEEqPW.ne_zero_ofReal`, `HEEqPW.phaseDeriv_mul_sq_ge`, `memHE_sAlpha_unique`; for the remark also
  `isHB_one` and the rotation lemmas listed in §10.
- M03: `theorem1_necessity`, and `exists_E` (`Necessity.lean`; the first half of the proof of
  necessity: Theorem C applied to the norm `(∑|f(λ)|²)^{1/2}` gives `E` with `H(E) = PW` and
  `‖f‖²_E = ∑_Λ |f(λ)|²`; no separation needed), used for the remark of p. 797.

**Used by:** M05 (`corollary1_strong`); M07 (`Corollary2.lean` calls `theorem1_sufficiency`); M06 imports
`Theorem1.Sufficiency` for its helpers only; M09 does not use M04.

## 0. Reading guide

All sets `Λ ⊆ ℝ` are `Set ℝ`; "separated" is `IsSeparated`, and `IsSepBy δ Λ` (M01, `PW/Basic.lean`) is the same with an explicit constant `δ` (the duplicate `Suff.IsSepBy` was removed before implementation; use `IsSepBy.mono` for `sepBy_mono`/`sepBy_subset`).
The proof of sufficiency (pp. 795–797) is long; the steps are:

| step | content | Lean |
|---|---|---|
| 1 | remove the real zeros of `F` | `Suff.exists_realFactor`, `Suff.exists_noRealZero_hb` |
| 2 | phase of `EG` is a homeomorphism, level sets | `HEEqPW.phase_tendsto`, `HEEqPW.phase_mul_bijective` |
| 3 | `Λ_α` is a union of two `δ`-separated sets | `Suff.phaseLevel_sepBy_two` |
| 4 | Theorem E ⇒ `‖f‖² ≤ C₀ ∑_{Λ_α}|f|²` uniformly in `α` | `HEEqPW.levelSet_ineq` |
| 5 | pass to the limit `α → π/2` | `Suff.levelSet_limit` |
| 6 | assemble | `theorem1_sufficiency` |

Notation: `E` is the given function with `H(E) = PW`, `G` the function without real zeros
obtained from `F` (the paper's `F̃`), `E' = EG`, `φ_E, φ_G` phase functions with
`φ' = phaseDeriv`, `ψ = φ_E + φ_G` (a phase function of `E'`, `Suff.isPhaseFunction_mul`).

## 1. Elementary helpers

```lean
/-- `Λ` is `δ`-separated. -/
def IsSepBy (δ : ℝ) (Λ : Set ℝ) : Prop :=
  ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ |a - b|
```

```lean
/-- `α` is *exceptional* for `E`: `e^{iα}E - e^{-iα}E^* ∈ H(E)` (the hypothesis of Theorem E fails). -/
def Exceptional (E : ℂ → ℂ) (α : ℝ) : Prop :=
  MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z)
```

("`α` is exceptional" is exactly the failure of the hypothesis of Theorem E for `E`.)

```lean
theorem sampleSum_eq_tsum_indicator (Λ : Set ℝ) (f : ℂ → ℂ) :
    sampleSum Λ f = ∑' x : ℝ, Λ.indicator (fun x : ℝ ↦ ‖f (x : ℂ)‖ₑ ^ 2) x := by
  unfold sampleSum
  exact tsum_subtype Λ (fun x : ℝ ↦ ‖f (x : ℂ)‖ₑ ^ 2)
```

```lean
theorem sampleSum_mono {Λ Λ' : Set ℝ} (h : Λ ⊆ Λ') (f : ℂ → ℂ) :
    sampleSum Λ f ≤ sampleSum Λ' f := by
  rw [sampleSum_eq_tsum_indicator, sampleSum_eq_tsum_indicator]
  exact ENNReal.tsum_le_tsum fun x ↦ Set.indicator_le_indicator_of_subset h (by intro; positivity) x
```

```lean
theorem sampleSum_union_le (Λ Λ' : Set ℝ) (f : ℂ → ℂ) :
    sampleSum (Λ ∪ Λ') f ≤ sampleSum Λ f + sampleSum Λ' f :=
  ENNReal.tsum_union_le (fun x : ℝ ↦ ‖f (x : ℂ)‖ₑ ^ 2) Λ Λ'
```

```lean
/-- Splitting a sampling sum into a bounded and an unbounded part. -/
theorem sampleSum_split (Λ : Set ℝ) (f : ℂ → ℂ) (R : ℝ) :
    sampleSum Λ f =
      sampleSum (Λ ∩ {x : ℝ | |x| < R}) f + sampleSum (Λ ∩ {x : ℝ | R ≤ |x|}) f := by
  rw [sampleSum_eq_tsum_indicator, sampleSum_eq_tsum_indicator, sampleSum_eq_tsum_indicator,
    ← ENNReal.tsum_add]
  congr 1
  ext x
  by_cases hΛ : x ∈ Λ <;> by_cases hR : |x| < R <;>
    simp [Set.indicator, hΛ, hR, not_le.mpr, not_lt.mp]
```

```lean
theorem phaseLevel_add_pi (φ : ℝ → ℝ) (α : ℝ) :
    phaseLevel φ (α + Real.pi) = phaseLevel φ α := by
  ext x
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rw [hk]; push_cast; ring⟩
  · rintro ⟨k, hk⟩
    exact ⟨k - 1, by rw [hk]; push_cast; ring⟩
```

(`sepBy_mono`, `sepBy_subset` below do not exist in the code; both are `IsSepBy.mono`, `PW/Basic.lean`.)

```lean
theorem sepBy_mono {δ δ' : ℝ} (h : δ' ≤ δ) {Λ : Set ℝ} (hΛ : IsSepBy δ Λ) : IsSepBy δ' Λ :=
  fun a ha b hb hab ↦ h.trans (hΛ a ha b hb hab)
```

```lean
theorem sepBy_subset {δ : ℝ} {Λ Λ' : Set ℝ} (h : Λ' ⊆ Λ) (hΛ : IsSepBy δ Λ) : IsSepBy δ Λ' :=
  fun a ha b hb hab ↦ hΛ a (h ha) b (h hb) hab
```

These are proved (`tsum_subtype`, `ENNReal.tsum_le_tsum`, `ENNReal.tsum_union_le`,
`ENNReal.tsum_add`). Note that `phaseLevel_add_pi` shows that `Exceptional E` and the level set depend on
`α` only modulo `π` (the level set trivially; exceptionality by `memHE_sAlpha_unique`).

```lean
/-- `ψ_G = φ_E + φ_F` is a phase function of `EF`. -/
theorem isPhaseFunction_mul {E F : ℂ → ℂ} {φ ψ : ℝ → ℝ} (hφ : IsPhaseFunction E φ)
    (hψ : IsPhaseFunction F ψ) :
    IsPhaseFunction (fun z ↦ E z * F z) (fun x ↦ φ x + ψ x) := by
  refine ⟨hφ.1.add hψ.1, fun x ↦ ?_⟩
  have h1 := hφ.2 x
  have h2 := hψ.2 x
  calc E x * F x = ((‖E x‖ : ℂ) * Complex.exp (-(I * φ x))) *
        ((‖F x‖ : ℂ) * Complex.exp (-(I * ψ x))) := by rw [← h1, ← h2]
    _ = ((‖E x * F x‖ : ℝ) : ℂ) * Complex.exp (-(I * ((φ x + ψ x : ℝ) : ℂ))) := by
      rw [norm_mul]
      push_cast
      rw [mul_add, neg_add, Complex.exp_add]
      ring
```


```lean
/-- At most one `n` has `π/2 + π/(n+2)` exceptional, so eventually none has. -/
theorem eventually_not_exceptional {E : ℂ → ℂ} (hE : IsStrictHB E) :
    ∀ᶠ n : ℕ in atTop, ¬ Exceptional E (Real.pi / 2 + Real.pi / (n + 2)) := by
  sorry
```

*Proof.* Put `α_n = π/2 + π/(n+2)`, `n ∈ ℕ`. If `n ≠ m` are both exceptional, `memHE_sAlpha_unique` gives
`k ∈ ℤ` with `α_m - α_n = kπ`, i.e. `1/(m+2) - 1/(n+2) = k`; but `0 < |1/(m+2) - 1/(n+2)| < 1/2`,
so `k` cannot be an integer. So the set of exceptional `n` has at most one element, hence is finite,
and the filter statement follows from `Nat.cofinite_eq_atTop` / `Set.Finite.eventually_cofinite_notMem`. ∎

*Implemented:* also `Suff.exists_not_exceptional` (some `α` is non-exceptional for strict `E`), used by
`phase_tendsto`, `phase_mul_bijective` and Corollary 1.

## 2. Step 1: the real zeros of `F`

```lean
/-- **Weierstrass factorisation of the real zeros** (new lemma, `S` of the paper): an entire
`F ∈ \overline{HB}`, `F ≢ 0`, factors as `F = S G` with `S` real entire (`S^* = S`) whose zeros are
exactly the real zeros of `F` (with multiplicity), and `G ∈ \overline{HB}` without real zeros.
Needs Weierstrass products of non-constant genus (not in Mathlib); see the blueprint. -/
theorem exists_realFactor {F : ℂ → ℂ} (hF : IsHB F) (hF0 : ∃ z, F z ≠ 0) :
    ∃ S G : ℂ → ℂ, Differentiable ℂ S ∧ IsHB G ∧ (∀ z, F z = S z * G z) ∧
      (∀ z, fstar S z = S z) ∧ (∀ z, S z = 0 → z.im = 0) ∧ (∀ x : ℝ, G x ≠ 0) := by
  sorry
```

*Proof.* This is the factorisation `F = S F̃` of p. 795 ("`S` is an entire function with real zero set `Z(S)`
and `S^* = S`"), which the paper asserts without proof.

**Can `F` have infinitely many real zeros?** Yes: *every real entire function `S` (`S^* = S`) with only real
zeros belongs to `\overline{HB}`*, and there are such functions with infinitely many (separated) zeros of
arbitrary multiplicity: with `E = e^{-iπz}` and `F = sin²(πz)`, `EF + E^*F^* = 2 sin²(πz) cos(πz)` has zero set `½ℤ`
and `F` has the infinitely many *double* real zeros `ℤ`; the same with `F = S` any real entire function with real zeros
gives zero set `Z(S) ∪ (ℤ + ½)`. So the general case must be handled, including
*multiplicities*. (Real zeros of `F` are zeros of `EF + E^*F^*`, hence they belong to the separated `Λ`.)

*Construction (Weierstrass product with variable genus).* Let `Z = {x ∈ ℝ : F x = 0}`; as `F ≢ 0` it is
discrete, and for `x ∈ Z` let `m(x) = analyticOrderNatAt F x ≥ 1`
(`AnalyticAt.analyticOrderAt_ne_top` for `F ≢ 0` and the identity theorem). Enumerate
`Z ∖ {0} = {a_n}_{n ≥ 1}` (finite or infinite; if infinite `|a_n| → ∞` since `Z` is discrete and
closed); `m_n = m(a_n)`. Let `E_p(w) = (1 - w) exp(w + w²/2 + … + w^p/p)`; one has
`|E_p(w) - 1| ≤ |w|^{p+1}` for `|w| ≤ 1` (Rudin, *Real and complex analysis* 15.8: the Taylor
coefficients of `1 - E_p` beyond `p` are `≥ 0` and sum to `1`). Choose `p_n ∈ ℕ` with `m_n 2^{-p_n} ≤ 2^{-n}`
and set
```
S(z) = z^{m(0)} ∏_n E_{p_n}(z/a_n)^{m_n}     (m(0) = 0 if 0 ∉ Z).
```
On `|z| ≤ R` and for `|a_n| ≥ 2R` the factor satisfies `|E_{p_n}^{m_n} - 1| ≤ 2 m_n |E_{p_n} - 1| ≤ 2 m_n 2^{-p_n-1} ≤ 2^{-n}`
whenever `m_n |E-1| ≤ 1`, so the product converges locally uniformly (`HasProdLocallyUniformlyOn`; the same pattern
as `OCS.hasProdLocallyUniformlyOn_canonicalProd`, `OrtegaCerdaSeip/Products/Canonical.lean`, which treats
*simple* zeros and `p = 1` only and therefore does **not** suffice when multiplicities are unbounded).
`S` is entire, vanishes exactly on `Z` with order exactly `m(x)` (a convergent product has the order of the
finitely many vanishing factors), and has real Taylor coefficients, so `S^* = S` (`fstar S z = conj (S (conj z))`:
`E_p(conj w) = conj E_p(w)` termwise, then pass to the limit).

*The quotient.* `G := F / S` is meromorphic with non-negative divisor (`order F ≥ order S` at every point,
and `S` is zero-free off `ℝ`), hence entire. In Lean: define `G z := F z / S z` where `S z ≠ 0` and at a real
zero `a` set `G a := limUnder (𝓝[≠] a) (F/S)`, and use
`Complex.differentiableOn_update_limUnder_of_bddAbove` on a punctured disc around `a` containing no other zero;
at `a` the quotient is bounded because `F = (z-a)^m F₁`, `S = (z-a)^m S₁` with `S₁(a) ≠ 0`
(`AnalyticAt.exists_eq_pow_smul_nonzero`-type lemma, or `MeromorphicOn.divisor`). The real zeros of `G` are
none, since the orders cancel.

`IsHB G`: `G z ≠ 0` for `Im z > 0` because `F z ≠ 0` there; and for `Im z > 0`,
`|S(z̄)| = |conj S(z)| = |S(z)| ≠ 0` so `|G(z̄)| = |F(z̄)|/|S(z̄)| ≤ |F(z)|/|S(z)| = |G(z)|`.

*Fallback if the implementer wants to avoid general Weierstrass products:* the only place where
non-simple zeros matter is the multiplicity; if one proves first (it is *not* known to follow from the
hypotheses) that real zeros of `F` are simple, `OCS.canonicalProd` suffices. In general it does not
(a real `F` with a zero of order `n` at `n`, `n ≥ 1`). ∎

*Implemented* (`Theorem1/Sufficiency/RealFactor/*`; `impl_notes/sufficiency.md`):
- the nonzero real zeros are indexed by the subtype `Zr F`, with genus `p_a = m(a) + rank(a) + 1`,
  `rank : Zr F → ℕ` an injection (`RealFactor/Product.lean`);
- the bound is `‖E_p(w)^m − 1‖ ≤ 4m‖w‖^{p+1}` for `‖w‖ ≤ 1/2` and `2m‖w‖^{p+1} ≤ 1`, from the tail of
  the logarithm series (`elemFactor_eq_exp_neg_tail`, `norm_elemFactor_pow_sub_one_le`,
  `RealFactor/Elem.lean`), not Rudin's coefficient argument;
- convergence goes through the abstract locally uniform product of `RealFactor/LUProd.lean`;
- `G = F/S` is extended by `limUnder` at the zeros of `S` and shown entire by the local factorisation
  `quotG_local` (`analyticOrderAt`, `RealFactor/Main.lean`).

Neither this route nor the enumeration above needs separation of the zeros.

```lean
/-- The reduction of p. 795: `F` can be replaced by `G` without real zeros, at the price of
shrinking `Λ`. -/
theorem exists_noRealZero_hb {E F : ℂ → ℂ} {Λ : Set ℝ} (hFHB : IsHB F)
    (hzero : ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ)) :
    ∃ G : ℂ → ℂ, IsHB G ∧ (∀ x : ℝ, G x ≠ 0) ∧
      ∀ z : ℂ, E z * G z + fstar E z * fstar G z = 0 → ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry
```

*Proof.* `F ≢ 0`: otherwise `z = i` would be a zero of `EF + E^*F^*` (value `0`), but the zero set is `⊆ ℝ`.
Take `S, G` from `exists_realFactor`. Then `fstar F = fstar S · fstar G = S · fstar G`, hence
`E F + E^* F^* = S (E G + E^* G^*)`. If `E G + E^* G^* = 0` at `z`, then `E F + E^* F^* = 0` at `z`,
and `hzero` gives `x ∈ Λ`, `z = x`. ∎

*Consequence.* If `Λ_1 := {x : E G + E^* G^* = 0}` then `Λ_1 ⊆ Λ`. The paper's claim "if `Λ_1` is sampling then so
is `Λ`" holds because `Λ ⊇ Λ_1` and `Λ` is separated: the lower sampling bound passes to the superset
(`sampleSum_mono`) and the upper bound for the separated `Λ` is `plancherelPolya` (M01); the paper
only mentions the former.

## 3. Step 2: the phase of `E G` is a homeomorphism of `ℝ`

The paper silently indexes `Λ_α = {λ_{α,k}}_{k ∈ ℤ}`, which presupposes that `φ_{EF}` is a bijection `ℝ → ℝ`.

```lean
/-- For `H(E) = PW` and `α` non-exceptional for `E`, `Γ_α = {φ_E ∈ α + πℤ}` is separated
(README §3.8). -/
theorem HEEqPW.levelSet_separated (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {α : ℝ}
    (hα : ¬ Exceptional E α) : IsSeparated (phaseLevel φ α) := by
  sorry
```

*Proof.* (README §3.8.) Let `c₁ > 0` with `φ_E'|E|² ≥ c₁` (`HEEqPW.phaseDeriv_mul_sq_ge`), and `(c, C)`
the equivalence constants of `hEPW`. By `HEEqPW.isStrictHB`, `E` is strict without real zeros, so `TheoremE`
applies to `E, φ, α`. For `γ ∈ Γ = phaseLevel φ α` let `a := Pi.single`-type datum `a x = if x = γ then 1 else 0`.
Then `∑' x : Γ, orthWeight E x * ‖a x‖ₑ² = orthWeight E γ ≤ ofReal(π/c₁) < ∞`
(`ENNReal.tsum_eq_...`/`tsum_eq_single`), so the second part of Theorem E gives `f_γ ∈ H(E)` with `f_γ = a`
on `Γ`, and the first part gives `heNormSq E f_γ = ∑' x : Γ, orthWeight E x * ‖f_γ x‖ₑ² = orthWeight E γ ≤ ofReal(π/c₁)`.
By `hEPW.1`, `f_γ ∈ PW`, and `c · pwNormSq f_γ ≤ heNormSq E f_γ` gives
`(pwNormSq f_γ).toReal ≤ π/(c c₁) =: K₁`. By `pw_deriv_bound`, `‖f_γ'(x)‖² ≤ C_B K₁` for all real `x`.
For `γ ≠ γ'` in `Γ`: `f_γ(γ) = 1`, `f_γ(γ') = 0`; the function `t ↦ f_γ(t)` on `ℝ` has derivative of norm
`≤ √(C_B K₁) =: Θ` (use `HasDerivAt.comp_ofReal`, `Convex.norm_image_sub_le_of_norm_deriv_le`), so
`1 ≤ Θ |γ - γ'|`, i.e. `|γ - γ'| ≥ 1/Θ`. (If `C_B K₁ ≤ 0` we get a contradiction, so `Θ > 0`; replace `Θ` by `max Θ 1`.) ∎

*Implemented* (`Theorem1/Sufficiency/LevelSet.lean`): separation constant `1/(Θ + 1)` with
`Θ = √((πe)² max(K, 0))`, `K = π/(c₁ c)` (`pw_deriv_bound` has the explicit constant `(πe)²`).

```lean
/-- For `H(E) = PW` and `α` non-exceptional, `Γ_α` is a complete interpolating sequence. -/
theorem HEEqPW.levelSet_cis (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {α : ℝ}
    (hα : ¬ Exceptional E α) : IsCompleteInterpolating (phaseLevel φ α) := by
  sorry
```

*Proof.* Let `w(x) = orthWeight E x ≤ ofReal(π/c₁)` as above. *Existence:* for `a : ℝ → ℂ` with
`∑'_Γ ‖a‖ₑ² < ∞`, `∑'_Γ w ‖a‖ₑ² ≤ ofReal(π/c₁) ∑'_Γ ‖a‖ₑ² < ∞` (`ENNReal.tsum_mul_left`), so Theorem E gives
`f ∈ H(E) = PW` with `f = a` on `Γ`. *Uniqueness:* if `f, g ∈ PW` agree on `Γ`, then `h = f - g ∈ PW = H(E)`
(`MemPW.sub`) vanishes on `Γ`, so by Theorem E `heNormSq E h = ∑' w · 0 = 0`; `c · pwNormSq h ≤ heNormSq E h`
gives `pwNormSq h = 0`, and `MemPW.eq_zero_of_pwNormSq_eq_zero` gives `h ≡ 0` (no `hPW` needed,
NOTEBOOK I-03). ∎

```lean
/-- If `H(E) = PW`, the phase of `E` is unbounded in both directions (so `Γ_α` is infinite on both
sides). -/
theorem HEEqPW.phase_tendsto (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ)
    (hφ' : ∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x) :
    Tendsto φ atTop atTop ∧ Tendsto φ atBot atBot := by
  sorry
```

*Proof* (needed to index `Γ_α` by `ℤ`; the paper does not mention it). Take the `+∞` end; `−∞` is symmetric. `φ` is
strictly increasing by `hφ'` and `IsStrictHB.phaseDeriv_pos` (`strictMono_of_hasDerivAt_pos`); `E` is strict without
real zeros by `HEEqPW.isStrictHB`, `ne_zero_ofReal`. By `Filter.tendsto_atTop_atTop_of_monotone`
it suffices to show `φ` is not bounded above. Suppose `φ ≤ b`. Choose `α` non-exceptional for `E`
(`eventually_not_exceptional` gives one). `Γ := phaseLevel φ α` is separated (`δ`) by `levelSet_separated`
and `Γ ∩ [0,∞) ⊆ {x ≥ 0 : φ(x) ∈ [φ 0, b]}` is *finite* (finitely many `k` with `α + kπ ∈ [φ 0, b]`, and
`x` determined by `k` since `φ` is injective). Let `g ∈ PW`, `g(0) = 1` (`exists_memPW_eval_ne_zero`); by
`pw_norm_sq_le`, `pwNormSq g ≠ 0`. For `R > 0` set `g_R(z) = g(z - R) ∈ PW` (`MemPW.comp_sub_ofReal`),
`pwNormSq g_R = pwNormSq g` (`pwNormSq_comp_sub_ofReal`). Now
```
c · pwNormSq g ≤ heNormSq E g_R = ∑_{γ ∈ Γ} orthWeight(γ) |g_R(γ)|²                  (Theorem E)
                ≤ ofReal(π/c₁) ( ∑_{γ ∈ Γ∩[0,∞)} |g(γ - R)|² + sampleSum ((Γ∩(-∞,0)) - R) g ).
```
The first sum is a *finite* sum of terms `|g(γ - R)|² → 0` as `R → ∞` (use `plancherelPolya_tail` with the
one-point set `{x}`: `|g(x)|² ≤ ε` for `|x| ≥ R_ε`). The set `(Γ ∩ (-∞,0)) - R` is `δ`-separated and contained in
`{x ≤ -R} ⊆ {|x| ≥ R}`, so by `plancherelPolya_tail` (with `δ`, `f = g`) its sum is `≤ ε` once `R ≥ R_ε`.
Taking `ε` with `ofReal(π/c₁) · 2ε < c · pwNormSq g` (positive, finite) gives a contradiction for `R` large.
The translation of the sampling sum is the bijection `x ↦ x - R` of `ℝ` (`Equiv.tsum_eq`). ∎

*Implemented* (`Theorem1/Sufficiency/Phase.lean`): with `Suff.exists_not_exceptional` and `pwBump`. The norm
identity gives a uniform lower bound `ε₀ ≤ sampleSum Γ (g(· − t))` for the translates
(`translate_lower_bound_aux`); the level set is bounded on one side (`bddAbove_phaseLevel`), and the
Plancherel–Pólya tail (`translate_tail`) gives the contradiction for far translates. No `ℤ`-indexing and no
finite-part/tail split.

```lean
/-- The phase `ψ = φ_E + φ_G` of `EG` is a continuous increasing bijection of `ℝ`
(`G ∈ \overline{HB}` without real zeros, `H(E) = PW`). -/
theorem HEEqPW.phase_mul_bijective (hPW : PaleyWienerThm) (hE : TheoremE) {E G : ℂ → ℂ}
    (hEHB : IsHB E) (hGHB : IsHB G) (hEPW : HEEqPW E) (hG0 : ∀ x : ℝ, G x ≠ 0)
    {φE φG : ℝ → ℝ} (hφE : IsPhaseFunction E φE) (hφE' : ∀ x : ℝ, HasDerivAt φE (phaseDeriv E x) x)
    (hφG : IsPhaseFunction G φG) (hφG' : ∀ x : ℝ, HasDerivAt φG (phaseDeriv G x) x) :
    StrictMono (fun x ↦ φE x + φG x) ∧ Function.Surjective (fun x ↦ φE x + φG x) := by
  sorry
```

*Proof.* `ψ' = φ_E' + φ_G' ≥ φ_E' > 0` (`phaseDeriv_mul` is not even needed: apply `HasDerivAt.add` to
`hφE'`, `hφG'`, and `IsHB.phaseDeriv_nonneg` for `G`, `IsStrictHB.phaseDeriv_pos` for `E`, with `E` strict from
`HEEqPW.isStrictHB`), so `ψ` is strictly increasing (`strictMono_of_hasDerivAt_pos`). Also `φ_G` is monotone
(`monotone_of_hasDerivAt_nonneg`), so for `x ≥ 0`, `ψ(x) ≥ φ_E(x) + φ_G(0)` and for `x ≤ 0`,
`ψ(x) ≤ φ_E(x) + φ_G(0)`; by `HEEqPW.phase_tendsto`, `ψ → ±∞` at `±∞`
(`tendsto_atTop_mono'`, `tendsto_atBot_mono'`). A continuous function with these limits is onto
(`Continuous.surjective`). ∎

## 4. Step 3: interlacing

```lean
/-- **Interlacing** (p. 796): if the level set `Λ = {φ ∈ π/2 + πℤ}` of a continuous strictly
increasing `φ` is `δ`-separated, then `{φ ∈ π/2 + ε + πℤ}` (`0 < ε < π`) is a union of two
`δ`-separated sets (even and odd index). -/
theorem phaseLevel_sepBy_two {φ : ℝ → ℝ} (hc : Continuous φ) (hφ : StrictMono φ) {δ : ℝ}
    (hsep : IsSepBy δ (phaseLevel φ (Real.pi / 2))) {ε : ℝ} (hε0 : 0 < ε) (hεπ : ε < Real.pi) :
    ∃ A B : Set ℝ, phaseLevel φ (Real.pi / 2 + ε) = A ∪ B ∧ IsSepBy δ A ∧ IsSepBy δ B := by
  sorry
```

*Proof* (p. 796, "interlaced ... union of two separated sequences"). Let `α = π/2 + ε`, `Λ_1 = phaseLevel φ (π/2)`.
Put `A := {x | ∃ k : ℤ, φ x = α + kπ ∧ Even k}`, `B := {x | ∃ k, φ x = α + kπ ∧ Odd k}`; `A ∪ B = phaseLevel φ α`
(`Int.even_or_odd`). Let `x < y` both in `A` (or both in `B`), with `φ x = α + kπ`, `φ y = α + k'π`. Then `k' > k`
(`φ` strictly increasing) and `k' - k` is even, so `k' ≥ k + 2`. The two numbers
`u₁ = π/2 + (k+1)π`, `u₂ = π/2 + (k+2)π` lie strictly between `φ x` and `φ y`:
`φ x = π/2 + ε + kπ < u₁` as `ε < π`, and `u₂ ≤ π/2 + k'π < π/2 + ε + k'π = φ y` as `ε > 0`.
By the intermediate value theorem (`intermediate_value_Icc`, `φ` continuous) there are `z₁, z₂ ∈ (x, y)` (strictly,
because the values `u_i` are not equal to `φ x, φ y`, and `φ` is injective) with `φ z_i = u_i`; thus
`z₁, z₂ ∈ Λ_1`, `z₁ ≠ z₂` (different `φ`-values), so `δ ≤ |z₁ - z₂| < y - x`. Hence `A, B` are `δ`-separated. ∎

(The paper says "each with separation constant not smaller than that of `Λ`"; this is confirmed and in fact strict.)

## 5. Step 4: Theorem E, uniformly in `α`

```lean
/-- Theorem E gives the uniform inequality `‖f‖² ≤ C₀ ∑_{Λ_α} |f|²` for `EG`, `G ∈ \overline{HB}`
without real zeros, for every non-exceptional `α`, with `C₀` depending only on `E`. -/
theorem HEEqPW.levelSet_ineq (hE : TheoremE) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) :
    ∃ C₀ : ℝ≥0, 0 < C₀ ∧ ∀ G : ℂ → ℂ, IsHB G → (∀ x : ℝ, G x ≠ 0) → ∀ ψ : ℝ → ℝ,
      IsPhaseFunction (fun z ↦ E z * G z) ψ → ∀ α : ℝ,
        ¬ Exceptional (fun z ↦ E z * G z) α → ∀ f : ℂ → ℂ, MemPW f →
          pwNormSq f ≤ C₀ * sampleSum (phaseLevel ψ α) f := by
  sorry
```

*Proof.* (p. 796, "`‖f‖² ≃ ∫|f/E|² = ... = ∑ ...`"; this is formula (equiv) with the constants made explicit.)
Let `(c, C)` be from `hEPW.2`, `c₁` from `HEEqPW.phaseDeriv_mul_sq_ge`; set
`C₀ := c⁻¹ · (π/c₁)` (as an element of `ℝ≥0`, via `Real.toNNReal`; `C₀ > 0`). Fix `G`, `ψ`, `α` as in the statement and
put `E' := fun z ↦ E z * G z`. Then:
1. `E'` is strict and has no real zeros: `HEEqPW.isStrictHB`, `IsStrictHB.mul_isHB`, `mul_ne_zero`.
2. For `f ∈ PW`: `f ∈ H(E)` (`hEPW.1`), so `g := fun z ↦ G z * f z ∈ H(E')` (`MemHE.mul_isHB`) and
   `heNormSq E' g = heNormSq E f` (`heNormSq_mul`).
3. Theorem E for `E', ψ, α` (hypothesis: `¬ Exceptional E' α`):
   `heNormSq E' g = ∑' γ : phaseLevel ψ α, orthWeight E' γ * ‖g γ‖ₑ²`.
4. *Termwise bound.* For real `γ`, by `phaseDeriv_mul`, `phaseDeriv E' γ = phaseDeriv E γ + phaseDeriv G γ ≥ phaseDeriv E γ > 0`
   (`IsHB.phaseDeriv_nonneg`, `IsStrictHB.phaseDeriv_pos`), `‖E' γ‖² = ‖E γ‖²‖G γ‖²`, `‖g γ‖ₑ = ‖G γ‖ₑ ‖f γ‖ₑ`, hence
   ```
   orthWeight E' γ * ‖g γ‖ₑ² = ofReal(π /(φ_{E'}'(γ) ‖E γ‖²)) ‖f γ‖ₑ²  ≤ ofReal(π/(φ_E'(γ)‖E γ‖²)) ‖f γ‖ₑ²
                                ≤ ofReal(π/c₁) ‖f γ‖ₑ².
   ```
   (`ENNReal.ofReal_mul`, `div_le_div_of_nonneg_left`; `‖G γ‖ ≠ 0` cancels.) **This is the step where
   "`φ_{EF}' ≥ φ_E'`" (as printed on p. 796) is used.**
5. Summing (`ENNReal.tsum_mul_left`, `ENNReal.tsum_le_tsum`) gives `heNormSq E f ≤ ofReal(π/c₁) · sampleSum (phaseLevel ψ α) f`,
   and `c · pwNormSq f ≤ heNormSq E f` gives `pwNormSq f ≤ c⁻¹ ofReal(π/c₁) · sampleSum … = C₀ · sampleSum …`.

`C₀` depends only on `c` (norm equivalence of `E`) and `c₁` (`φ_E'|E|² ≥ c₁`), *not* on `G`, `ψ`, `α` or `f`.
(The *Plancherel–Pólya* inequality (planpol) is not needed at this point; the paper's "inequality (planpol)"
is used only to control tails in §6.) ∎

## 6. Step 5: the limit `α_n → π/2`

```lean
/-- **The limit argument** (README §3.5): if `{φ ∈ π/2 + πℤ}` is `δ`-separated, `φ` is a
continuous increasing bijection of `ℝ`, and `‖f‖² ≤ C₀ ∑_{Λ_{α_n}} |f|²` for all `f ∈ PW` and
all `n` large, with `α_n = π/2 + ε_n`, `0 < ε_n < π`, `ε_n → 0`, then the same inequality holds for
`Λ = Λ_{π/2}`. -/
theorem levelSet_limit (hPW : PaleyWienerThm) {ψ : ℝ → ℝ} (hψc : Continuous ψ)
    (hψm : StrictMono ψ) (hψs : Function.Surjective ψ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : IsSepBy δ (phaseLevel ψ (Real.pi / 2))) {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hεπ : ∀ n, ε n < Real.pi)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hlev : ∀ᶠ n in atTop, ∀ f : ℂ → ℂ, MemPW f →
      pwNormSq f ≤ C₀ * sampleSum (phaseLevel ψ (Real.pi / 2 + ε n)) f) :
    ∀ f : ℂ → ℂ, MemPW f → pwNormSq f ≤ C₀ * sampleSum (phaseLevel ψ (Real.pi / 2)) f := by
  sorry
```

*Proof.* (README §3.5.) `Λ_c := phaseLevel ψ c`. Let `Ψ := (hψm.orderIsoOfSurjective ψ hψs).symm` (continuous,
`OrderIso.continuous`); then `Λ_c = range (k ↦ Ψ(c + kπ))` and the points `x^c_k := Ψ(c + kπ)` are strictly
increasing in `k`. Write `Λ₀ = Λ_{π/2}`, `T := sampleSum Λ₀ f`. Fix `f ∈ PW`; `pwNormSq f < ∞` (`pwNormSq_ne_top`).
To show `pwNormSq f ≤ C₀ T` it suffices (`ENNReal.le_of_forall_pos_le_add`, `C₀ ≠ ∞`) to show
`pwNormSq f ≤ C₀ (T + 3η)` for every real `η > 0`.

(a) *Uniform tail.* `plancherelPolya_tail` (`δ`, `f`, `ε := ofReal η`) gives `R > 0` with
`sampleSum (Λ' ∩ {|x| ≥ R}) f ≤ η` for every `δ`-separated `Λ'`.

(b) For `n` with `hlev n` and (by `phaseLevel_sepBy_two`, using `hsep`, `hε0`, `hεπ`) `Λ_{α_n} = A_n ∪ B_n` with
`A_n, B_n` `δ`-separated, `α_n = π/2 + ε_n`:
`sampleSum (Λ_{α_n} ∩ {|x| ≥ R}) f ≤ sampleSum (A_n ∩ {|x| ≥ R}) f + sampleSum (B_n ∩ {|x| ≥ R}) f ≤ 2η`
(`Set.inter_union_distrib_right`, `sampleSum_union_le`, `sampleSum_mono`, `IsSepBy.mono`). Hence, by `sampleSum_split` with this `R`,
`sampleSum Λ_{α_n} f ≤ sampleSum (Λ_{α_n} ∩ {|x| < R}) f + 2η`. **This replaces the "dominated convergence" of the paper.**

(c) *Finite part.* Let `K := {k ∈ ℤ | |x^{π/2}_k| < R + 1}` — finite, because `|x^{π/2}_k| < R+1` forces
`π/2 + kπ ∈ (ψ(-R-1), ψ(R+1))`, a bounded interval. Let `κ := ψ(-R) - ψ(-R-1) > 0`. For `n` so large that `ε_n < κ`
(`hεlim`): if `|x^{α_n}_k| < R` then `ψ(-R) < α_n + kπ < ψ(R)`, so
`π/2 + kπ = α_n + kπ - ε_n ∈ (ψ(-R-1), ψ(R))`, whence `|x^{π/2}_k| < R + 1`, i.e. `k ∈ K`. Therefore
`Λ_{α_n} ∩ {|x| < R} ⊆ {x^{α_n}_k : k ∈ K}` and
`sampleSum (Λ_{α_n} ∩ {|x| < R}) f ≤ ∑_{k ∈ K} ‖f(x^{α_n}_k)‖ₑ²` (monotonicity, and the sum over a finite image is
at most the finite sum: `Finset.sum_image_le`-type, `tsum_fintype`).

(d) *Convergence.* For each fixed `k`, `x^{α_n}_k = Ψ(π/2 + ε_n + kπ) → Ψ(π/2 + kπ) = x^{π/2}_k` (continuity of `Ψ`),
and `‖f(·)‖ₑ²` is continuous (`Continuous.enorm`, `ENNReal.continuous_pow`), so the finite sums converge:
`∑_{k ∈ K}‖f(x^{α_n}_k)‖ₑ² → ∑_{k ∈ K}‖f(x^{π/2}_k)‖ₑ² =: T_K` (`tendsto_finset_sum`). `T_K < ∞`, so eventually
`≤ T_K + η` (`Filter.Tendsto.eventually_lt` with `T_K < T_K + η`). Finally `T_K ≤ T` (the points `x^{π/2}_k`, `k ∈ K`,
are distinct elements of `Λ₀`).

(e) Choose `n` large for (b)–(d): `pwNormSq f ≤ C₀ sampleSum Λ_{α_n} f ≤ C₀ (T_K + η + 2η) ≤ C₀ (T + 3η)`. ∎

*Implemented* (`Theorem1/Sufficiency/Limit.lean`): one application of `plancherelPolya_tail_union` to
`A_n ∪ B_n` replaces the two tails of (a)–(b), so the bound is `C₀(T + 2η)`; the limit `η → 0` is taken
along `η_m = (m+1)⁻¹` in `ℝ≥0∞`.

(*Remark.* No indexing issue arises at the ends: surjectivity of `ψ` guarantees `Λ_c = {x^c_k : k ∈ ℤ}` for all `c`;
if `ψ` were bounded, one extra point could escape to infinity, which is also covered by the tail estimate, but
surjectivity (§3) makes it unnecessary.)

## 7. The theorem

```lean
/-- **Theorem 1** (p. 795), sufficiency. -/
theorem theorem1_sufficiency (hPW : PaleyWienerThm) (hE : TheoremE)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) {E F : ℂ → ℂ} (hEHB : IsHB E) (hFHB : IsHB F)
    (hEPW : HEEqPW E) (hzero : ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ)) :
    IsSampling Λ := by
  sorry
```

*Proof.*
1. `E` is strict without real zeros: `HEEqPW.isStrictHB hPW hEHB hEPW`, `HEEqPW.ne_zero_ofReal`.
2. `exists_noRealZero_hb` gives `G ∈ \overline{HB}` without real zeros and `Λ_1 := {x : E G + E^* G^* = 0} ⊆ Λ`.
3. `exists_isPhaseFunction` gives `φ_E, φ_G` with `HasDerivAt φ (phaseDeriv ·) x`; `ψ := φ_E + φ_G`
   is a phase function of `E' = EG` (`isPhaseFunction_mul`), `ψ` is continuous, strictly increasing and surjective
   (`HEEqPW.phase_mul_bijective`).
4. By `zero_set_eq_phaseLevel` (`E` strict, `G ∈ \overline{HB}`, no real zeros) and `exists_noRealZero_hb`:
   `Λ₁ := phaseLevel ψ (π/2) ⊆ Λ` (for `x ∈ Λ₁`, `E G + E^* G^*` vanishes at `x`, so `x ∈ Λ`). Let `δ > 0`
   separate `Λ`; then `Λ₁` is `δ`-separated.
5. `HEEqPW.levelSet_ineq` gives `C₀ > 0`; let `ε_n := π/(n+2) ∈ (0, π/2]`, `ε_n → 0`. By `eventually_not_exceptional`
   for the strict `E'`, `¬ Exceptional E' (π/2 + ε_n)` eventually, so `hlev` of `levelSet_limit` holds.
6. `levelSet_limit` gives `pwNormSq f ≤ C₀ · sampleSum Λ₁ f` for all `f ∈ PW`.
7. `IsSampling Λ` with `A := C₀⁻¹` (`ENNReal.coe_inv`, `ENNReal.inv_mul_le_iff`): `A · pwNormSq f ≤ sampleSum Λ₁ f
   ≤ sampleSum Λ f` (`sampleSum_mono`), and `B` from `plancherelPolya hPW hδ` (`Λ` is `δ`-separated). ∎

*Constants.* The lower sampling constant is `C₀⁻¹ = c · c₁/π`, depending only on the norm equivalence of `E` and on
`inf φ_E'|E|²`; the upper one on `δ` only.

## 8. `theorem1`

```lean
/-- **Theorem 1** (p. 795): a separated sequence `Λ` is sampling for `PW` if and only if there are
`E, F ∈ \overline{HB}` with `H(E) = PW` such that `Λ` is the zero set of `EF + E^*F^*`. -/
theorem theorem1 (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) :
    IsSampling Λ ↔ ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  constructor
  · intro hs
    exact theorem1_necessity hPW hC hF hΛ hs
  · rintro ⟨E, F, hEHB, hFHB, hEPW, hzero⟩
    exact theorem1_sufficiency hPW hE hΛ hEHB hFHB hEPW hzero
```

*Proof.* `(→)` is `theorem1_necessity hPW hC hF hΛ hs` (M03); `(←)` is `theorem1_sufficiency hPW hE hΛ …`. ∎

## 9. Corollary 1 (p. 798)

```lean
/-- A continuous increasing bijection `φ` of `ℝ` has level sets `{φ ∈ α + πℤ}` enumerated
increasingly by `ℤ`. -/
theorem exists_levelSet_enum {φ : ℝ → ℝ} (hm : StrictMono φ) (hs : Function.Surjective φ)
    (α : ℝ) : ∃ γ : ℤ → ℝ, StrictMono γ ∧ Set.range γ = phaseLevel φ α := by
  classical
  let e : ℝ ≃o ℝ := hm.orderIsoOfSurjective φ hs
  refine ⟨fun k ↦ e.symm (α + k * Real.pi), ?_, ?_⟩
  · intro j k hjk
    apply e.symm.strictMono
    have := Real.pi_pos
    have : (j : ℝ) < k := by exact_mod_cast hjk
    nlinarith
  · ext x
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      have : φ (e.symm (α + k * Real.pi)) = α + k * Real.pi := e.apply_symm_apply _
      exact this
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply e.injective
      rw [e.apply_symm_apply]
      exact hk.symm
```


```lean
/-- A half-open interval `[u, v)` with `v - u ≥ π` meets every coset `c + πℤ`. -/
theorem exists_mem_Ico_add_int_mul_pi (c u v : ℝ) (h : u + Real.pi ≤ v) :
    ∃ j : ℤ, u ≤ c + j * Real.pi ∧ c + j * Real.pi < v := by
  have hπ := Real.pi_pos
  refine ⟨⌈(u - c) / Real.pi⌉, ?_, ?_⟩
  · have := Int.le_ceil ((u - c) / Real.pi)
    rw [div_le_iff₀ hπ] at this
    linarith
  · have := Int.ceil_lt_add_one ((u - c) / Real.pi)
    have h2 : (⌈(u - c) / Real.pi⌉ : ℝ) * Real.pi < ((u - c) / Real.pi + 1) * Real.pi :=
      mul_lt_mul_of_pos_right this hπ
    have h3 : ((u - c) / Real.pi + 1) * Real.pi = u - c + Real.pi := by field_simp
    linarith
```


```lean
/-- **Corollary 1**, strong form: the complete interpolating sequence `Γ` can be taken
separated (needed by Pavlov's theorem in the Claim). -/
theorem corollary1_strong (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE)
    (hF : TheoremF) {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ IsSeparated (Set.range γ) ∧
      IsCompleteInterpolating (Set.range γ) ∧ ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1) := by
  sorry
```

*Proof.*
1. By `theorem1_necessity` there are `E, F ∈ \overline{HB}` with `H(E) = PW` and `Λ` the zero set of `EF + E^*F^*`.
   (This is *all* we use from `F`; `E` and `F` are fixed from now on.) As in §7, `E` is strict without real zeros,
   `exists_noRealZero_hb` gives `G` (no real zeros, `Λ_1 ⊆ Λ`), and there are phases `φ_E, φ_G` with derivatives
   `phaseDeriv`. `φ_E` is continuous, strictly increasing, and onto (`phase_tendsto`, `Continuous.surjective`).
2. Choose `α` non-exceptional for `E` (`eventually_not_exceptional ... |>.exists`), `Γ := phaseLevel φ_E α`
   (the paper's `Γ_α`; "the choice of `α` is at our disposal"). By `exists_levelSet_enum` there is a strictly
   increasing `γ : ℤ → ℝ` with `range γ = Γ`. `Γ` is separated (`HEEqPW.levelSet_separated`) and complete
   interpolating (`HEEqPW.levelSet_cis`).
3. *Interlacing.* Fix `k` and put `ψ = φ_E + φ_G`. `φ_G` is nondecreasing (`monotone_of_hasDerivAt_nonneg`,
   `IsHB.phaseDeriv_nonneg`), and `φ_E(γ_{k+1}) - φ_E(γ_k) = π`, so
   `ψ(γ_{k+1}) - ψ(γ_k) ≥ π`. This is the precise form of the paper's "`φ_E` grows more slowly than `φ_{EF}`":
   `φ_{EF} - φ_E = φ_G` is *nondecreasing* (it is not true that `φ_{EF} ≥ φ_E`; only increments matter).
   By `exists_mem_Ico_add_int_mul_pi` there is `j ∈ ℤ` with `ψ(γ_k) ≤ π/2 + jπ < ψ(γ_{k+1})`. By the intermediate value
   theorem (`intermediate_value_Icc`, `ψ` continuous) there is `x ∈ [γ_k, γ_{k+1}]` with `ψ(x) = π/2 + jπ`;
   `x ≠ γ_{k+1}` since `ψ(γ_{k+1}) > π/2 + jπ`. Thus `x ∈ phaseLevel ψ (π/2)`, so `E G + E^* G^* = 0` at `x`
   (`zero_set_eq_phaseLevel`), so `x ∈ Λ` (`exists_noRealZero_hb`), and `γ_k ≤ x < γ_{k+1}`. ∎

*Implemented* (`Corollary1.lean`): step 2 takes `α` from `exists_not_exceptional`. In step 3 the enumeration
of `exists_levelSet_enum` is abstract, so the code shows `φ_E(γ_{k+1}) − φ_E(γ_k) ≥ π` (distinct points of
`Γ` have `φ_E`-values differing by a positive multiple of `π`), not `= π`; this suffices.

```lean
/-- **Corollary 1** (p. 798): a separated sampling sequence is "everywhere denser" than some
complete interpolating sequence `Γ = {γ_k}`: every `[γ_k, γ_{k+1})` contains a point of `Λ`. -/
theorem corollary1 (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ IsCompleteInterpolating (Set.range γ) ∧
      ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1) := by
  obtain ⟨γ, h1, -, h3, h4⟩ := corollary1_strong hPW hC hE hF hΛ hs
  exact ⟨γ, h1, h3, h4⟩
```


**Why the strong form.** `PavlovBMO` is stated for *separated* `Γ`, and M05 applies it to the `Γ` of Corollary 1.
`corollary1` as stated in `comparator/statements.lean` loses the separation; so M05 uses `corollary1_strong`.
(Alternatively, a general lemma "complete interpolating ⇒ separated" would do, but it requires the bounded inverse
`isSampling_of_isCompleteInterpolating` below and the Bernstein argument; the proof above is shorter.)

## 10. The remark of p. 797

> "If `Λ` is a complete interpolating sequence, then there exists an `E ∈ \overline{HB}` such that `H(E) = PW`
> and `Λ` constitutes the zero sequence of `E + E^*`. This follows from Theorems C and E."

The paper's justification is two lines. Our proof uses Theorems C and **D** (not E) and goes as follows
(`Λ` separated, as in the Lean statement).

```lean
/-- A complete interpolating sequence is a sampling sequence (bounded inverse of the sampling map
`PW → ℓ²(Λ)`, open mapping theorem). -/
theorem isSampling_of_isCompleteInterpolating (hPW : PaleyWienerThm) {Λ : Set ℝ}
    (hΛ : IsSeparated Λ) (hcis : IsCompleteInterpolating Λ) : IsSampling Λ := by
  sorry
```

*Proof.* (Open mapping / closed graph.) Let `ℓ² = lp (fun _ : Λ ↦ ℂ) 2` and `L² = Lp ℂ 2 (volume : Measure ℝ)`.
The sampling map `S : PW → ℓ²`, `f ↦ (f(λ))_λ`, is well-defined and bounded by `plancherelPolya` (M01). By `hcis`,
for each `a ∈ ℓ²` (extended by `0` off `Λ`) there is a unique `f_a ∈ PW` with `f_a|_Λ = a`; `a ↦ f_a` is linear by
uniqueness. Define `T : ℓ² →ₗ L²`, `T a = [f_a|_ℝ]` (`MemLp.toLp`; `f_a|_ℝ ∈ L²` by `MemPW`). `T` has closed graph:
if `a_n → a` in `ℓ²` and `T a_n → g` in `L²`, then `(f_{a_n})` is Cauchy in `L²`, hence (by `pw_complete`, M01)
converges locally uniformly to some `f ∈ PW` whose restriction to `ℝ` represents `g`; evaluation at `λ ∈ Λ`
(continuous on `ℓ²` and on locally uniform limits) gives `f(λ) = lim a_n(λ) = a(λ)`; by uniqueness `f = f_a` and `g = T a`.
By the closed graph theorem (`LinearMap.continuous_of_isClosed_graph`, or the open mapping theorem via
`ContinuousLinearEquiv.ofBijective` applied to `S`) `T` is bounded: `‖f_a‖_{L²} ≤ C ‖a‖_{ℓ²}`. For `f ∈ PW`
take `a = (f(λ))_λ`: `f_a = f` (uniqueness), so `pwNormSq f ≤ C² · sampleSum Λ f` (lower sampling bound, `A = C⁻²`);
the upper bound is `plancherelPolya`. (Existence of `a` in `ℓ²`: `sampleSum Λ f < ∞` by `plancherelPolya`.) ∎

*Implemented:* the closed graph theorem for `T : ℓ²(Λ) → L²(ℝ)` as `LinearMap.continuous_of_seq_closed_graph`
(`Corollary1/ClosedGraph.lean`).

*Rotation lemmas used below* (all elementary): `IsHB.rotate` is in `HB/Basic.lean`, `IsPhaseFunction.rotate`
in `HB/Phase.lean` (moved at assembly); only `HEEqPW.rotate` is in `Corollary1.lean`, proved in
`Corollary1/Rotate.lean`.

```lean
theorem IsHB.rotate {E : ℂ → ℂ} (hE : IsHB E) (θ : ℝ) :
    IsHB (fun z ↦ Complex.exp (I * θ) * E z) := by
  sorry
```

```lean
theorem HEEqPW.rotate {E : ℂ → ℂ} (h : HEEqPW E) (θ : ℝ) :
    HEEqPW (fun z ↦ Complex.exp (I * θ) * E z) := by
  sorry
```

```lean
theorem IsPhaseFunction.rotate {E : ℂ → ℂ} {φ : ℝ → ℝ} (h : IsPhaseFunction E φ) (θ : ℝ) :
    IsPhaseFunction (fun z ↦ Complex.exp (I * θ) * E z) (fun x ↦ φ x - θ) := by
  sorry
```

(`|e^{iθ}| = 1`: same zeros off `ℝ`, same `‖·‖`, `H(e^{iθ}E) = H(E)` with the same norms, and
`e^{iθ}E(x) = |E(x)| e^{-i(φ(x) - θ)}`.)

```lean
/-- The zero set of `E + E^*` for `E` strict without real zeros. -/
theorem zero_set_single {E : ℂ → ℂ} (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0)
    {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) (z : ℂ) :
    E z + fstar E z = 0 ↔ ∃ x ∈ phaseLevel φ (Real.pi / 2), z = (x : ℂ) := by
  sorry
```

(*Proof:* `zero_set_eq_phaseLevel` with `F := fun _ ↦ 1`, which is in `\overline{HB}` (`isHB_one`) with phase `0`;
`fstar (fun _ ↦ 1) z = 1`.)

```lean
/-- Formula (1) of p. 793 on the real axis: `K_E(x, y) = |E(x)E(y)| sin(φ(y) - φ(x)) /
(π (y - x))` for real `x ≠ y`. -/
theorem deBrangesKernel_real {E : ℂ → ℂ} {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {x y : ℝ}
    (hxy : x ≠ y) :
    deBrangesKernel E x y =
      ((‖E x‖ * ‖E y‖ * Real.sin (φ y - φ x) / (Real.pi * (y - x)) : ℝ) : ℂ) := by
  sorry
```

(*Proof:* for `x ≠ y` real, `y ≠ conj x`, so the second branch of `deBrangesKernel` applies, and
`fstar E z = conj (E z)` for real `z`. With `E(x) = |E(x)|e^{-iφ(x)}`:
`E(y) conj E(x) - conj E(y) E(x) = 2i Im(E(y) conj E(x)) = -2i |E(x)E(y)| sin(φ(y) - φ(x))`, and
`(i/2) · (-2i) = 1`.)

```lean
/-- The kernels at the points of a complete interpolating sequence are orthogonal:
`K_E(a, b) = 0` for `a ≠ b` in `Λ` (Theorem D, Cauchy–Schwarz and the norm identity). -/
theorem kernel_orthogonal (hPW : PaleyWienerThm) (hD : TheoremD) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {Λ : Set ℝ} (hΛ : IsSeparated Λ)
    (hcis : IsCompleteInterpolating Λ)
    (hnorm : ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Λ f)
    {a b : ℝ} (ha : a ∈ Λ) (hb : b ∈ Λ) (hab : a ≠ b) : deBrangesKernel E a b = 0 := by
  sorry
```

*Proof.* `E` has no real zeros and `H(E) = PW` (so `E` is strict; `TheoremD` applies). Let `a ∈ Λ` and let `e_a ∈ PW` be the
interpolant of the datum `δ_a`, so `heNormSq E e_a = sampleSum Λ e_a = 1` by `hnorm`. Let `K := deBrangesKernel E a`;
by `TheoremD`, `K ∈ H(E) = PW`, so `k := ‖K‖²_E = heNormSq E K` is finite, and the reproducing property gives:
- with `f = K` at `w = a`: `∫ |K|²/|E|² = K(a)`, so `K(a) = k` (a non-negative real number);
- with `f = e_a` at `w = a`: `∫ e_a conj K/|E|² = e_a(a) = 1`; by Cauchy–Schwarz for the measure `|E|⁻² dt`
  (`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2`, `norm_integral_le_integral_norm`;
  integrability from `|e_a K̄| ≤ (|e_a|² + |K|²)/2` and the finiteness of the two norms), `1 ≤ ‖e_a‖_E ‖K‖_E = √k`, i.e. `k ≥ 1`.
By `hnorm` for `K`: `k = ∑_{γ ∈ Λ} |K(γ)|² ≥ |K(a)|² + ∑_{γ ≠ a} |K(γ)|² = k² + ∑_{γ ≠ a}|K(γ)|²`.
Since `k ≥ 1`, this forces `k = 1` and `∑_{γ ≠ a} |K(γ)|² = 0`, i.e. `K(b) = deBrangesKernel E a b = 0` for `b ∈ Λ`, `b ≠ a`. ∎

*Implemented* (`Corollary1/Kernel.lean`): instead of Cauchy–Schwarz, `uv ≤ (u² + v²)/2` gives
`1 ≤ (‖e_a‖²_E + k)/2 = (1 + k)/2`, i.e. `k ≥ 1`.

```lean
/-- Completeness: a complete interpolating `Λ` is a full level set of the phase. -/
theorem levelSet_eq_of_cis (hPW : PaleyWienerThm) (hD : TheoremD) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {Λ : Set ℝ} (hΛ : IsSeparated Λ)
    (hcis : IsCompleteInterpolating Λ)
    (hnorm : ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Λ f)
    {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) : ∃ β : ℝ, Λ = phaseLevel φ β := by
  sorry
```

*Proof.* `Λ ≠ ∅`: otherwise any two elements of `PW` (e.g. `0` and `g` from `exists_memPW_eval_ne_zero`) would
interpolate the empty datum, contradicting uniqueness. Fix `a₀ ∈ Λ`, `β := φ(a₀)`.
- `Λ ⊆ phaseLevel φ β`: for `b ∈ Λ`, `b ≠ a₀`, `kernel_orthogonal` and `deBrangesKernel_real` give
  `‖E a₀‖‖E b‖ sin(φ b - φ a₀) = 0`; `E` has no real zeros (`HEEqPW.ne_zero_ofReal`), so `sin(φ b - φ a₀) = 0` and
  `φ b - φ a₀ ∈ πℤ` (`Real.sin_eq_zero_iff`).
- `phaseLevel φ β ⊆ Λ`: let `x` be in the level set, `x ∉ Λ`. Then `K_x := deBrangesKernel E x ∈ H(E) = PW` (`TheoremD`)
  and for every `b ∈ Λ` (`b ≠ x`) `K_x(b) = ‖E x‖‖E b‖ sin(φ b - φ x)/(π(b - x)) = 0` since `φ b - φ x ∈ πℤ`.
  By uniqueness in the complete interpolating property, `K_x ≡ 0`. But then by the reproducing property
  `f(x) = ∫ f conj K_x/|E|² = 0` for all `f ∈ PW`, contradicting `g(· - x)(x) = 1` (`MemPW.comp_sub_ofReal`). ∎

```lean
/-- **Remark** (p. 797): a separated complete interpolating sequence is the zero set of `E + E^*`
for some `E ∈ \overline{HB}` with `H(E) = PW`. -/
theorem completeInterpolating_zero_set (hPW : PaleyWienerThm) (hC : TheoremC) (hD : TheoremD)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hcis : IsCompleteInterpolating Λ) :
    ∃ E : ℂ → ℂ, IsHB E ∧ HEEqPW E ∧ ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry
```

*Proof.* `isSampling_of_isCompleteInterpolating` gives `IsSampling Λ`; `exists_E hPW hC hs` (M03) gives `E₀ ∈ \overline{HB}`,
`HEEqPW E₀`, `heNormSq E₀ f = sampleSum Λ f` (`PW`). `E₀` is strict without real zeros; take a phase `φ`
(`exists_isPhaseFunction`). `levelSet_eq_of_cis` gives `β` with `Λ = phaseLevel φ β`. Put `θ := β - π/2` and
`E := fun z ↦ e^{iθ} E₀ z`: `IsHB E` (`IsHB.rotate`), `HEEqPW E` (`HEEqPW.rotate`), `E` strict without zeros on `ℝ`
(`HEEqPW.isStrictHB`, `ne_zero_ofReal` again), with phase `φ - θ` (`IsPhaseFunction.rotate`). By `zero_set_single`,
`E z + fstar E z = 0 ↔ ∃ x ∈ phaseLevel (φ - θ) (π/2), z = x`, and
`phaseLevel (φ - θ) (π/2) = phaseLevel φ (π/2 + θ) = phaseLevel φ β = Λ`. ∎

(Uses: sampling ⇒ the Hilbert space structure of Theorem C, hence `hC`; the reproducing kernel, hence `hD`; no `hE`.)

## Issues in the source

(Page/line references: journal pages; the tex line numbers of `literature/ArxivOrtega.tex`.)

1. **p. 795, "we may assume that `F` has no real zeros", tex ~l. 449–456** (*certain*). The paper writes `F = S F̃`
   with `S` "an entire function with real zero set `Z(S)` and `S^* = S`", and asserts `Λ = Λ_1 ∪ Z(S)`. Missing: (i) the
   *construction* of `S` (Weierstrass product, with multiplicities; genus one is not enough; `F` may have infinitely
   many real zeros, e.g. any real entire function with real zeros is in `\overline{HB}`); (ii) that real zeros of
   `F` lie in `Λ` and that `Λ ⊇ Λ_1` (the equality `Λ = Λ_1 ∪ Z(S)` is true but only `⊇` is used); (iii) why
   `Λ_1` sampling implies `Λ` sampling: lower bound by inclusion, upper bound by Plancherel–Pólya for the separated `Λ`.
   Fix: `exists_realFactor`, `exists_noRealZero_hb`, §2.
2. **p. 796, `Λ_α` indexed by `ℤ`** (*certain*): "Given `α ∈ (0, π]` we let `Λ_α` be the sequence of points `λ_{α,k}`
   such that `φ_{EF}(λ_{α,k}) = α + kπ`, `k ∈ ℤ`" presupposes that `φ_{EF}` is a bijection `ℝ → ℝ` (unbounded in both
   directions). This is not discussed. It follows from `H(E) = PW`: `HEEqPW.phase_tendsto` (§3), via the norm
   identity and Plancherel–Pólya tails, and `φ_G` monotone.
3. **p. 796, "`α ∈ (0, π]`" and later "`α ∈ [0, π)`"** (*certain*, cosmetic). The exceptional set is "at most one `α` modulo `π`";
   we use `α = π/2 + ε`, `0 < ε < π`.
4. *Withdrawn*: OCR artifact. The print has `φ'_{EF} = φ'_E + φ'_F ≥ φ'_E`, which is what §5, step 4 uses
   (NOTEBOOK N-10).
5. **p. 796, `1 = sup_{f ∈ PW, ‖f‖² ≤ 1} |f(x)|² ≃ sup_{f ∈ H(E),...}|f(x)| = K_E(x,x) = π^{-1}φ_E'(x)|E(x)|²`** (*certain*):
   the second `sup` lacks the square (`sup_{‖f‖_E ≤ 1}|f(x)|² = K_E(x,x)`). Harmless; the bound `φ_E'|E|² ≃ 1`
   is proved in M02 (`HEEqPW.phaseDeriv_mul_sq_ge`, README §3.1) without Theorem D.
6. **p. 797, "by (planpol) we may apply Lebesgue's dominated convergence theorem"** (*certain*): no domination of
   `|f(λ_{α_n,k})|²` by a summable sequence independent of `n` follows from (planpol) (which bounds the full sum, not
   pointwise terms). Fix: split into a finite part (continuity) and a tail controlled *uniformly in `α`* by the
   Plancherel–Pólya tail estimate for `δ`-separated sets (§6, steps (a)–(b); README §3.5). Also, the convergence
   `λ_{α_n,k} → λ_k` "for all `k`" needs the indexing of item 2.
7. **p. 797, "we may assume it fails for `α = π/2`"** (*certain*, simplification): unnecessary. Choose `α_n = π/2 + π/(n+2)`;
   at most one is exceptional (`eventually_not_exceptional`), and the limit gives the inequality for `Λ` directly.
8. **p. 796, (equiv)** (*certain*, notation): it uses `‖Ff‖_{H(EF)} = ‖f‖_{H(E)}` and `g = Ff ∈ H(EF)`; the latter needs
   `F ∈ \overline{HB}` (bounded `F^*/F` on `ℂ₊`), M02 `MemHE.mul_isHB`.
9. **p. 797, remark "follows from Theorems C and E"** (*probable*): a complete proof needs (i) that CIS implies *sampling* (open
   mapping/closed graph) to apply Theorem C; (ii) orthogonality of the kernels `K_E(λ,·)`, `λ ∈ Λ` (Theorem D and the explicit
   formula (1)), which forces `Λ` into one level set; (iii) completeness (no further point of the level set can be
   added) by uniqueness; (iv) the rotation `E ↦ e^{iβ}E` to put the level set at `π/2`. Theorem E (the
   orthonormal basis `K(γ,·)`, `γ ∈ Γ_α`) can replace D in (ii)–(iii) but needs a non-exceptional `α` first.
10. **p. 798, Corollary 1 proof, "`Γ_α` is a complete interpolating sequence for all values of `α` except possibly one"**
    (*certain*): (i) needs `φ_E'|E|² ≃ 1` (so that the weights of Theorem E are comparable to `1`) — M02;
    (ii) enumeration of `Γ_α` as `{γ_k}_{k ∈ ℤ}` needs `φ_E` unbounded in both directions (item 2);
    (iii) **separation of `Γ_α`** (needed to apply Pavlov's Theorem A in §4) is not mentioned; proof via the Bernstein inequality (README §3.8, `levelSet_separated`).
11. **p. 798, Corollary 1 proof, "`φ_E` is an increasing function which grows more slowly than `φ_{EF}`"** (*certain*): the correct statement
    is that `φ_{EF} - φ_E = φ_F` is nondecreasing. Fix: §9, step 3, the half-open interval `[γ_k, γ_{k+1})` has `ψ`-image of length `≥ π`.
12. **p. 797, `G = (EF + E^*F^*)/2` by "`G` is the real part of `EF` for real `z`"** (*probable*, M03's business):
    see README §3.3.

## Requested changes to M00

None required. Optional: add `IsSeparated (Set.range γ)` to the conclusion of `corollary1` in `comparator/statements.lean`
(it is true and is what M05 needs); currently the strengthened statement is the extra theorem `corollary1_strong`.
