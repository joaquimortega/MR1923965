# M06 — The example `Λ = {k + log⁺|k|}` and the sharpness of Landau's inequality

- **Lean file:** `FourierFrames/LogExample.lean` (compiles with `lake env lean`, only `sorry` warnings).
- **Paper:** p. 798 (the paragraph before the Claim); the "sine-type" assertion and the appeal to
  Levin's theorem are replaced by the construction of §3–§6 below.
- **Main statements (identical to `comparator/statements.lean`):** `logExample_count`,
  `logExample_isCompleteInterpolating`, `landau_sharp`.
- **Depends on**
  - M01: `MemPW.comp_sub_ofReal`, `pwNormSq_comp_sub_ofReal` (translation invariance), `MemPW.sub`.
  - M02: `IsHB.mul`, `HEEqPW.isStrictHB`, `heEqPW_of_comparable` (main statement),
    `IsPhaseFunction.hasDerivAt` (new name, see below), `HEEqPW.phaseDeriv_mul_sq_ge`,
    `HEEqPW.phaseDeriv_mul_sq_le`, `fstar_mul`, `fstar_ofReal`.
  - M07: `exists_hb_of_density_phase` with the drifted hypothesis `∃ κ C, |U - π Im z - κ Re z| ≤ C`
    (`Construction.lean`; replaces the old `README.md` §4 statement; the normalisation by `e^{-κ z}` is done
    inside M07).
  - vendored OCS: `OCS.IsMultWeight`, `OCS.multPrim`, `OCS.multPt`, `OCS.multBary`,
    `OCS.multGamma`, `OCS.multU`, `OCS.multUIntegrand`, `OCS.multPt_eq_of`,
    `OCS.integrable_multUIntegrand`, `OCS.log_norm_one_sub_div`.
  - cited `Prop`s: `PaleyWienerThm` (`hPW`), `TheoremE` (`hE`).
- **Used by:** none (final result). `landau_inequality` (M05) is independent of this module.

## 0. Overview and what is new compared with the paper

The paper (p. 798) says: `F(z) = lim ∏_{|λ_k|<R} (1 - z/λ_k)` is sine-type, hence (Levin) `Λ` is a
complete interpolating sequence (CIS); and "clearly" `n_Λ(R) = R - log R + O(1)`,
`-n_Λ(-R) = R + log R + O(1)`. Landau's inequality `n(b) - n(a) ≥ b - a - A log⁺(b-a) - B` is thus
best possible (the term `A log⁺` cannot be dropped).

We avoid Levin (README §3.7) and instead run the machinery of the paper itself:

1. **Exact barycentre density (§3).** There is a measurable `m` with `1/10 ≤ m ≤ 20`, `m → 1` at
   `±∞`, whose [OS99] barycentre sequence `OCS.multGamma m` is *exactly* `Λ + 1/2`. (A piecewise
   constant `m` with one value per interval fails: see §3.0; a *two-level* step function on each
   interval works with no condition at all.)
2. **Sine-type estimate (§4).** `OCS.multU m 0 z = π Im z + κ Re z + O(1)` on `Im z ≥ 0`, with an
   explicit constant `κ = ∫_{|t|>1} (m(t) - 1)/t dt ≈ -1.352` (numerically checked). **A linear
   term `κ Re z` does appear** (it is an artefact of the normalisation `Re(z/t)` for `|t|>1` in
   `OCS.multU`; the symmetric product of the paper has none). It is removed by `E ↦ E e^{-κ z}`,
   which preserves `\overline{HB}`, the zero set of `E + E^*`, and the phase.
3. **`H(E) = PW` (§5)** by `heEqPW_of_comparable`.
4. **Theorem E at the phase level `π/2` (§6)** gives the norm identity and the interpolation with
   weights `≃ 1`, hence sampling and CIS for `Λ + 1/2`. The only non-formal point is that
   `S_{π/2} = i(E + E^*) ∉ H(E)`; this is proved from `φ' ≃ 1`.
5. **Translation (§2)** gives the result for `Λ`; **`landau_sharp` (§7)** follows from the counting.

Numerical sanity checks (done while writing, Python, not part of the repository): the gaps
`g_k` lie in `[0.30685, 1.69315]`; `max_k |g_k - 1|(1+|k|) = 2.08`; `m ∈ [0.4386, 4.9874]` and
`max |m - 1|(1+|j|) ≈ 9.9`; `U(z) - π Im z - κ Re z` stays bounded (it tends to about `+8.2`
as `Re z → +∞` and `-1.7` as `Re z → -∞`, difference `≈ π²`, as predicted by the Hilbert
transform of `log|t|`); the count formulas hold with `|error| ≤ 1.31`.

All constants below are absolute (they depend on nothing), except where stated.

---

## 1. The points `λ_k = k + log⁺|k|`

Notation: `λ_k = k + log⁺|k|` (`logLam`), `g_k = λ_{k+1} - λ_k` (`logGap`),
`γ₀ := 1 - log 2 ∈ (0.3068, 0.3069)`. Mathlib: `Real.posLog`, `Real.posLog_eq_log`,
`Real.posLog_eq_zero_iff`, `Real.log_two_lt_d9` (`log 2 < 0.6931471808`).

```lean
/-- `λ_k = k + log⁺|k|`. -/
def logLam (k : ℤ) : ℝ := (k : ℝ) + Real.posLog |(k : ℝ)|
```
```lean
/-- The gap `g_k = λ_{k+1} - λ_k`. -/
def logGap (k : ℤ) : ℝ := logLam (k + 1) - logLam k
```
```lean
theorem logExample_eq_range : logExample = Set.range logLam := rfl
```

`logExample_eq_range` is `rfl` (unfold `FF.logExample`).

### 1.1 Gaps

```lean
/-- `1 - log 2 ≤ g_k ≤ 1 + log 2`; in particular `3/10 ≤ g_k ≤ 17/10`. -/
theorem logGap_bounds (k : ℤ) : 3 / 10 ≤ logGap k ∧ logGap k ≤ 17 / 10 := by
  sorry
```

**Proof.** Four cases.
- `k ≥ 1`: `|k|, |k+1| ≥ 1`, so `g_k = 1 + log(k+1) - log k = 1 + log(1 + 1/k) ∈ (1, 1 + log 2]`.
- `k = 0`: `g_0 = λ_1 - λ_0 = 1 - 0 = 1`. `k = -1`: `g_{-1} = λ_0 - λ_{-1} = 0 - (-1) = 1`
  (`log⁺ 1 = 0`).
- `k ≤ -2`: `|k| ≥ 2`, `|k+1| = |k| - 1 ≥ 1`, `λ_{k+1} - λ_k = 1 + log|k+1| - log|k| =
  1 - log(|k|/(|k|-1)) = 1 - log(1 + 1/(|k|-1))`. Since `0 < 1/(|k|-1) ≤ 1`, this is in
  `[1 - log 2, 1)`.
So `g_k ∈ [1 - log 2, 1 + log 2] ⊂ [3/10, 17/10]` using `log 2 < 0.7` (from `log_two_lt_d9`).
(`Real.log_le_sub_one_of_pos` and `Real.log_le_log` give `log(1+u) ≤ u`, `log(1+u) ≤ log 2` for
`u ≤ 1`.) ∎

```lean
/-- `|g_k - 1| ≤ 3/(1 + |k|)`. -/
theorem abs_logGap_sub_one_le (k : ℤ) : |logGap k - 1| ≤ 3 / (1 + |(k : ℝ)|) := by
  sorry
```

**Proof.** `k ≥ 1`: `|g_k - 1| = log(1 + 1/k) ≤ 1/k ≤ 2/(1+k)` (as `1 + k ≤ 2k`). `k ∈ {0,-1}`:
`0`. `k ≤ -2`: `|g_k - 1| = log(1 + 1/(|k|-1)) ≤ 1/(|k|-1) ≤ 2/|k| ≤ 3/(1+|k|)` (as `|k| - 1 ≥ |k|/2`
and `2(1+|k|) ≤ 3|k|` for `|k| ≥ 2`). In all cases `≤ 3/(1+|k|)`. ∎

```lean
theorem logLam_sub_ge {a b : ℤ} (hab : a < b) : 3 / 10 * ((b : ℝ) - a) ≤ logLam b - logLam a := by
  sorry
```
```lean
theorem strictMono_logLam : StrictMono logLam := by
  sorry
```

**Proof.** `λ_b - λ_a = ∑_{k=a}^{b-1} g_k ≥ (b-a)·3/10`: induction on `b - a` (Int.le_induction),
using `logGap_bounds` and `λ_{k+1} - λ_k = g_k`. `strictMono_logLam` follows (`3/10 (b-a) > 0`). ∎

```lean
theorem logLam_pos_iff (k : ℤ) : 0 < logLam k ↔ 1 ≤ k := by
  sorry
```
```lean
theorem logLam_nonpos_iff (k : ℤ) : logLam k ≤ 0 ↔ k ≤ 0 := by
  sorry
```

**Proof.** `λ_0 = 0` and `λ_1 = 1`; `λ` strictly increasing gives `λ_k > 0` for `k ≥ 1` and
`λ_k ≤ 0` for `k ≤ 0`. (`strictMono_logLam` and `λ_0 = 0`, `λ_1 = 1 > 0`.) ∎

```lean
theorem logExample_isSeparated : IsSeparated logExample := by
  sorry
```

**Proof.** `δ = 3/10`. If `a ≠ b` in `Λ`, `a = λ_i`, `b = λ_j`, `i ≠ j` (injectivity), wlog `i < j`;
`|a - b| = λ_j - λ_i ≥ (3/10)(j - i) ≥ 3/10` by `logLam_sub_ge`. ∎

### 1.2 Counting: `logExample_count`

```lean
theorem ncard_logExample_inter_Ioc_pos (R : ℝ) :
    (logExample ∩ Ioc 0 R).ncard = {k : ℤ | 1 ≤ k ∧ (k : ℝ) + Real.log k ≤ R}.ncard := by
  sorry
```

**Proof.** `Λ ∩ Ioc 0 R = logLam '' {k : ℤ | 0 < λ_k ∧ λ_k ≤ R}` (`Set.range` intersected, direct), and
`0 < λ_k ↔ 1 ≤ k` (`logLam_pos_iff`); for `k ≥ 1`, `λ_k = k + log k` (`posLog_eq_log`, `|k| = k`).
`Set.ncard_image_of_injective` with `strictMono_logLam.injective`. ∎

```lean
theorem ncard_logExample_inter_Ioc_neg (R : ℝ) :
    (logExample ∩ Ioc (-R) 0).ncard = {k : ℤ | k ≤ 0 ∧ -R < logLam k}.ncard := by
  sorry
```

**Proof.** Same: `Λ ∩ Ioc (-R) 0 = logLam '' {k | -R < λ_k ∧ λ_k ≤ 0}` and `λ_k ≤ 0 ↔ k ≤ 0`. ∎

```lean
theorem card_pos_bounds {R : ℝ} (hR : 1 ≤ R) :
    |(({k : ℤ | 1 ≤ k ∧ (k : ℝ) + Real.log k ≤ R}.ncard : ℕ) : ℝ) - (R - Real.log R)| ≤ 2 := by
  sorry
```

**Proof.** Let `S = {k : ℤ | 1 ≤ k ∧ k + log k ≤ R}`, `N = #S`, `R ≥ 1`. Note `log R ≥ 0`,
`R - log R ≥ 1` (`log R ≤ R - 1`), and `log x ≤ x/e ≤ x/2` for `x > 0`
(`Real.log_le_rpow_div` with `ε = 1` gives `log x ≤ x`; for `x/2` use `Real.add_one_le_exp` at
`log x - 1`, or `log x ≤ x - 1` applied to `x/2`: `log x = log 2 + log(x/2) ≤ 0.7 + x/2 - 1 ≤ x/2`).

*Lower bound.* Every integer `k` with `1 ≤ k ≤ R - log R` lies in `S`: `k ≤ R - log R ≤ R`
and `log k ≤ log R` (monotonicity, `k ≤ R`), so `k + log k ≤ R - log R + log R = R`. These are
`⌊R - log R⌋` integers (`Int.card_Icc`, `R - log R ≥ 1`), so `N ≥ ⌊R - log R⌋ > R - log R - 1`.

*Upper bound.* Let `k ∈ S`. If `k ≤ R/2` then `k ≤ R/2 ≤ R - log R` (as `log R ≤ R/2`). If
`k > R/2` then `log k ≥ log R - log 2`, hence `k ≤ R - log k ≤ R - log R + log 2`. So
`S ⊂ Icc 1 ⌊R - log R + log 2⌋` and `N ≤ R - log R + log 2 < R - log R + 1`.
Hence `|N - (R - log R)| ≤ 1 ≤ 2`. ∎

```lean
theorem card_neg_bounds {R : ℝ} (hR : 1 ≤ R) :
    |(({k : ℤ | k ≤ 0 ∧ -R < logLam k}.ncard : ℕ) : ℝ) - (R + Real.log R)| ≤ 2 := by
  sorry
```

**Proof.** `T = {k ≤ 0 : -R < λ_k}`: `k = 0 ∈ T` (as `R ≥ 1 > 0`), and for `k = -j`, `j ≥ 1`:
`λ_{-j} = -j + log j`, so `-R < λ_{-j} ↔ j - log j < R`. Thus `#T = 1 + #S'`,
`S' = {j ≥ 1 : j - log j < R}`.

*Lower bound.* Let `1 ≤ j ≤ R + log R - 1`. If `j ≥ R/2`: `log j ≥ log R - log 2` so
`j - log j ≤ R + log R - 1 - log R + log 2 = R - 1 + log 2 < R`. If `j < R/2`:
`j - log j ≤ j < R/2 < R` (as `log j ≥ 0`). So `S' ⊃ Icc 1 ⌊R + log R - 1⌋`, `#S' ≥ R + log R - 2`
(`R + log R - 1 ≥ 0`), `#T ≥ R + log R - 1`.

*Upper bound.* Let `j ∈ S'`, i.e. `j < R + log j`. Since `log j ≤ j/2`, `j < R + j/2`, so `j < 2R`;
then `log j < log 2R`, hence `j < R + log R + log 2`. So `S' ⊂ Icc 1 ⌊R + log R + log 2⌋` and
`#T ≤ 1 + R + log R + 0.7`. Altogether `R + log R - 1 ≤ #T ≤ R + log R + 1.7`, so
`|#T - (R + log R)| ≤ 2`. ∎


```lean
/-- **The example of p. 798**: `n_Λ(R) = R - log R + O(1)` and `-n_Λ(-R) = R + log R + O(1)` for
`Λ = {k + log⁺|k|}`. -/
theorem logExample_count : ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
    |((logExample ∩ Ioc 0 R).ncard : ℝ) - (R - Real.log R)| ≤ C ∧
      |((logExample ∩ Ioc (-R) 0).ncard : ℝ) - (R + Real.log R)| ≤ C := by
  sorry
```

**Proof.** `C = 2`: `ncard_logExample_inter_Ioc_pos` + `card_pos_bounds`, and
`ncard_logExample_inter_Ioc_neg` + `card_neg_bounds`. ∎

---

## 2. Translation invariance

Let `τ_s Λ = (· + s) '' Λ`. For `f ∈ PW` and real `s`, `g(z) = f(z + s) = f(z - (-s))` is in `PW`
with the same norm (M01: `MemPW.comp_sub_ofReal f (-s)`, `pwNormSq_comp_sub_ofReal`; the PW space
is translation invariant, and note `|z - a| ≤ |z| + |a|`, so the exponential type is unchanged). The
reindexing of sums uses the bijection `Λ ≃ τ_s Λ`, `x ↦ x + s` (`Equiv.Set.image` with
`add_left_injective s`; `Equiv.tsum_eq`).

```lean
theorem isSampling_image_add (s : ℝ) {Λ : Set ℝ} (h : IsSampling Λ) :
    IsSampling ((fun x : ℝ ↦ x + s) '' Λ) := by
  sorry
```

**Proof.** Let `A, B` be the constants for `Λ`. For `f ∈ PW`, let `g = f(· + s) ∈ PW`. Then
`sampleSum (τ_s Λ) f = ∑'_{y ∈ τ_s Λ} ‖f y‖ₑ² = ∑'_{x ∈ Λ} ‖f(x + s)‖ₑ² = sampleSum Λ g` (via the
equivalence) and `pwNormSq g = pwNormSq f`. So the same `A, B` work. ∎

```lean
theorem isCompleteInterpolating_image_add (s : ℝ) {Λ : Set ℝ} (h : IsCompleteInterpolating Λ) :
    IsCompleteInterpolating ((fun x : ℝ ↦ x + s) '' Λ) := by
  sorry
```

**Proof.** Let `a : ℝ → ℂ` with `∑'_{y ∈ τ_s Λ} ‖a y‖ₑ² < ∞`. Put `ã(x) = a(x + s)`; then
`∑'_{x ∈ Λ} ‖ã x‖ₑ² = ∑'_{y ∈ τ_s Λ} ‖a y‖ₑ² < ∞` (reindexing), so there is a unique
`f ∈ PW` with `f = ã` on `Λ`. Then `g(z) = f(z - s) ∈ PW` solves `g(y) = f(y - s) = ã(y - s) =
a(y)` on `τ_s Λ`. *Uniqueness:* if `g₁, g₂ ∈ PW` both interpolate `a` on `τ_s Λ`, then
`f_i = g_i(· + s) ∈ PW` interpolate `ã` on `Λ`, so `f₁ = f₂`, i.e. `g₁ = g₂` (`g_i(z) = f_i(z - s)`). ∎

```lean
theorem isSampling_of_image_add (s : ℝ) {Λ : Set ℝ} (h : IsSampling ((fun x : ℝ ↦ x + s) '' Λ)) :
    IsSampling Λ := by
  sorry
```
```lean
theorem isCompleteInterpolating_of_image_add (s : ℝ) {Λ : Set ℝ}
    (h : IsCompleteInterpolating ((fun x : ℝ ↦ x + s) '' Λ)) : IsCompleteInterpolating Λ := by
  sorry
```

**Proof.** Apply the two previous lemmas with `-s` to `τ_s Λ`, and `(· + (-s)) '' ((· + s) '' Λ) = Λ`
(`Set.image_image`, `simp`). ∎

---

## 3. The step density whose barycentres are `Λ + 1/2`

Recall (OCS, `Lemma3/Partition.lean`): for `a ≤ m ≤ b`, `M = OCS.multPrim m` (`M(x) = ∫_0^x m`),
`x_j = OCS.multPt m j` is the point with `M(x_j) = j` (so `x_0 = 0`), `I_j = [x_j, x_{j+1}]` has
`m`-mass `1`, `γ_j = OCS.multBary m j = ∫_{I_j} t m(t) dt` and `OCS.multGamma m = {γ_j}`.

### 3.0 Design (why two levels)

*Target*: a density `m` with `x_j = p_j` (some partition) and `γ_j = β_j := λ_j + 1/2`.
*One level per interval* (`m = 1/(p_{j+1} - p_j)` on `I_j`, barycentre = midpoint) forces
`p_{j+1} = 2β_j - p_j`, i.e. `d_{j+1} = 2Δβ_j - d_j` for `d_j = p_{j+1} - p_j`. With
`ε_j = Δβ_j - 1` this is `v_{j+1} = v_j + 2(-1)^{j+1} ε_j` for `v_j = (-1)^j (d_j - 1)`. For
`d_j → 1` at **both** `±∞` one needs `v_{+∞} = v_{-∞} = 0`, but only one parameter (`p_0 = 0`, i.e.
the shift `s`) is free: overdetermined in general. (Also `d_j ≥ 0.3`, `≤ 1.7` is not guaranteed.)
*Midpoints of `β`'s + two levels.* Choose `p_j := (λ_{j-1} + λ_j + 1)/2` (the midpoint of
`β_{j-1}` and `β_j`; `p_0 = 0` since `λ_{-1} = -1`, `λ_0 = 0`), so that
`l_j := β_j - p_j = g_{j-1}/2`, `r_j := p_{j+1} - β_j = g_j/2`, `L_j := p_{j+1} - p_j = (g_{j-1} + g_j)/2`,
and take on `I_j = [p_j, p_{j+1}]` the two-level function
`m = u_j := r_j/(l_j L_j)` on `[p_j, β_j)`, `m = v_j := l_j/(r_j L_j)` on `[β_j, p_{j+1})`.
Then (mass) `u_j l_j + v_j r_j = r_j/L_j + l_j/L_j = 1` and (first moment about `β_j`)
`-u_j l_j²/2 + v_j r_j²/2 = (-r_j l_j + l_j r_j)/(2 L_j) = 0`, so the barycentre is exactly `β_j`,
**for any positive `l_j, r_j`**. In terms of the gaps,
`u_j = 2g_j/(g_{j-1}(g_{j-1} + g_j))`, `v_j = 2g_{j-1}/(g_j(g_{j-1} + g_j))`.

```lean
/-- Partition points `p_j = (λ_{j-1} + λ_j + 1)/2` (`p_0 = 0`). -/
def logPt (j : ℤ) : ℝ := (logLam (j - 1) + logLam j + 1) / 2
```
```lean
/-- Target barycentres `β_j = λ_j + 1/2`. -/
def logBary (j : ℤ) : ℝ := logLam j + 1 / 2
```
```lean
/-- The index `j` with `p_j ≤ t < p_{j+1}`. -/
def logIdx (t : ℝ) : ℤ := sSup {j : ℤ | logPt j ≤ t}
```
```lean
/-- Value of the density on `[p_j, β_j)`: `2 g_j / (g_{j-1}(g_{j-1} + g_j))`. -/
def logWeightL (j : ℤ) : ℝ := 2 * logGap j / (logGap (j - 1) * (logGap (j - 1) + logGap j))
```
```lean
/-- Value of the density on `[β_j, p_{j+1})`: `2 g_{j-1} / (g_j(g_{j-1} + g_j))`. -/
def logWeightR (j : ℤ) : ℝ := 2 * logGap (j - 1) / (logGap j * (logGap (j - 1) + logGap j))
```
```lean
/-- The step density `m`. -/
def logDensity (t : ℝ) : ℝ :=
  if t < logBary (logIdx t) then logWeightL (logIdx t) else logWeightR (logIdx t)
```

(`logIdx` uses `sSup` on `ℤ`, a `ConditionallyCompleteLinearOrder`; for a nonempty set bounded above it is
the maximum: `Int.csSup_mem`.) The index `j` with `p_j ≤ t < p_{j+1}` is unique.

```lean
theorem logPt_zero : logPt 0 = 0 := by
  sorry
```

**Proof.** `λ_{-1} = -1 + log⁺ 1 = -1`, `λ_0 = 0`; `(−1 + 0 + 1)/2 = 0`. ∎

```lean
theorem strictMono_logPt : StrictMono logPt := by
  sorry
```
```lean
theorem logPt_lt_logBary (j : ℤ) : logPt j < logBary j ∧ logBary j < logPt (j + 1) := by
  sorry
```

**Proof.** `p_{j+1} - p_j = (λ_j - λ_{j-1} + λ_{j+1} - λ_j)/2 = (g_{j-1} + g_j)/2 ≥ 3/10`;
`β_j - p_j = g_{j-1}/2 > 0`, `p_{j+1} - β_j = g_j/2 > 0` (`logGap_bounds`). ∎

```lean
theorem logIdx_spec (t : ℝ) : logPt (logIdx t) ≤ t ∧ t < logPt (logIdx t + 1) := by
  sorry
```
```lean
theorem logIdx_eq_iff {t : ℝ} {j : ℤ} : logIdx t = j ↔ t ∈ Ico (logPt j) (logPt (j + 1)) := by
  sorry
```

**Proof.** `A_t = {j | p_j ≤ t}` is nonempty and bounded above: `p_j ≥ λ_{j-1} ≥ (3/10)(j-1)`
(`p_j = λ_{j-1} + g_{j-1}/2` and `logLam_sub_ge` with `λ_0 = 0`) so `j ∈ A_t ⇒ j ≤ 1 + 10t/3`; and
`p_j < β_j = λ_j + 1/2 ≤ j/2 + 1/2` for `j ≤ -1` (as `log|j| ≤ |j|/2`), so `p_j ≤ t` for `j` very
negative. Thus `j* = sSup A_t ∈ A_t`, `j* + 1 ∉ A_t`: `p_{j*} ≤ t < p_{j*+1}`. The `iff` follows
from `strictMono_logPt` (the intervals `[p_j, p_{j+1})` are disjoint). ∎

```lean
theorem measurable_logDensity : Measurable logDensity := by
  sorry
```

**Proof.** `logIdx` is measurable because the fibres `{t | logIdx t = j} = Ico (p_j) (p_{j+1})`
are measurable (`logIdx_eq_iff`; `measurable_of_countable`-style: `Measurable` for a function into a
countable discrete space with measurable fibres, `measurable_to_countable'`). `logDensity` is then a
piecewise definition by the measurable set `{t | t < β_{logIdx t}}`, i.e. a countable union over `j`
of `{logIdx = j} ∩ Iio β_j`; use `Measurable.ite` with that set, and
`measurable_from_top`/`measurable_of_countable` for `t ↦ logWeightL (logIdx t)`. ∎

```lean
/-- `1/10 ≤ m ≤ 20`. -/
theorem logDensity_bounds (t : ℝ) : 1 / 10 ≤ logDensity t ∧ logDensity t ≤ 20 := by
  sorry
```

**Proof.** With `g_{j-1}, g_j ∈ [3/10, 17/10]`: `g_{j-1} + g_j ∈ [3/5, 17/5]`.
`u_j = 2g_j / (g_{j-1}(g_{j-1} + g_j)) ≥ 2(3/10)/((17/10)(17/5)) = 0.6/5.78 > 1/10` and
`≤ 2(17/10)/((3/10)(3/5)) = 3.4/0.18 < 19 < 20`. Same for `v_j` (swap `g_j ↔ g_{j-1}`). `m(t)`
is `u_j` or `v_j`, `j = logIdx t`. (`div_le_div`, `div_le_iff₀`; or `nlinarith`/`norm_num` after
substituting the bounds.) ∎

```lean
theorem isMultWeight_logDensity : OCS.IsMultWeight logDensity (1 / 10) 20 :=
  ⟨measurable_logDensity, by norm_num, fun t ↦ (logDensity_bounds t).1,
    fun t ↦ (logDensity_bounds t).2⟩
```

```lean
/-- `|m(t) - 1| ≤ C_m / (1 + |t|)` (one can take `C_m = 1100`). -/
theorem abs_logDensity_sub_one_le (t : ℝ) : |logDensity t - 1| ≤ 1100 / (1 + |t|) := by
  sorry
```

**Proof.** Write `ε_j = g_j - 1` (`|ε_j| ≤ 3/(1+|j|)`, `|ε_j| ≤ 7/10`). Then
`u_j - 1 = N/(g_{j-1}(g_{j-1}+g_j))` with
`N = 2g_j - g_{j-1}² - g_{j-1}g_j = ε_j - 3ε_{j-1} - ε_{j-1}² - ε_{j-1}ε_j` (expand with `g = 1 + ε`),
so `|N| ≤ |ε_j| + 3|ε_{j-1}| + 0.7|ε_{j-1}| + 0.7|ε_j| ≤ 4(|ε_j| + |ε_{j-1}|)`; the denominator is
`≥ 0.3 · 0.6 = 0.18`. Hence `|u_j - 1| ≤ 23(|ε_j| + |ε_{j-1}|)`. By symmetry
(`v_j - 1 = (ε_{j-1} - 3ε_j - ε_jε_{j-1} - ε_j²)/(g_j(g_{j-1}+g_j))`) the same for `v_j`.
Finally `1 + |j-1| ≥ (1+|j|)/2`, so `|ε_j| + |ε_{j-1}| ≤ 9/(1+|j|)` and `|m(t) - 1| ≤ 207/(1+|j|)`
for `t ∈ [p_j, p_{j+1})`.
*From `j` to `t`:* `|p_j - j| = (log⁺|j-1| + log⁺|j|)/2 ≤ |j| + 1/2`, so `|p_j| ≤ 2|j| + 1/2`,
and `t ∈ [p_j, p_{j+1})` gives `|t| ≤ 2|j| + 2.5`, hence `1 + |t| ≤ 5(1 + |j|)`. Therefore
`|m(t) - 1| ≤ 207 · 5/(1+|t|) = 1035/(1+|t|) ≤ 1100/(1+|t|)`. ∎

(The true optimal constant is about `10`; `1100` is a safe crude one.)

```lean
theorem tendsto_logDensity : Tendsto logDensity (cocompact ℝ) (𝓝 1) := by
  sorry
```

**Proof.** `|m - 1| ≤ 1100/(1+|t|) → 0` along `cocompact ℝ` (`Real.cocompact_eq`, or
`tendsto_norm_cocompact_atTop`). ∎

```lean
/-- `∫_{p_j}^{p_{j+1}} m = 1`. -/
theorem integral_logDensity_logPt (j : ℤ) : ∫ t in logPt j..logPt (j + 1), logDensity t = 1 := by
  sorry
```

**Proof.** On `[p_j, β_j)` `m = u_j` and on `[β_j, p_{j+1})` `m = v_j` (`logIdx_eq_iff` and the
definition, using `β_j ∈ (p_j, p_{j+1})`). So `∫_{p_j}^{p_{j+1}} m = u_j(β_j - p_j) + v_j(p_{j+1} - β_j)
= u_j l_j + v_j r_j = r_j/L_j + l_j/L_j = 1` (`intervalIntegral.integral_add_adjacent_intervals`,
`intervalIntegral.integral_congr_ae` / `integral_congr` on `Ioo`, `intervalIntegral.integral_const`;
the endpoint values do not matter). ∎

```lean
/-- `∫_{p_j}^{p_{j+1}} t m(t) dt = β_j`. -/
theorem integral_mul_logDensity_logPt (j : ℤ) :
    ∫ t in logPt j..logPt (j + 1), t * logDensity t = logBary j := by
  sorry
```

**Proof.** Same splitting: `∫ t m = u_j (β_j² - p_j²)/2 + v_j (p_{j+1}² - β_j²)/2` (`integral_id`).
Writing `p_j = β_j - l_j`, `p_{j+1} = β_j + r_j`: `β_j² - p_j² = 2β_j l_j - l_j²`,
`p_{j+1}² - β_j² = 2β_j r_j + r_j²`, so the sum is
`β_j (u_j l_j + v_j r_j) + (-u_j l_j² + v_j r_j²)/2 = β_j + 0`. ∎

```lean
theorem multPrim_logDensity_logPt (j : ℤ) : OCS.multPrim logDensity (logPt j) = j := by
  sorry
```

**Proof.** Induction on `j ∈ ℤ` (`Int.induction_on`): `j = 0` is `logPt_zero` and `multPrim_zero`;
`multPrim m (p_{j+1}) = multPrim m (p_j) + ∫_{p_j}^{p_{j+1}} m = j + 1` and downwards
`multPrim m (p_{j-1}) = multPrim m (p_j) - ∫_{p_{j-1}}^{p_j} m = j - 1` using
`OCS.multPrim_sub_eq (isMultWeight_logDensity)` and `integral_logDensity_logPt`. ∎

```lean
theorem multPt_logDensity (j : ℤ) : OCS.multPt logDensity j = logPt j := by
  sorry
```

**Proof.** `OCS.multPt_eq_of isMultWeight_logDensity (multPrim_logDensity_logPt j)`. ∎

```lean
theorem multBary_logDensity (j : ℤ) : OCS.multBary logDensity j = logLam j + 1 / 2 := by
  sorry
```

**Proof.** Unfold `OCS.multBary`, rewrite `multPt_logDensity` (twice, `j` and `j+1`) and use
`integral_mul_logDensity_logPt`. ∎

```lean
/-- The barycentre sequence of `m` is `Λ + 1/2`, exactly. -/
theorem multGamma_logDensity :
    OCS.multGamma logDensity = (fun x : ℝ ↦ x + 1 / 2) '' logExample := by
  sorry
```

**Proof.** `OCS.multGamma m = Set.range (OCS.multBary m) = Set.range (fun j ↦ λ_j + 1/2)` by
`multBary_logDensity`, which is `(· + 1/2) '' Set.range logLam` (`Set.range_comp`/`Set.image_range`),
and `logExample = Set.range logLam`. ∎

---

## 4. The sine-type estimate: `U(z) = π Im z + κ Re z + O(1)`

Notation: `m = logDensity`, `M = multPrim m`, `W(t) = M(t) - t` (`logW`), so `W(0) = 0`,
`W' = m - 1` a.e., `W(p_j) = j - p_j = -(log⁺|j-1| + log⁺|j|)/2`. Write `z = x + iy`.
`OCS.multU m 0 z = ∫ [log|1 - z/t| + (1 - 1_{[-1,1]}(t)) Re(z/t)] m(t) dt`.

### 4.1 The primitive `W`

```lean
/-- `W(t) = M(t) - t` where `M = ∫_0^t m`. -/
def logW (t : ℝ) : ℝ := OCS.multPrim logDensity t - t
```
```lean
/-- `W` is Lipschitz with `W' = m - 1` a.e. -/
theorem logW_lipschitz : LipschitzWith 19 logW := by
  sorry
```

**Proof.** `W(y) - W(x) = ∫_x^y (m - 1)` and `-0.9 ≤ m - 1 ≤ 19`
(`logDensity_bounds`), so `|W(y) - W(x)| ≤ 19|y - x|` (`OCS.multPrim_sub_eq`; `LipschitzWith.of_dist_le_mul`). ∎

```lean
/-- `W(t) = -log⁺|t| + ρ(t)` with `|ρ(t)| ≤ C_ρ min(|t|, (1+|t|)^{-1/2})`. -/
theorem abs_logW_add_posLog_le : ∃ Cρ : ℝ, ∀ t : ℝ,
    |logW t + Real.posLog (|t|)| ≤ Cρ * min |t| (1 / Real.sqrt (1 + |t|)) := by
  sorry
```

**Proof.** Put `ρ(t) = W(t) + log⁺|t|`.
*(a) `|t| ≤ 1`:* `log⁺|t| = 0`, `|ρ(t)| = |W(t)| ≤ 19|t|` (Lipschitz, `W(0) = 0`).
*(b) `|t| ≥ 1`:* let `j = logIdx t`, `J = |j|`. If `J < 8`, `t` lies in a bounded set
(`|t| ≤ 2J + 2.5 < 19`), where `|ρ| ≤ 19·19 + log 19` is bounded, and
`(1+|t|)^{-1/2} ≥ 20^{-1/2}`, so `|ρ(t)| ≤ C (1+|t|)^{-1/2}` with an absolute `C`. Let `J ≥ 8`.
 1. `|W(t) - W(p_j)| ≤ ∫_{p_j}^{t} |m - 1| ≤ L_j · 207/(1+J) ≤ 352/(1+J)`
   (from the proof of `abs_logDensity_sub_one_le`, `L_j ≤ 1.7`).
 2. `W(p_j) = -(log|j-1| + log J)/2` (as `J ≥ 8`, both `|j|, |j-1| ≥ 1`). With
   `δ_j := p_j - j = (log|j-1| + log J)/2 ∈ [0, log J]`: `|p_j| = J ± δ_j ≥ J - log J ≥ J/2 ≥ 4`, so
   `log⁺|p_j| = log|p_j|` and `|log|p_j| - log J| ≤ δ_j/(J/2) ≤ 2 log J/J`
   (`|log a - log b| ≤ |a-b|/min(a,b)`). Moreover
   `|log J - (log|j-1| + log J)/2| = (log J - log|j-1|)/2 ≤ 1/(2(J-1)) ≤ 1/J`.
   So `|W(p_j) + log⁺|p_j|| ≤ (2 log J + 1)/J`.
 3. `|log⁺|p_j| - log⁺|t|| ≤ |t - p_j|/min(|t|,|p_j|) ≤ 1.7/(J/2 - 2) ≤ 8/J` (`|t| ≥ |p_j| - 1.7`).
 Summing: `|ρ(t)| ≤ 352/(1+J) + (2 log J + 1)/J + 8/J ≤ C (1 + log J)/J`. Since `1 + |t| ≤ 5(1+J)`
 and `(1 + log J)/J ≤ C' J^{-1/2}` (`Real.log_le_rpow_div`, `ε = 1/4`: `log J ≤ 4 J^{1/4}`), we get
 `|ρ(t)| ≤ C'' (1+|t|)^{-1/2}`.
For `|t| ≥ 1` the claim `|ρ| ≤ C_ρ min(|t|, (1+|t|)^{-1/2})` holds since `min(|t|, ·) = (1+|t|)^{-1/2}`
there (`|t| ≥ 1 ≥ (1+|t|)^{-1/2}`), and for `|t| ≤ 1` from (a) with `(1 + |t|)^{-1/2} ≥ 2^{-1/2}`,
`|t| ≤ 1`: `19|t| ≤ C_ρ min(|t|, 2^{-1/2})` for `C_ρ ≥ 19·2^{1/2}`. ∎

### 4.2 `κ` and the decomposition of `U`

```lean
/-- `κ = ∫_{|t|>1} (m(t) - 1)/t dt` (absolutely convergent). -/
def logKappa : ℝ :=
  ∫ t : ℝ, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((logDensity t - 1) / t)
```
```lean
theorem integrable_logKappa :
    Integrable (fun t : ℝ ↦ (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((logDensity t - 1) / t)) := by
  sorry
```

**Proof.** Measurable; `|(1 - 1_I) (m-1)/t| ≤ 1100/((1+|t|)|t|)` for `|t| > 1` and `0` otherwise;
`∫_{|t|>1} 1100/((1+|t|)|t|) ≤ 2·1100 ∫_1^∞ dt/t² < ∞` (`integrableOn_Ioi_rpow_of_lt`). ∎

```lean
/-- The model computation: for `m ≡ 1`, `U(z) = π |Im z|`. -/
theorem multU_model {z : ℂ} (hz : 0 < z.im) :
    ∫ t : ℝ, OCS.multUIntegrand (fun _ ↦ 1) z t = Real.pi * z.im := by
  sorry
```

**Proof.** (The only place where an explicit computation is needed.) By
`OCS.integrable_multUIntegrand` (applied to the constant weight `1`: `IsMultWeight (fun _ ↦ 1) 1 1`)
the integrand is integrable, so `∫_ℝ = lim_{R→∞} ∫_{-R}^{R}` (`intervalIntegral_tendsto_integral`).
For `t ≠ 0`, `log‖1 - z/t‖ = log‖t - z‖ - log|t|` (`OCS.log_norm_one_sub_div`) and
`∫_{-R}^{R} (1 - 1_I(t)) Re(z/t) dt = x ∫_{1≤|t|≤R} dt/t = 0` (odd). Remains
`I_R := ∫_{-R}^{R} [log|t - z| - log|t|] dt`.

Since `y > 0`, `w = t - z` stays in the lower half-plane, in the slit plane. With
`G(w) = w Log w - w` (`Complex.log`), `d/dt Re G(t - z) = Re Log(t - z) = log|t - z|`, so
`∫_{-R}^{R} log|t - z| dt = Re[G(R - z) - G(-R - z)]` (`intervalIntegral.integral_eq_sub_of_hasDerivAt`;
the integrand is continuous since `y ≠ 0`). For `R > 2|z|`:
`Log(R - z) = log R + Log(1 - z/R)`, and, as `Im(R + z) = y > 0`,
`Log(-R - z) = log R + Log(1 + z/R) - iπ`. With `Log(1 + u) = u - u²/2 + O(u³)`:
`G(R - z) = R log R - z log R - R + O(1/R)`,
`G(-R - z) = -(R + z) log R + iπ(R + z) + R + O(1/R)`.
Hence `Re[G(R - z) - G(-R - z)] = 2R log R - 2R + π y + O(1/R)` (as `Re(-iπ(R+z)) = π y`),
while `∫_{-R}^{R} log|t| dt = 2R log R - 2R`. So `I_R → π y`. ∎

(Alternative if the `Log` expansions are painful: differentiate in `y`:
`∂_y ∫_{-R}^{R} log|t - z| dt = ∫ y/((t-x)² + y²) dt → π`, and check `y → ∞` and the value
`U(iy) = π y` by a direct computation; the closed form above is more direct.)

```lean
theorem integrable_log_mul_sub_one {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ ↦ Real.log ‖1 - z / t‖ * (logDensity t - 1)) := by
  sorry
```

**Proof.** For `y > 0`, `|log‖1 - z/t‖| ≤ log‖t - z‖ - log|t|` bounded for `|t| ≥ 2|z|` by
`|z|/|t|·2` (`|log|1 - u|| ≤ 2|u|` for `|u| ≤ 1/2`), times `|m-1| ≤ 1100/(1+|t|)`, integrable at
infinity (`∼ 1/t²`); near `0`, `log|t|` is locally integrable and `m - 1` is bounded; elsewhere
continuous. ∎

```lean
/-- `U(z) = π Im z + κ Re z + V(z)` for `Im z > 0`, `V(z) = ∫ log|1 - z/t| (m(t) - 1) dt`. -/
theorem multU_logDensity_eq {z : ℂ} (hz : 0 < z.im) :
    OCS.multU logDensity 0 z = Real.pi * z.im + logKappa * z.re +
      ∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1) := by
  sorry
```

**Proof.** For `t ≠ 0`, with `Φ_z(t) := log‖1 - z/t‖ + (1 - 1_I(t)) Re(z/t)`,
`Φ_z m = Φ_z·1 + Φ_z·(m - 1)`, and `Re(z/t) = x/t` (`t` real: `Complex.div_ofReal_re`).
Integrate: `∫ Φ_z · 1 = π y` by `multU_model`; `∫ Φ_z (m-1) = ∫ log‖1 - z/t‖ (m-1) + x ∫ (1 - 1_I)
(m-1)/t` by linearity, both integrable (`integrable_log_mul_sub_one`, `integrable_logKappa`); the
second is `x κ`. The constant `C = 0` in `OCS.multU m 0 z`. ∎

### 4.3 Integration by parts: `V(z) = -∫ W K_z`

```lean
/-- The kernel `K_z(t) = (t - x)/((t - x)² + y²) - 1/t = Re(z / (t (t - z)))`. -/
def logKernel (z : ℂ) (t : ℝ) : ℝ := (t - z.re) / ((t - z.re) ^ 2 + z.im ^ 2) - 1 / t
```
```lean
theorem abs_logKernel_le {z : ℂ} (hz : 0 < z.im) {t : ℝ} (ht : t ≠ 0) :
    |logKernel z t| ≤ ‖z‖ / (|t| * ‖(t : ℂ) - z‖) := by
  sorry
```

**Proof.** `Re(1/(t - z)) = (t - x)/((t-x)² + y²)` (`Complex.inv_re`, `Complex.normSq`), and
`1/(t - z) - 1/t = z/(t(t - z))`, so `K_z(t) = Re(z/(t(t-z)))` and `|Re w| ≤ ‖w‖`. ∎

```lean
/-- Integration by parts: `V(z) = -∫ W(t) K_z(t) dt`. -/
theorem integral_log_mul_sub_one_eq {z : ℂ} (hz : 0 < z.im) :
    ∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1) = -∫ t : ℝ, logW t * logKernel z t := by
  sorry
```

**Proof.** Put `φ_z(t) = log‖t - z‖ - log|t|` for `t ≠ 0` (this is `log‖1 - z/t‖`), which is `C¹` on
`(0,∞)` and on `(-∞, 0)` with `φ_z' = K_z` (`OCS.hasDerivAt_logDist`: derivative of `log‖t - z‖`
is `(t-x)/((t-x)²+y²)`; `Real.hasDerivAt_log`). `W` is Lipschitz, hence absolutely continuous
(`LipschitzOnWith.absolutelyContinuousOnInterval`), with `deriv W = m - 1` a.e. (Lebesgue
differentiation: `intervalIntegral.integral_hasDerivAt_right` at continuity points, or
`AbsolutelyContinuousOnInterval.ae_differentiableAt` together with `W(y) - W(x) = ∫_x^y (m-1)`).
Mathlib's `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul` gives, on `[ε, R]` and
`[-R, -ε]` (`0 < ε < R`),
`∫_ε^R φ_z (m - 1) = φ_z(R) W(R) - φ_z(ε) W(ε) - ∫_ε^R K_z W`, and similarly on `[-R, -ε]`.
Boundary terms: `|φ_z(±R)| = |log‖1 ∓ z/R‖| ≤ 2|z|/R` and `|W(±R)| ≤ log R + C`
(`abs_logW_add_posLog_le`), so `→ 0`; `|φ_z(±ε)| ≤ |log ε| + C_z` and `|W(±ε)| ≤ 19 ε`, so `→ 0`.
Let `ε → 0`, `R → ∞`: both `φ_z (m - 1)` and `W K_z` are integrable on `ℝ` (the latter: near
`0`, `|K_z| ≤ 1/|t| + 1`, `|W| ≤ 19|t|`; at infinity `|K_z| ≤ |z|/(|t||t-z|) ≲ 1/t²` and
`|W| ≲ log|t|`). `intervalIntegral_tendsto_integral` and dominated convergence. ∎

### 4.4 The two estimates for `W K_z`

```lean
/-- `∫_0^∞ log((1+σ)/|1-σ|) dσ/σ < ∞` (its value is `π²/2`). -/
theorem integrableOn_log_ratio_div :
    IntegrableOn (fun σ : ℝ ↦ Real.log ((1 + σ) / |1 - σ|) / σ) (Ioi 0) := by
  sorry
```

**Proof.** Let `h(σ) = log((1+σ)/|1-σ|)/σ ≥ 0` on `(0, ∞)`. On `(0, 1/2]`:
`log((1+σ)/(1-σ)) = log(1 + 2σ/(1-σ)) ≤ 2σ/(1-σ) ≤ 4σ`, so `h ≤ 4`. On `[2, ∞)`:
`log((1+σ)/(σ-1)) = log(1 + 2/(σ-1)) ≤ 2/(σ-1) ≤ 4/σ`, so `h ≤ 4/σ²`, integrable. On `[1/2, 2]`:
`h ≤ 2(log 3 + |log|1 - σ||)`, and `log|1-σ|` is integrable near `σ = 1`
(`intervalIntegral.intervalIntegrable_log`, `intervalIntegrable_log'` after translating). (Its value is
`π²/2`, which is not needed.) ∎

```lean
/-- The Hilbert-transform estimate for `log⁺|t|`: `|∫ log⁺|t| K_z(t) dt| ≤ C` for `Im z ≥ 1`. -/
theorem abs_integral_posLog_mul_logKernel_le : ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im →
    Integrable (fun t : ℝ ↦ Real.posLog |t| * logKernel z t) ∧
      |∫ t : ℝ, Real.posLog |t| * logKernel z t| ≤ C := by
  sorry
```

**Proof.** Fix `z = x + iy`, `y ≥ 1`. Write `P(s) = s/(s² + y²)`; `|P(s)| ≤ 1/(2y) ≤ 1/2` and
`|P(s)| ≤ 1/|s|`. `logKernel z t = P(t - x) - 1/t`.
*Integrability:* for `|t| ≥ 1`, `|K_z(t)| ≤ |z|/(|t| |t - z|)`, and `|t - z| ≥ y ≥ 1`, `|t - z| ≥ |t|/2`
for `|t| ≥ 2|z|`: so `|log|t| · K_z|` is bounded on `1 ≤ |t| ≤ 2|z|` and `≲ |z| log|t|/t²` beyond.
*Value:* `ℓ(t) = log⁺|t| = 0` on `|t| ≤ 1`, so the integral is over `|t| ≥ 1`. Since
`∫_{1≤|t|≤R} log|t|/t dt = 0` (odd),
`T₁ = lim_{R→∞} ∫_{1≤|t|≤R} log|t| P(t - x) dt = lim_R [Q_R - ∫_{-1}^{1} log|t| P(t - x) dt]`,
`Q_R := ∫_{-R}^{R} log|t| P(t-x) dt`. The second term is bounded by `(1/2) ∫_{-1}^{1} |log|t|| dt = 1`.
For `Q_R`: by `t ↦ -t`, `Q_R(-x) = -Q_R(x)`, so take `x ≥ 0`, and `R ≥ 2x + 1`:
`Q_R = ∫_{-(R+x)}^{R-x} log|x + s| P(s) ds`. The part `|s| ≤ R - x` equals (`P` odd)
`∫_0^{R-x} [log|x + s| - log|x - s|] P(s) ds`, bounded in modulus by
`∫_0^∞ |log|(x+s)/(x-s)|| ds/s = ∫_0^∞ log((1+σ)/|1-σ|) dσ/σ =: c_*` (`s = xσ`, `x > 0`; the integrand
`log|(1+σ)/(1-σ)| ≥ 0` for `σ > 0`; for `x = 0` the integrand is `0`) `< ∞` by
`integrableOn_log_ratio_div` (`c_* = π²/2`). The remaining part `-(R + x) ≤ s ≤ -(R - x)` has length
`2x`, `|P(s)| ≤ 1/(R - x)` and `|log|x + s|| ≤ log(2R)` (as `R - 2x ≤ |x + s| ≤ R + x`, `≥ 1`), so it
is `≤ 2x log(2R)/(R - x) → 0`. Hence `|T₁| ≤ c_* + 1`. ∎

(The point of `T₁`: this is the boundedness of the conjugate function `H[log|t|] = -π arg z` up to
the truncation; the scale-invariant bound `|P(s)| ≤ 1/|s|` makes the proof elementary, without the
Cauchy–Schwarz integral formula.)

```lean
/-- `∫ |ρ| |K_z| ≤ C` for `Im z ≥ 1`, for `ρ` as in `abs_logW_add_posLog_le`. -/
theorem integral_abs_rho_logKernel_le : ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im →
    Integrable (fun t : ℝ ↦ |logW t + Real.posLog (|t|)| * |logKernel z t|) ∧
      ∫ t : ℝ, |logW t + Real.posLog (|t|)| * |logKernel z t| ≤ C := by
  sorry
```

**Proof.** Let `ρ(t) = W(t) + log⁺|t|`, `|ρ(t)| ≤ C_ρ min(|t|, (1+|t|)^{-1/2})`. Fix `z`, `y ≥ 1`,
`R_0 = |z| ≥ 1`. Use `|K_z(t)| ≤ R_0/(|t||t - z|)`.
- `|t| ≤ R_0/2`: `|t - z| ≥ R_0/2`, so `|K_z| ≤ 2/|t|`, and
  `∫_{|t| ≤ R_0/2} |ρ| 2/|t| ≤ 2 ∫_{|t|≤1} C_ρ dt + 2 ∫_{|t| ≥ 1} C_ρ |t|^{-3/2} dt = 4 C_ρ + 8 C_ρ`.
- `|t| ≥ 2R_0`: `|t - z| ≥ |t|/2`, `|K_z| ≤ 2R_0/t²`,
  `∫_{|t|≥2R_0} C_ρ |t|^{-1/2} 2R_0/t² dt = 4 C_ρ R_0 · (2/3)(2R_0)^{-3/2} ≤ 4 C_ρ`.
- `R_0/2 ≤ |t| ≤ 2R_0`: `|ρ| ≤ C_ρ (R_0/2)^{-1/2}`, `R_0/|t| ≤ 2`, so `|K_z| ≤ 2/|t - z| ≤
  2/√((t - x)² + y²)`, and `∫_{|t| ≤ 2R_0} dt/√((t-x)² + y²) ≤ 2 ∫_0^{3R_0} ds/√(s² + 1) = 2 arsinh(3 R_0)
  ≤ 2 log(7R_0)` (`|t - x| ≤ 3R_0`, `y ≥ 1`). The total is `≤ 4√2 C_ρ R_0^{-1/2} log(7 R_0) ≤ C C_ρ`.
Integrability is clear from the same pointwise bounds. ∎

```lean
theorem abs_integral_log_mul_sub_one_le : ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im →
    |∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1)| ≤ C := by
  sorry
```

**Proof.** `integral_log_mul_sub_one_eq`: `V = -∫ W K_z = -∫ (-log⁺|t| + ρ) K_z = ∫ log⁺|t| K_z -
∫ ρ K_z`; the first is `≤ c_* + 1` (previous lemma) and `|∫ ρ K_z| ≤ ∫ |ρ||K_z| ≤ C`. Both pieces
are integrable (so splitting `∫` is legitimate). ∎

### 4.5 The strip `0 ≤ y ≤ 1`

```lean
/-- Comparison in the strip: `|U(x + iy) - U(x + i)| ≤ 20 π` for `0 ≤ y ≤ 1`. -/
theorem abs_multU_sub_multU_le {z : ℂ} (h0 : 0 ≤ z.im) (h1 : z.im ≤ 1) :
    |OCS.multU logDensity 0 z - OCS.multU logDensity 0 ((z.re : ℂ) + Complex.I)| ≤ 20 * Real.pi := by
  sorry
```

**Proof.** Let `z = x + iy`, `z' = x + i`. For each `t ≠ 0`, the terms `-log|t|` and
`(1 - 1_I) Re(z/t) = (1 - 1_I) x/t` coincide for `z, z'`, so
`OCS.multUIntegrand m z t - OCS.multUIntegrand m z' t = (log‖t - z‖ - log‖t - z'‖) m(t)`, with
`log‖t - z‖ - log‖t - z'‖ = ½ log((s² + y²)/(s² + 1))`, `s = t - x`. As `0 ≤ y ≤ 1`, this is
`≤ 0` and `|·| = ½ log((s² + 1)/(s² + y²)) ≤ ½ log(1 + 1/s²)` (since `s² + 1 ≤ ...`:
`(s²+1)/(s²+y²) ≤ (s²+1)/s²`). Hence (`m ≤ 20`)
`|U(z) - U(z')| ≤ 20 ∫_ℝ ½ log(1 + 1/s²) ds = 20 π`
(`∫_ℝ log(1 + 1/s²) ds = 2π`: e.g. by parts, `∫_0^∞ log(1 + 1/s²) ds = [s log(1+1/s²)]_0^∞ +
∫_0^∞ 2/(s² + 1) ds = π`; any finite bound suffices and the exact constant `20π` can be replaced
by any `C`). ∎

(The constant in the Lean statement is `20π`; if the implementer prefers, replace it by an
existential `∃ C`; no downstream use depends on the value.)

```lean
/-- **The sine-type estimate**: `U(z) = π Im z + κ Re z + O(1)` for `Im z ≥ 0`. -/
theorem logDensity_U_estimate : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
    |OCS.multU logDensity 0 z - Real.pi * z.im - logKappa * z.re| ≤ C := by
  sorry
```

**Proof.** Case `y ≥ 1`: `multU_logDensity_eq` and `abs_integral_log_mul_sub_one_le`
(`C_1 = c_* + 1 + C`). Case `0 ≤ y < 1`: with `z' = x + i` (`Im z' = 1`),
`|U(z) - πy - κx| ≤ |U(z) - U(z')| + |U(z') - π - κ x| + |π - π y| ≤ 20π + C_1 + π`. ∎

**Remark (the linear term).** `κ = ∫_{|t|>1} (m-1)/t dt ≈ -1.3523` (numerically). It does not vanish;
this is consistent with the paper: `OCS.multU` adds `Re(z/t) m(t)` for `|t| > 1`, whereas the
symmetric product `lim ∏_{|λ|<R}(1 - z/λ)` has no such term, and `∫_{1<|t|<R} x m/t dt → κ x`, so
`log|F_sym| = U - κ x + O(1) = π Im z + O(1)`. Here we simply absorb `κ x` into `E`.

---

## 5. The Hermite–Biehler function

```lean
/-- The function `E` of the example: `H(E) = PW`, no real zeros, zero set of `E + E^*` equal to
`Λ + 1/2`, with a phase function. -/
theorem exists_E_logExample (hPW : PaleyWienerThm) :
    ∃ E : ℂ → ℂ, IsHB E ∧ (∀ x : ℝ, E x ≠ 0) ∧ HEEqPW E ∧
      (∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
        c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) ∧
      (∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ (fun x : ℝ ↦ x + 1 / 2) '' logExample, z = (γ : ℂ)) ∧
      ∃ φ : ℝ → ℝ, IsPhaseFunction E φ := by
  sorry
```

**Proof.** Apply `exists_hb_of_density_phase` to `m = logDensity`, `a = 1/10`, `b = 20`
(`measurable_logDensity`, `logDensity_bounds`, `tendsto_logDensity`) with
`hU := ⟨logKappa, C_U, logDensity_U_estimate⟩`, `|U - πy - κx| ≤ C_U` (§4). It returns an `E` with
`IsHB E`, no real zeros, `c e^{πy} ≤ ‖E‖ ≤ C e^{πy}` on `Im z ≥ 0` (the normalisation `E = E₀ e^{-κ z}`
that this section used to perform is now inside M07), `E + E^* = 0 ⟺ z ∈ multGamma m` and a phase
function `φ`. The remaining items:
- `HEEqPW E`: `heEqPW_of_comparable hPW (IsHB E) hcomp`.
- Zero set: `multGamma_logDensity` rewrites `multGamma m` as `(· + 1/2) '' logExample`. ∎

(Before the assembly this section constructed `E = E₀ e^{-κ z}` itself with
`isHB_exp_neg_mul (κ) : IsHB (fun z ↦ exp (-(κ z)))`; that lemma was removed from `LogExample.lean`.)

---

## 6. Theorem E at phase level `π/2`

Let `E ∈ \overline{HB}` without real zeros, `H(E) = PW` (`HEEqPW E`), `|E| ≃ e^{π Im z}` on `Im z ≥ 0`
(`hcomp`, in particular `c ≤ |E(x)| ≤ C` on `ℝ`), `φ` a phase function of `E`.

```lean
theorem phaseLevel_eq_of_zero_set {E : ℂ → ℂ} {φ : ℝ → ℝ} {Γ : Set ℝ}
    (h0 : ∀ x : ℝ, E x ≠ 0) (hφ : IsPhaseFunction E φ)
    (hΓ : ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ Γ, z = (γ : ℂ)) :
    phaseLevel φ (Real.pi / 2) = Γ := by
  sorry
```

**Proof.** `E(x) = |E(x)| e^{-iφ(x)}` and `E^*(x) = conj(E(x)) = |E(x)| e^{iφ(x)}` (`fstar_ofReal`),
so `E(x) + E^*(x) = 2|E(x)| cos φ(x)`. With `|E(x)| ≠ 0`:
`x ∈ Γ ⟺ E x + E^* x = 0` (hypothesis at `z = x`, injectivity of `ofReal`) `⟺ cos φ(x) = 0 ⟺
∃ k : ℤ, φ(x) = π/2 + kπ` (`Real.cos_eq_zero_iff`). ∎

```lean
/-- `E + E^*` is not in `H(E)`: `|E + E^*| = 2|E||cos φ|` is not square integrable on `ℝ`,
because `φ' ≃ 1`. -/
theorem not_memHE_sAlpha (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ} {φ : ℝ → ℝ}
    (hHB : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (hEPW : HEEqPW E) (hφ : IsPhaseFunction E φ)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) :
    ¬ MemHE E (fun z ↦ Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * E z -
      Complex.exp (-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ))) * fstar E z) := by
  sorry
```

**Proof.** Put `S(z) = e^{iπ/2} E(z) - e^{-iπ/2} E^*(z) = i(E(z) + E^*(z))` (`Complex.exp_pi_div_two_mul_I`-type
simp; or `Complex.exp_mul_I`, `cos_pi_div_two`, `sin_pi_div_two`). Suppose `MemHE E S`. Then
`MemPW S` (`(hEPW.1 S).1`), so `∫⁻ ‖S x‖ₑ² < ∞` (`MemLp.eLpNorm_lt_top`, `eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top`).
For real `x`, `|S(x)| = 2|E(x)||cos φ(x)| ≥ 2c|cos φ(x)|`.

*Bounds on `φ'`.* By `HasDerivAt φ (phaseDeriv E x) x` (`IsPhaseFunction.hasDerivAt`) and the M02 bounds
`c_φ ≤ φ'|E|² ≤ C_φ`: with `c ≤ |E| ≤ C`, `m₁ := c_φ/C² ≤ φ'(x) ≤ M₁ := C_φ/c²`, `m₁ > 0`
(replace `C_φ` by `max C_φ 1`).
Hence (mean value theorem, `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` and
`strictMono_of_deriv_pos`) `φ` is strictly increasing, `m₁(x - y) ≤ φ(x) - φ(y) ≤ M₁(x - y)` for `y ≤ x`;
so `φ(x) → ±∞` as `x → ±∞` and, by the intermediate value theorem (`intermediate_value_univ`,
`φ` continuous), for every `k ∈ ℤ` there is `x_k` with `φ(x_k) = kπ`, `x_{k+1} - x_k ≥ π/M₁`.

*Non-integrability.* Let `r = π/(4M₁)` and `J_k = [x_k - r, x_k + r]` (disjoint: `x_{k+1} - x_k ≥ 4r > 2r`).
For `x ∈ J_k`: `|φ(x) - kπ| ≤ M₁ r = π/4`, so `|cos φ(x)| = |cos(φ(x) - kπ)| ≥ cos(π/4) = √2/2`, hence
`‖S x‖² ≥ 4c² · 1/2 = 2c²`. For every `K`,
`∫⁻_ℝ ‖S x‖ₑ² ≥ ∑_{k=1}^{K} ∫⁻_{J_k} ‖S x‖ₑ² ≥ K · 2r · 2c²` (disjoint union, `lintegral_finset_biUnion`
or `lintegral_union`), contradicting finiteness. ∎

```lean
theorem eq_zero_of_pwNormSq_eq_zero {f : ℂ → ℂ} (hf : MemPW f) (h : pwNormSq f = 0) :
    ∀ z, f z = 0 := by
  sorry
```

**Proof.** `∫⁻ ‖f x‖ₑ² = 0` with `f|_ℝ` continuous implies `f(x) = 0` for a.e. `x`
(`lintegral_eq_zero_iff`, measurability from continuity), hence for all `x ∈ ℝ`
(`Continuous.ae_eq_iff_eq` with the open-positive measure `volume`). An entire function vanishing
on `ℝ` is zero (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, `ℝ` accumulates at
`0`; or `Complex.eq_of_eq_on_real...`; the identity theorem). ∎

```lean
/-- From `H(E) = PW`, `|E| ≃ 1` on `ℝ`, `φ_E' |E|² ≃ 1`, `E + E^* ∉ H(E)`: the zero set of
`E + E^*` is sampling and complete interpolating for `PW`. -/
theorem sampling_cis_of_zero_set (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ} {φ : ℝ → ℝ}
    {Γ : Set ℝ} (hHB : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (hEPW : HEEqPW E)
    (hφ : IsPhaseFunction E φ)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im))
    (hΓ : ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ Γ, z = (γ : ℂ)) :
    IsSampling Γ ∧ IsCompleteInterpolating Γ := by
  sorry
```

**Proof.** Let `α = π/2` and `Γ' = phaseLevel φ α = Γ` (`phaseLevel_eq_of_zero_set`).
*Hypotheses of Theorem E:* `IsStrictHB E` (`HEEqPW.isStrictHB`), no real zeros, `IsPhaseFunction E φ`,
and `¬ MemHE E (e^{iα}E - e^{-iα}E^*)` (`not_memHE_sAlpha`). `hE` then gives
 (i) `heNormSq E f = ∑'_{γ ∈ Γ} orthWeight E γ ‖f γ‖ₑ²` for all `f ∈ H(E) = PW`;
 (ii) for `a` with `∑'_Γ orthWeight E γ ‖a γ‖ₑ² < ∞`, some `f ∈ H(E)` interpolates.
*Weights.* `orthWeight E γ = ofReal(π/(φ'(γ)|E(γ)|²))`, `φ' = phaseDeriv E`. By M02
(`phaseDeriv_mul_sq_ge/le`): `c_φ ≤ φ'(γ)|E(γ)|² ≤ C_φ` (`c_φ, C_φ > 0`), so
`ofReal(π/C_φ) ≤ orthWeight E γ ≤ ofReal(π/c_φ)` for all `γ ∈ ℝ`.
*Norm equivalence.* `HEEqPW`: `c₁ ‖f‖²_PW ≤ ‖f‖²_E ≤ C₁ ‖f‖²_PW` for `f ∈ PW`.
*Sampling.* For `f ∈ PW` (so `f ∈ H(E)`):
`c₁ pwNormSq f ≤ heNormSq E f = ∑' w_γ ‖f γ‖ₑ² ≤ ofReal(π/c_φ) · sampleSum Γ f`
(`ENNReal.tsum_mul_left`, `ENNReal.tsum_le_tsum`), i.e. `A = c₁ c_φ/π` works as lower constant; and
`sampleSum Γ f ≤ ofReal(C_φ/π) ∑' w_γ ‖f γ‖ₑ² = ofReal(C_φ/π) heNormSq E f ≤ ofReal(C_φ C₁/π) pwNormSq f`.
(`A, B : ℝ≥0` via `Real.toNNReal`; `A > 0`.)
*Interpolation.* Given `a` with `∑'_Γ ‖a‖ₑ² < ∞`: `∑' w_γ ‖a γ‖ₑ² ≤ ofReal(π/c_φ) ∑' ‖a‖ₑ² < ∞`, so (ii)
gives `f ∈ H(E) = PW` with `f = a` on `Γ`. *Uniqueness.* If `f, g ∈ PW` both interpolate `a`, `h = f - g ∈ PW`
(`MemPW.sub`) vanishes on `Γ`, so by (i) `heNormSq E h = 0`, thus `c₁ pwNormSq h ≤ 0`, `pwNormSq h = 0`,
and `h ≡ 0` by `eq_zero_of_pwNormSq_eq_zero`. ∎

(The sampling half also follows from `theorem1_sufficiency` (M04) with `F = 1`; the above proof
reuses the norm identity needed for CIS and shows sampling "directly", as requested.)

---

## 7. Main statements

```lean
theorem logExample_shift_sampling_cis (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsSampling ((fun x : ℝ ↦ x + 1 / 2) '' logExample) ∧
      IsCompleteInterpolating ((fun x : ℝ ↦ x + 1 / 2) '' logExample) := by
  sorry
```

**Proof.** `exists_E_logExample hPW` gives `E`, `φ`; apply `sampling_cis_of_zero_set` with
`Γ = (· + 1/2) '' logExample`. ∎

```lean
/-- **The example of p. 798**: `{k + log⁺|k|}` is a complete interpolating sequence. -/
theorem logExample_isCompleteInterpolating (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsCompleteInterpolating logExample := by
  sorry
```

**Proof.** `isCompleteInterpolating_of_image_add (1/2)` applied to `(logExample_shift_sampling_cis hPW hE).2`. ∎

```lean
theorem logExample_isSampling (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsSampling logExample := by
  sorry
```

**Proof.** `isSampling_of_image_add (1/2)` applied to `(logExample_shift_sampling_cis hPW hE).1`. ∎

```lean
/-- **Landau's inequality is best possible** (p. 798): `{k + log⁺|k|}` is a separated sampling
sequence for which the logarithmic term cannot be removed. -/
theorem landau_sharp (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsSeparated logExample ∧ IsSampling logExample ∧
      ¬ ∃ B : ℝ, ∀ a b : ℝ, a < b →
        ENNReal.ofReal (b - a - B) ≤ ((logExample ∩ Ioc a b).encard : ℝ≥0∞) := by
  sorry
```

**Proof.** `logExample_isSeparated`, `logExample_isSampling`. Suppose `B` is such that for all `a < b`,
`ofReal(b - a - B) ≤ (Λ ∩ Ioc a b).encard` (coerced to `ℝ≥0∞`). Take `a = 0`, `b = R ≥ max(1, B+1)`
(so `R - B > 0`). `Λ ∩ Ioc 0 R` is finite (image of the finite set of `k` with `1 ≤ k ≤ R`;
`logExample_count` gives `ncard`; or `Set.Finite` from `ncard_pos`/`Set.finite_of_ncard_pos`), so `encard = ncard`
(`Set.Finite.cast_ncard_eq`) and `ofReal(R - B) ≤ ncard` gives `R - B ≤ ncard` (`ENNReal.ofReal_le_iff_le_toReal`).
By `logExample_count` (first estimate, `C = 2`): `ncard ≤ R - log R + 2`. So `log R ≤ B + 2`, false for
`R > e^{B+2}`. ∎

(Finiteness of `Λ ∩ Ioc 0 R`: it is contained in `logLam '' Finset.Icc 1 ⌈R⌉` because `λ_k ≥ k` for `k ≥ 1`.)

---

## 8. Upstream interface used (temporary declarations at the top of the Lean file)

All of these must exist in the final assembly; signatures are my guesses and should be matched to
the real ones (module owners: adjust the file or tell me).

| declaration | owner | statement as used |
|---|---|---|
| `exists_hb_of_density_phase` | M07 | as in `Construction.lean` (hypothesis `∃ κ C, \|U - π Im z - κ Re z\| ≤ C`) |
| `MemPW.comp_sub_ofReal` | M01 | `MemPW f → ∀ a : ℝ, MemPW (fun z ↦ f (z - a))` |
| `pwNormSq_comp_sub_ofReal` | M01 | `pwNormSq (fun z ↦ f (z - a)) = pwNormSq f` |
| `IsHB.mul` | M02 | `IsHB E → IsHB F → IsHB (fun z ↦ E z * F z)` |
| `HEEqPW.isStrictHB` | M02 | `IsHB E → HEEqPW E → IsStrictHB E` (as in `HB/DeBranges.lean`) |
| `heEqPW_of_comparable` | M02 | comparator statement |
| `IsPhaseFunction.hasDerivAt` | M02 (**new name**) | `E` entire, no real zeros, `IsPhaseFunction E φ ⇒ HasDerivAt φ (phaseDeriv E x) x` |
| `HEEqPW.phaseDeriv_mul_sq_ge/le` | M02 | `∃ c > 0, ∀ x, c ≤ phaseDeriv E x * ‖E x‖^2` and `∃ C, … ≤ C`, for `IsHB E`, `HEEqPW E` (as in `HB/DeBranges.lean`; the no-real-zeros hypothesis is not needed) |
| `MemPW.sub`, `fstar_mul`, `fstar_ofReal` | M01/M02 | used only in proofs |

Interface note for M07: **`exists_hb_of_density_phase` with the drifted hypothesis is what is used.**
The phase asymptotics `φ - π M → c₀` returned there are not used here (M02's `φ' ≃ 1` is used
instead); only `IsHB`, the absence of real zeros, `|E| ≃ e^{π Im z}`, the zero set of `E + E^*` and the
existence of a phase function.

## 9. Issues in the source

1. **(p. 798, l. "Set `Λ = …`") `F` is not defined at `λ_0 = 0`.** The paper writes
   `F(z) = lim ∏_{|λ_k|<R}(1 - z/λ_k)` and `0 = λ_0 ∈ Λ` (`λ_0 = 0 + log⁺0 = 0`), so the factor
   `1 - z/λ_0` is undefined. Fix: `F(z) = z ∏_{k≠0, |λ_k|<R}(1 - z/λ_k)`. *Certain.* Minor.
2. **Sine-type assertion "without proof".** "`F` is a sine-type function; i.e.
   `|F(z)|e^{-π|Im z|} ≃ 1` for `|Im z| > 1`" is true (my numerical check of `U - π y - κ x` and
   the structure of the argument: the conjugate function `H[log|t|]` is bounded), but non-trivial:
   the key point is that `n_Λ(t) - t = -log|t| + O(1)` is *even*, and the Hilbert transform of an
   even function with log growth is bounded (`-π arg z`). A naive reading ("`n_Λ(R) = R - log R` is
   not `R + O(1)`, so it cannot be sine-type") would suggest the opposite. We prove it in §4
   (for `Λ + 1/2` and with the normalisation `OCS.multU`, which produces an extra linear term
   `κ Re z`, harmless). *Sure that the claim is true.*
3. **(p. 798) "Thus a classical theorem of Levin implies that `Λ` is a complete interpolating
   sequence"** (and "this sequence is sampling because…"): the logic is: sine-type zero set ⇒ CIS
   (Levin / Pavlov); CIS ⇒ sampling. Replaced by §5–§6 (no Levin). Also "Alternatively, note that
   this means `v = 0` in Theorem A" is a pointer to Pavlov's characterisation, not used.
4. **Counting statements.** `n_Λ(R) = R - log R + O(1)` and `-n_Λ(-R) = R + log R + O(1)` are
   correct with the convention `n_Λ(b) - n_Λ(a) = #(Λ ∩ (a, b])`, `n_Λ(0) = 0` (so that `0 ∈ Λ`
   is counted in `-n_Λ(-R) = #(Λ ∩ (-R, 0])`). With the other convention (`[a, b)`) both sides
   change by `O(1)`. *Sure.* The error is `≤ 1.31` numerically for `R ≥ 1`, `≤ 2` proved.
5. **Sharpness is not argued.** The paper only says "let us show by an example that the inequality
   is best possible", then gives the example and the counting; the (easy) deduction that no
   inequality `n(b) - n(a) ≥ b - a - B` holds (take `a = 0`, `b = R`; the deficiency is `log R`) is
   left to the reader. "Best possible" means: the `A log⁺(b - a)` term cannot be dropped (the
   example has deficiency exactly `log R`, so it matches `A = 1` up to `O(1)`). Formalised as
   `landau_sharp` in the weakest reasonable form (no constant `B` works). *Sure.*
6. **A simplification.** Because `m ↦ OCS.multGamma m` with the two-level step density gives the
   zero set exactly `Λ + 1/2` (§3), no perturbation argument is needed: with a perturbation
   `δ_k → 0`, sampling would follow from M07's `IsSampling.of_perturbation`, but CIS would
   require a separate (Kadec/Avdonin-type) argument, which this design avoids.

## 10. Requested changes to M00

None. (`logExample_count`, `logExample_isCompleteInterpolating`, `landau_sharp` are true as stated;
`logExample_count` holds with `C = 2`; the hypotheses `hPW`, `hE` are exactly those used here.
`IsCompleteInterpolating` for `logExample` requires only that the uniqueness holds among `f : ℂ → ℂ`
with `MemPW f`, which is what is proved.)

## 11. Doubts

- None about the truth of the paper's claim (sampling/CIS of `{k + log⁺|k|}`, counting): the
  construction is complete, and numerically confirmed (including the boundedness of
  `U - π Im z - κ Re z`).
- The implementation risk is concentrated in §4 (`multU_model`, `integral_log_mul_sub_one_eq`,
  `abs_integral_posLog_mul_logKernel_le`, `integral_abs_rho_logKernel_le`), roughly 400 lines of
  real analysis; and in §3 (`logIdx` bookkeeping). §1, §2, §6, §7 are routine.
- Reuse note: the three analytic ingredients of §4 (`log⁺` Hilbert estimate, `ρ`-estimate,
  integration by parts against `W = M - t`) are also what M07 needs for Corollary 2 (with
  `ψ` in place of `W`, `U_ψ = ∫ log|1 - z/t| dψ`); M07's writer could factor them out.
