# M08 — Theorem 2 (i)

**Lean:** `FourierFrames/Theorem2i.lean` (compiles, only `sorry` warnings).
**Paper:** pp. 801–804, "We consider first statement (i)" to "are done with the proof of (10)"
(tex: `literature/ArxivOrtega.tex` lines 841–950; the two displays called `(logcent)` = (9) and
`(deff)` = (10) here).
**Depends on:** M07 `corollary2` (copied under the same name in the upstream-interface section);
vendored `OCS.canonicalProd`, `OCS.IsGenusOneData`, `OCS.hasSum_log_norm_canonicalProd`,
`OCS.canonicalProd_eq_zero_iff`, `OCS.differentiable_canonicalProd`,
`OCS.hasProdLocallyUniformlyOn_canonicalProd`; Mathlib `logDeriv_tprod_eq_tsum`.
**Used by:** nothing (it is a main statement).

> **READ FIRST — status.** The paper's argument proves `theorem2_i` only under an *extra*
> hypothesis, `DensBound`: `ψ'(s) ≤ K/d_n` on `[t_{n-1}, t_n]` (§A of "Issues"). This is not
> implied by the hypotheses of the theorem, and without it the function `f` constructed
> below does **not** satisfy `|U_ψ - log|f|| ≲ 1` (explicit family of counterexamples to the
> *construction* in §A). Everything else is proved here with explicit constants. The scaffold
> contains `theorem2_i_of_regular` (with `DensBound`; fully proved on paper) and `theorem2_i`
> (statement identical to `comparator/statements.lean`, no honest proof from the paper's
> argument). **Requested change to M00 / `statements.lean`:** add `DensBound` (equivalently
> add the clause `∃ K, ∀ n ≥ 1, ∀ s ∈ [t_{n-1}, t_n], ψ'(s) ≤ K/(t_n - t_{n-1})` to
> `IsLogRegularPartition`), or find another proof. It holds automatically when `ψ'` is
> eventually nonincreasing (§A.4), which covers `√x`, `x^a`, `x/log x`, `log log`, ….
> I do not know whether `theorem2_i` is true for spiky `ψ`; I only know the paper's `f` fails.

## 0. Plan and notation

Throughout `ψ ∈ C¹(ℝ)` is nondecreasing, `ψ = 0` on `(-∞,0]`, `ψ' → 0`, `ψ(∞) = ∞`
(`IsAdmissiblePsi` + `h0`: the alternative `ψ → -∞` at `-∞` is impossible since `ψ = 0` on `ℝ₋`).
`t : ℕ → ℝ` is the partition from `IsLogRegularPartition` (`t 0 = 0`, `StrictMono`, `ψ(t n) = n`
for `n ≥ 1`), `C` the regularity constant, `M` the sup bound; `RegData ψ t C M` packages these
(we may take `C ≥ 1`: replace `C` by `max C 1`; `RegData.of_isLogRegularPartition`, trivial).

* cell `I_n = (t_{n-1}, t_n]` (`cell t n`), `d_n = t_n - t_{n-1}` (`cellLen t n`), `n ≥ 1`;
  the cells partition `(0,∞)` (since `t_n → ∞`, below).
* `ν_n = ψ'(s) ds|_{I_n}` is a probability measure (`RegData.integral_cell`:
  `∫_{I_n} ψ' = ψ(t_n) - ψ(t_{n-1}) = 1`, FTC for the `C¹` function `ψ`, using `ψ(t_0) = ψ(0) = 0`
  by `h0` and continuity).
* `r_n = exp ∫ log s dν_n` (`rCentre`, formula (9)); `λ_n = log(t_n/t_{n-1})` (`n ≥ 2`).
* `h_z(σ) = log|e^σ - z| - σ = log|1 - z e^{-σ}|` (so `log|1 - z/s| = h_z(log s)`).
* For `z = x + iy`, `y ≥ 0`.
* `c`, `θ_n`, `z_n` defined in §2.

**Strategy** (as in the paper, after Lyubarskii–Malinnikova): `f` is the canonical product with one
zero `z_n ∈ ℂ₋` per cell. Then
`U_ψ - log|f| = ∑_n j_n`, `j_n(z) = ∫_{I_n} (log|1 - z/s| - log|1 - z/z_n|) dψ(s)`
(the `Re(z/s)` terms cancel *exactly* against the convergence factors, §3).
Each `j_n` is split `j_n = A_n + B_n` (`A_n`: smearing the cell mass at `r_n`; `B_n`: moving the
point mass from `r_n` to `z_n`), and every `|j_n|` is bounded by a summable quantity
depending on the position of `z` relative to the cell.

## 1. The partition data

All statements as in the Lean file (section "§1").

**1.1 `integral_cell`.** `ψ` is `C¹` so `∫_{t_{n-1}}^{t_n} ψ' = ψ(t_n) - ψ(t_{n-1})`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`, `integral_Ioc_eq_integral_Ioo`/
`intervalIntegral.integral_of_le`). For `n = 1`: `ψ(t_0) = ψ(0) = 0` by `h0 0`.

**1.2 `tendsto_t`.** `t` strictly increasing; if bounded by `T`, then `ψ(t_n) = n ≤ ψ(T)`
(monotone) for all `n`, absurd. Use `StrictMono.tendsto_atTop`-style: `tendsto_atTop_of_...`,
or `not_bddAbove_iff` with `Nat` archimedean.

**1.3 `tendsto_cellLen`.** Let `ε > 0`. Since `ψ' → 0` along `cocompact`, there is `T` with
`ψ'(s) ≤ ε` for `s ≥ T`. For `n` with `t_{n-1} ≥ T` (eventually, by 1.2):
`1 = ∫_{I_n} ψ' ≤ ε d_n`, so `d_n ≥ 1/ε`.

**1.4 `t_le`:** for `n ≥ 2`: `t_n ≤ (1+C) t_{n-1}`. Proof: `ratio (n-1)` gives
`d_n ≤ C d_{n-1} ≤ C t_{n-1}` (as `t_{n-2} ≥ 0`: `t` is increasing from `t_0 = 0`), so
`t_n = t_{n-1} + d_n ≤ (1+C)t_{n-1}`. Consequences for `n ≥ 2`:
`λ_n ≤ min(log(1+C), d_n/t_{n-1})` (use `Real.log_le_sub_one_of_pos`, `log(1+u) ≤ u`), and
`t_{n-1} > r_n/(1+C)` (since `r_n < t_n ≤ (1+C)t_{n-1}`).
**Remark.** `hlow` (`ψ' ≥ c/x`) is never used: the averaged version
`1/d_n ≥ 1/t_n ≥ 1/((1+C)t_{n-1})` is a consequence of `d_n ≃ d_{n+1}`. (Issue F.)

**1.5 `rCentre_mem`.** `ν_n` is a probability measure with density `ψ'` (continuous, `≥ 0`) with
`∫ ψ' = 1`, so it is not a Dirac mass; `s ↦ log s` is integrable on `I_n` against `ψ'`
(`ψ'` bounded on `[0,t_1]`, `log` integrable near `0`: `intervalIntegral.intervalIntegrable_log'`),
and `log t_{n-1} ≤ ∫ log s dν_n ≤ log t_n`, both strict because `{s : ψ'(s) > 0} ∩ I_n` has
positive measure (integral of a nonneg continuous function is `1`) and `log` is strictly
monotone: `∫ (log s - log t_{n-1}) dν_n > 0` (`integral_pos_iff_support_of_nonneg`). For `n = 1`,
`t_0 = 0` and the left inequality reads `0 < r_1`, true as `r_1 = exp(·)`.
**`integral_log_sub_centre`:** `∫ (log s - log r_n) dν_n = ∫ log s dν_n - log r_n · 1 = 0`
(definition of `r_n`, `Real.log_exp`, 1.1). *This is the only place (9) enters.*

**1.6 `kappa`.** `κ = max(1+C, t_1/r_1)`. For `n ≥ 2`: `t_n/r_n < t_n/t_{n-1} ≤ 1+C ≤ κ`;
`n = 1`: `t_1/r_1 ≤ κ`. Since `r_1 < t_1`: `t_1/r_1 > 1` so `κ > 1`. Also `d_n < t_n ≤ κ r_n`.
**`cAngle`:** `c = π/(4κ) ∈ (0, π/4)`, `θ_n := c d_n/r_n ≤ c κ = π/4` (using `d_n ≤ t_n ≤ κ r_n`).
*(The paper says "`c > 0` so small that `c d_n/r_n ≤ π/4` for all `n`": exists because `d_n/r_n` is
bounded; here it is explicit.)* Note: `d_n/r_n` need *not* tend to `0` (e.g. `ψ = (1/a) log x`).

## 2. The zeros

`z_n = r_n e^{-iθ_n}`, `n ≥ 1`, `θ_n ∈ (0, π/4]` (`zPt`). Facts (`RegData.*_zPt`):

* `|z_n| = r_n`; `Re z_n = r_n cos θ_n ≥ r_n/√2`; `Im z_n = -r_n sin θ_n < 0`.
* `|Im z_n| = r_n sin θ_n ≤ r_n θ_n = c d_n =: ρ_n` (`Real.sin_le`); and `≥ (2/π) r_n θ_n = (2/π) ρ_n`
  (`Real.mul_le_sin`, valid as `θ_n ≤ π/4 ≤ π/2`).
* `|z_n - r_n| = |r_n(e^{-iθ_n} - 1)| ≤ r_n θ_n = ρ_n ≤ d_n`
  (`Complex.norm_exp_I_mul_ofReal_sub_one_le`; `c < 1`).
* `r_n - Re z_n = r_n(1 - cos θ_n) ≤ r_n θ_n²/2 = ρ_nθ_n/2` (`Real.one_sub_sq_div_two_le_cos`).
* `r_n < t_n < r_{n+1}`, so `n ↦ z_n` is injective (moduli differ): `zPt_injOn`.
* **Summability.** `r_n ≥ t_{n-1}` and `d_n → ∞` imply `d_n ≥ 1` for `n ≥ n_0`, so `t_n ≥ n - n_0`
  eventually, whence `∑ r_n^{-2} < ∞` (`summable_inv_sq`; compare with `1/(n - n_0)²`).
  And `∑ d_n/r_n² < ∞` (`summable_cellLen_div_sq`): for `n ≥ 2`, `s ∈ I_n ⇒ s ≤ t_n ≤ (1+C) r_n`
  so `d_n/r_n² ≤ (1+C)² ∫_{I_n} s^{-2} ds`, and `∑_{n ≥ 2} ∫_{I_n} s^{-2} ≤ ∫_{t_1}^∞ s^{-2} = 1/t_1`.

**Convergence factors.** `c_n := ∫_{I_n} 1_{|s|>1}/s dψ(s)` (`convFac`), real. This is exactly the
coefficient of `Re z` that `UPsi` produces on `I_n` (`UPsi` keeps `Re(z/s)` iff `|s| > 1`):
`∫_{I_n} 1_{|s|>1} Re(z/s) dψ = Re(z c_n) = (Re z)·c_n`.
*Claim `summable_convFac_sub`:* `∑ |c_n - 1/z_n| < ∞`. Proof. For `n ≥ 2` and `s ∈ I_n`
(`s > t_{n-1} ≥ t_1`; if `t_1 ≥ 1` the indicator is `1` on all cells; in general only finitely many
cells meet `[-1,1]`, and for these `c_n` is finite, so the claim concerns the tail, `n ≥ n_1 := `
first `n` with `t_{n-1} ≥ 1`):
`|c_n - 1/r_n| = |∫_{I_n} (1/s - 1/r_n) dν_n| ≤ sup_{s ∈ I_n} |r_n - s|/(s r_n) ≤ d_n/(t_{n-1} r_n)
 ≤ (1+C) d_n/r_n²`, and `|1/r_n - 1/z_n| = |1 - e^{iθ_n}|/r_n ≤ θ_n/r_n = c d_n/r_n²`.
Sum: `summable_cellLen_div_sq`.

**Genus-one data** (`RegData.isGenusOneData`): `Z = zSet = {z_n : n ≥ 1}`, `0 ∉ Z`
(`|z_n| = r_n > 0`); `∑_{a ∈ Z} |a|^{-2} = ∑ r_n^{-2} < ∞` (reindex the subtype `↥Z` by `n`, using
injectivity: `Equiv.ofInjective`/`Function.Injective.summable_iff`); `∑ |convFun a - a⁻¹| =
∑ |c_n - 1/z_n| < ∞` by the previous claim (`convFun_zPt` : `convFun (z_n) = c_n`, by
`Classical.choose_spec` and injectivity).

## 3. The function `f` (`fProd := OCS.canonicalProd Z convFun`)

`f(z) = ∏_n (1 - z/z_n) e^{c_n z}`.

1. `f` entire: `OCS.differentiable_canonicalProd`.
2. Zeros: `f(z) = 0 ⇔ z ∈ Z` (`OCS.canonicalProd_eq_zero_iff`), and `Im z_n < 0`. So `f(z) ≠ 0` for
   `Im z ≥ 0` (`fProd_ne_zero`); in particular `f(x) ≠ 0` for real `x`.
3. **`f ∈ \overline{HB}`** (`isHB_fProd`): let `Im z > 0`. By 2, `f(z) ≠ 0`. If `z̄ ∈ Z`, `f(z̄) = 0`
   and `|f(z̄)| ≤ |f(z)|` trivially. Else apply `hasSum_log_norm_canonicalProd` at `z` and `z̄`: both
   series are over the same index; termwise
   `log|1 - z̄/z_n| + Re(z̄ c_n) ≤ log|1 - z/z_n| + Re(z c_n)`:
   `Re(z̄ c_n) = c_n Re z = Re(z c_n)` (`c_n` real), and
   `|z_n - z̄|² - |z_n - z|² = (y_n + y)² - (y_n - y)² = 4 y_n y < 0` (`y_n = Im z_n < 0`, `y = Im z > 0`),
   so `|1 - z̄/z_n| = |z_n - z̄|/r_n ≤ |z_n - z|/r_n`, both nonzero (`log` monotone on `(0,∞)`).
   `hasSum_le` gives `log|f(z̄)| ≤ log|f(z)|`; exponentiate (`Real.log_le_log_iff`).
4. **`log|f|`** (`hasSum_log_fProd`): for `Im z ≥ 0` (so `z ∉ Z`):
   `log|f(z)| = ∑_{n ≥ 1} ( log|1 - z/z_n| + Re z · c_n )` (OCS lemma; `(z * c a).re = z.re * c_n` as
   `c_n` real). Index shift `n ↦ n+1` in Lean.
5. **`phaseDeriv f(x) = ∑_n |Im z_n|/|x - z_n|²`** (`hasSum_phaseDeriv_fProd`), `x ∈ ℝ`.
   Use `logDeriv_tprod_eq_tsum` with `s = univ`, `f_i(z) = (1 - z/z_i)e^{c_i z}` (nonvanishing at `x`;
   differentiable; `MultipliableLocallyUniformlyOn` from
   `OCS.hasProdLocallyUniformlyOn_canonicalProd`; `∏' f_i x = f(x) ≠ 0`; summability of the
   individual log-derivatives: `logDeriv f_i (x) = 1/(x - z_i) + c_i` and
   `|1/(x - z_i) + c_i| ≤ |x|/(|z_i||x - z_i|) + |c_i - 1/z_i|`, with `|x - z_i| ≥ r_i - |x| ≥ r_i/2`
   for large `i`, summable by §2). Then
   `f'(x)/f(x) = ∑ (1/(x - z_n) + c_n)`, and `-Im` of it (take `Im` termwise,
   `Complex.hasSum_im`): `Im c_n = 0`, `Im (1/(x - z_n)) = -Im(x - z_n)/|x-z_n|² = Im z_n/|x - z_n|²`
   so `Im(x - z_n) = -Im z_n = |Im z_n|`, so `Im(1/(x-z_n)) = -|Im z_n|/|x - z_n|²` and
   `phaseDeriv = -Im(f'/f) = ∑ |Im z_n|/|x - z_n|²` ✓. (Lean: `-(zPt n).im / ‖x - zPt n‖^2`.)

## 4. `phaseDeriv f(x) → 0` as `|x| → ∞` (`tendsto_phaseDeriv_fProd`)

*(Not treated in the paper at all, although Corollary 2 needs it.)* Write
`P_n(x) = |Im z_n|/|x - z_n|²`. Facts: `|Im z_n| ≤ c d_n`; `|x - z_n| ≥ |Im z_n| ≥ (2/π)c d_n`, so
`P_n(x) ≤ π/(2 c d_n)`. Let `Φ(x) = ∑ P_n(x)`.

**(a) `x = -ξ ≤ 0`.** `|x - z_n|² ≥ (ξ + Re z_n)² ≥ ξ² + r_n²/2 ≥ (ξ² + r_n²)/2`, so
`P_n ≤ 2 c d_n/(ξ² + r_n²)`. For `s ∈ I_n`, `s ≤ κ r_n`, `ξ² + s² ≤ κ²(ξ² + r_n²)`, so
`d_n/(ξ²+r_n²) ≤ κ² ∫_{I_n} ds/(ξ²+s²)` and `Φ(x) ≤ 2cκ² · π/(2ξ) = cπκ²/ξ`.

**(b) `x > 0`.** Split indices (all `n ≥ 1`).
* `r_n ≤ x/2`: `|x - z_n| ≥ x - r_n ≥ x/2`, `P_n ≤ 4c d_n/x²`; `∑ d_n ≤ t_{n_max} ≤ κ x/2`
  (telescoping; `t_n ≤ κ r_n`); contribution `≤ 2cκ/x`.
* `r_n ≥ 2x`: `|x - z_n| ≥ r_n - x ≥ r_n/2`, `P_n ≤ 4c d_n/r_n²`. For `n ≥ 2`, `s ∈ I_n`:
  `s ≤ (1+C) r_n`, so `d_n/r_n² ≤ (1+C)²∫_{I_n} s^{-2}`, and the cells involved lie in
  `[t_{m-1}, ∞)`, `m` the first such index, `t_{m-1} ≥ r_m/(1+C) ≥ 2x/(1+C)` (for `m ≥ 2`, true when
  `x > t_1`): contribution `≤ 4c(1+C)³/(2x)`.
* `x/2 < r_n < 2x` ("middle"). Then `t_n > r_n > x/2`; either `t_n < 2x` (then `n ∈ W⁺(x) :=
  {n : x/2 < t_n < 2x}`) or `t_n ≥ 2x > r_n > t_{n-1}`, i.e. `n = n_1(x)`, the unique index with
  `t_{n-1} < 2x ≤ t_n`. For `n ∈ W⁺`: from `|x - t_n| ≤ |x - z_n| + |z_n - r_n| + |r_n - t_n|
  ≤ |x - z_n| + 2 d_n`: `(x - t_n)² + d_n² ≤ 2|x - z_n|² + 9 d_n²`, and
  `d_n² ≤ (π/(2c))² |x - z_n|²` (from `|x - z_n| ≥ (2/π)cd_n`); so
  `d_n²/|x - z_n|² ≤ Γ · d_n²/((x - t_n)² + d_n²)` with `Γ = 2 + 9π²/(4c²)`; hence
  `P_n ≤ c d_n/|x - z_n|² = (c/d_n) d_n²/|x - z_n|² ≤ (cΓ/d_n) · d_n²/((x-t_n)²+d_n²)`.
  Summing with `sum_le` (hypothesis `M`): `∑_{W⁺} P_n ≤ cΓ M / min_{W⁺} d_n`, and
  `min_{W⁺} d_n → ∞` as `x → ∞` (`t_n > x/2` forces `n` large; `tendsto_cellLen`). The extra
  index `n_1`: `P_{n_1} ≤ π/(2c d_{n_1}) → 0`.
  (`sum_le` is stated with `ENNReal.ofReal`; convert with `ENNReal.ofReal_tsum_of_nonneg`
  / `ENNReal.toReal_le_of_le_ofReal`.)

All four contributions → 0 as `x → +∞`; together with (a): `Φ → 0` along `cocompact ℝ`
(`Filter.cocompact_eq_atBot_atTop`/`Real.cocompact_eq`).

## 5. `U_ψ` as a sum over cells (`§4` of the Lean file)

**5.1 Integrability** (`integrable_UPsi`). `F_z(s) = (log|1 - z/s| + 1_{|s|>1} Re(z/s)) ψ'(s)`.
`ψ'` is continuous, `= 0` on `(-∞,0)` (as `ψ = 0` there; `Filter.EventuallyEq.deriv_eq`), tends to
`0` at `±∞`, hence bounded by some `B`. (i) On `(0, S]`, `S = 2|z| + 2`: `|F_z| ≤ B(|log|s - z|| +
|log s| + |z|/s·1_{s>1})`, and `s ↦ log|s - z|` is locally integrable (`|s - z| ≥ |s - x|`: use
`log⁻|s - z| ≤ log⁻|s - x|`, `log⁺|s - z| ≤ log(1 + S + |z|)`;
`intervalIntegral.intervalIntegrable_log'`); (ii) on `(S, ∞)`, `|w| = |z/s| ≤ 1/2`:
`|log|1 - w| + Re w| ≤ |Log(1-w) + w| ≤ |w|²` (`OCS.norm_log_one_sub_add_le`), so
`|F_z| ≤ B|z|²/s²`, integrable. Without this the Bochner integral in `UPsi` would be the junk `0`.

**5.2 Cell decomposition** (`hasSum_UPsi`). `UPsi ψ z = ∫_{ℝ} F_z = ∫_{(0,∞)} F_z` (`F_z = 0` on
`(-∞,0)`, `{0}` null) `= ∑_{n ≥ 1} ∫_{I_n} F_z`: `MeasureTheory.hasSum_integral_iUnion` with the
disjoint measurable cells `I_{n+1}` and `⋃ I_{n+1} = Ioi 0` (`t_n → ∞`, `t_0 = 0`).

**5.3 The identity** (`hasSum_cellTerm`). By §3.4, 5.2:
`UPsi ψ z - log|f(z)| = ∑_{n≥1} ( ∫_{I_n} F_z - log|1 - z/z_n| - Re z · c_n )` (difference of two
`HasSum`). On `I_n`, `∫_{I_n} 1_{|s|>1} Re(z/s) ψ' = Re z · c_n` and `∫_{I_n} ψ' = 1`, so the
bracket is
`j_n(z) = ∫_{I_n} (log|1 - z/s| - log|1 - z/z_n|) ψ'(s) ds` (= `cellTerm`).
(Integrability of the two pieces separately on `I_n`: first piece by 5.1 restricted, second is a
constant. For the splitting of `F_z` into its two parts on `I_n` use that `s ↦ Re(z/s) ψ'` is
bounded on `I_n`, `n` with `t_{n-1} ≥ 1`; for the finitely many cells meeting `[-1,1]`
`1_{|s|>1}` makes the piece vanish or bounded, and `log|1-z/s|ψ'` is integrable.)
*This also shows that the series `∑ j_n(z)` converges; moreover §6 shows it converges
absolutely, so the paper's separate "uniform convergence on compact sets" is not needed (entire-ness
of `f` comes from `OCS`).*

**Note (key rewriting).** Since `∫ dν_n = 1`,
`j_n(z) = ∫ log|s - z| dν_n(s) - log|z_n - z|` (the terms `-log s`, `+log r_n` are `∫ - log s dν_n =
-log r_n` by (9), and `-log|z_n|`, `|z_n| = r_n`). This is also `∫ log|1 - s/z| dν_n - log|1 - z_n/z|`
for `z ≠ 0`.

## 6. The estimate `|∑ j_n(z)| ≤ B`, `Im z ≥ 0`

Fix `z = x + iy`, `y ≥ 0`. `z = 0` is trivial (`U_ψ(0) = 0`: integrand `0`; `f(0) = 1`
since each factor is `1`; or use any of the bounds below with `|z| → 0`, they are uniform). Assume
`z ≠ 0`. Constants: `ρ₁ = 2(1+C)`, `K₀ = 8 + 2ρ₁`, `c = π/(4κ) < 1`.

### 6.1 The splitting `j_n = A_n + B_n`
`A_n(z) = ∫_{I_n} (h_z(log s) - h_z(log r_n)) dν_n(s)`,
`B_n(z) = log|1 - z/r_n| - log|1 - z/z_n| = log|z - r_n| - log|z - z_n|` (as `|z_n| = r_n`).
Indeed `j_n = A_n + B_n` using `∫ dν_n = 1`.

### 6.2 Taylor lemma for `A_n` (`n ≥ 2`)
`h_z'(σ) = Re(z/(e^σ - z))`, `h_z''(σ) = -Re(z e^σ/(e^σ - z)²)`, so
`|h_z''(σ)| ≤ |z| e^σ/|e^σ - z|²` whenever `e^σ ≠ z`. If `|e^σ - z| > 0` on
`[log t_{n-1}, log t_n]`, Taylor's formula with integral remainder (or `taylor_mean_remainder_lagrange`)
and `s_n = log r_n`:
`h_z(σ) - h_z(s_n) = h_z'(s_n)(σ - s_n) + R`, `|R| ≤ ½ (σ - s_n)² sup|h_z''|`. Integrate against `ν_n`:
the linear term integrates to `h_z'(s_n) ∫ (log s - s_n) dν_n = 0` by **(9)** (§1.5), so
**`|A_n(z)| ≤ ½ λ_n² · sup_{s ∈ I_n} |z| s/|s - z|²`**, with `|σ - s_n| ≤ λ_n` (both in
`[log t_{n-1}, log t_n]`). (This is the paper's `V_1 = Re ∑∫ Q_n dψ`; working with real `h_z` on the
real variable `σ` avoids branches of `L(ω) = log(1 - ze^{-ω})`.)

### 6.3 Index classes (relative to `|z|`)
* **Below**: `t_n ≤ |z|/2`.
* **Above**: `t_{n-1} ≥ 2|z|` (then `n ≥ 2`).
* **Middle**: the rest, i.e. `t_n > |z|/2` and `t_{n-1} < 2|z|`. Either `t_n < 2|z|`
  (`n ∈ W⁺(z) = {n : |z|/2 < t_n < 2|z|}`, the index set of the hypothesis `sum_le` at `x = |z|`) or
  `t_n ≥ 2|z| > t_{n-1}`: the single index `n_1(z)`. So Middle `⊆ W⁺ ∪ {n_1}`.
* For Middle `n ≥ 2`: `|z|/ρ₁ ≤ r_n ≤ ρ₁|z|`. [`W⁺`: `r_n < t_n < 2|z|`; `r_n > t_{n-1} ≥ t_n/(1+C)
  > |z|/(2(1+C))`. `n_1`: `r_n < t_n ≤ (1+C)t_{n-1} < 2(1+C)|z|`; `r_n > t_{n-1} ≥ t_n/(1+C) ≥
  2|z|/(1+C)`.] Hence `|z - r_n| ≤ |z| + r_n ≤ (ρ₁ + 1) r_n`.
* Middle `n = 1`: `|z| < 2 t_1`, `|z - r_1| ≤ |z| + r_1 < 3 d_1`.

### 6.4 Below (`abs_cellTerm_below`)
`n = 1`: `|w| = t/|z| ≤ 1/2`, `|log|1 - w|| ≤ 2|w|` (`|Log(1-w)| ≤ |w|/(1-|w|)`); by the key
rewriting `|j_1| ≤ 2 t_1/|z| + 2 r_1/|z| ≤ 4 d_1/|z|`.
`n ≥ 2`: `A_n`: for `s ∈ I_n`, `|s - z| ≥ |z| - s ≥ |z|/2`, so `|z|s/|s - z|² ≤ 4 s/|z| ≤ 4 t_n/|z|`;
`|A_n| ≤ 2 λ_n² t_n/|z|`, and `λ_n² t_n ≤ log(1+C) · (d_n/t_{n-1}) t_n ≤ (1+C) log(1+C) d_n`. So
`|A_n| ≤ 2(1+C)log(1+C) d_n/|z|`. `B_n = log|1 - r_n/z| - log|1 - z_n/z|`: the segment between
`r_n/z` and `z_n/z` stays in `|w| ≤ r_n/|z| ≤ 1/2` (equal moduli; convex combination), `|∇ log|1 - w|| = 1/|1-w| ≤ 2`;
`|r_n - z_n|/|z| ≤ c d_n/|z|`: `|B_n| ≤ 2c d_n/|z| ≤ 2d_n/|z|`. Total
`|j_n| ≤ (4 + 2(1+C)log(1+C)) d_n/|z|`, and `∑_{Below} d_n ≤ |z|/2` (telescoping), so
**`∑_{Below} |j_n| ≤ 2 + (1+C)log(1+C)`.**

### 6.5 Above (`abs_cellTerm_above`)
`s ∈ I_n ⇒ s ≥ t_{n-1} ≥ 2|z|`, `|s - z| ≥ s/2`, `|z|s/|s-z|² ≤ 4|z|/s ≤ 4|z|/t_{n-1}`;
`|A_n| ≤ 2λ_n²|z|/t_{n-1} ≤ 2 log(1+C) d_n|z|/t_{n-1}²` (as `λ_n² ≤ log(1+C) d_n/t_{n-1}`).
`B_n = log|1 - z/r_n| - log|1 - z/z_n|`: `w = 1/ζ` on the segment between `1/r_n` and `1/z_n`
(moduli `1/r_n`), `|zw| ≤ |z|/r_n ≤ |z|/t_{n-1} ≤ 1/2`, `|∇_w log|1 - zw|| = |z|/|1 - zw| ≤ 2|z|`,
`|1/r_n - 1/z_n| ≤ θ_n/r_n = c d_n/r_n²`: `|B_n| ≤ 2c|z| d_n/r_n² ≤ 2|z|d_n/t_{n-1}²`
(`r_n > t_{n-1}`). Total `|j_n| ≤ (2 log(1+C) + 2) d_n|z|/t_{n-1}²`. For `s ∈ I_n`:
`s ≤ t_n ≤ (1+C) t_{n-1}`, so `d_n/t_{n-1}² ≤ (1+C)² ∫_{I_n} s^{-2} ds` and
`∑_{Above} d_n/t_{n-1}² ≤ (1+C)² ∫_{2|z|}^∞ s^{-2} = (1+C)²/(2|z|)`:
**`∑_{Above} |j_n| ≤ (log(1+C) + 1)(1+C)²`.**

### 6.6 Middle, far: `|z - r_n| ≥ K₀ d_n`, `n ≥ 2` (`abs_cellTerm_far`)
Write `u = |z - r_n|`, `d = d_n`.
*`A_n`.* For `s ∈ I_n`: `|s - z| ≥ u - d ≥ u(1 - 1/K₀) ≥ u/2`; `|z| s ≤ ρ₁ r_n · (1+C) r_n`
(`s ≤ t_n ≤ (1+C)t_{n-1} < (1+C)r_n`); `λ_n ≤ d/t_{n-1} ≤ (1+C)d/r_n`. So
`|A_n| ≤ ½ (1+C)² d²/r_n² · 4ρ₁(1+C) r_n²/u² = 2ρ₁(1+C)³ d²/u²`.
*`B_n`.* `B_n = -½ log(1 + v)`, `v = Δ/u²`, `Δ = |z - z_n|² - |z - r_n|²`. With `a = Re z_n = r_n cos θ_n`,
`b = r_n sin θ_n`: `Δ = (r_n - a)(2x - a - r_n) + 2 y b + b²`. Bounds: `r_n - a ≤ ρθ/2`
(`ρ = c d`, `θ = θ_n`); `|2x - a - r_n| ≤ 2u + (r_n - a)`; `b ≤ ρ`; `θ < 1`; `r_n ≥ u/(ρ₁+1)`:
`|Δ| ≤ ρθ u + ρ²/4 + 2yρ + ρ²`, so
`|v| ≤ c²(ρ₁ + 9/4) d²/u² + 2c d y/u²` (used `ρθ/u = c²d²/(r_n u) ≤ c²(ρ₁+1)d²/u²`).
With `u ≥ K₀ d` and `y ≤ u`: `|v| ≤ c²(ρ₁+9/4)/K₀² + 2c/K₀ ≤ 1/2` (check: `c < 0.79`,
`K₀ ≥ 8 + 2ρ₁ ≥ 16`). `|log(1+v)| ≤ 2|v|` for `|v| ≤ 1/2` (`Real.abs_log_sub_add_sum_range_le`
or `Complex.norm_log_one_add_sub_self_le`), so
`|B_n| ≤ |v| ≤ (3+ρ₁)d²/u² + 2 d y/u²` (`c < 1`).
**Total:** `|j_n| ≤ (2ρ₁(1+C)³ + 3 + ρ₁) d²/u² + 2 d y/u²`.
*The first-order term `2 d y/u²` is genuinely first order in `d_n` (Issue D), and is summed as a
Riemann sum, not by `sum_le`.*

### 6.7 Middle, near: `|z - r_n| < K₀ d_n`, any `n ≥ 1` (`abs_cellTerm_near`; needs `DensBound`)
Key rewriting: `j_n = ∫ log|s - z| dν_n - log|z - z_n|`.
*Upper.* `sup_{s ∈ I_n} |s - z| ≤ u + d < (K₀+1) d`, so `∫ log|s - z| dν_n ≤ log((K₀+1)d)`;
`|z - z_n| ≥ -Im z_n ≥ (2/π) c d` (as `y ≥ 0`). `j_n ≤ log(K₀+1) + log(π/(2c))`.
*Lower.* `|s - z| ≥ |s - x|`; `∫ log|s - x| dν_n = log d + ∫ log(|s - x|/d) dν_n ≥ log d - ∫ log⁻(|s-x|/d) dν_n`, and with `ν_n ≤ (K/d) ds`
(`DensBound`): `∫ log⁻(|s-x|/d)(K/d) ds ≤ K ∫_{-1}^{1} log(1/|w|) dw = 2K` (substitute `s = x + d w`;
`∫_{-1}^1 -log|w| dw = 2`: `integral_log`). And `|z - z_n| ≤ u + c d ≤ (K₀+1) d`. So
`j_n ≥ -2K - log(K₀+1)`. Since `π/(2c) > 1`: `|j_n| ≤ 2K + log(K₀+1) + log(π/(2c)) =: C_near`.
This covers `n = 1` in the middle class (there `u < 3d_1 < K₀d_1`).
**Where `K` enters, and why it cannot be dropped: Issue A.**

### 6.8 Counting and summing the middle terms
Let `x₀ = |z| > 0`. For `n ∈ W⁺`: `|x₀ - r_n| ≤ |z - r_n|` and `|x₀ - r_n|` vs `|x₀ - t_n|`:
`(x₀ - t_n)² ≤ 2(x₀ - r_n)² + 2d_n² ≤ 2|z - r_n|² + 2d_n²`, hence
`(x₀ - t_n)² + d_n² ≤ 3(|z - r_n|² + d_n²)`, i.e.
`d_n²/(|z - r_n|² + d_n²) ≤ 3 d_n²/((x₀ - t_n)² + d_n²)` and `∑_{W⁺} d_n²/(|z - r_n|² + d_n²) ≤ 3M`
(`sum_le` at `x₀`). Consequences:
* **near terms in `W⁺`**: each has `d_n²/(|z-r_n|²+d_n²) ≥ 1/(1+K₀²)`, so there are at most
  `3(1+K₀²)M` of them (`card_near_le`), each `≤ C_near`;
* **far terms in `W⁺`**: `d²/u² ≤ (1 + K₀^{-2}) d²/(u²+d²)`, so `∑ d²/u² ≤ 3(1+K₀^{-2})M` (`sum_far_le`);
* **the first-order terms**: for far `n` (any `n`), `s ∈ I_n ⇒ |z - s| ≤ u + d ≤ (9/8)u`, hence
  `d y/u² ≤ (81/64) ∫_{I_n} y ds/|z - s|²` and `∑ d y/u² ≤ (81/64)∫_ℝ y/((x-s)²+y²) ds = (81/64)π ≤ 9π/4`
  (`sum_far_im_le`; Mathlib: `integral_inv_one_add_sq`-type / `integral_comp_div...`
  or `MeasureTheory.integral_univ_inv_one_add_sq` after the substitution `s = x + y w`; `y = 0`: term `0`);
* **`n_1`**: bounded by `max(C_near, (2ρ₁(1+C)³+3+ρ₁)/K₀² + 2/K₀)` (near, or far with `d/u ≤ 1/K₀`).

### 6.9 Conclusion (`exists_bound_cellTerm`, `exists_approx`)
`∑_n |j_n(z)| ≤ B`,
`B = [2 + (1+C)log(1+C)] + [(log(1+C)+1)(1+C)²] + (2ρ₁(1+C)³+3+ρ₁)·3(1+K₀^{-2})M + 2·(9π/4)
 + 3(1+K₀²)M·C_near + max(C_near, …)`,
depending only on `C, M, K, κ` (through `c`). Hence `HasSum` of `j_n(·)` (§5.3) gives
`|U_ψ(z) - log|f(z)|| ≤ B` for all `Im z ≥ 0`, `z ≠ 0`; `z = 0` trivial. **All `z` with `Im z ≥ 0`**
(including `Re z < 0`, `|z|` small) are covered: only `|z|`, `y`, and the cell geometry enter.
For `|z|` small the Below class is empty, `n = 1` is near, and every `n ≥ 2` is Above or Middle-far.

*Numerical sanity check* (done in the scratchpad, `ψ = 2(√(x+1) - 1)`): `V(z)` stays in `[-1.1, -0.3]`
for `z ∈ {0.5, 3, 10i, 50, 50+i, 100, 100+30i, 200i, 300, 300.5, 600+2i}`.

## 7. Conclusion of Theorem 2 (i) (`theorem2_i_of_regular`)
Given `RegData ψ t C M` and `DensBound ψ t K`: `f = fProd` is entire, in `\overline{HB}` (§3.3),
`phaseDeriv f → 0` on `cocompact ℝ` (§4), and `B` from §6 gives: for `Im z ≥ 0`, `f(z) ≠ 0`
(§3.2) so `‖f z‖ = exp(log‖f z‖)` and `|U_ψ z - log‖f z‖| ≤ B` yields
`exp(U_ψ z - B) ≤ ‖f z‖ ≤ exp(U_ψ z + B)` (`Real.exp_log`, `Real.exp_le_exp`). Apply
`corollary2 hPW hE hDS hψ hf hφ ⟨B, _⟩`. The hypothesis `hlow` is not used.
`theorem2_i` follows from `theorem2_i_of_regular` once `DensBound` is available
(`RegData.of_isLogRegularPartition` produces `t, C, M`).

## Issues in the source

**A. [major, certain for the construction; truth of the theorem unknown] Missing local regularity of
`ψ'`.** Paper (p. 802): "Given `z ∈ ℂ`, … Then if `Im z ≥ 0`, it is plain that the smoothness of `ψ`
ensures that `∑_{n=n(z)-1}^{n(z)+1} j_n(z) ≃ 1`." Smoothness (`C¹`, `ψ' → 0`, `ψ' ≥ c/x`) does not
give this. For `z = x` real inside the support of `ν_n`, `j_n(x) = ∫ log|s - x| dν_n - log|x - z_n|`
and `|x - z_n| ≥ (2/π)c d_n`. If `ν_n` is concentrated near `x` (e.g. `ψ'` equal to `ε_n` on an
interval of length `ℓ_n = 1/ε_n ≪ d_n` carrying the whole mass, plus the baseline `c₀/s`), then
`j_n(x) ≈ log ℓ_n - log d_n → -∞`. All hypotheses of Theorem 2 (i) hold for
`d_n = √t_n`, `ℓ_n = log t_n` (`ψ' → 0`; `ψ' ≥ c₀/s`; `d_n ≃ d_{n+1}`; the sum in the regular-partition
condition only involves `t_n, d_n`). The other terms are `O(1)` by §6, so `V(x) → -∞`: the
paper's `f` does not satisfy (appr). Replacing `f` by a product with other zero positions does not
help in general (a cell whose mass is split into two far-apart bumps cannot be matched by one zero).
Fix: add `DensBound` (`ψ' ≤ K/d_n` on `I_n`), used only in 6.7 (the "near" cells), with
`C_near = 2K + …`. Sufficient: `ψ'` eventually nonincreasing, with `K = C`: `ψ'|_{I_n} ≤ ψ'(t_{n-1}) ≤
1/d_{n-1} ≤ C/d_n` (`ψ'` nonincreasing ⇒ `ψ'(t_{n-1}) ≤ mean_{I_{n-1}} ψ' = 1/d_{n-1}`).
Whether Λ(ψ) is actually sampling for such spiky `ψ` I do not know. Confidence in the failure of the
construction: high; in the necessity of an extra hypothesis for the theorem: unknown.
**Requested change (M00/statements):** add this clause to `IsLogRegularPartition` or to `theorem2_i`.

**B. [certain] Wrong integration ranges in (10) and the display of `log|f|`.** Paper:
`log|f(z)| = ∑_{n=1}^∞ ∫_{r_{n-1}}^{r_n} (log|1 - z/z_n| + Re(z/t)) dψ(t)` and
`V = ∑ ∫_{r_{n-1}}^{r_n} (log|1 - z/t| - log|1 - z/z_n|) dψ`. Since `ψ(t_n) - ψ(t_{n-1}) = 1` but
`ψ(r_n) - ψ(r_{n-1}) ≠ 1` in general, the zero `z_n` would carry the wrong mass and the
`Re(z/t)` terms would not match `U_ψ`. Correct: `[t_{n-1}, t_n]` (also in the display splitting `V = V_1 + V_2`, which is again over `r_{n-1}..r_n`, while the
following formula `V_1 = Re ∑ ∫_{t_{n-1}}^{t_n} Q_n dψ` uses `t_{n-1}, t_n`, as it must). For `n = 1` `r_0` is undefined; `t_0 = 0`. Also the statement "`f` satisfies
`log|f| = …`" must be read with convergence factors `Re z · c_n`, `c_n = ∫_{I_n ∩ {|s| > 1}} dψ/s`
(§2), to match the normalisation of `UPsi` (README §2.5) exactly.

**C. [certain] The index window `n(z) - 1, n(z), n(z) + 1` is too small.** With only
`d_n ≃ d_{n+1}` (constant `C > 1`) a cell at index distance `≥ 2` from `n(z)` can still be within
`≲ d_n` of `z`, so the Taylor estimate (which needs `dist(z, I_n) ≳ d_n`) fails. Fix (§6.3,
6.8): classify by `|z - r_n| ≷ K₀ d_n`; the number of near cells is bounded by the regular-partition
hypothesis (`≤ 3(1+K₀²)M`), which is the real purpose of that hypothesis (paper: "Using the
assumption … we obtain `V_1 ≃ 1`" only for the far cells).

**D. [certain] `|log|z - r_n| - log|z - z_n|| ≲ d_n²/|z - r_n|²` is false for non-real `z`.**
Paper (p. 803): "Integrating along the arc … we obtain `≲ d_n²/|z - r_n|²`." For `z = iy`, `y = r_n`:
`|z - z_n|² - |z - r_n|² = 2 y r_n sin θ_n`, so the difference is `≈ θ_n/2 = c d_n/(2r_n)`, first
order in `d_n/r_n`. (For real `z` the first-order term `2 y b` vanishes and the estimate is correct.)
The correct bound is `≲ d_n²/u² + d_n y/u²` (§6.6); the second term is summed by comparison with the
Poisson integral (`≤ π`), not by the regular-partition hypothesis. The conclusion `V_2 ≃ 1` survives.

**E. [certain] "`∑_{n ≥ n⁺+1} j_n ≃ 1`" and "`∑_{n < n⁻} j_n ≃ 1`" are not termwise
first-order statements.** Termwise `j_n` is `O(|z|²/r_n²)` (above) with `∑ |z|²/r_n²` unbounded
(e.g. `ψ = 2√x`: `|z|^{1/2}`); one needs the cancellation of the first *and* second order terms
between `ν_n` and the point mass, i.e. the log-centre (9) and the Taylor estimate `|A_n| ≲ λ_n²|z|/t_n`
(§6.5), `|B_n| ≲ |z| d_n/r_n²`, together with the summation `∑ d_n/t_{n-1}² ≲ 1/|z|`. The remark
"after observing that by (9) we may write `j_n = ∫(log|1 - t/z| - log|1 - z_n/z|)dψ`" is correct and is
exactly the identity of §5 (note).

**F. [fairly sure] `ψ'(x) ≥ c/x` (`hlow`) is never needed** once `d_n ≃ d_{n+1}` is assumed
(§1.4: `t_n ≤ (1+C)t_{n-1}`). (It only gives the pointwise version of an averaged bound.)

**G. [minor] `c` and `r_n ∈ (t_{n-1}, t_n)`.** "with `c > 0` so small that `cd_n/r_n ≤ π/4` for all `n`"
needs `sup d_n/r_n < ∞` (true: `≤ κ`, §1.6). Also the paper never says `d_n/r_n` need not tend to 0.

**H. [certain] Omitted: `φ_f' → 0`.** Corollary 2 requires `phaseDeriv f → 0`; the paper never checks it
for the constructed `f` (done in §4; it needs the log-regular hypothesis and `d_n → ∞`).

**I. [minor] Uniform convergence on compacts.** Stated as the thing to prove "it is enough to prove that
the series converges uniformly on compact sets and `V = O(1)`". Both `f` entire (canonical product,
`OCS`) and the pointwise identity `V = ∑ j_n` hold without it; absolute convergence is a by-product of §6.

**J. [minor] `U_ψ` principal value.** The integrability of the `UPsi` integrand (§5.1) must be proved;
otherwise Lean's `∫` silently returns `0`.

## Requested changes to M00
1. Add `DensBound` (see A) to `IsLogRegularPartition` (or as a separate hypothesis of `theorem2_i`);
   suggested form: in `IsLogRegularPartition`, `∃ K : ℝ, ∀ n, 1 ≤ n → ∀ s ∈ Icc (t (n-1)) (t n),
   deriv ψ s ≤ K / (t n - t (n-1))`.
2. `hlow` of `theorem2_i` is superfluous (F); keep for faithfulness.
