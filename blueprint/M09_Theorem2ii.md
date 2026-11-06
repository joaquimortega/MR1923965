# M09 — Theorem 2 (ii)

**Lean:** `FourierFrames/Theorem2ii.lean` (compiles, only `sorry` warnings).
**Paper:** §5, pp. 804–805 (journal), `literature/ArxivOrtega.tex` lines ~967–1040, page images p-16, p-17.
**Main statement:** `theorem2_ii` (identical to `comparator/statements.lean`).

```lean
theorem theorem2_ii (hPW : PaleyWienerThm) {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ)
    (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hsmall : Tendsto (fun x ↦ x * deriv ψ x) atTop (𝓝 0)) :
    ¬ IsSampling (LambdaPsi ψ)
```

**Depends on:** `Defs.lean` only (`MemPW`, `pwNormSq`, `sampleSum`, `IsSampling`, `LambdaPsi`,
`IsAdmissiblePsi`, `IsExpTypeLE`); the vendored `OCS` library: `OCS.IsMultWeight`, `OCS.multF`,
`OCS.multU`, `OCS.multUIntegrand`, `OCS.multL`, `OCS.exp_multL`, `OCS.multF_estimate_three`,
`OCS.multPrim`, `OCS.multPt`, `OCS.multBary`, `OCS.multIdx`, `OCS.multGammaC`,
`OCS.multF_eq_zero_iff`, `OCS.differentiable_multF`, `OCS.integrable_multU_integrand`,
`OCS.multPt_eq_of`, `OCS.multPt_succ_sub_bounds`, `OCS.multBary_mem`, `OCS.multIdx_mem`,
`OCS.exists_infDist_multGammaC_eq`.  **No dependence on M01–M08.**  `hPW` is not used (it is kept
because the statement in `comparator/statements.lean` has it).
**Upstream interface (one item, see §0.3):** `lemma3_estimate_uniform` (uniform constants in Lemma 3
estimate (2)).
**Used by:** nothing.

---

## 0. Summary

### 0.1 Verdict

**Theorem 2 (ii) is true**, and its proof is in fact simpler than the printed one: only a *single
window* of `ψ` is used, and nothing about the global shape of `ψ`.  The printed proof is broken in
several places (§5 below); its *intention* (critical decay `|f_n|² ≈ 1/x` over a logarithmically
long range, so that the mass diverges logarithmically while everything else costs `O(1)`) is
right, but its choice of `φ_n`, of `ε_n`, and of the region `Ω_n` does not realise it.  We
reconstruct a correct, explicit construction.

I checked the construction numerically (scratch script, not in the repo): for the zero set built
from the density `m` below, `2 log|f(x)| - log env(x)` stays within `[-6, 1]` for
`x ∈ {10, …, 3200}` (`a₁ = 20`, `a₂ = 2·20·e³`), and the ratio (sampling sum on
`ℤ_{≤0} ∪ (ℤ+1/2)_{>0}`)/(mass) decreases like `a₁/(a₁(c L + c'))` when `L = log(a₂/2a₁)` grows
(0.71, 0.59, 0.50 for `L = 2, 4, 6`, `a₁ = 10`), the sampling sum staying `≈ const·a₁` while the mass
grows linearly in `L`.

### 0.2 The idea

Notation: `g(x) = x + ψ(x)`, `Λ = Λ(ψ) = g⁻¹(ℤ)`.

1. `Λ ∩ (-∞, 0] = ℤ_{≤0}` (since `ψ = 0` there).
2. **Window.**  `ψ` is continuous, nondecreasing, unbounded, and `ψ(x) - ψ(x₀) ≤ ε log(x/x₀)` for
   `x ≥ x₀ ≥ R` when `xψ'(x) ≤ ε` on `[R, ∞)`.  So given `η > 0`, `s > 0`, there is a window
   `[x₀, x₀ e^{s}]` (as far out as we like) on which `|ψ - (n + 1/2)| ≤ η` (`n` an integer,
   `ψ(x₀) = n + 1/2`): take `ε = η/s`.  On the window `Λ` is within `η` of `ℤ + 1/2`.
   *This is the only place where `ψ' = o(1/x)` is used.*  It says: the "phase" `ψ mod 1` of `Λ`
   relative to `ℤ` stays near `1/2` for a logarithmically long range of scales.
3. **Test function.**  Choose a density `m = 1 + μ` where `μ` consists of two negative uniform
   "ramps" of total mass `-1/2` each, on `[a₁, 2a₁]` and `[a₂, 2a₂]`, with
   `2a₁ + 3 = x₀`, `a₂ - 3 = x₀ e^{s}`.  The primitive `ρ(t) = ∫₀ᵗ μ` is `0`, then `-1/2` on the
   window, then `-1`.  The [OS99] function `F` of `m` has zeros `ℤ + 1/2` (before the shift) on the
   left, `ℤ + 1` on the window, `ℤ + 3/2` after; with the shift `f(z) = G(z + 1/2)` (where
   `G = F e^{-κz}` removes a linear exponential): zeros `ℤ` on the left, **`ℤ + 1/2` on the window
   (matching `Λ`)**, `ℤ` after.
4. **Size.**  For real `x`: `|f(x)|² ≃ env(x) · dist(x, zeros)²` with
   `env(x) = min(1, a₁/|x|) · min(1, a₂/|x|)`: flat `1` up to `a₁`, then **critical decay `a₁/x`
   (the mass per e-fold is constant `≈ a₁`)** until `a₂`, then `a₁a₂/x²`.
5. **Ratio.**  `‖f‖² ≳ a₁ · log(a₂/(4a₁))` (log-divergent mass of the critical range, where
   `dist(x, ℤ + 1/2)² ` averages `1/12`), whereas
   `∑_{Λ} |f|² ≲ a₁ (1 + η² log(a₂/a₁))` (everything outside the window costs `O(a₁)`, and on the
   window `dist(λ, zeros) ≤ η`).  The ratio is `≲ 1/L + η²`.  Letting `L → ∞`, `η → 0`
   shows `Λ` is not sampling.
6. Left half-line: `f(j) = 0` for all integers `j ≤ 0` and `Λ ∩ (-∞,0] = ℤ_{≤0}`, so it costs nothing.

### 0.3 Request to the vendored library (needed by this module)

`OCS.lemma3` / `OCS.multF_estimate_two` give constants `c₁, c₂` after `m` is fixed.  We need them
**uniform over all `m` with `a ≤ m ≤ b` for fixed `(a, b) = (1/2, 1)`**, because the family
`m = dens a₁ a₂` varies with the window.  The vendored proof gives it: `c₁ = e^{-K}`, `c₂ = e^{K}`
with `K = K₃ + 3K₁ + 3K₂`, `K₁ = log(3/a+1) + b ∫_{-3/a}^{3/a}|log|s||ds`,
`K₂ = |log(a/(2b²))| + |log(3/a+1)|`, `K₃ = (1/2a)∫ 1_{|s|≥1/b} s⁻² ds`
(`OrtegaCerdaSeip/Lemma3/Main.lean`, `exists_abs_sum_multErr_sub_log_infDist_le`, which already
says "`K = K(a, b)`" in its docstring but hides it in `∃ K`).  So:

```lean
theorem lemma3_estimate_uniform {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (m : ℝ → ℝ), OCS.IsMultWeight m a b → ∀ C : ℝ, ∀ z : ℂ,
      |z.im| ≤ 1 →
        c₁ * infDist z (OCS.multGammaC m) ≤ ‖OCS.multF m C z‖ * Real.exp (-OCS.multU m C z) ∧
        ‖OCS.multF m C z‖ * Real.exp (-OCS.multU m C z) ≤ c₂ * infDist z (OCS.multGammaC m)
```
It is declared in the "Upstream interface" section of the scaffold.  Proof: copy the vendored
proof of `multF_estimate_two` with `K` made explicit and uniform (the proof of
`exists_abs_sum_multErr_sub_log_infDist_le` never uses `m` beyond `IsMultWeight m a b`).  If the
vendored library cannot be changed, the implementer may re-prove it in `FF` from the same
ingredients.

---

## 1. Definitions (all real, in the scaffold)

```lean
def rampMu (a₁ a₂ : ℝ) (t : ℝ) : ℝ :=
  -((1 / 2) / a₁) * (Icc a₁ (2 * a₁)).indicator 1 t -
    ((1 / 2) / a₂) * (Icc a₂ (2 * a₂)).indicator 1 t
def dens (a₁ a₂ : ℝ) (t : ℝ) : ℝ := 1 + rampMu a₁ a₂ t
def env (a₁ a₂ x : ℝ) : ℝ := a₁ / max a₁ |x| * (a₂ / max a₂ |x|)
def potW (a₁ a₂ : ℝ) (z : ℂ) : ℝ := ∫ t : ℝ, rampMu a₁ a₂ t * Real.log ‖1 - z / t‖
def kappaMu (a₁ a₂ : ℝ) : ℝ := ∫ t : ℝ, rampMu a₁ a₂ t / t
def gFun (a₁ a₂ : ℝ) (z : ℂ) : ℂ :=
  OCS.multF (dens a₁ a₂) 0 z * Complex.exp (-(kappaMu a₁ a₂ : ℂ) * z)
def testFn (a₁ a₂ : ℝ) (z : ℂ) : ℂ := gFun a₁ a₂ (z + 1 / 2)
```
`env a₁ a₂ x = min(1, a₁/|x|)·min(1, a₂/|x|)` (no division by `0`: `a/max a |x|`);
explicitly `env = 1` on `|x| ≤ a₁`, `= a₁/|x|` on `a₁ ≤ |x| ≤ a₂`, `= a₁a₂/x²` on `|x| ≥ a₂`;
it is even and nonincreasing in `|x|`, and `0 < env ≤ 1`.

Standing assumptions on the parameters in lemmas: `1 ≤ a₁` (or `2 ≤ a₁`, `8 ≤ a₁`) and
`2a₁ < a₂` (so the ramps `[a₁,2a₁]`, `[a₂,2a₂]` are disjoint).  Then
`1/2 ≤ 1 - 1/(2a₁) ≤ dens ≤ 1`.

---

## 2. Part A: the density and the potential

### A1. `dens_isMultWeight`
```lean
theorem dens_isMultWeight {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    OCS.IsMultWeight (dens a₁ a₂) (1 / 2) 1
```
`IsMultWeight m a b` = `⟨Measurable m, 0 < a, ∀ t, a ≤ m t, ∀ t, m t ≤ b⟩`.  Measurability: indicators of
`Icc` (`measurable_const.indicator measurableSet_Icc`, then `.add`, `.mul`).  Bounds: the two
indicators have disjoint supports (`2a₁ < a₂`), so `rampMu ∈ [-(1/2)/a₁, 0] ⊂ [-1/2, 0]`
(case split on `t ∈ Icc a₁ (2a₁)`, `t ∈ Icc a₂ (2a₂)`; at most one holds).

### A2. `multUIntegrand_one_real`, `multUIntegrand_one`  (`U₁ = π|Im z|`)
```lean
theorem multUIntegrand_one_real (x : ℝ) :
    ∫ t : ℝ, OCS.multUIntegrand (fun _ ↦ (1 : ℝ)) (x : ℂ) t = 0
theorem multUIntegrand_one (z : ℂ) :
    ∫ t : ℝ, OCS.multUIntegrand (fun _ ↦ (1 : ℝ)) z t = Real.pi * |z.im|
```
(The first is the case `Im z = 0` of the second; it is stated separately because the real case
needs only `integral_log`, no `arctan`.)

*Proof.*  Write `z = x + iy`.  `m ≡ 1` is a weight with `(a, b) = (1, 1)`, so by
`OCS.integrable_multU_integrand` the integrand
`u(t) = log|1 - z/t| + (1 - χ_{[-1,1]}(t)) Re(z/t)` is integrable; hence
`∫_ℝ u = lim_{R→∞} ∫_{-R}^{R} u` (`MeasureTheory.intervalIntegral_tendsto_integral`).
For `R > 1`: `∫_{-R}^{R}(1-χ)Re(z/t) dt = x ∫_{1<|t|<R} dt/t = 0` (odd integrand; use
`integral_comp_neg`/`intervalIntegral.integral_comp_neg` or split `[-R,-1] ∪ [1,R]` and substitute).
It remains to compute `I_R = ∫_{-R}^{R} (log|t - z| - log|t|) dt` (note `Re(z/t) = x/t` for real `t`,
and `log|1 - z/t| = log|t - z| - log|t|` for `t ≠ 0`).

* `∫_{-R}^R log|t| dt = 2(R log R - R)` (`integral_log` on `[0,R]` and symmetry; `Real.log_abs`).
* `log|t - z| = ½ log((t-x)² + y²)`.  For `y ≠ 0` an antiderivative in `s = t - x` is
  `A(s) = (s/2) log(s² + y²) - s + y·arctan(s/y)`
  (check: `A' = ½log(s²+y²) + s²/(s²+y²) - 1 + y²/(s²+y²) = ½ log(s²+y²)`).  For `y = 0`:
  `A₀(s) = s log|s| - s`.  So `∫_{-R}^R log|t-z| dt = A(R-x) - A(-R-x)`.
* Hence, with `ε = 1/R`,
  `I_R = ½[(R-x) log((1-xε)² + y²ε²) + (R+x) log((1+xε)² + y²ε²)] + y[arctan((R-x)/y) + arctan((R+x)/y)]`
  (the terms `2R log R - 2R` cancel exactly).  As `R → ∞`:
  `(R∓x) log(1 ∓ 2xε + O(ε²)) → ∓2x` (use `Real.log_le_sub_one_of_pos`/`Real.abs_log_sub_add_sum_range_le`
  or the expansion `log(1+u) = u + O(u²)`), so the bracket tends to `0`; and
  `y·arctan((R∓x)/y) → y·(π/2)·sign(y) = π|y|/2`.  Total `π|y|`.
  For `y = 0` the arctan terms are absent and `I_R → 0`.

(`R > |x| + 1` avoids evaluating `A` across the singularity at `t = x`; for `y = 0` the antiderivative
`s log|s| - s` is continuous so `integral_eq_sub_of_hasDerivAt` with `intervalIntegrable` works
also across `s = 0`; or split the interval at `x`.)

### A3. `multU_dens`
```lean
theorem multU_dens {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (z : ℂ) :
    OCS.multU (dens a₁ a₂) 0 z = Real.pi * |z.im| + potW a₁ a₂ z + kappaMu a₁ a₂ * z.re
```
*Proof.*  `multUIntegrand (dens) z t = multUIntegrand 1 z t + rampMu t · (log‖1 - z/t‖ + (1-χ(t)) Re(z/t))`
pointwise (`ring` after unfolding).  `multU m 0 z = ∫ multUIntegrand m z t + 0` (`OCS.multU_eq`).  Integrate:
the first part is A2.  For the second, `rampMu` is bounded with support in `[a₁, 2a₂] ⊂ [1, ∞)`, where
`1 - χ_{[-1,1]}(t) = 1` except possibly at `t = 1` (a null set), and `Re(z/t) = Re z / t` for real `t`.
So the second integral is `∫ μ log‖1 - z/t‖ + Re z ∫ μ/t = potW + kappaMu · Re z`.  Integrability of
`μ(t) log‖1-z/t‖`: `μ` bounded with compact support, `log‖t - z‖` and `log|t|` are locally
integrable (`intervalIntegral.intervalIntegrable_log'`, `intervalIntegrable_log`), `t ≥ a₁ ≥ 1`
keeps `log|t| `bounded on the support; `∫ μ/t` is a bounded compactly supported integrand.  Use
`integral_add` with the integrability of each piece.

### A4. Ramp potential — `rampPot_estimate`
```lean
theorem rampPot_estimate {a : ℝ} (ha : 1 ≤ a) (x : ℝ) :
    |(1 / a) * ∫ t in a..2 * a, Real.log ‖1 - (x : ℂ) / t‖ - Real.log (max 1 (|x| / a))| ≤ 4
```
Let `R(x) = (1/a)∫_a^{2a} log|1 - x/t| dt`, `u = |x|`, `ℓ = log max(1, u/a)`.  For `t ∈ [a, 2a]`,
`‖1 - (x:ℂ)/t‖ = |1 - x/t|`.

* **`u ≤ a/2`.**  `|x/t| ≤ 1/2`, and `|log|1-s|| ≤ 2|s|` for `|s| ≤ 1/2`
  (`Real.abs_log_sub_add_sum_range_le`, or `log(1+s) ≤ s`, `-log(1-s)... ≤ s/(1-s)`), so `|R| ≤ 1`, `ℓ = 0`.
* **`u ≥ 4a`.**  For `x > 0`: `1 - x/t = -(x/t)(1 - t/x)`; for
  `x < 0`: `1 + u/t = (u/t)(1 + t/u)`; in both cases `log|1-x/t| = log(u/t) + log(1 ∓ t/u)` with
  `t/u ≤ 1/2`, so `|log(1 ∓ t/u)| ≤ 1`.  And `log(u/(2a)) ≤ log(u/t) ≤ log(u/a)`.  Hence
  `ℓ - log 2 - 1 ≤ R ≤ ℓ + 1`, `|R - ℓ| ≤ 2`.
* **`a/2 < u < 4a`.**  Here `0 ≤ ℓ ≤ log 4`.  `R = (1/a)∫ log(|t - x|/t) dt`.  Upper: `|t-x| ≤ 6a`
  (`x ∈ (-4a, 4a)`, `t ∈ [a, 2a]`), `t ≥ a`, so `|t-x|/t ≤ 6` and `R ≤ log 6`.  Lower:
  `log(|t-x|/t) ≥ log(|t-x|/(2a))` and, since `s ↦ log|s|` increases in `|s|`, the integral of
  `log|t - x|` over an interval of length `a` is at least that over `[-a/2, a/2]`, i.e.
  `∫_{-a/2}^{a/2} log|s| ds = a log(a/2) - a` (`integral_log`).  So
  `R ≥ log(a/2) - 1 - log(2a) = -(1 + log 4)`.  Therefore `R - ℓ ≥ -(1 + 2 log 4) > -4` and
  `R - ℓ ≤ log 6 < 4`.

Note this lemma is stated for a weight-1 normalised ramp; the actual `rampMu` ramp has the factor
`-(1/2)` in front.

### A5. Envelope — `potW_estimate`
```lean
theorem potW_estimate {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (x : ℝ) :
    |potW a₁ a₂ (x : ℂ) - Real.log (env a₁ a₂ x) / 2| ≤ 4
```
`potW a₁ a₂ x = -(1/2)(R_{a₁}(x) + R_{a₂}(x))` (split the integral over the two indicator pieces,
`integral_indicator`, `intervalIntegral.integral_of_le`; the pieces are integrable).
`log env a₁ a₂ x = -ℓ₁ - ℓ₂` with `ℓ_i = log max(1, |x|/a_i)` (since `a/max a |x| = 1/max 1 (|x|/a)`).
So `potW - ½ log env = -(½)[(R₁ - ℓ₁) + (R₂ - ℓ₂)]`, absolute value `≤ ½(4+4) = 4` by A4
(for `a₂ ≥ 1`, which follows from `a₂ > 2a₁ ≥ 2`).

### A6. `potW_le_complex`
```lean
theorem potW_le_complex {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (z : ℂ) :
    potW a₁ a₂ z ≤ Real.log (2 * a₂) + 1
```
`μ ≤ 0`, so `potW z = ∫ |μ| (log t - log‖t - z‖)` (`log‖1 - z/t‖ = log‖t - z‖ - log t` for `t ≠ 0`).
`∫|μ| = 1`, `log t ≤ log(2a₂)` on the support.  For the second term use `-log‖t - z‖ ≤ (-log|t - Re z|)⁺ ·1`...
precisely `-log‖t-z‖ ≤ -log|t - Re z|` would be wrong; use `‖t - z‖ ≥ |t - Re z|`, so
`-log‖t - z‖ ≤ -log|t - Re z|`, and `-log|s| ≤ (-log|s|)⁺ = max(0, -log |s|)` which vanishes for
`|s| ≥ 1`; hence `∫|μ|(-log‖t-z‖) ≤ ‖μ‖_∞ ∫_{|s|<1} -log|s| ds = ‖μ‖_∞ · 2 ≤ 1`
(`‖μ‖_∞ ≤ 1/(2a₁) ≤ 1/2`; `∫_{-1}^{1} -log|s| = 2`, `integral_log`).  (Careful about `z` real:
the bound `‖t-z‖ ≥ |t - Re z|` covers it.)

---

## 3. Part B: the zeros of `F`

Throughout `m = dens a₁ a₂`, a weight with `(a, b) = (1/2, 1)` for `1 ≤ a₁`, `2a₁ < a₂`
(A1).  Recall (`Partition.lean`): `multPrim m x = ∫_0^x m`; `multPt m j` is the point with
`multPrim = j`; `multBary m j = ∫_{pt_j}^{pt_{j+1}} t m(t) dt`; `multGamma m = {γ_j}`; `multIdx m x = ⌊multPrim m x⌋`.

### B1. `multPrim_dens_stretch`
For `x ∈ [2a₁, a₂]`: `multPrim m x = x + ∫_0^x μ = x - 1/2` (the first ramp is entirely inside `[0, x]`,
contributes `-(1/2)/a₁ · a₁ = -1/2`; the second ramp is not reached).  Also `multPrim m x = x` for
`x ≤ a₁`.  (`intervalIntegral.integral_add`, `integral_indicator`, `Real.volume_Icc`.)

### B2. `testFn_eq_zero_of_nonpos`  (left lattice)
```lean
theorem testFn_eq_zero_of_nonpos {a₁ a₂ : ℝ} (h₁ : 2 ≤ a₁) (h₂ : 2 * a₁ < a₂) (j : ℤ)
    (hj : j ≤ 0) : testFn a₁ a₂ (j : ℂ) = 0
```
For `j ≤ 0`, `j + 1 ≤ 1 ≤ a₁`: `multPrim m j = j` and `multPrim m (j+1) = j+1`, so by `OCS.multPt_eq_of`
`pt_j = j`, `pt_{j+1} = j + 1`, and `m = 1` on `[j, j+1]` (`j + 1 ≤ a₁`) so
`multBary m j = ∫_j^{j+1} t dt = j + 1/2`.  Then `testFn (j) = gFun (j + 1/2) = multF (j+1/2) · e^{…} = 0`
by `OCS.multF_eq_zero_iff` (zero set of `multF` is `multGammaC`).

### B3. `infDist_dens_stretch`
```lean
theorem infDist_dens_stretch {a₁ a₂ : ℝ} (h₁ : 2 ≤ a₁) (h₂ : 2 * a₁ < a₂) {x : ℝ}
    (hx : x ∈ Icc (2 * a₁ + 3) (a₂ - 3)) :
    infDist (((x + 1 / 2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂)) =
      |x - 1 / 2 - round (x - 1 / 2)|
```
Let `y = x + 1/2 ∈ [2a₁ + 7/2, a₂ - 5/2]`.  By B1, `multPrim m y = y - 1/2 = x`, so
`k := multIdx m y = ⌊x⌋` and `y ∈ [k + 1/2, k + 3/2)`.  For every integer `j` with
`j + 1/2 ∈ [2a₁, a₂]`, `multPrim m (j + 1/2) = j` so `pt_j = j + 1/2` (`OCS.multPt_eq_of`).  For
`j ∈ {k-1, …, k+2}`: `j + 1/2 ≥ k - 1/2 ≥ x - 3/2 ≥ 2a₁ + 3/2` and `j + 1/2 ≤ k + 5/2 ≤ x + 5/2 ≤ a₂ - 1/2`,
so `pt_j = j + 1/2` for these four `j`, and `m = 1 - 1/2·0`, i.e. `μ = 0` on `[pt_j, pt_{j+1}] ⊂ [2a₁, a₂]`
(`[2a₁, a₂]` is disjoint from the ramps up to the endpoints `2a₁`, `a₂` themselves).  Thus
`γ_j = ∫_{j+1/2}^{j+3/2} t dt = j + 1` for `j ∈ {k-1, k, k+1}`.  By
`OCS.exists_infDist_multGammaC_eq`, `infDist y Γ = min_{i ∈ {k-1,k,k+1}} |y - γ_i| = min |y - (i+1)|`;
since `y - 1 ∈ [k - 1/2, k + 1/2)`, the nearest of `{k, k+1, k+2}` to `y` is `k + 1 = round(y - 1) + 1`
(for `y - 1 = x - 1/2`), at distance `|x - 1/2 - round(x - 1/2)|`.
(Tie-breaking of `round` is irrelevant: at a tie both distances are `1/2`.)

### B4. `infDist_multGammaC_le`
```lean
theorem infDist_multGammaC_le {m : ℝ → ℝ} {a b : ℝ} (hw : OCS.IsMultWeight m a b) (y : ℝ) :
    infDist (y : ℂ) (OCS.multGammaC m) ≤ 1 / a
```
Let `k = multIdx m y`.  `y ∈ [pt_k, pt_{k+1})` (`OCS.multIdx_mem`), `γ_k ∈ [pt_k, pt_{k+1}]`
(`OCS.multBary_mem`), so `|y - γ_k| ≤ pt_{k+1} - pt_k ≤ 1/a` (`OCS.multPt_succ_sub_bounds`).
`infDist ≤ dist` to a member (`Metric.infDist_le_dist_of_mem`).

---

## 4. Part C: `testFn ∈ PW` and its size on `ℝ`

Set `a = 1/2`, `b = 1`, and let `c₁, c₂` be the constants of `lemma3_estimate_uniform (a, b)`.  Let
`a₁ ≥ 1`, `2a₁ < a₂`; write `Γ = multGammaC (dens a₁ a₂)`, `κ = kappaMu a₁ a₂`.

### C1. `testFn_norm_real`
```lean
theorem testFn_norm_real :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a₁ a₂ : ℝ, 1 ≤ a₁ → 2 * a₁ < a₂ → ∀ x : ℝ,
      c * √(env a₁ a₂ (x + 1/2)) * infDist (((x + 1/2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂)) ≤ ‖testFn a₁ a₂ x‖ ∧
      ‖testFn a₁ a₂ x‖ ≤ C * √(env a₁ a₂ (x + 1/2)) * infDist (((x + 1/2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂))
```
*Proof.*  Take `c = c₁ e^{-4}`, `C = c₂ e^{4}`.  For real `y = x + 1/2`, `|Im y| = 0 ≤ 1`, and
`‖testFn x‖ = ‖F(y)‖ e^{-κ y}` (`Complex.norm_exp`, `Complex.exp_re`, `ofReal`).  By A3 (real `y`):
`U(y) := multU m 0 y = 0 + potW y + κ y`, so `‖F y‖ e^{-U(y)} = ‖testFn x‖ e^{-potW y}`.
`lemma3_estimate_uniform` gives `c₁ dist ≤ ‖testFn x‖ e^{-potW y} ≤ c₂ dist`.  By A5,
`e^{potW y} ∈ [e^{-4} √env(y), e^{4} √env(y)]`.  So the constants are `c = c₁e^{-4}`, `C = c₂e^{4}`
(`|W - ½ log env| ≤ 4` gives `e^{±4}`).

### C2. `differentiable_testFn`
`OCS.differentiable_multF` (needs `IsMultWeight`, A1), `Complex.exp` of a linear function is entire,
`.comp (differentiable_id.add_const _)`.

### C3. `isExpTypeLE_testFn`
```lean
theorem isExpTypeLE_testFn {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    IsExpTypeLE Real.pi (testFn a₁ a₂)
```
We show `‖testFn z‖ ≤ C₀ e^{π|Im z|}` for all `z` with `C₀ = C₀(a₂)`.  This gives type `≤ π`:
`e^{π|Im z|} ≤ e^{(π+ε)‖z‖}`.  Put `w = z + 1/2` (same `Im`), `G(w) = F(w) e^{-κ w}`.

* **`|Im w| ≥ 1`.**  `OCS.exp_multL`: `F w = exp(L w)`, so `‖F w‖ = exp(Re L w)`.  By
  `OCS.multF_estimate_three` (with `a = 1/2`): `‖L w - U w - i V w‖ ≤ π/(2a)/|Im w| = π/|Im w| ≤ π`;
  `Re(i V) = 0` (`V` real), so `Re L(w) ≤ U(w) + π`.  With A3, `U(w) = π|Im w| + potW w + κ Re w`
  and A6: `‖G w‖ = ‖F w‖ e^{-κ Re w} ≤ exp(π|Im w| + log(2a₂) + 1 + π)`.
* **`|Im w| ≤ 1`.**  `lemma3_estimate_uniform` (upper): `‖F w‖ ≤ c₂ e^{U(w)} infDist w Γ`, and
  `infDist w Γ ≤ ‖w - Re w‖ + infDist (Re w) Γ ≤ 1 + 1/a = 3` (B4; `Metric.infDist_le_infDist_add_dist`).
  Same computation: `‖G w‖ ≤ 3 c₂ · 2a₂ · e · e^{π|Im w|}`.

### C4. `memLp_testFn`
`|f(x)| ≤ C √env(x + 1/2) · infDist ≤ C √env(x+1/2) · 2` (C1, B4, `1/a = 2`).  `env` is integrable:
`∫_ℝ env = 2[a₁ + a₁ log(a₂/a₁) + a₁] < ∞` (explicit; or dominate
`env(x) ≤ 1` on `[-a₂, a₂]` and `env(x) = a₁a₂/x²` beyond; any finite bound suffices).  Use
`memLp_two_iff_integrable_sq` + `Integrable.mono'` for the measurable function `testFn` (continuous,
by C2); `(√env)² = env`.

### C5. `memPW_testFn`
`⟨differentiable_testFn, isExpTypeLE_testFn, memLp_testFn⟩` — already proved term in the scaffold.

---

## 5. Part D: mass and sampling sums

### D0. Counting lemma (inside the proof of D2; not a separate statement in the scaffold)
Let `B = sup |ψ'| < ∞` (`ψ'` continuous, tends to `0` at `cocompact`, so bounded; e.g.
from `Tendsto (deriv ψ) (cocompact ℝ) (𝓝 0)`: eventually `≤ 1`
outside a compact set, and continuous on the compact set).  `g(x) = x + ψ(x)` has `g' = 1 + ψ' ∈ [1, 1+B]`
(monotone ⇒ `ψ' ≥ 0`; `deriv` of a `C¹` monotone function is `≥ 0`).  Distinct `λ < λ'` in `Λ`:
`g(λ') - g(λ) ∈ ℤ`, `> 0`, so `≥ 1`, and `≤ (1+B)(λ' - λ)` (mean value theorem
`Convex.norm_image_sub_le_of_norm_deriv_le` / `image_sub_le_mul_sub_of_deriv_le`).  Hence
`λ' - λ ≥ 1/(1+B)` and **every interval `[j, j+1)` contains at most `2 + B` points of `Λ`**
(`n` points need `(n-1)/(1+B) ≤ 1`).  Also `Λ ∩ (-∞, 0] = ℤ_{≤0}` (`ψ = 0` ⇒ `x ∈ ℤ`; conversely
`ψ(j) = 0`).  Tool for converting `sampleSum` (an `ℝ≥0∞` `tsum` over the subtype `Λ`) to sums over
`j`: `ENNReal.tsum_comp_le_tsum_of_injective` is not what is needed; use the fibration
`l ↦ ⌊l⌋`: `∑'_{l:Λ} h(l) = ∑'_{j:ℤ} ∑'_{l:Λ, ⌊l⌋ = j} h(l)` (`ENNReal.tsum_sigma'`/`tsum_fiberwise`
or `ENNReal.tsum_eq_iSup_sum` + finite sums), then `∑'_{l ∈ Λ∩[j,j+1)} h(l) ≤ (2+B)·sup h` as a
finite sum of at most `2 + B` terms (`Set.Finite`, `ENNReal.tsum_le_card_mul…`/`Finset.sum_le_card_nsmul`).

### D1. `pwNormSq_testFn_ge`  (mass)
```lean
theorem pwNormSq_testFn_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ a₁ a₂ : ℝ, 8 ≤ a₁ → 16 * a₁ ≤ a₂ →
      ENNReal.ofReal (c * a₁ * Real.log (a₂ / (4 * a₁))) ≤ pwNormSq (testFn a₁ a₂)
```
`pwNormSq f = ∫⁻ ‖f x‖ₑ²`.  Restrict to `S = [2a₁ + 3, a₂ - 3]` (`lintegral_mono_set`), then use C1 (lower
bound, constant `c₀` of C1) and B3: for `x ∈ S`
`‖f x‖² ≥ c₀² env(x + 1/2) d(x)²`, `d(x) = |x - 1/2 - round(x - 1/2)| = dist(x, ℤ + 1/2)`.
On `S`, `x + 1/2 ∈ [2a₁, a₂]`, so `env(x + 1/2) = a₁/(x + 1/2)`.  Convert to a real integral
(`ofReal_integral_eq_lintegral_ofReal` with integrability, or keep everything in `ℝ≥0∞` and compare
with a Riemann-type sum):
`∫_S a₁ d(x)²/(x + 1/2) dx ≥ a₁ ∑_{k=k₀}^{k₁-1} (1/(k + 3/2)) ∫_k^{k+1} d(x)² dx`,
`k₀ = ⌈2a₁ + 3⌉`, `k₁ = ⌊a₂ - 3⌋`, using `1/(x + 1/2) ≥ 1/(k + 3/2)` on `[k, k+1]`.
`∫_k^{k+1} d² = ∫_{-1/2}^{1/2} s² ds = 1/12` (`d` is 1-periodic and even about the lattice
`ℤ + 1/2`; `Function.Periodic.intervalIntegral_add_eq`, then `integral_pow`; or split each cell
at `k + 1/2` and substitute).  Then
`∑_{k=k₀}^{k₁-1} 1/(k + 3/2) ≥ ∫_{k₀+3/2}^{k₁+3/2} ds/s = log((k₁ + 3/2)/(k₀ + 3/2))`
(`1/(k+3/2) ≥ ∫_{k+3/2}^{k+5/2} ds/s`, i.e. `AntitoneOn.integral_le_sum`/ `sum_le_integral`‑family), and
`(k₁ + 3/2)/(k₀ + 3/2) ≥ (a₂ - 5/2)/(2a₁ + 11/2) ≥ a₂/(4a₁)` when `a₁ ≥ 8` and `a₂ ≥ 16a₁`
(`⇔ a₂(2a₁ - 11/2) ≥ 10a₁`, and `16a₁(2a₁ - 11/2) ≥ 10a₁` for `a₁ ≥ 8`).
Therefore `‖f‖² ≥ (c₀²/12) a₁ log(a₂/(4a₁))`; take `c = c₀²/12`.

### D2. `sampleSum_testFn_le`  (sampling sum)
```lean
theorem sampleSum_testFn_le {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ a₁ a₂ η : ℝ, 8 ≤ a₁ → 16 * a₁ ≤ a₂ → 0 ≤ η →
      (∀ l ∈ LambdaPsi ψ, l ∈ Icc (2 * a₁ + 3) (a₂ - 3) → ∃ k : ℤ, |l - (k + 1 / 2)| ≤ η) →
      sampleSum (LambdaPsi ψ) (testFn a₁ a₂) ≤
        ENNReal.ofReal (C * a₁ * (1 + η ^ 2 * Real.log (a₂ / a₁)))
```
`C` depends on `ψ` only through `B = sup|ψ'|` and on the constants of C1, B4.  Let `C₁` be the upper
constant of C1, `δ(l) = |l - 1/2 - round(l - 1/2)|` (distance of `l` to `ℤ + 1/2`).  By C1 and B4:
`|f(l)|² ≤ C₁² env(l + 1/2) · infDist(l + 1/2, Γ)² ≤ 4C₁² env(l + 1/2)` for all real `l`.
Split `Λ = Λ_0 ∪ Λ_1 ∪ Λ_2 ∪ Λ_3` with `Λ_0 = Λ ∩ (-∞, 0]`, `Λ_1 = Λ ∩ (0, 2a₁ + 3)`,
`Λ_2 = Λ ∩ [2a₁ + 3, a₂ - 3]`, `Λ_3 = Λ ∩ (a₂ - 3, ∞)`.

* **`Λ_0`:** `l ∈ ℤ_{≤0}` (D0) and `f(l) = 0` (B2): contributes `0`.  (This uses `a₁ ≥ 2` and `2a₁ < a₂`.)
* **`Λ_1`:** `env ≤ 1`; at most `1 + (1+B)(2a₁ + 3) ≤ (2+B)(2a₁ + 4)` points (D0): contribution `≤ 4C₁²(2+B)(2a₁+4) ≤ C' a₁`.
* **`Λ_2`:** by hypothesis `δ(l) ≤ η`, and by B3 `infDist(l + 1/2, Γ) = δ(l)`; so `|f(l)|² ≤ C₁² η² env(l + 1/2)`
  with `env(l + 1/2) = a₁/(l + 1/2)` (`2a₁ + 3 ≤ l`, `l + 1/2 ≤ a₂ - 5/2 ≤ a₂`).  `env` is nonincreasing in
  `|x|`, so grouping by `j = ⌊l⌋` (D0) the contribution is
  `≤ C₁² η² (2+B) ∑_{j = ⌊2a₁+3⌋}^{⌊a₂-3⌋} a₁/(j + 1/2)
   ≤ C₁² η² (2+B) a₁ (1 + log(a₂/(2a₁+2)))` (`∑_{j=j₀}^{j₁} 1/(j+1/2) ≤ 1/(j₀+1/2) + ∫_{j₀+1/2}^{j₁+1/2} ds/s`).
* **`Λ_3`:** `l > a₂ - 3`: `env(l + 1/2) ≤ a₁/(a₂ - 3)·1` for `l + 1/2 ≤ a₂` and `= a₁a₂/(l+1/2)²` after;
  `∑_{j ≥ ⌊a₂ - 3⌋} env(j + 1/2) ≤ 4 a₁/(a₂ - 3) + a₁ a₂ ∑_{j ≥ ⌊a₂⌋} (j + 1/2)^{-2} ≤ 4a₁/(a₂-3) + 2a₁ ≤ 3a₁`
  (`∑_{j ≥ m} (j+1/2)^{-2} ≤ 1/(m - 1/2)`).  Contribution `≤ 12 C₁²(2+B) a₁`.

Add up; use the `Λ_2` bound is `η² a₁ (1 + log(a₂/a₁))`; since `a₂/a₁ ≥ 16`,
`log(a₂/a₁) ≥ log 16 > 1`, so `η² a₁ ≤ η² a₁ log(a₂/a₁)`, hence the total is
`≤ C a₁ (1 + η² log(a₂/a₁))`.

---

## 6. Part E: the window

### E1. `exists_window`
```lean
theorem exists_window {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hsmall : Tendsto (fun x ↦ x * deriv ψ x) atTop (𝓝 0)) {η s : ℝ} (hη : 0 < η) (hs : 0 < s)
    (A₀ : ℝ) :
    ∃ a₁ a₂ : ℝ, A₀ ≤ a₁ ∧ 8 ≤ a₁ ∧ 16 * a₁ ≤ a₂ ∧ s ≤ Real.log (a₂ / (4 * a₁)) ∧
      ∀ l ∈ LambdaPsi ψ, l ∈ Icc (2 * a₁ + 3) (a₂ - 3) → ∃ k : ℤ, |l - (k + 1 / 2)| ≤ η
```
*Proof.*
1. `ψ → ∞` at `+∞`: the alternative `Tendsto ψ atBot atBot` contradicts `ψ = 0` on `(-∞, 0]` (`h0`).
2. Put `s' = max (s + 1) 3` (so `e^{s'} ≥ 8`) and `ε = η/s'`.  By `hsmall`, `∃ R ≥ 1`,
   `∀ x ≥ R, x * deriv ψ x ≤ ε` (`Tendsto.eventually_le_const`/`eventually_atTop`).
3. Choose `R' = max R (max 19 (2A₀ + 3))`.  Since `ψ` is continuous, unbounded above, choose an integer `n`
   with `n + 1/2 ≥ ψ(R')`; by `intermediate_value_Ici` there is `x₀ ≥ R'` with `ψ(x₀) = n + 1/2`.
4. **Key estimate.**  For `x ∈ [x₀, x₀ e^{s'}]`: `0 ≤ ψ(x) - ψ(x₀) ≤ ε log(x/x₀) ≤ ε s' = η`.
   Lower bound: `ψ` monotone.  Upper: `h(x) = ε log x - ψ(x)` has `h'(x) = ε/x - ψ'(x) ≥ 0` on `[R, ∞)`,
   so `h` is monotone there (`monotoneOn_of_deriv_nonneg` on `Ici R`, `ψ` differentiable) and
   `ψ(x) - ψ(x₀) ≤ ε(log x - log x₀)`.
5. Set `a₁ = (x₀ - 3)/2` (so `2a₁ + 3 = x₀`; `a₁ ≥ 8` as `x₀ ≥ 19`; `a₁ ≥ A₀`) and `a₂ = x₀ e^{s'} + 3`
   (so `a₂ - 3 = x₀ e^{s'}`).  `16a₁ = 8x₀ - 24 ≤ x₀ e^{s'} + 3 = a₂` since `e^{s'} ≥ 8`.
   `a₂/(4a₁) = 2(x₀e^{s'} + 3)/(4(x₀ - 3)) ≥ e^{s'}/2`, so `log(a₂/(4a₁)) ≥ s' - log 2 ≥ s`.
6. **Matching.**  Let `l ∈ Λ ∩ [x₀, x₀e^{s'}]`, `l + ψ(l) = k ∈ ℤ`.  Then
   `l - ((k - n - 1) + 1/2) = l - k + n + 1/2 = (n + 1/2) - ψ(l)`, of absolute value `≤ η` by step 4.
   So the integer `k - n - 1` works.

(Remark: `x₀` need not be related to any `t_n`; no "logarithmically regular partition", no `ε_n`,
no `ξ_n` are needed.)

---

## 7. Main theorem

```lean
theorem theorem2_ii ... : ¬ IsSampling (LambdaPsi ψ)
```
*Proof.*  Suppose `IsSampling Λ` with `A > 0` (`A : ℝ≥0`) and `∀ f ∈ PW, A ‖f‖² ≤ ∑_Λ |f|²`.
Let `c` be the constant of D1 and `C` that of D2 (for this `ψ`; `hψ`, `h0`).  Choose
`s ≥ 1` with `3C ≤ A c s`, and `η > 0` with `3 C η² (1 + log 4) ≤ A c`.  [Then for `L = log(a₂/(4a₁)) ≥ s`:
`log(a₂/a₁) = L + log 4 ≤ L(1 + log 4)` (as `L ≥ 1`), so
`C (1 + η² log(a₂/a₁)) ≤ C + C η² (1 + log 4) L ≤ (A c/3) L + (A c/3) L < A c L` — more precisely
`≤ (2/3) A c L`.]  Take `a₁, a₂` from `exists_window` (with `A₀ = 8`), `f = testFn a₁ a₂ ∈ PW`
(`memPW_testFn`).  Then
`A · pwNormSq f ≥ A · ofReal(c a₁ L)` (D1) `> ofReal(C a₁(1 + η² log(a₂/a₁)))` (strict, as
`(2/3) A c a₁ L < A c a₁ L` and `L ≥ 1`, `a₁ ≥ 8`) `≥ sampleSum Λ f` (D2) `≥ A · pwNormSq f`
(sampling): contradiction.  (No finiteness of `pwNormSq f` is needed in this chain, since the strict
inequality is between `ENNReal.ofReal` numbers and `A * ofReal(...)`; keep the multiplication by
`(A : ℝ≥0∞)` outside.)

---

## 8. Issues in the source

Quotes are from `literature/ArxivOrtega.tex` (lines ≈ 967–1040); page images p-16, p-17 agree.

1. **Typo `ψ_n`** (line 979): "`φ_n(t)=\psi_n(t)-n-1/2`" must be `ψ(t)` (there is no `ψ_n`).  *Certain.*
2. **Typo in the hypothesis** (line 997): "the assumption `\phi_n'(t)=o(1/t)`" should be `ψ'(t) = o(1/t)`
   (`φ_n'` is a combination of `ψ'`, `1` and `0` and is not `o(1/t)`, e.g. `φ_n' = -1/ξ_n` on `[ξ_n, 2ξ_n]`
   is `≃ 1/t` there).  *Certain.*
3. **`ε_n → 0` is not justified, and false in general** (line 986: "It is clear that `ε_n → 0`").
   `ε_n` is defined by `∫_{t_n}^{ξ_n} φ_n(x)/x dx = 0`, i.e. in `s = log x` by
   `∫ (ψ - n - 1/2) ds = 0` over `[log t_n, log ξ_n]` where `ψ - n - 1/2` runs from `-1/2` up to `ε_n`.
   For `ψ` locally linear in `s` with slope `σ ≪ 1` this is `∫_{-1/2}^{ε} u du/σ = 0`, i.e. `ε = 1/2`
   (so `ψ(ξ_n) = n + 1`, contradicting `ξ_n < t_{n+1}/2`).  For `ψ = log log x`
   (`ds = e^{ψ} dψ`) it gives `∫_{-1/2}^{ε} u e^{u} du = 0`, whose root `ε ≈ 0.37`.
   (Consistent with the coordinator's `e^{a}(a - 3/2) + 3/2 = 0`, `a = 1/2 + ε`; I did not re-derive that
   numeric value but the two-line computation above shows `ε_n ↛ 0`.)  *Sure that the argument as written
   does not give `ε_n → 0`.*  Moreover the *intended* quantity is not `ε_n` but the matching of `ψ` to a
   half integer on a long range (§0.2).
4. **The heuristic formula** (line 994): "`U_n(x)=\int_0^{|x|}\frac{\phi_n(t)-1/2}{t}dt+O(1)`" is divergent at `0` as
   written (`φ_n(t) - 1/2 → -1/2` at `0`); it should be `∫_1^{|x|}`.  With the paper's `φ_n`
   (`φ_n = -1/2` on `[1/2, t_n]`, `φ_n(-t) = +1/2`) the slope of `U_n` in `log x` is `φ_n - 1/2`
   (`= -1` on `[1, t_n]`, i.e. `U_n = -log x` there, as the paper says, and between `-1` and
   `-1/2 + ε_n` on `(t_n, ξ_n)`).  *Fairly sure.*
5. **The claimed behaviour `U_n(x) + ½ log x ≃ 1` on `[(1-o(1))ξ_n, 2ξ_n]` does not follow**: on `[t_n, ξ_n]`
   the slope of `U_n` is `ψ - n - 1 ∈ (-1, -1/2 + ε_n)`, so
   `U_n(ξ_n) = -log t_n + ∫_{t_n}^{ξ_n}(ψ - n - 1)dt/t`, which is `≈ -½ log ξ_n - ½ log t_n` (`not`
   `-½ log ξ_n + O(1)`) when `ψ - n - 1 ≈ -1/2` on most of the range.  *Sure that the estimate is
   not justified as stated; the right statement is of the form `U + ½ log x = O(1)` on a range where
   the slope is `-1/2`, which requires `ψ ≈ n + 1/2` there.*
6. **(∞) and (finite)** (lines 1004–1010): `Ω_n = [t_n, ξ_n] ∪ [2ξ_n, t_{n+1}]` and the claims
   `∫_{Ω_n} e^{2U_n} → ∞`, `∫_{ℝ∖Ω_n} e^{2U_n} ≲ 1` are not correct as set up: the mass `∫_{[t_n,ξ_n]} e^{2U_n}`
   is `≈ ∫ dx/x · e^{O(1)}` only if the slope is `-1/2` throughout, and `∫_{ℝ∖Ω_n}` contains the
   region near the origin (mass `≃ 1` there) *and* `[ξ_n, 2ξ_n]`, the region where the zero of the
   deleted point is smeared (mass comparable to that of `Ω_n` if `Ω_n` has only bounded logarithmic
   length).  Also `dist(λ_k, Γ) → 0` on `[ξ_n, 2ξ_n]` fails: the smeared deletion shifts `Γ` by up to
   `1` relative to `Λ` there, and a *sharp* deletion creates a peak `|f| ≈ x_d e^{...}` of mass
   comparable to its sampling value.  *Fairly sure; this is why the reconstruction places the
   smearing at logarithmic distance (in both directions) from the bulk of the mass.*
7. **The statement "`Ω_n` has `∫_{Ω_n} → ∞`" needs `ψ' = o(1/x)` in the following precise way**, never
   stated in the paper: `ψ' = o(1/x)` is *equivalent to the existence, for every `s`, `η`, of arbitrarily
   far windows `[x, x e^{s}]` on which `|ψ - (integer + 1/2)| ≤ η`*; the log-length of the window is the
   quantity `→ ∞` which makes the critical mass `∫ dx/x` diverge.  *(Remark, not an error.)*
8. **Minor:** (line 1033) "`\dist(λ_k, Γ) → 0` uniformly for `λ_k ∈ Ω_n`" and "`γ_k = k` for all
   `k < 0`": in [OS99] Lemma 3, `Γ = {barycentres}` is `ℤ + 1/2` for `m ≡ 1`; the zero set must be
   translated by `1/2` (as done here by `f(z) = G(z + 1/2)`).  The final line has `|f(λ_k)|²/‖f‖²`
   with `f` instead of `f_n` and `\sum_k` over `Λ`.  *Certain, harmless.*
9. **The linear exponential factor.**  The paper says "the construction of `f_n` is identical to that of
   `A` in the proof of Corollary 2" and `f_n = lim ∏_{|γ_k|<R} (1 - z/γ_k)`; the product is in the
   symmetric (principal value) sense and equals `F(z) e^{-κ z}` where `F` is Lemma 3's function (whose
   `|F| ≃ e^{U}` includes the linear term `Re(z/t)`).  Without this correction `F` itself can have type
   `> π` (`e^{κz}` factor) — here handled by `G = F e^{-κz}`.  *Certain (see README §2.5).*
10. **`f_n ∈ PW` also needs `‖f_n‖ < ∞` and `‖f_n‖_{PW} → ∞` is not the point**; the point is the
    ratio `∑|f_n(λ)|²/‖f_n‖² → 0`, which the paper deduces from `dist(λ, Γ) → 0` on `Ω_n`, which needs
    the whole mass to sit where `Γ ≈ Λ` (see 6).  *Fairly sure.*

**Possible simplification vs. the paper:** no "logarithmically regular partition" is needed for (ii),
no `t_n`, `ξ_n`, `ε_n`: a single window and two uniform ramps suffice, with all estimates explicit
(constants `4` in A4/A5).

---

## 9. Requested changes to M00

None.  (`theorem2_ii` is true as stated; `hPW` is unused.)

Possible remark for M00: `IsAdmissiblePsi` as stated in `Defs.lean` allows `Tendsto ψ atBot atBot`; combined
with `h0` this alternative is impossible, so no change is needed.

## 10. Request to other modules

* The owner of the vendored library `OCS` (or whoever assembles): `lemma3_estimate_uniform` (see §0.3).
  Without it, replace the proof of `testFn_norm_real` by a re-proof inside `FF`.
