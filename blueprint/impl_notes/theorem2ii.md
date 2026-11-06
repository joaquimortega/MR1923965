# Implementation notes: theorem2ii (M09)

All 27 `sorry`s of `FourierFrames/Theorem2ii.lean` are proved. The only `sorryAx` that remains in
`#print axioms FF.theorem2_ii` comes from the upstream `lemma3_estimate_uniform`
(`FourierFrames/Lemma3Uniform.lean`, other implementer). The unused-variable warning for `hPW` in
`theorem2_ii` is left as instructed. `check_statements.py scaffold-reviewed` passes.

Helper files (all under `FourierFrames/Theorem2ii/`):
`Window.lean` (window lemma), `UOne.lean` (`U_1 = π|Im z|`), `Ramp.lean` (ramp estimate),
`Mass.lean` (`dev`, `∫_k^{k+1} dev² = 1/12`, harmonic comparison for the mass),
`Cells.lean` (`Λ(ψ)` has at most `⌊1+B⌋+1` points per unit cell, cell-sum lemma in `ℝ≥0∞`,
harmonic and `1/j²` sums).

## Deviations from the blueprint (proofs only; no statement changed)

* `multUIntegrand_one`: instead of the explicit antiderivative `A(s)` for `z = x + iy`, the proof
  reduces to `x = 0` by the shift trick: `∫_{-R}^{R}[G_y(t-x) - G_y(t)] dt = ∫_0^x [G_y(R+u) -
  G_y(R-x+u)] du = O(x²/R)` (`G_y(s) = log(s²+y²)/2`), and for `x = 0` uses the antiderivative
  `t log(t²+c²) - 2 t log t + 2c arctan(t/c)` of `log(t²+c²) - 2 log t`. `multUIntegrand_one_real`
  is a corollary.
* `rampPot_estimate`: **parsing remark.** In the scaffold statement
  `|(1 / a) * ∫ t in a..2 * a, log ‖1 - x/t‖ - log (max 1 (|x|/a))| ≤ 4` the binder of `∫`
  extends over `- log (max ...)`, i.e. it reads `(1/a) * ∫ (g - ℓ)`. This equals
  `(1/a) ∫ g - ℓ` (the constant integrates to `ℓ a`); the proof treats both forms
  (`T2ii.rampPot_estimate'` is the version with explicit parentheses).
  The proof of the `4` uses cruder bounds than the blueprint (`∫_1^2 log|s-ξ| ≥ -2` via
  `min(0, log|v|)` and `∫ min(0,log|v|) = -2`; case split `|ξ| ≤ 3`, `|ξ| ≥ 3`), with `log 3 < 1.11`.
* `exists_window`: `s' = max (s+1) 3`, `ε = η/s'`, as in the blueprint; `x₀` found by
  `intermediate_value_Icc` between `R'` and a point where `ψ ≥ n + 1/2`.
* `potW_le_complex`: proved as in the blueprint with `Vneg(v) = min 0 (log|v|)`, `∫ Vneg = -2`.
* `memLp_testFn`: dominated by `env ≤ (1 + a₁a₂)/(1 + y²)` (a one-line case check, `env_mul_le`)
  instead of the explicit `∫ env`.
* `pwNormSq_testFn_ge`: `dev x = |fract x - 1/2|` (equal to `|x - 1/2 - round (x-1/2)|`), the sum
  over unit cells uses `intervalIntegral.sum_integral_adjacent_intervals` and
  `AntitoneOn.integral_le_sum`.
* `sampleSum_testFn_le`: indexing of cells by `⌊l⌋₊` and a finite-sum argument
  (`tsum_cells_le`: `ENNReal.tsum_eq_iSup_sum` + fibres of `⌊·⌋₊`). The constant is
  `C = 20 (⌊1+B⌋₊+1) C₁²` where `B ≥ sup |ψ'|`. Tail `Λ ∩ (a₂-3, ∞)`: `env ≤ a₁a₂/y²` and the
  telescoping bound `∑_{j ≥ J} 1/(j+1/2)² ≤ 1/J`.

## False / changed statements

None. All scaffold statements were provable as stated.

## Source issues

None new. (Blueprint §0.3 is consistent with the upstream `lemma3_estimate_uniform` as stated.)
