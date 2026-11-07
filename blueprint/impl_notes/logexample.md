# logexample implementation notes (M06)

Files: `FourierFrames/LogExample.lean`, `FourierFrames/LogExample/Basic.lean` (log estimates),
`FourierFrames/LogExample/Phase.lean` (`integral_cos_sq_phase_ge`),
`FourierFrames/LogExample/Potential.lean` (the §4 analysis: `logPrimD`, `integral_log_one_add_inv_sq`,
`integral_posLog_kern_eq`, `abs_integral_phiK_le`, `young_uv`, …).

## Deviations from the blueprint
- `logLam_sub_ge_of_le` (new, non-strict) is proved first; `logLam_sub_ge` follows. Needed for
  `logPt_ge` at `j = 1`.
- `not_memHE_sAlpha`: instead of the disjoint-intervals argument, uses
  `∫_0^T cos²(φ) ≥ (m₁T/2 - 1/2)/M₁` (FTC with the antiderivative `φ/2 + sin(2φ)/4` and
  `m₁ ≤ φ' ≤ M₁`), see `LogEx.integral_cos_sq_phase_ge`. Needs continuity of `φ' = phaseDeriv E`
  (from `deriv E` continuous).
- Extra helpers: `orthWeight_bounds`, `finite_logExample_inter_Ioc_pos`,
  `integral_mul_density_split`, `re_eq_norm_mul_cos`, `norm_sAlpha_eq`, ...
- `landau_sharp` is the strengthened statement (all `A < 1`); proof uses `logExample_count` with
  `C = 2` and `R = exp((|B|+C+1)/(1-A)+1)`.

## Status
All declarations in `FourierFrames/LogExample.lean` and its aux files are `sorry`-free (the only
`sorry`s reachable are upstream black boxes: M01/M02/M07, `Construction.lean`, `HB/*`, ...).
No statement was changed; `check_statements.py scaffold-reviewed` passes.

## Proof strategy deviations in section 4
- `abs_integral_posLog_mul_logKernel_le`: not the blueprint's `Q_R` splitting.  Direct integration
  by parts of `log t * K_z(t) = log t * phi'(t)` on `[1,R]` and `[-R,-1]` with the explicit primitive
  `phi(t) = log D(t)/2 - log t` (`LogEx.integral_posLog_kern_eq`), reflection `t -> -t`, then
  `|phi(s) - phi(-s)| <= log((s+|x|)/|s-|x||)` and scaling to `integrableOn_log_ratio_div`
  (`LogEx.abs_integral_phiK_le`).  The constant is `int_0^infty H`.
- `integral_abs_rho_logKernel_le`: the trivial bound `|K| <= 1/||t-z|| + 1/|t|` and Young's
  inequality `u v <= u^3/3 + 2 v^{3/2}/3` give an `x`-independent majorant (no case analysis in
  `|t|` versus `|z|`).
- `integral_log_mul_sub_one_eq`: `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`
  on `[-R,R]` for `Psi = log||1 - z/t|| * W` with exceptional set `{breakpoints of m} ∪ {0}`
  (no absolute continuity machinery); the continuity of `Psi` at `0` comes from `|W| <= 19|t|` and
  continuity of `t log t`.
- `multU_model`: real antiderivative `logPrimD` of `log((t-x)^2+y^2)` (no `Complex.log`).
- `abs_multU_sub_multU_le` (strip): exact constant `20 pi` via `int_R log(1+1/s^2) = 2 pi`
  (antiderivative `s log(1+1/s^2) + 2 arctan s`, `LogEx.integral_log_one_add_inv_sq`).
- `integrable_log_mul_sub_one` does not use the hypothesis `0 < Im z`; it is deduced from
  `OCS.integrable_multUIntegrand` for `m` and for `1`. (The hypothesis was removed in the lint pass,
  NOTEBOOK I-03.)
