# logexample implementation notes (M06)

Files: `FourierFrames/LogExample.lean`, `FourierFrames/LogExample/Basic.lean` (log estimates),
`FourierFrames/LogExample/Phase.lean` (`integral_cos_sq_phase_ge`).

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
See the report; remaining `sorry`s are all in section 4 (potential estimate).
