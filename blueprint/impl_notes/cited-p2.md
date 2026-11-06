# cited-p2 notes

## Part A (DSPerturbation) -- complete, no sorry
- `enorm_sq_sub_le`: dropped the unused hypothesis `hPW` (helper owned by this module; call sites updated).
- Added helpers: `enorm_ofReal_eq`, `l2pi_mul_t_aux`, `ennreal_rpow_half_sq`, `lintegral_sq_le`
  (Cauchy-Schwarz on a set in ENNReal), `IsSepBy.finite_inter_Icc`, `IsSepBy.countable`,
  `tsum_indicator_Icc_le`.
- Route as in blueprint (Bernstein in L2 via `hasDerivAt_pwFT`, FTC + CS, finite overlap, transfer);
  constants A' = A/4, B' = 2B + 2*(A/4), L = min d (A/(12 pi^2)).
