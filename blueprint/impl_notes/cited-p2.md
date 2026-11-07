# cited-p2 notes

## Part A (DSPerturbation) -- complete, no sorry
- `enorm_sq_sub_le`: dropped the unused hypothesis `hPW` (helper owned by this module; call sites updated).
- Added helpers: `enorm_ofReal_eq`, `l2pi_mul_t_aux`, `ennreal_rpow_half_sq`, `lintegral_sq_le`
  (Cauchy-Schwarz on a set in ENNReal), `IsSepBy.finite_inter_Icc`, `IsSepBy.countable`,
  `tsum_indicator_Icc_le`.
- Route as in blueprint (Bernstein in L2 via `hasDerivAt_pwFT`, FTC + CS, finite overlap, transfer);
  constants A' = A/4, B' = 2B + 2*(A/4), L = min d (A/(12 pi^2)).

## Part B (JohnNirenberg) -- complete, no sorry
- Followed the blueprint: `cz_step` via the stopping tree (selected cells `czSel`, index type
  `CzIdx`), not the generation-by-generation fallback. Constants C = 2, c = log 2 / 4.
- New helpers (all in `JohnNirenberg.lean`): `dyadic_eq`, `dyadicIdx_eq_of_mem`, `dyadic_anc`,
  `dyadic_nested` (the nested-or-disjoint lemma, in the form "common point => k = k'/2^m"),
  `dyadic_subset`, `measurableSet_dyadic`, `osc`, `locInt_osc`, `integral_osc_le`,
  `abs_intervalMean_sub_le`, `czG/cl/cr/czStop/czSel`, `czSel_disjoint`, `czSel_mean`,
  `czSel_length`, `dyadicIdx_anc`, `dyadicIdx_lt`, `czStop_exists_sel`, `czSel_good`.
- `volume_dyadic`: hypothesis renamed `_hab` (unused; *later* removed in the lint pass, NOTEBOOK I-03). Other
  scaffold statements unchanged.
- Lebesgue differentiation: `IsUnifLocDoublingMeasure.ae_tendsto_average` with `ι := ℕ`, `l := atTop`, K = 1.
