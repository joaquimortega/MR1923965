# Implementation notes: necessity (M03)

All 47 original `sorry`s in `FourierFrames/Theorem1/Necessity.lean` are proved; no statement was changed
(`scripts/check_statements.py scaffold-reviewed` passes). Helper file: `Necessity/Sep.lean`
(summability of `1/(1+x^2)` over a separated set by bucketing into unit cells).

Deviations / remarks
- New helper declarations in the main file (not statements of the scaffold): `PWFun.mk`, `PWFun.val_mk`,
  `IsSeparated.eventually_le_abs` (cofinite lemma used throughout).
- `differentiableOn_tsum_of_cofinite_bound`: `u` need not be nonnegative; proof uses `|u|`.
- Remaining linter warnings are unused-variable / unused-section-variable warnings on frozen statements
  (`sampInner_self`, `sampInner_conj_symm`, `sampInner_smul_left`, `samp_H1`, `samp_H3`: hs/hf/hg unused;
  `entSum_eq`: hΛ, hcs unused; `summable_norm_herglotz` is fine). They cannot be removed without changing statements.
- `herglotzEnt_eq` / `exists_herglotz_const`: as warned in the blueprint, `(c := ...)` must be given explicitly
  to `entSum_eq` to avoid whnf timeouts.
- No upstream problems found. Upstream `IsSeparated.finite_inter_Icc` (PW/Basic) and `pw_complete`, `pw_norm_sq_le`,
  `MemPW.eq_zero_of_pwNormSq_eq_zero`, `HEEqPW.*` etc. are used as black boxes.
