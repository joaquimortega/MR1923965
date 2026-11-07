# Implementation notes: hb (M02)

All `sorry`s in `FourierFrames/HB/{Basic,Phase,H2,DeBranges,Comparable}.lean` are closed.
No statement changed (`check_statements.py scaffold-reviewed` passes).

New helper files (all under `FourierFrames/HB/`):
- `Hopf.lean`: elementary Hopf-type boundary lemma (`hopf_trig`, `hopf_boundary`) used for `phaseDeriv > 0`.
- `MeanValue.lean`: circle/area mean-value inequality for `|G|^2` (Cauchy-Schwarz on circles + polar coordinates), `lintegral_strip` (Tonelli on horizontal strips).

Deviations from the blueprint:
- `phaseDeriv_nonneg` / `phaseDeriv_pos_of_exists_lt` are both derived from one dichotomy
  `IsHB.phaseDeriv_pos_or_eventuallyEq` (either `E^* = c E` near x, then phi'(x)=0, or phi'(x) > 0) via the
  analytic normal form of `Theta - c` and `hopf_boundary`. The `D(y)` one-sided-extremum argument of blueprint 5.1 is not used.
- `exists_isPhaseFunction`: avoids differentiating `|E|`; shows `E(x) exp(i Phi(x) - R(x))` is constant, `R = int Re(E'/E)`.
- `area` mean value: circle Cauchy-Schwarz then polar `lintegral`, rather than area average of `G` then Cauchy-Schwarz.
- `memPW_of_memHE`: Fatou is only needed for `L^2(R)`; the exponential type bound uses `enorm_sq_le_of_lines` on a.e. lines in (-2,2)
  (line `s = 0` is a null set), so no estimate on the real axis is needed there.
- Unused-variable warnings for the frozen hypothesis `hPW` remained (`phaseDeriv_mul_sq_ge`, `memPW_of_memHE`), as instructed;
  the hypothesis was removed from both in the final lint pass (NOTEBOOK I-03).

Upstream usage (black boxes, possibly `sorry`): `exists_memPW_eval_ne_zero`, `MemPW.comp_sub_ofReal`, `MemPW.fstar`,
`pwNormSq_ne_top`, `pw_norm_sq_le`, `pw_line_integral_le`, `pw_eval_lower`, `pwNormSq_fstar`.
Theorem E (`TheoremE`) is a hypothesis of `phaseDeriv_mul_sq_{ge,le}`.
