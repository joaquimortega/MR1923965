# Implementation notes: corollary2 (M07 §1, §3)

## Files
- `FourierFrames/Perturbation.lean`: fully proved (no `sorry`).
- `FourierFrames/Corollary2.lean`: main theorem `corollary2` and all of §3 proved (no `sorry` in
  `Perturbation.lean`, `Corollary2.lean` or the helper files; only upstream `sorry`s are used).
- Helper files `FourierFrames/Corollary2/{Affine,Kernel,Density,LogInt}.lean`.

## Deviations from the blueprint
- `isSampling_of_replace_finite`: the hypothesis `hsep'` (separation of `Γ'`) is not needed (the
  replacement lemma gives separation of the intermediate sets automatically); it is kept in the
  statement and merely unused (*later:* removed in the lint pass, NOTEBOOK I-03).
- `IsSampling.of_perturbation`: the proof follows the blueprint (finite near part replaced, far part
  perturbed by Duffin-Schaeffer); only `isSeparated_image_far` (new helper) was added.
- `multU_compact_sub_linear`: the bound holds for all `z` (no `Im z >= 0` needed).
- Plan for `log_norm_eq_multU_add_affine` (changed): instead of a holomorphic logarithm `L` of `f` on
  the closed half plane, use `Phi = e^{i phi(0)} f e^{-P}`, `P = potC g / pi`, which is continuous on
  `Im >= 0`, holomorphic on `Im > 0` and REAL on `R`. Schwarz reflection (`exists_entire_reflection`
  with `c = 0`) gives an entire zero-free `Phi^`, `Phi^ = e^G`, `G` entire with `|Re G| <~ |z|^{3/2}`,
  hence affine; reality on `R` forces the slope of `G` to be real.
- `multU_one` is a corollary of `log_norm_eq_multU_add_affine` applied to `f = e^{-i pi z}`
  (`g = pi`): `pi y = U_1 + b x + c`, and evenness (`U_1(-z-bar...)`) + `U_1(0)=0` give `b = c = 0`.
- `continuous_multU_of_bdd` (measurable `g`) is proved by Vitali's theorem
  (`tendsto_Lp_finite_of_tendsto_ae` + `unifIntegrable_of`): the potential is split as `a + b + c`
  according to the window `|t - Re z| <= 1`; `a`, `c` by dominated convergence, the singular piece
  `b = win * log|t - z| * g` by uniform integrability (tail estimate `tail_eLpNorm`, explicit
  `int_{|u|<=a} -log|u| du = 2a(1 - log a)`).
- Helper files: `Affine` (Borel-Caratheodory + Cauchy), `Kernel` (`potKernel`), `Density`
  (weighted Cesaro, `modDens`), `LogInt` (`int |log|t - z||` bounds, `abs_multU_le_potBound`,
  `multU_compact_aux`), `Reflection` (Schwarz reflection via Morera), `PotC`/`PotCDiff`/`PotCCont`
  (the complex potential `potC'`, a copy of `potC`), `UCont` (continuity of the potential),
  `LogNorm` (`log_norm_aux`, `multU_one_aux`).
- Frozen definitions `argUp`, `potC` stay in `Corollary2.lean`; the helper files use identical
  copies `argUp'`, `potC'` (transfer by `rfl`).

## Source / statement observations
- `multU_compact_sub_linear` holds for all `z` (the hypothesis `Im z >= 0` is not needed).
- `isSampling_of_replace_finite` does not need `hsep'`.
- No false or changed statements found in the owned files.
