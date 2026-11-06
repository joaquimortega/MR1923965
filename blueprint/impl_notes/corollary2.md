# Implementation notes: corollary2 (M07 §1, §3)

## Files
- `FourierFrames/Perturbation.lean`: fully proved (no `sorry`).
- `FourierFrames/Corollary2.lean`: main theorem `corollary2` and all of §3 proved except the items
  listed under "Remaining sorries" below.
- Helper files `FourierFrames/Corollary2/{Affine,Kernel,Density,LogInt}.lean`.

## Deviations from the blueprint
- `isSampling_of_replace_finite`: the hypothesis `hsep'` (separation of `Γ'`) is not needed (the
  replacement lemma gives separation of the intermediate sets automatically); it is kept in the
  statement and merely unused.
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
