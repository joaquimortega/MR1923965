# Implementation notes — `cited-p3e` (P3, Theorem E: Space, EntireHerglotz, Orthogonal, Complete)

## Mathlib API names in this version (v4.35.0, filter-indexed `∑'[L]`)
* `Summable.tsum_sub`, `Summable.tsum_add`, `Summable.tsum_mul_left` (no root `tsum_sub`/`tsum_add`);
  `Summable.tsum_le_tsum` (no root `tsum_le_tsum`); `Complex.conj_tsum`, `Complex.ofReal_tsum`
  hold without summability; `Complex.re_tsum` needs it; `Complex.summable_conj`, `Summable.star`.
* `MeasureTheory.lintegral_liminf_le` (Fatou); `differentiableOn_dslope` (root namespace).

## EntireHerglotz
* Added helpers `continuousOn_poissonKernel_sphere`, `pickKer` (the kernel `k_w`),
  `continuousOn_pickKer`, `im_div_im_eq_circleAverage`, `im_div_im_le` (one half of
  `im_div_im_eq`, the limit `κ(r,R) → 1` via `t = r/R → 0`).  No deviation from the blueprint.
