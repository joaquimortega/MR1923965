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

## Space
* **Changed statement** `heInner_self`: the hypothesis `h0 : ∀ x : ℝ, E x ≠ 0` was unused and is
  removed (`include hE in` instead of `include hE h0 in`; call as `heInner_self hE hf`).  The
  identity holds without it: if `‖f‖_E = ∞`, the Bochner integral of the non-integrable
  nonnegative function is `0 = ∞.toReal`.
* Added helpers: `measurable_div_real`, `heInner_sub_right`, `lintegral_enorm_sq_le_of_tendsto`
  (Fatou for `‖·‖ₑ²` along pointwise limits, used three times in `memHE_of_cauchy`),
  `uniformCauchySeqOn_of_cauchy`, `exists_limit_of_cauchy` (they live in `Space.lean` itself, since
  they use the lemmas of the file).
* `norm_heInner_sq_le`: via `ENNReal.lintegral_mul_le_Lp_mul_Lq` (p = q = 2), as in the blueprint.
* `memHE_of_cauchy`: the uniform bound `B` on `‖f n‖²` is only needed eventually
  (`n ≥ N(1)`), since the Fatou helper takes an eventual bound.
