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

## Interface with Kernel.lean (Theorem D implementer)
* `conj_deBrangesKernel` changes signature in the other branch (`hE` dropped, `E` explicit).  To
  be independent of either version, Theorem E uses a self-contained copy
  `deBrangesKernel_conj_symm (E) (w z)` in `Cited/DeBrangesDE/EAux/KernelSymm.lean` (proved for
  every `E`, with `deriv_fstar` on the diagonal).  `fstar_deBrangesKernel` is not used.
* Other Kernel black boxes used: `deBrangesKernel_mul`, `deBrangesKernel_diag_real`,
  `memHE_deBrangesKernel`, `heInner_kernel`, `exists_bound_deBrangesKernel`,
  `isH2Cont_of_memHE`, `MemHE.heNormSq_lt_top`, `integrable_heInner`, `kernelNum`; from Cauchy:
  `IsH2Cont.lintegral_line_le`.

## Orthogonal
* Import changed to `EAux/KernelSymm` (which imports `Space`).
* **Changed statements** (unused hypothesis `D : DBData E φ` removed, flagged by the linter):
  `fstar_dFun (E φ α)` (true for every `E`: `C^* = C`, and each Mittag-Leffler term satisfies
  `conj r_γ(z̄) = r_γ(z)`; `Complex.conj_tsum` needs no summability) and `defectKer_diag (w)`
  (`Complex.ofReal_tsum` needs no summability).
* Added helpers: `conj_exp_I_mul`, `conj_exp_neg_I_mul`, `exp_neg_mul_exp`,
  `exp_I_mul_sub_pi_div_two`, `cFun_ofReal`, `sFun_ofReal` (on `ℝ`, `C = Re U`, `S = Im U`),
  `sFun_level`, `im_U_level`, `cFun_level_real`, `conj_cFun_level`, `norm_cFun_level_sq`,
  `hasDerivAt_sFun`, `deriv_sFun_ofReal`, `conj_mul_wt_mul`, `finite_level_abs_lt`,
  `differentiable_dslope_sFun`, `differentiable_rTerm`, `sFun_conj`, `dslope_sFun_conj`,
  `conj_rTerm_conj`, `rTerm_level_ne`, `rTerm_level_self`, `cFun_level_ne_zero`.
* `heNormSq_partialSum` is proved from `heInner_partialSum` + `partialSum_level` (simpler than the
  double sum of the blueprint).
* `im_hFun_nonneg`: only `Re Q(w,w) ≥ 0` is needed (imaginary part of the identity
  `Q·π·2i Im w = |S|²·2i Im h`), not the reality of `Q(w,w)`.

## Complete
* Added helpers: `tendsto_sum_exhaustion`, `heNormSq_sub_comm`, `heNormSq_partialSum_sub`,
  `summable_mul_wt_mul` (AM–GM summability), `exists_defect_decomp` (the decomposition
  `Q_w = K_w - g_w` shared by `memHE_defectKer` and `heInner_defectKer_of_level_zero`),
  `orthWeight_mul_enorm_sq`.
* `eq_zero_of_level_zero`: real points by `f(x) = lim f(x + i/(n+1))`.
* No deviation from the blueprint otherwise.  All four files and `EAux/KernelSymm.lean` are
  sorry-free; `#print axioms FF.theoremE_holds` shows `sorryAx` only through the Kernel/Cauchy
  black boxes (`integrable_heInner`, `deBrangesKernel_mul`, `deBrangesKernel_diag_real`,
  `memHE_deBrangesKernel`, `heInner_kernel`, `MemHE.heNormSq_lt_top`,
  `exists_bound_deBrangesKernel`, `isH2Cont_of_memHE`, `IsH2Cont.lintegral_line_le`).
