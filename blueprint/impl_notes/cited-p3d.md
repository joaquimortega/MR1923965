# Implementation notes — `cited-p3d` (P3: `Cauchy.lean`, `Kernel.lean`)

Status: `Cauchy.lean`, `Kernel.lean` and the helper `CauchyAux/Basic.lean` have no `sorry`;
`theoremD_holds` (top file) depends only on `propext`, `Classical.choice`, `Quot.sound`.
No axioms, no linter suppression, no raised heartbeats.

## Changed statements (unused hypotheses removed)
* `conj_deBrangesKernel`: hypothesis `hE : Differentiable ℂ E` unused (the diagonal case only
  needs `deriv_fstar`, which is unconditional).  New: `conj_deBrangesKernel (E : ℂ → ℂ) (w z : ℂ)`.
* `fstar_deBrangesKernel`: same.  New: `fstar_deBrangesKernel (E : ℂ → ℂ) (w : ℂ)`.
* `IsH2Cont.exists_side_seq`: hypothesis `hY : 0 < Y` unused (for `Y ≤ 0` the strip is empty;
  Tonelli gives `C · ofReal Y` for every `Y`).  New call: `hF.exists_side_seq (Y := Y)`.
* `IsH2Cont.tendsto_integral_line_of_dominated`: hypothesis `hc` (continuity of `G`) unused: the
  bound `‖∫ G‖ ≤ ∫ bound` (`norm_integral_le_of_norm_le`) needs no integrability of `G`.  Removed.

No statement was found false.

## New helper lemmas
* `CauchyAux/Basic.lean`: `lintegral_lintegral_strip_le` (Tonelli on a strip),
  `measurable_lintegral_strip`, `exists_ge_add_neg_le_one` (good abscissae, via
  `lintegral_neg_eq_self`), `enorm_intervalIntegral_le`, `rect_identity` (rectangle
  Cauchy–Goursat on `[-R,R]×[0,Y]` in the normalized form), `le_of_dom` (AM–GM form of the
  domination hypothesis), `enorm_le_of_dom_side`.
* `Cauchy.lean`: `IsH2Cont.continuousAt`, `IsH2Cont.integral_sq_le`,
  `IsH2Cont.norm_integral_line_le` (top-side bound), `sub_mul_div_self_eq_zero`,
  `IsH2Cont.continuousOn_dslope`, `IsH2Cont.differentiableAt_dslope`, `norm_dslope_le`
  (domination of the regularized `dslope`), `cauchy_pair_eq`, `integrable_cauchy_pair`,
  `lintegral_poissonKernel`, `sq_lintegral_mul_le` (Cauchy–Schwarz for a probability density in
  `ℝ≥0∞`).
* `Kernel.lean`: `integrable_conj`, `heInner_kernel_eq_of_ae` (decomposition
  `⟨f, K_w⟩ = (-i/2π)[E(w)∫A/(t-w) - E^*(w) conj ∫B/(t-w̄)]` for nonreal `w`, shared by the upper
  and lower reproducing formulas; reusable by P4).

## Deviations from the blueprint
* Domination estimates: one pointwise AM–GM inequality `‖G‖ ≤ (ε/2)‖F‖² + (1/(2ε)+|A|) d⁻²`
  (`le_of_dom`) with `ε = 1` (line integrability), `ε → 0` (top side), `ε = ρ⁻¹` (vertical sides).
* Vertical sides in `integral_eq_integral_line_of_sides`: bounded directly in `ℝ≥0∞` by
  `enorm_integral_le_lintegral_enorm` and `le_lintegral_add`, then
  `tendsto_zero_iff_enorm_tendsto_zero` (no `toReal`, no continuity of the sides; this is the
  referee's F1).
* `exists_sides_of_dominated`: bound `ofReal(ρ⁻¹/2 + 2(ρ⁻¹/2 + |A|ρ⁻²)Y)` with `ρ = Rₙ - ‖w₀‖`.
* `lintegral_line_le`: Cauchy–Schwarz by `ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2`
  (`sq_lintegral_mul_le`), Tonelli by `lintegral_lintegral_swap`.
* `exists_bound_deBrangesKernel`: bound `‖i/2π‖ · 2 M₁ M₀` with `M₀, M₁` bounds of `E`, `E'` on the
  closed ball (closed under `conj`); `(E^*)' = conj E'(conj ·)` by `deriv_fstar`.
* `if_pos`/`if_neg` (deprecated in this Mathlib) replaced by `ite_eq_left`/`ite_eq_right`.
