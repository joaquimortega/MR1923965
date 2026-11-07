# Implementation notes — `cited-p3d` (P3: `Cauchy.lean`, `Kernel.lean`)

## Changed statements (unused hypotheses removed)
* `conj_deBrangesKernel`: the hypothesis `hE : Differentiable ℂ E` was unused (the diagonal case
  only needs `deriv_fstar`, which has no differentiability hypothesis).  New signature
  `conj_deBrangesKernel (E : ℂ → ℂ) (w z : ℂ)`.
* `fstar_deBrangesKernel`: same, `hE` unused.  New signature `fstar_deBrangesKernel (E : ℂ → ℂ) (w : ℂ)`.

* `IsH2Cont.exists_side_seq`: hypothesis `hY : 0 < Y` unused (for `Y ≤ 0` the strip is empty;
  Tonelli gives `C · ofReal Y` for every `Y`).  Removed: `IsH2Cont.exists_side_seq hF (Y := Y)`.
* `IsH2Cont.tendsto_integral_line_of_dominated`: hypothesis `hc` (continuity of `G`) unused: the
  bound `‖∫ G‖ ≤ ∫ bound` (`norm_integral_le_of_norm_le`) needs no integrability of `G`.  Removed.

## Deviations from the blueprint
* New helper file `FourierFrames/Cited/DeBrangesDE/CauchyAux/Basic.lean` (Tonelli on a strip,
  good abscissae `exists_ge_add_neg_le_one`, rectangle identity `rect_identity`, AM–GM form
  `le_of_dom` of the domination hypothesis, side bound `enorm_le_of_dom_side`).
* Domination estimates: one pointwise AM–GM inequality `‖G‖ ≤ (ε/2)‖F‖² + (1/(2ε)+|A|) d⁻²`
  (`le_of_dom`) with `ε = 1` (line integrability), `ε → 0` (top side), `ε = ρ⁻¹` (vertical sides).
* Vertical sides in `integral_eq_integral_line_of_sides`: bounded directly in `ℝ≥0∞` by
  `enorm_integral_le_lintegral_enorm` and `le_lintegral_add` (no continuity of the sides needed).
