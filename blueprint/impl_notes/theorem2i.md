# Implementation notes: theorem2i (M08)

- File split: `FourierFrames/Theorem2i.lean` (section 6 glue), `Theorem2i/Basic.lean` (data, sections 1-2),
  `Product.lean` (section 3), `Cells.lean` (section 4), `Estimates.lean` (section 5), plus helper files.
  Statements unchanged (moved between files only).
- tsum statements (`exists_bound_cellTerm`, `card_near_le`, `sum_far_le`, `sum_far_im_le`) are vacuous when the
  series is not summable; uniform finset forms are proved in helper files and the tsum forms derived from them.
- `densBound_of_antitoneOn`, `of_isLogRegularPartitionWithDensity`, `theorem2_i_of_regular`,
  `theorem2_i_of_densityBound`, `theorem2_i` proved in `Theorem2i.lean` from the section 1-5 black boxes.
# D3 notes (assembly)
- `exists_bound_cellTerm`/`exists_approx` moved from Estimates.lean to Assembly.lean (Assembly imports Estimates; main imports Assembly). Stubs deleted from Estimates.
- Uses finset black boxes `RegData.finset_card_near_le / finset_sum_far_le / finset_sum_far_im_le` (m-indexed, hypotheses on all m in F) sorried in Assembly.lean; must be supplied by D2 (or moved).
- Above sum proved by telescoping with constant (1+C) instead of (1+C)^2.

- Merged from sub-worktrees theorem2i-{A,B1,B2,C,D1,D2,D3}. No statement was false. `Assembly.lean` holds
  `exists_bound_cellTerm`/`exists_approx` (stubs removed from Estimates.lean). D2's finset lemmas take a generic
  constant `k`; Assembly has `K0_finset_*` wrappers. `NearAux.lean` imports Mathlib (module-system lint warning).
- `sum_far_im_le` holds without `0 ≤ z.im`. `M ≥ 1` is derivable from `sum_le`.
