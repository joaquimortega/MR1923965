# Implementation notes: theorem2i (M08)

- File split: `FourierFrames/Theorem2i.lean` (section 6 glue), `Theorem2i/Basic.lean` (data, sections 1-2),
  `Product.lean` (section 3), `Cells.lean` (section 4), `Estimates.lean` (section 5), plus helper files.
  Statements unchanged (moved between files only).
- tsum statements (`exists_bound_cellTerm`, `card_near_le`, `sum_far_le`, `sum_far_im_le`) are vacuous when the
  series is not summable; uniform finset forms are proved in helper files and the tsum forms derived from them.
- `densBound_of_antitoneOn`, `of_isLogRegularPartitionWithDensity`, `theorem2_i_of_regular`,
  `theorem2_i_of_densityBound`, `theorem2_i` proved in `Theorem2i.lean` from the section 1-5 black boxes.
