# sufficiency fork: Corollary1.lean, Landau.lean

All `sorry`s of `FourierFrames/Corollary1.lean` and `FourierFrames/Landau.lean` are proved (upstream black boxes
remain sorry: `exists_realFactor` in Sufficiency, M01-M03 lemmas).

Deviations / notes
- `exists_HB_of_sampling` -> `exists_E` (M03), as in IMPORTS.md.
- `osc_bound_of_JN`: hypothesis `hD : 0 <= D` is unused (the bound holds for any D with the constants chosen);
  kept via `have _ := hD` to avoid a linter warning on a frozen statement (*later:* removed in the lint pass,
  NOTEBOOK I-03).
- `corollary1_strong`: the enumeration `gamma` from `exists_levelSet_enum` is abstract, so the interlacing
  uses only that distinct points of `Gamma` have `phi_E`-values differing by a positive multiple of pi
  (so `psi(gamma_{k+1}) - psi(gamma_k) >= pi`), not the explicit formula for `gamma_{k+1}`.
- `isSampling_of_isCompleteInterpolating`: closed graph theorem for `T : l^2(Lambda) -> L^2(R)`
  (`LinearMap.continuous_of_seq_closed_graph`), in `Corollary1/ClosedGraph.lean`; uses `pw_complete`,
  `plancherelPolya`.
- `kernel_orthogonal`: Cauchy-Schwarz is replaced by `uv <= (u^2+v^2)/2` (enough, since `||e_a||_E = 1`).
- Helper files: `Corollary1/Rotate.lean`, `Corollary1/Kernel.lean`, `Corollary1/ClosedGraph.lean`.
