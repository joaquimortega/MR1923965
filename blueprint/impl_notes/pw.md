# Implementation notes: pw (M01, M10)

All `sorry`s of `PW/Basic.lean`, `PW/Bounds.lean`, `PW/PlancherelPolya.lean`, `PW/Complete.lean`,
`Frames.lean` are closed. No statement changed.

Deviations from the blueprint:
- R2-01: `memPW_pwFT` is `hPW.1 g hg`; `exists_pwFT` takes `g` from part 2 and gets the norm identity
  from part 1. `pwFT_sub`, `tsum_enorm_sq_pwFT_int`, `l2piSq_eq_of_pwFT_eq` are still proved
  (Mathlib Parseval `hasSum_sq_fourierCoeffOn`) though no longer needed by the PW chain.
- R2-04: `pw_complete` applies `memPW_of_tendsto` to `m ↦ f (m + N) - f n`.
- `pw_normal_family` follows blueprint §4 (liminf subsequence `ψ`, ultrafilter Montel, subsequence
  `φ` via `MapClusterPt.tendsto_subseq`), result subsequence is `ψ ∘ φ`.
- `plancherelPolya_tail_union` from `plancherelPolya_tail` with `ε/2` and `sampleSum_union_le`.
- New helper lemmas (public, in own files): `lintegral_enorm_sq_lt_top_of_memLp`, `memLp_two_of_lintegral`,
  `memL2pi_of_continuous`, `circle_sq_le`, `sampleSum_le_lintegral` (packing argument for both
  Plancherel-Polya and its tail), `norm_le_of_pwNormSq_le`, `isExpTypeLE_lin`, `MemPW.lin`,
  `integral_exp_abs`, `pwBump` bound lemmas.
- `Bounds.lean` docstring of `pw_norm_sq_le` still says "constant exactly 1" (R2-03: exponent is the
  sharp part); left unchanged (cosmetic).
- `Frames.lean`: `fourierCoeff` name clash (R2-10) not renamed (statement frozen).
