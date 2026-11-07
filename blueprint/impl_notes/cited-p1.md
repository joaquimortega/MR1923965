# cited-p1 notes

* `L2Fourier.lean`: `F2_symm_ae_eq` (inverse = transform followed by reflection) was removed: it was only used to
  derive `F2_symm_toLp_ae_eq`, which is now proved directly (same pairing argument via tempered distributions:
  `Lp.fourier_toTemperedDistribution_eq`, `Lp.fourierInv_toTemperedDistribution_eq`).  Added helpers
  `integral_fourier_smul`, `integral_fourierInv_smul`, `integral_smul_F2`, `integral_smul_F2_symm`,
  `ae_eq_of_schwartz_pairing`.
* `Part1.lean`: `MemLp` is just `eLpNorm < ⊤` in this Mathlib (no `.1/.2` projections).  Added helper lemmas
  `norm_cexp_le`, `norm_cexp_real`, `aesm_mul_cexp`, `abs_le_pi_of_mem_*`.
* `Spectrum.lean`: dropped the unused hypothesis `ha : 0 ≤ a` from `integral_exp_abs_sub_sq_le` (true for all real a).
* `norm_integral_gauss_mul_le`: dropped unused hypothesis `ha`. Added helpers `gaussH`, `norm_gaussH_le`, `tendsto_exp_gauss_zero`, `exp_lin_sub_sq_eq`, `integral_exp_lin_sub_sq`.
* `Spectrum.lean`: added helpers `gauss_le_one` and `fourier_mul_gauss_eq` (the `𝓕` of `f e^{-η·²}` in the
  shape of `norm_integral_gauss_mul_le`, with `ξ = 2πw`).  `tendsto_eLpNorm_mul_gauss` is proved by dominated
  convergence on `∫⁻ ‖·‖ₑ^2` (bound `‖f‖ₑ^2`) followed by continuity of `t ↦ t^{1/2}`; `spectrum_vanish` uses
  the whole sequence `𝓕 f_n w → 0` (not only a subsequence) and `tendstoInMeasure_of_tendsto_Lp` +
  `exists_seq_tendsto_ae` for the a.e. limit, as in the blueprint.
* `Part2.lean`: added helpers `stronglyMeasurable_specOf` (`Lp.stronglyMeasurable`) and `norm_le_exp_re_im`
  (turns `IsExpTypeLE` constants into the `|C| e^{τ|re| + τ|im|}` bound; no sign on `C` is needed).
  Deviations from the blueprint: inversion is unfolded with `fourierInv_eq_fourier_neg` +
  `fourier_real_eq_integral_exp_smul` (not `fourierInv_eq'`); `L2pi g` for `g(t) = Φ(t/2π)/2π` is proved with
  `memLp_two_iff_integrable_sq_norm` + `Integrable.comp_div` instead of `map_volume_mul_right`; the identity
  theorem is `AnalyticOnNhd.eq_of_frequently_eq` at `z₀ = 0` along `1/(n+1)`.
* Status: no `sorry` in `FourierFrames/Cited/PaleyWiener*`; `#print axioms FF.paleyWiener_holds` gives only
  `[propext, Classical.choice, Quot.sound]`; `scripts/check_statements.py scaffold-reviewed` passes.
