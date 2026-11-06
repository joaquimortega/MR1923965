# cited-p1 notes

* `L2Fourier.lean`: `F2_symm_ae_eq` (inverse = transform followed by reflection) was removed: it was only used to
  derive `F2_symm_toLp_ae_eq`, which is now proved directly (same pairing argument via tempered distributions:
  `Lp.fourier_toTemperedDistribution_eq`, `Lp.fourierInv_toTemperedDistribution_eq`).  Added helpers
  `integral_fourier_smul`, `integral_fourierInv_smul`, `integral_smul_F2`, `integral_smul_F2_symm`,
  `ae_eq_of_schwartz_pairing`.
* `Part1.lean`: `MemLp` is just `eLpNorm < ⊤` in this Mathlib (no `.1/.2` projections).  Added helper lemmas
  `norm_cexp_le`, `norm_cexp_real`, `aesm_mul_cexp`, `abs_le_pi_of_mem_*`.
