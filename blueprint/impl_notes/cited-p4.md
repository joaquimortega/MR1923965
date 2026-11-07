# Implementation notes — `cited-p4` (P4: `Cited/DeBrangesFC.lean`, Part C)

## Status
* **Part C is proved.** `#print axioms FF.theoremC_holds` gives `[propext, Classical.choice,
  Quot.sound]`. All 43 Part C lemmas of the blueprint are proved; no axiom, no linter suppression,
  no raised heartbeats, no `have _ :=`. The only `sorry`s left are Part F (8 lemmas and
  `theoremF_holds`, deferred as planned).
* No Part C statement was found false. P3 lemmas were used as black boxes with their final
  signatures (`memHE_deBrangesKernel_of_isHB`, `heInner_kernel_upper_of_isH2Cont`,
  `deBrangesKernel_mul`, `deBrangesKernel_diag`, `differentiable_deBrangesKernel`,
  `heInner_self` (only `IsHB E`), `measurable_div_real`, `heInner_conj_symm`,
  `heInner_smul_left/right`, `MemHE.add/const_mul`, `memHE_zero`, `memHE_fstar`, `heNormSq_fstar`,
  `IsH2Cont.lintegral_line_le/lintegral_real_lt_top/memLp_real`).

## Layout
The Part C declarations are split over helper files (statements moved verbatim, up to the
`CompleteSpace` change below; the P4 file did not exist at tag `scaffold-reviewed`, so
`check_statements.py` does not track them, and it still reports "OK"):
* `FourierFrames/Cited/DeBrangesFC/Analytic.lean`: §1.1 general helpers and §1.2 real zeros of `E`
  (`divExt` and its lemmas).
* `FourierFrames/Cited/DeBrangesFC/Space.lean`: §1.3, the `_of_isHB` lemmas.
* `FourierFrames/Cited/DeBrangesFC/Kernel.lean`: `DBAxioms`, `IsKernelFamily`, `kernelE`,
  `DBAxioms.eq_zero_of_upper` and C.1–C.8.
* `FourierFrames/Cited/DeBrangesFC.lean`: `UHP`, `thetaFn`, `kernelSpan`, C.9–C.14,
  `theoremC_holds` (assembly unchanged), Part F. (After the merge, Part F moved to
  `FourierFrames/Cited/DeBrangesFC/PartF.lean`, built only by `FourierFramesScaffold`; `DeBrangesFC.lean` is in the
  default target.)

## Changed statements (unused hypotheses removed)
* `[CompleteSpace H]` is no longer a section variable of Part C (it was unused, and was being
  auto-included). It is now an explicit instance argument only where it is used (Riesz or the
  orthogonal complement): `exists_kernel`, `kernelSpan_topologicalClosure`,
  `exists_seq_kernelSpan`, `memHE_iota`, `heNormSq_iota`, `mem_range_of_memHE`. It is dropped from
  `DBAxioms`, `IsKernelFamily`, `kernelE`, `kernelSpan`, `DBAxioms.eq_zero_of_upper`,
  `kernel_diag`, `kernel_norm_pos`, `kernel_symm`, `exists_conjMap`, `kernel_fstar`,
  `exists_mulMap`, `kernel_identity`, `differentiable_kernelE`, `fstar_kernelE`, `kernel_mul_eq`,
  `kernel_eq_deBrangesKernel`, `isStrictHB_kernelE`, `memHE_kernel`, `memHE_of_mem_kernelSpan`,
  `heInner_iota_of_mem_kernelSpan`, `heNormSq_iota_of_mem_kernelSpan`. `TheoremC` and the assembly
  are untouched (callers supply the instance anyway).

## New helper lemmas
* `Analytic.lean`: `eq_of_eventuallyEq_entire`, `eq_of_eqOn_open`, `eq_of_eq_off_finite` (identity
  theorem in the forms used), `sub_conj_ne_zero`, `meromorphicOn_div_entire`,
  `meromorphicOrderAt_divExt`, `analyticOrderAt_divExt`, `divExt_ae_eq`.
* `Space.lean`: `divExt_line`, `heInner_integrand_eq` (pointwise `f conj g/|E|² = (f/E) conj (g/E)`,
  also at zeros of `E`), `norm_heInner_sq_le_of_isHB` (squared Cauchy–Schwarz).
* `Kernel.lean`: `DBAxioms.eq_of_eq_off_finite`, `kernel_diag_ne_zero`, `kernelE_eq` and
  `fstar_kernelE_eq` (normalised forms with `√K(i,i) = ‖k i‖`), `kernel_diag_neg_I`
  (`K(-i,-i) = K(i,i)`).

## Deviations from the blueprint
* `analyticOrderAt_le_of_isH2Upper_div`: the global division by `(z - x)^k₀` is done with
  `divExt (fun z ↦ (z - x)^k₀) f` and `divExt (fun z ↦ (z - x)^k₀) E` (meromorphic normal form,
  orders computed by `analyticOrderAt_divExt`) instead of `Function.update` quotients.
  `toMeromorphicNFOn` worked without trouble; the `limUnder` fallback was not needed.
* "Equal off a point / off `{ζ, ζ̄}` / off `{w̄}`" is done with the identity theorem on the open
  complement of a finite set (`eq_of_eq_off_finite`), not `Continuous.ext_on`.
* `exists_mulMap`: linearity of `T` on `H_ζ = ker (proj ζ ∘ ι)` by injectivity; the isometry is
  bundled as `H_ζ →ₗᵢ[ℂ] H` and clause 2 is `LinearIsometry.inner_map_map` (no polarization).
  `exists_conjMap` (conjugate-linear) uses polarization `inner_eq_sum_norm_sq_div_four`.
* `norm_heInner_le_of_isHB`: P3's `ℝ≥0∞`-Hölder proof of `norm_heInner_sq_le` with
  `MemHE.heNormSq_lt_top_of_isHB` in place of `h0`, then square roots.
* `integrable_heInner_of_isHB`: `MemLp.integrable_mul` (Hölder `2,2`) on `f/E` and `conj (g/E)`.

## Part F
* `division_lemma` is FALSE as stated (referee R10, `reviews/R10_TheoremC.md`): counterexample
  `E = exp(-iz/2)`, `Θ = e^{iz}`, `a = θ = 0`, `B = Θ`, `Ξ ≡ 1/2` (the factorization hypothesis
  does not force `0 ≤ a`, `‖B‖ ≤ 1` or Blaschke division). Marked `-- FALSE` in the file, `sorry`
  kept. Part F is deferred (all its lemmas and `theoremF_holds` stay `sorry`).
