# Implementation notes — `cited-p3d` (P3: `Cauchy.lean`, `Kernel.lean`)

## Changed statements (unused hypotheses removed)
* `conj_deBrangesKernel`: the hypothesis `hE : Differentiable ℂ E` was unused (the diagonal case
  only needs `deriv_fstar`, which has no differentiability hypothesis).  New signature
  `conj_deBrangesKernel (E : ℂ → ℂ) (w z : ℂ)`.
* `fstar_deBrangesKernel`: same, `hE` unused.  New signature `fstar_deBrangesKernel (E : ℂ → ℂ) (w : ℂ)`.

## Deviations from the blueprint
