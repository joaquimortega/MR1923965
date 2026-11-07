# R12 — Code review of the elementary proof of Theorem F

**Date:** 2026-11-07. **Reviewer:** `sol_kernel` (author of `Kernel.lean`; independently reviewed the subsequent assembly).

**Scope:** `DeBrangesF.lean`, `Contractive.lean`, `Analytic.lean`, `Schur.lean`, `KernelIdentities.lean`, `Poisson.lean`, and their normalization, isometry, transform, and Cauchy dependencies. Compared the assembled conclusion against `FF.TheoremF` in `Defs.lean` and the approved R11 route. Root handles compilation and the final axiom audit separately.

**Findings:** No mathematical defect or statement weakening found in the inspected code.

- The final theorem proves the existing `TheoremF` directly from its stated isometry, strict Hermite–Biehler, and real nonvanishing hypotheses. It supplies `p = 0`, including the required finiteness assertion for the Poisson integral. The import chain uses the completed C/D/E kernel results; it does not import the deferred `DeBrangesFC/PartF.lean` or assume Theorem F.
- Cancellation at zeros is sound. `Contractive.lean` uses the entire numerator `E* - a E`, proves it nonzero at the real point zero using real nonvanishing and `|a| < 1`, and cancels the normalized inner function only where that numerator is nonzero. `Analytic.lean` obtains a punctured neighborhood free of zeros from the identity theorem and passes the continuous norm inequality to the center. This covers all zeros, including the normalization point `i`.
- Both transform identities come from original-space reproducing kernels and the polarized isometry. The reflected identity handles `z = i` before dividing by its Cayley coordinate. The exact normalized kernel norm is supplied separately to Cauchy–Schwarz.
- No essential equality relies on assigning zero to a divergent Bochner integral. Isometry first gives `MemLp` and integrable pairings; normalized pairings have an explicit integrability transfer. Cauchy transforms and model kernels have finite-measure bounds, and the Schur argument uses `MemLp` inputs. Splitting the inverse circle weight and the Poisson integral uses explicit integrability hypotheses. Unconditional scalar and density transport identities are used in conjunction with these integrability results.
- The inverse change of measure is a pointwise density equality. Its cancellations are justified by positive defect and base norm, nonzero `E(i)` and real `E(t)`, nonzero disk-automorphism denominator, and `1+t² > 0`. It requires no absolute continuity of the original measure with respect to Lebesgue measure and therefore retains atomic and singular measures.
- The recovered holomorphic parameter has a separately proved nonzero denominator. Its norm bound and strict interior bound for `E*/E` justify the final Cayley quotient; no hidden factorization or division-closure lemma is used.

This is a mathematical source audit; successful compilation and the final `#print axioms` result remain the separate machine checks performed by the assembling agent.
