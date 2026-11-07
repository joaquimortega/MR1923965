# Implementation notes — `cited-p4` (P4: `Cited/DeBrangesFC.lean`, Part C)

## Layout
The Part C declarations are split over helper files (statements moved verbatim; the file did not
exist at tag `scaffold-reviewed`, so `check_statements.py` does not track them):
* `FourierFrames/Cited/DeBrangesFC/Analytic.lean`: §1.1 general helpers and §1.2 real zeros of `E`
  (`divExt` and its lemmas).

## New helper lemmas
* `Analytic.lean`: `eq_of_eventuallyEq_entire`, `eq_of_eqOn_open`, `eq_of_eq_off_finite` (identity
  theorem in the forms used), `sub_conj_ne_zero`, `meromorphicOn_div_entire`,
  `meromorphicOrderAt_divExt`, `analyticOrderAt_divExt`, `divExt_ae_eq`.

## Deviations from the blueprint
* `analyticOrderAt_le_of_isH2Upper_div`: the global division by `(z - x)^k₀` is done with
  `divExt (fun z ↦ (z - x)^k₀) f` and `divExt (fun z ↦ (z - x)^k₀) E` (meromorphic normal form,
  whose orders are computed by `analyticOrderAt_divExt`) instead of `Function.update` quotients.

## Part F
* `division_lemma` is FALSE as stated (referee R10, `reviews/R10_TheoremC.md`): counterexample
  `E = exp(-iz/2)`, `Θ = e^{iz}`, `a = θ = 0`, `B = Θ`, `Ξ ≡ 1/2`. Marked `-- FALSE` in the file,
  `sorry` kept. Part F is deferred (all its lemmas and `theoremF_holds` stay `sorry`).
