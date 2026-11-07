# Phase 2: proving the cited results

Phase 1 formalized every argument of the paper with the cited results as explicit `Prop`
hypotheses (`FourierFrames/Defs.lean`). Phase 2 proves as many of these `Prop`s as feasible, so that
the main theorems become unconditional (`theorem1_unconditional := theorem1 paleyWiener_holds …`).

| `Prop` | Result | Source | Module | Assessment | Status (2026-11-07) |
|---|---|---|---|---|---|
| `PaleyWienerThm` | Paley–Wiener + Plancherel | classical | P1 | feasible (estimate ~1300 lines): part 1 by Parseval on `[-π,π]`; part 2 by Gaussian regularisation, the `L²` Fourier isometry and Phragmén–Lindelöf (`blueprint/P1_PaleyWiener.md`) | **done**: `paleyWiener_holds`, unconditional, 0 `sorry`, standard axioms; 1018 lines in `Cited/PaleyWiener.lean` + `Cited/PaleyWiener/{Part1,L2Fourier,Spectrum,Part2}.lean`. The `L¹ ∩ L²` agreement goes through Mathlib's tempered-distribution lemmas (`impl_notes/cited-p1.md`) |
| `DSPerturbation` | Duffin–Schaeffer Lemma III | [DS52] | P2 | feasible: `L²` Bernstein + FTC (`blueprint/P2_DS_JN.md`), `PaleyWienerThm → DSPerturbation` | **done**: `dsPerturbation_of_paleyWiener`, 0 `sorry`; unconditional as `dsPerturbation_of_paleyWiener paleyWiener_holds` |
| `JohnNirenberg` | John–Nirenberg inequality | [JN61], [Ga81] | P2 | feasible: dyadic stopping time + Lebesgue differentiation (`blueprint/P2_DS_JN.md`) | **done**: `johnNirenberg_holds`, unconditional, 0 `sorry` (`C = 2`, `c = log 2/4`) |
| `TheoremD` | reproducing kernel of `H(E)` | [dB68, Thm 19] | P3 | being implemented (blueprint `blueprint/P3_DeBrangesDE.md`, forthcoming) | in progress: scaffold `Cited/DeBrangesDE.lean` + `Cited/DeBrangesDE/*` on master (`sorry`), implementation in a separate worktree; not imported by `FourierFrames.lean` |
| `TheoremE` | orthogonal sampling | [dB68, Thm 22] | P3 | as `TheoremD` | in progress, as `TheoremD` |
| `TheoremF` | isometric measures | [dB60], [dB68, Thm 32] | P4 | feasible only as a long project (est. 5–8k lines, high risk: inner-function factorization, Blaschke division, Herglotz transform); `blueprint/P4_DeBrangesFC.md` (with the referee corrections of R7) | assessed; scaffold `Cited/DeBrangesFC.lean` (`sorry`). Recommendation: keep `hF` |
| `TheoremC` | axiomatic de Branges spaces | [dB68, Thm 23] | P4 | feasible (est. 2.5–4k lines from scratch; about 1.5–2.5k on top of P3 via Theorem D and kernel-space uniqueness, R7 finding 7); `blueprint/P4_DeBrangesFC.md` | assessed; scaffold `Cited/DeBrangesFC.lean` (`sorry`), which still declares a temporary stub `theoremD_holds` that clashes with P3's (remove at P3 assembly) |
| `PavlovBMO` | CIS ⇒ `n_Γ - t ∈ BMO` | [Pa79], [HNP81] | P5 | **not feasible**: needs the Hilbert transform, Muckenhoupt weights and BMO conjugation, none in Mathlib (est. 6–10k lines; `blueprint/P5_Pavlov.md`) | kept as the cited hypothesis `hA` of `landau_inequality` |

**What is discharged.** With `paleyWiener_holds` the hypothesis `hPW` of every main statement can be
supplied, so `isFourierFrame_iff_isSampling` and `heEqPW_of_comparable` are unconditional, and
`hJN` (`landau_inequality`) and `hDS` (`corollary2`, `theorem2_i`, `theorem2_i_of_densityBound`) can
be supplied by `johnNirenberg_holds` and `dsPerturbation_of_paleyWiener paleyWiener_holds`. The
statements themselves keep their parameters (they are frozen and checked by comparator).
`logExample_count` and `theorem2_ii` need no cited result.

**Recommended order** (referee R7): P3 first (largest payoff: `theorem1_sufficiency`, `corollary2`,
`theorem2_i`, `theorem2_i_of_densityBound`, `logExample_isCompleteInterpolating`, `landau_sharp` lose
`hE` and become unconditional); then P4-C through P3's Theorem D and uniqueness of the kernel space,
after generalising P3's kernel layer to strict `E` with real zeros (R7 finding 7). This makes only
`completeInterpolating_zero_set` unconditional: `hC` also occurs in `theorem1_necessity`, `theorem1`,
`corollary1` and `landau_inequality`, which all need `hF` as well. Keep `TheoremF` and `PavlovBMO` as
hypotheses. End state: Theorem 1 (necessity half and `theorem1`), Corollary 1 and the Claim (Landau)
remain conditional on these two named, faithful hypotheses.

Conventions: Lean files under `FourierFrames/Cited/`, one blueprint `blueprint/P*_*.md` per module,
same standards as `blueprint/WRITING.md`. Each module ends with a theorem
`<prop>_holds : <Prop>` (e.g. `paleyWiener_holds : PaleyWienerThm`). The statements of the `Prop`s
in `Defs.lean` are frozen; if one turns out to be unprovable as stated (too strong), report it.
Writers may use any already-proved project lemma (`FourierFrames/**`; all phase-1 modules are
proved), but must not create import cycles: `Cited/*` files may import `Defs`, `PW/*`, `HB/*` only
when the corresponding `Prop` is not a hypothesis of the lemma used (e.g. a proof of
`PaleyWienerThm` must not use lemmas taking `hPW`).
