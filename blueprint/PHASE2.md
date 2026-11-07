# Phase 2: proving the cited results

Phase 1 formalized every argument of the paper with the cited results as explicit `Prop`
hypotheses (`FourierFrames/Defs.lean`). Phase 2 proves as many of these `Prop`s as feasible, so that
the main theorems become unconditional (`FourierFrames/Unconditional.lean`, e.g.
`theorem1_sufficiency_unconditional := theorem1_sufficiency paleyWiener_holds theoremE_holds …`).

**Status (2026-11-07):** P1, P2 and P3 are proved; P4-C is in progress along the route recommended by
referee R7 (through Theorem D); P4-F is deferred; P5 is infeasible with current Mathlib.

| `Prop` | Result | Source | Module | Assessment | Status (2026-11-07) |
|---|---|---|---|---|---|
| `PaleyWienerThm` | Paley–Wiener + Plancherel | classical | P1 | feasible (estimate ~1300 lines): part 1 by Parseval on `[-π,π]`; part 2 by Gaussian regularisation, the `L²` Fourier isometry and Phragmén–Lindelöf (`blueprint/P1_PaleyWiener.md`) | **done**: `paleyWiener_holds`, unconditional, 0 `sorry`, standard axioms; 1018 lines in `Cited/PaleyWiener.lean` + `Cited/PaleyWiener/{Part1,L2Fourier,Spectrum,Part2}.lean`. The `L¹ ∩ L²` agreement goes through Mathlib's tempered-distribution lemmas (`impl_notes/cited-p1.md`) |
| `DSPerturbation` | Duffin–Schaeffer Lemma III | [DS52] | P2 | feasible: `L²` Bernstein + FTC (`blueprint/P2_DS_JN.md`), `PaleyWienerThm → DSPerturbation` | **done**: `dsPerturbation_of_paleyWiener`, 0 `sorry`; unconditional as `dsPerturbation_holds := dsPerturbation_of_paleyWiener paleyWiener_holds` (`Unconditional.lean`) |
| `JohnNirenberg` | John–Nirenberg inequality | [JN61], [Ga81] | P2 | feasible: dyadic stopping time + Lebesgue differentiation (`blueprint/P2_DS_JN.md`) | **done**: `johnNirenberg_holds`, unconditional, 0 `sorry` (`C = 2`, `c = log 2/4`) |
| `TheoremD` | reproducing kernel of `H(E)` | [dB68, Thm 19] | P3 | feasible (est. 2–2.5k lines): half-plane Cauchy–Goursat for `H²` functions continuous up to `ℝ`, no boundary values (`blueprint/P3_DeBrangesDE.md`, referee R9: 0 critical, 0 major, 8 minor) | **done**: `theoremD_holds`, unconditional, 0 `sorry`, standard axioms; 1647 lines in `Cited/DeBrangesDE/{Cauchy,Kernel}.lean` + helper `CauchyAux/Basic.lean` (`impl_notes/cited-p3d.md`) |
| `TheoremE` | orthogonal sampling | [dB68, Thm 22] | P3 | feasible (est. 2.5–3.6k lines): elementary Mittag-Leffler / entire-Pick-function proof, not de Branges' route | **done**: `theoremE_holds`, unconditional, 0 `sorry`, standard axioms; 2039 lines in `Cited/DeBrangesDE/{Space,EntireHerglotz,Orthogonal,Complete}.lean` + helper `EAux/KernelSymm.lean` (`impl_notes/cited-p3e.md`). P3 in all: 3726 lines in 9 files (estimate 4.3–6.2k) |
| `TheoremF` | isometric measures | [dB60], [dB68, Thm 32] | P4 | feasible only as a long project (est. 5–8k lines, high risk: inner-function factorization, Blaschke division, Herglotz transform); `blueprint/P4_DeBrangesFC.md` (with the referee corrections of R7) | **deferred**; scaffold `Cited/DeBrangesFC.lean` (`sorry`). Recommendation: keep `hF` |
| `TheoremC` | axiomatic de Branges spaces | [dB68, Thm 23] | P4 | feasible (est. 2.5–4k lines from scratch; about 1.5–2.5k on top of P3 via Theorem D and kernel-space uniqueness, R7 finding 7); `blueprint/P4_DeBrangesFC.md` | **in progress** along the R7 route; scaffold `Cited/DeBrangesFC.lean` (`sorry`) in the separate Lake target `FourierFramesScaffold`. It still declares a temporary stub `theoremD_holds` (`sorry`), to be replaced by `import FourierFrames.Cited.DeBrangesDE` (R7 finding 8, R9 F4); no clash meanwhile, since the default target does not import it |
| `PavlovBMO` | CIS ⇒ `n_Γ - t ∈ BMO` | [Pa79], [HNP81] | P5 | **not feasible**: needs the Hilbert transform, Muckenhoupt weights and BMO conjugation, none in Mathlib (est. 6–10k lines; `blueprint/P5_Pavlov.md`) | kept as the cited hypothesis `hA` of `landau_inequality` |

**What is discharged** (`FourierFrames/Unconditional.lean`; all its theorems are in
`comparator/statements.lean`, and comparator accepts the 33 theorems). The proved results supply
`hPW`, `hD`, `hE`, `hJN` and `hDS` (`dsPerturbation_holds := dsPerturbation_of_paleyWiener
paleyWiener_holds`). The frozen main statements keep their parameters; the new versions are
* unconditional: `isFourierFrame_iff_isSampling_unconditional`, `heEqPW_of_comparable_unconditional`,
  `theorem1_sufficiency_unconditional`, `logExample_isCompleteInterpolating_unconditional`,
  `landau_sharp_unconditional`, `corollary2_unconditional`, `theorem2_i_unconditional`,
  `theorem2_i_of_densityBound_unconditional` (`logExample_count` and `theorem2_ii` need no cited
  result);
* conditional on `TheoremC`: `completeInterpolating_zero_set_of_theoremC`;
* conditional on `TheoremC` and `TheoremF`: `theorem1_necessity_of_theoremCF`, `theorem1_of_theoremCF`,
  `corollary1_of_theoremCF`;
* conditional on `TheoremC`, `TheoremF` and `PavlovBMO`: `landau_inequality_of_theoremCF_pavlov`.

**Recommended order** (referee R7), now carried out up to P3: P3 first (done; `theorem1_sufficiency`,
`corollary2`, `theorem2_i`, `theorem2_i_of_densityBound`, `logExample_isCompleteInterpolating`,
`landau_sharp` lost `hE` and are unconditional); then P4-C through P3's Theorem D and uniqueness of the
kernel space, after generalising P3's kernel layer to strict `E` with real zeros (R7 finding 7; R9 F5
lists the two missing lemmas: an order version of `not_isH2Upper_div_of_zero` and `IsH2Cont`
extensions of `f/E`, `f^*/E` across real zeros of `E`). P4-C is in progress. It makes only
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
