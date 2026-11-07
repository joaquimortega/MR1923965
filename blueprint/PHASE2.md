# Phase 2: proving the cited results

Phase 1 formalized every argument of the paper with the cited results as explicit `Prop`
hypotheses (`FourierFrames/Defs.lean`). Phase 2 proves all eight of these `Prop`s in the forms used, so that
the main theorems become unconditional (`FourierFrames/Unconditional.lean`, e.g.
`theorem1_sufficiency_unconditional := theorem1_sufficiency paleyWiener_holds theoremE_holds …`).

**Status (2026-11-07):** P1–P5 are proved. The strongest versions of every formalized
main result, including `landau_inequality_unconditional`, have no remaining cited hypotheses.
P5 proves BMO necessity for complete interpolating sequences, not the full Pavlov iff criterion.
Theorem F uses 2349 lines in 15 files (`Cited/DeBrangesF.lean` and `Cited/DeBrangesF/*`),
following the independently reviewed elementary proof in `P4F_Elementary.md` (R11).
The old `PartF.lean` and `FourierFramesScaffold` are import-only compatibility modules.

| `Prop` | Result | Source | Module | Assessment | Status (2026-11-07) |
|---|---|---|---|---|---|
| `PaleyWienerThm` | Paley–Wiener + Plancherel | classical | P1 | feasible (estimate ~1300 lines): part 1 by Parseval on `[-π,π]`; part 2 by Gaussian regularisation, the `L²` Fourier isometry and Phragmén–Lindelöf (`blueprint/P1_PaleyWiener.md`) | **done**: `paleyWiener_holds`, unconditional, 0 `sorry`, standard axioms; 1018 lines in `Cited/PaleyWiener.lean` + `Cited/PaleyWiener/{Part1,L2Fourier,Spectrum,Part2}.lean`. The `L¹ ∩ L²` agreement goes through Mathlib's tempered-distribution lemmas (`impl_notes/cited-p1.md`) |
| `DSPerturbation` | Duffin–Schaeffer Lemma III | [DS52] | P2 | feasible: `L²` Bernstein + FTC (`blueprint/P2_DS_JN.md`), `PaleyWienerThm → DSPerturbation` | **done**: `dsPerturbation_of_paleyWiener`, 0 `sorry`; unconditional as `dsPerturbation_holds := dsPerturbation_of_paleyWiener paleyWiener_holds` (`Unconditional.lean`) |
| `JohnNirenberg` | John–Nirenberg inequality | [JN61], [Ga81] | P2 | feasible: dyadic stopping time + Lebesgue differentiation (`blueprint/P2_DS_JN.md`) | **done**: `johnNirenberg_holds`, unconditional, 0 `sorry` (`C = 2`, `c = log 2/4`) |
| `TheoremD` | reproducing kernel of `H(E)` | [dB68, Thm 19] | P3 | feasible (est. 2–2.5k lines): half-plane Cauchy–Goursat for `H²` functions continuous up to `ℝ`, no boundary values (`blueprint/P3_DeBrangesDE.md`, referee R9: 0 critical, 0 major, 8 minor) | **done**: `theoremD_holds`, unconditional, 0 `sorry`, standard axioms; 1647 lines in `Cited/DeBrangesDE/{Cauchy,Kernel}.lean` + helper `CauchyAux/Basic.lean` (`impl_notes/cited-p3d.md`) |
| `TheoremE` | orthogonal sampling | [dB68, Thm 22] | P3 | feasible (est. 2.5–3.6k lines): elementary Mittag-Leffler / entire-Pick-function proof, not de Branges' route | **done**: `theoremE_holds`, unconditional, 0 `sorry`, standard axioms; 2039 lines in `Cited/DeBrangesDE/{Space,EntireHerglotz,Orthogonal,Complete}.lean` + helper `EAux/KernelSymm.lean` (`impl_notes/cited-p3e.md`). P3 in all: 3726 lines in 9 files (estimate 4.3–6.2k) |
| `TheoremC` | axiomatic de Branges spaces | [dB68, Thm 23] | P4 | feasible (est. 2.5–4k lines from scratch; about 1.5–2.5k on top of P3 via Theorem D and kernel-space uniqueness, R7 finding 7); `blueprint/P4_DeBrangesFC.md` (referee R10: no false Part C statement) | **done**: `theoremC_holds`, unconditional, 0 `sorry`, standard axioms; 1046 lines in `Cited/DeBrangesFC.lean` + `Cited/DeBrangesFC/{Analytic,Space,Kernel}.lean` (`impl_notes/cited-p4.md`). Route: the kernel of `H` from (H1)–(H3), an explicit strict `E` with `ι(k_w) = K_E(w,·)`, real zeros of `E` through the `IsH2Cont` extension of `f/E`, and RKHS uniqueness without completeness of `H(E)`. In the default target since the stub `theoremD_holds` was replaced by `import FourierFrames.Cited.DeBrangesDE` (R7 finding 8, R9 F4) |
| `TheoremF` | isometric measures | [dB60], [dB68, Thm 32] | P4 | elementary normalized kernels, Cauchy–Schwarz and explicit measure algebra (`P4F_Elementary.md`, R11) | **done**: `theoremF_holds`, unchanged statement with `p = 0`; 2349 lines in 15 files, no `sorry` |
| `PavlovBMO` | CIS ⇒ `n_Γ - t ∈ BMO` | [Pa79], [HNP81] | P5 | specialized cardinal/A₂, logarithmic dispersion and conjugate-Poisson BMO route (`P5_Pavlov.md`, R13–R15) | **done**: `pavlovBMO_holds`, unchanged statement, 6761 lines in 37 project files, no `sorry`, standard axioms; selected unchanged Tau Ceti tools recorded in `TauCeti/VENDORED.md` |

**What is discharged** (`FourierFrames/Unconditional.lean`; all its theorems are in
`comparator/statements.lean`, with a 46-statement comparator target). The proved results supply
`hPW`, `hC`, `hD`, `hE`, `hF`, `hA`, `hJN` and `hDS` (`dsPerturbation_holds := dsPerturbation_of_paleyWiener
paleyWiener_holds`). The frozen main statements keep their parameters; the new versions are

* unconditional: `isFourierFrame_iff_isSampling_unconditional`, `heEqPW_of_comparable_unconditional`,
  `theorem1_sufficiency_unconditional`, `completeInterpolating_zero_set_unconditional`,
  `logExample_isCompleteInterpolating_unconditional`, `landau_sharp_unconditional`,
  `corollary2_unconditional`, `theorem2_i_unconditional`, `theorem2_i_of_densityBound_unconditional`,
  `theorem1_necessity_unconditional`, `theorem1_unconditional`, `corollary1_unconditional`,
  `landau_inequality_unconditional` (`logExample_count` and `theorem2_ii` need no cited result).

The earlier `landau_inequality_of_pavlov` wrapper retains its explicit hypothesis for compatibility.

The previous `*_of_theoremF` and `landau_inequality_of_theoremF_pavlov` versions remain for compatibility.
The intermediate versions from before Theorem C was proved are kept: `completeInterpolating_zero_set_of_theoremC`
(C); `theorem1_necessity_of_theoremCF`, `theorem1_of_theoremCF`, `corollary1_of_theoremCF` (C, F);
`landau_inequality_of_theoremCF_pavlov` (C, F, A).

**Order followed** (referee R7). P3 came first: `theorem1_sufficiency`, `corollary2`, `theorem2_i`,
`theorem2_i_of_densityBound`, `logExample_isCompleteInterpolating` and `landau_sharp` lost `hE` and became
unconditional. Then came P4-C, through P3's Theorem D and uniqueness of the kernel space. Real zeros of `E` are handled
by the two lemmas listed in R9 F5: an order version of `not_isH2Upper_div_of_zero`, and `IsH2Cont` extensions of
`f/E`, `f^*/E` across real zeros of `E`. They are proved in P4 (`Cited/DeBrangesFC/Analytic.lean`), so P3's kernel
layer did not need to change. P4-C made `completeInterpolating_zero_set` unconditional, and it removed `hC` from
`theorem1_necessity`, `theorem1`, `corollary1` and `landau_inequality`, which all need `hF` as well.

P4-F then supplied `hF` by a different route from the abandoned factorization scaffold:
two normalized kernel identities imply a Schur bound by Cauchy–Schwarz; explicit inverse
measure algebra gives the Poisson identity with `p = 0`. This preserves `Defs.TheoremF`.

P5 then supplied `hA`: cardinal synthesis and shifted sampling yield A₂ and boundary
logarithmic BMO; weighted Schwarz dispersion identifies a conjugate-Poisson boundary
limit with the counting discrepancy, and uniform BMO estimates plus Fatou finish the proof.
The project vendors 41 unchanged Tau Ceti modules (8882 lines), pinned at v4.35.0 commit
`1f9b4414105d86e487a4ac4c3d3397076a44d0d2`; provenance and upstream library-scoped
elaboration options are documented in `TauCeti/VENDORED.md`.

**End state.** Every formalized main result has an unconditional version. The BMO necessity
consequence of Pavlov is proved; its full iff characterization is outside the formalized scope.
The former factorization helper `division_lemma` was false as stated (R10); it was retired
and plays no role in the new proof. The earlier assessment in `P4_DeBrangesFC.md` is historical.

Conventions: Lean files under `FourierFrames/Cited/`, one blueprint `blueprint/P*_*.md` per module,
same standards as `blueprint/WRITING.md`. Each module ends with a theorem
`<prop>_holds : <Prop>` (e.g. `paleyWiener_holds : PaleyWienerThm`). The statements of the `Prop`s
in `Defs.lean` are frozen; if one turns out to be unprovable as stated (too strong), report it.
Writers may use any already-proved project lemma (`FourierFrames/**`; all phase-1 modules are
proved), but must not create import cycles: `Cited/*` files may import `Defs`, `PW/*`, `HB/*` only
when the corresponding `Prop` is not a hypothesis of the lemma used (e.g. a proof of
`PaleyWienerThm` must not use lemmas taking `hPW`).
