# Formalization of J. Ortega-Cerdà and K. Seip, *Fourier frames* 

A Lean 4 / Mathlib formalization of

> J. Ortega-Cerdà and K. Seip, *Fourier frames*, Ann. of Math. (2) **155** (2002), 789–806.
> [doi:10.2307/3062132](https://doi.org/10.2307/3062132), MR1923965.

Page references ("p. 795") are to the journal pagination. 

## What the paper proves

**Fourier frames and sampling.** A sequence `Λ` of real numbers generates a Fourier frame
`{e^{iλx}}` of `L²(-π, π)` if and only if it is a *sampling sequence* for the Paley–Wiener space
`PW` (entire functions of exponential type at most `π`, square integrable on `ℝ`):
`A ‖f‖² ≤ ∑_{λ ∈ Λ} |f(λ)|² ≤ B ‖f‖²`. Duffin and Schaeffer asked in 1952 which `Λ` have this
property. The paper answers it through de Branges' theory of Hilbert spaces of entire functions.

**Theorem 1.** A separated `Λ` is sampling for `PW` if and only if there are two entire functions
`E, F` of the Hermite–Biehler class (`|E(z̄)| ≤ |E(z)|` on the upper half-plane) such that the de
Branges space `H(E)` equals `PW` with equivalent norms and `Λ` is the zero set of `EF + E^*F^*`.
The function `F` measures the redundancy of `Λ`.

**Consequences.** A sampling sequence is everywhere denser than some complete interpolating
sequence (Corollary 1). Combined with Pavlov's description of complete interpolating sequences
(`n_Γ(t) − t ∈ BMO`) and the John–Nirenberg theorem, this gives Landau's inequality
`n_Λ(b) − n_Λ(a) ≥ b − a − A log⁺(b − a) − B`, which the example `{k + log⁺|k|}` shows to be
sharp.

**Approximation of subharmonic functions.** For a nondecreasing `ψ`, let `Λ(ψ)` be the sequence
`λ + ψ(λ) ∈ ℤ`. Corollary 2 gives a sufficient condition for `Λ(ψ)` to be sampling in terms of the
approximation of the logarithmic potential `U_ψ` by `log|f|`, and Theorem 2 determines the critical
growth: with `ψ = 0` on `(−∞, 0]`, `Λ(ψ)` is sampling if `ψ' ≥ c/x` (and `ψ` is regular) and is not
sampling if `ψ'(x) = o(1/x)`.

## Main results

The fifteen main statements are in `comparator/statements.lean`, with the definitions in
`FourierFrames/Defs.lean`. All are proved without `sorry`, with the cited results as explicit
hypotheses (below), and depend only on `propext`, `Classical.choice` and `Quot.sound`. The same file
lists the eight cited results proved in phase 2 and the twenty-three versions of the main statements in
which they are discharged, including historical conditional versions. The current
[comparator](https://github.com/leanprover/comparator) accepts all 46 theorems against the
self-contained `FFChallenge.lean` (2026-11-07, `comparator/last_run.log`).

| Paper | Lean (namespace `FF`) | Cited hypotheses |
|---|---|---|
| p. 790: Fourier frame ⟺ sampling | `isFourierFrame_iff_isSampling` | PW |
| p. 799: `|E| ≃ e^{π Im z}` on `Im z ≥ 0` ⇒ `H(E) = PW` | `heEqPW_of_comparable` | PW |
| Theorem 1 | `theorem1`, `theorem1_necessity`, `theorem1_sufficiency` | PW, C, E, F |
| Remark p. 797: a complete interpolating sequence is the zero set of `E + E^*` | `completeInterpolating_zero_set` | PW, C, D |
| Corollary 1 | `corollary1` | PW, C, E, F |
| Claim (§4): Landau's inequality | `landau_inequality` | PW, C, E, F, A, JN |
| Example p. 798: `{k + log⁺|k|}` | `logExample_count`, `logExample_isCompleteInterpolating`, `landau_sharp` | PW, E |
| Corollary 2 | `corollary2` | PW, E, DS |
| Theorem 2 (i) | `theorem2_i`, `theorem2_i_of_densityBound` | PW, E, DS |
| Theorem 2 (ii) | `theorem2_ii` | — |

**Cited results as hypotheses.** The paper rests on deep theorems it quotes: the Paley–Wiener
theorem (PW), de Branges' Theorems C, D, E, F, Pavlov's Theorem A, the John–Nirenberg theorem (JN)
and Lemma III of Duffin–Schaeffer (DS). Each is a `Prop` in `Defs.lean`, stated in the weakest form
the paper uses, and appears as an explicit hypothesis of exactly the main theorems that use it;
there are no axioms. Phase 2 of the project proves all eight cited results in the forms used
(`FourierFrames/Cited/`, plan and assessments in `blueprint/PHASE2.md`):

| Cited result | Lean | Status |
|---|---|---|
| Paley–Wiener theorem | `paleyWiener_holds` | proved |
| John–Nirenberg | `johnNirenberg_holds` | proved |
| Duffin–Schaeffer Lemma III | `dsPerturbation_holds` (`= dsPerturbation_of_paleyWiener paleyWiener_holds`) | proved |
| de Branges' Theorem D (reproducing kernel) | `theoremD_holds` | proved |
| de Branges' Theorem E (orthogonal sampling) | `theoremE_holds` | proved |
| de Branges' Theorem C (axiomatic de Branges spaces) | `theoremC_holds` | proved |
| de Branges' Theorem F (isometric measures) | `theoremF_holds` | proved by normalized kernels and Cauchy–Schwarz (`blueprint/P4F_Elementary.md`, review R11) |
| Pavlov's Theorem A (BMO necessity) | `pavlovBMO_holds` | proved; finite weighted tests, logarithmic dispersion and uniform conjugate-Poisson BMO |

The proved ones depend only on `propext`, `Classical.choice` and `Quot.sound`; the proof of
Theorem E is an elementary one, not de Branges' (`blueprint/P3_DeBrangesDE.md`). Theorem C is proved
through Theorem D and the uniqueness of a reproducing-kernel space, without completeness of `H(E)`
(`blueprint/P4_DeBrangesFC.md`). Theorem F uses two normalized reproducing-kernel identities,
Cauchy–Schwarz and explicit measure algebra, with `p = 0` in the unchanged statement
(`blueprint/P4F_Elementary.md`, independently reviewed in `reviews/R11_TheoremF.md`). Its proof
occupies 2349 lines in 15 files: `Cited/DeBrangesF.lean` and `Cited/DeBrangesF/*`. The former
`Cited/DeBrangesFC/PartF.lean` and `FourierFramesScaffold` are import-only compatibility modules;
the abandoned factorization helpers have been retired.

Pavlov's BMO necessity consequence is proved in `Cited/Pavlov.lean` and 36 helper files
(6761 lines). Cardinal functions and Harnack estimates lead to finite weighted Cauchy tests,
A₂ and boundary logarithmic BMO. A regularized Schwarz integral, cancellation of boundary
zeros, harmonic reflection and a PW uniqueness argument give exact logarithmic dispersion.
Uniform conjugate-Poisson BMO bounds and a boundary staircase limit then give
`countFn Γ x-x ∈ BMO` by Fatou. This proves precisely `PavlovBMO`, not the full Pavlov iff
criterion. See `blueprint/P5_Pavlov.md` and reviews R13–R15. The project vendors 41 unchanged
Tau Ceti v4.35.0 modules (8882 lines), pinned and documented in `TauCeti/VENDORED.md`.
The proof uses selected multiplier, harmonic and analytic-logarithm tools; the project
supplies the specialized kernel, weighted, and BMO bridges.

**Unconditional versions.** `FourierFrames/Unconditional.lean` supplies the proved cited results to
the main theorems. Their strongest versions have no remaining cited hypotheses:

| Paper | Lean (namespace `FF`) | Remaining hypotheses |
|---|---|---|
| p. 790: Fourier frame ⟺ sampling | `isFourierFrame_iff_isSampling_unconditional` | — |
| p. 799: `|E| ≃ e^{π Im z}` on `Im z ≥ 0` ⇒ `H(E) = PW` | `heEqPW_of_comparable_unconditional` | — |
| Theorem 1, sufficiency | `theorem1_sufficiency_unconditional` | — |
| Example p. 798 | `logExample_isCompleteInterpolating_unconditional`, `landau_sharp_unconditional` (and `logExample_count`) | — |
| Corollary 2 | `corollary2_unconditional` | — |
| Theorem 2 (i) | `theorem2_i_unconditional`, `theorem2_i_of_densityBound_unconditional` | — |
| Theorem 2 (ii) | `theorem2_ii` | — (since phase 1) |
| Remark p. 797 | `completeInterpolating_zero_set_unconditional` | — |
| Theorem 1, necessity, and Theorem 1 | `theorem1_necessity_unconditional`, `theorem1_unconditional` | — |
| Corollary 1 | `corollary1_unconditional` | — |
| Claim (§4): Landau's inequality | `landau_inequality_unconditional` | — |

The file also states `dsPerturbation_holds : DSPerturbation`. It keeps the intermediate versions
`completeInterpolating_zero_set_of_theoremC`, `theorem1_necessity_of_theoremCF`, `theorem1_of_theoremCF`,
`corollary1_of_theoremCF` and `landau_inequality_of_theoremCF_pavlov`, which were stated before Theorem C
was proved. It also retains the historical `*_of_theoremF` and
`landau_inequality_of_theoremF_pavlov` versions for compatibility. The earlier
`landau_inequality_of_pavlov` wrapper also retains its explicit hypothesis.

**Corrections to the paper.** The formalization found that two proofs do not work as printed and
replaced them: the appeal to Meĭman's theorem on p. 801 (false as quoted) and the proof of
Theorem 2 (ii) (pp. 804–805). Theorem 2 (i) needs a regularity hypothesis on `ψ` that its
statement omits; `theorem2_i` assumes `ψ'` eventually nonincreasing, and
`theorem2_i_of_densityBound` assumes the cell density bound the proof uses. Neither assumes the
printed hypothesis `ψ'(x) = 1/O(x)`, which the proof does not use. Theorem F as printed
(for the closed Hermite–Biehler class) is false. All errata, gaps and simplifications are in
`NOTEBOOK.md` (45 entries: N-01–N-38 confirmed by independent referee agents against the printed
pages, N-39–N-42 found during the implementation, N-43–N-45 found in the blueprint of de Branges'
Theorems D and E and confirmed by referee R9). The
corrected paper is uploaded to arxiv.

## Layout

| Path | Content |
|---|---|
| `FourierFrames/Defs.lean` | statement-level definitions and the cited results as `Prop`s (imports only Mathlib) |
| `FourierFrames/**` | the formalization (namespace `FF`; 41,257 lines in 151 files), one or more files per blueprint module |
| `FourierFrames/Cited/` | phase 2: proofs of the cited results |
| `FourierFrames/Unconditional.lean` | the main results with the proved cited results discharged |
| `FourierFramesScaffold.lean` | compatibility import of the proved Theorem F via `Cited/DeBrangesFC/PartF.lean` |
| `OrtegaCerdaSeip/` | vendored, do not edit: the part of the companion formalization [MR1682065](https://github.com/joaquimortega/MR1682065) that proves the multiplier lemma of [OS99] and a Bernstein-space toolkit (`OrtegaCerdaSeip/VENDORED.md`) |
| `TauCeti/` | unchanged, pinned analytic tools used by Pavlov; provenance, license and import closure in `TauCeti/VENDORED.md` |
| `blueprint/` | the blueprint: `README.md` (plan, conventions, design decisions, module table), one detailed document per module (`M00`–`M10`, `P1`–`P5`), `IMPORTS.md` (module graph, interface reconciliation), `impl_notes/` (implementers' deviations) |
| `reviews/` | the independent referee reports (`R1`–`R5` on the phase-1 blueprint, `R6`–`R15` on phase 2 and on the final code) |
| `comparator/` | the main statements, the comparator configuration and the log of the accepted run |
| `NOTEBOOK.md` | errata (N-xx) and implementation notes (I-xx) |
| `formalization.yaml` | metadata in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) v0.4 format |
| `scripts/` | `make_challenge.py`, `check_statements.py` (statement freeze-check), `check_main_statements.py`, `make_imports.py`, `new_worktree.sh`, `bwrap-pkgs` |

## Building

Lean `v4.35.0`, Mathlib `v4.35.0`:

```sh
lake exe cache get
lake build                       # FourierFrames (builds the needed part of OrtegaCerdaSeip)
lake build FourierFramesScaffold # optional: compatibility import of the proved Theorem F
lake build FFChallenge FFSolution
COMPARATOR_BWRAP=$PWD/scripts/bwrap-pkgs lake comparator --config comparator/config.json
```

Initial formalization with Claude (Anthropic) in Claude Code; Theorem F and Pavlov's
BMO necessity consequence completed with Codex (OpenAI), using GPT-6.1 Sol subagents for implementation and independent review.
Directed by J. Ortega-Cerdà. License: Apache-2.0 (`LICENSE`).
