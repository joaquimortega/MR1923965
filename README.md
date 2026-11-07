# Formalization of Ortega-Cerdà–Seip, *Fourier frames* (Annals of Mathematics 2002)

A Lean 4 / Mathlib formalization of

> J. Ortega-Cerdà and K. Seip, *Fourier frames*, Ann. of Math. (2) **155** (2002), 789–806.
> [doi:10.2307/3062132](https://doi.org/10.2307/3062132), MR1923965.

Page references ("p. 795") are to the journal pagination. The journal PDF and the author's tex
source, used during the work, are not included in the repository.

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
`FourierFrames/Defs.lean`. All are proved without `sorry`, depend only on `propext`,
`Classical.choice` and `Quot.sound`, and are accepted by
[comparator](https://github.com/leanprover/comparator) against the self-contained
`FFChallenge.lean` (2026-11-07, `comparator/last_run.log`).

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
there are no axioms. Phase 2 of the project proves them where feasible
(`FourierFrames/Cited/`, plan and assessments in `blueprint/PHASE2.md`):

| Cited result | Lean | Status |
|---|---|---|
| John–Nirenberg | `johnNirenberg_holds` | proved |
| Duffin–Schaeffer Lemma III | `dsPerturbation_of_paleyWiener : PaleyWienerThm → DSPerturbation` | proved |
| Paley–Wiener theorem | `paleyWiener_holds` | in progress |
| de Branges' Theorems D, E | `theoremD_holds`, `theoremE_holds` | in progress |
| de Branges' Theorems C, F | `theoremC_holds`, `theoremF_holds` | stated; assessed (long) |
| Pavlov's Theorem A (BMO half) | `PavlovBMO` | hypothesis; assessed infeasible with current Mathlib |

**Corrections to the paper.** The formalization found that two proofs do not work as printed and
replaced them: the appeal to Meĭman's theorem on p. 801 (false as quoted) and the proof of
Theorem 2 (ii) (pp. 804–805). Theorem 2 (i) needs a regularity hypothesis on `ψ` that its
statement omits; `theorem2_i` assumes `ψ'` eventually nonincreasing, and
`theorem2_i_of_densityBound` assumes the cell density bound the proof uses. Theorem F as printed
(for the closed Hermite–Biehler class) is false. All errata, gaps and simplifications are in
`NOTEBOOK.md` (38 entries, confirmed by independent referee agents against the printed pages). The
corrected paper, with the changes marked in red, was produced locally (`fixed/`, not committed).

## Layout

| Path | Content |
|---|---|
| `FourierFrames/Defs.lean` | statement-level definitions and the cited results as `Prop`s (imports only Mathlib) |
| `FourierFrames/**` | the formalization (namespace `FF`; about 27,000 lines in 90 files), one or more files per blueprint module |
| `FourierFrames/Cited/` | phase 2: proofs of the cited results |
| `OrtegaCerdaSeip/` | vendored, do not edit: the part of the companion formalization [MR1682065](https://github.com/joaquimortega/MR1682065) that proves the multiplier lemma of [OS99] and a Bernstein-space toolkit (`OrtegaCerdaSeip/VENDORED.md`) |
| `blueprint/` | the blueprint: `README.md` (plan, conventions, design decisions, module table), one detailed document per module (`M00`–`M10`, `P1`–`P5`), `IMPORTS.md` (module graph, interface reconciliation), `impl_notes/` (implementers' deviations) |
| `reviews/` | the independent referee reports (`R1`–`R5` on the phase-1 blueprint, `R6`–`R8` on phase 2 and on the final code) |
| `comparator/` | the main statements, the comparator configuration and the log of the accepted run |
| `NOTEBOOK.md` | errata (N-xx) and implementation notes (I-xx) |
| `formalization.yaml` | metadata in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) v0.4 format |
| `scripts/` | `make_challenge.py`, `check_statements.py` (statement freeze-check), `check_main_statements.py`, `make_imports.py`, `new_worktree.sh`, `bwrap-pkgs` |

## Building

Lean `v4.35.0`, Mathlib `v4.35.0`:

```sh
lake exe cache get
lake build                       # FourierFrames (builds the needed part of OrtegaCerdaSeip)
lake build FFChallenge FFSolution
COMPARATOR_BWRAP=$PWD/scripts/bwrap-pkgs lake comparator --config comparator/config.json
```

Formalized with Claude (Anthropic) in Claude Code, directed by J. Ortega-Cerdà. License:
Apache-2.0 (`LICENSE`).
