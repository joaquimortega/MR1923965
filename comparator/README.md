# Checking the main results with comparator

[comparator](https://github.com/leanprover/comparator) is a trustworthy judge for Lean proofs; Lean
v4.35 ships it as `lake comparator`. It checks that every theorem in `config.json`:
1. is stated in `FFSolution` exactly as in `FFChallenge` (all declarations used in the statements
   must coincide);
2. uses no axioms beyond `propext`, `Quot.sound` and `Classical.choice`;
3. is accepted by the Lean kernel.

## Files

| File | Role |
|---|---|
| `../FFChallenge.lean` | **The self-contained file with the main results.** It imports only `Mathlib`, contains every definition used in the statements (a verbatim copy of `FourierFrames/Defs.lean`, including the cited results as `Prop`s) and states the 33 theorems with `sorry`. |
| `statements.lean` | The 33 statements (main theorems, proved cited results, discharged versions), copied verbatim from the project. |
| `../scripts/make_challenge.py` | Regenerates `FFChallenge.lean`, `FFSolution.lean` and `config.json` from `Defs.lean` and `statements.lean`. |
| `../FFSolution.lean` | `import FourierFrames`. The project proves the theorems with the same names (namespace `FF`). |
| `config.json` | The comparator configuration (33 theorems). |
| `last_run.log` | The log of the last accepted run. |

## The 33 theorems

**The fifteen main statements**, with the cited results they use as explicit `Prop` hypotheses
(phase 1):

| Name | Paper |
|---|---|
| `FF.isFourierFrame_iff_isSampling` | p. 790: Fourier frame ⟺ sampling for PW (from the Paley–Wiener theorem) |
| `FF.heEqPW_of_comparable` | p. 799: `|E(z)| ≃ e^{π Im z}` on `Im z ≥ 0` ⇒ `H(E) = PW` |
| `FF.theorem1_necessity`, `FF.theorem1_sufficiency`, `FF.theorem1` | Theorem 1 |
| `FF.completeInterpolating_zero_set` | remark p. 797: a complete interpolating sequence is the zero set of `E + E^*` |
| `FF.corollary1` | Corollary 1 |
| `FF.landau_inequality` | the Claim of §4: Landau's inequality from John–Nirenberg, Pavlov and Theorem 1 |
| `FF.logExample_count`, `FF.logExample_isCompleteInterpolating`, `FF.landau_sharp` | the example `{k + log⁺|k|}` of p. 798 and the sharpness of Landau's inequality |
| `FF.corollary2` | Corollary 2 |
| `FF.theorem2_i` | Theorem 2 (i), with `ψ'` eventually nonincreasing (NOTEBOOK N-22) and without the unused hypothesis `ψ' = 1/O(x)` (N-26, I-03) |
| `FF.theorem2_i_of_densityBound` | Theorem 2 (i) with the cell density bound the proof uses |
| `FF.theorem2_ii` | Theorem 2 (ii), by the reconstructed proof (NOTEBOOK N-21); unconditional (no cited hypothesis) |

The cited results (Paley–Wiener, de Branges' Theorems C, D, E, F, Pavlov's Theorem A, John–Nirenberg,
Duffin–Schaeffer's Lemma III) appear as explicit hypotheses of the theorems that use them.

**Five cited results, proved** (phase 2; `blueprint/PHASE2.md`):

| Name | Cited result |
|---|---|
| `FF.paleyWiener_holds` | the Paley–Wiener theorem with Plancherel's identity (`FourierFrames/Cited/PaleyWiener.lean`) |
| `FF.johnNirenberg_holds` | the John–Nirenberg inequality (`Cited/JohnNirenberg.lean`) |
| `FF.theoremD_holds` | de Branges' Theorem D, the reproducing kernel of `H(E)` (`Cited/DeBrangesDE.lean`) |
| `FF.theoremE_holds` | de Branges' Theorem E, orthogonal sampling on the level sets of the phase (`Cited/DeBrangesDE.lean`) |
| `FF.dsPerturbation_holds` | Lemma III of Duffin–Schaeffer (`Unconditional.lean`, from `dsPerturbation_of_paleyWiener`) |

**Thirteen main statements with the proved cited results discharged** (`FourierFrames/Unconditional.lean`).
The remaining hypotheses are de Branges' Theorems C and F and Pavlov's Theorem A, which are not proved:

| Name | Paper | Remaining hypotheses |
|---|---|---|
| `FF.isFourierFrame_iff_isSampling_unconditional` | p. 790: Fourier frame ⟺ sampling | — |
| `FF.heEqPW_of_comparable_unconditional` | p. 799: `|E(z)| ≃ e^{π Im z}` ⇒ `H(E) = PW` | — |
| `FF.theorem1_sufficiency_unconditional` | Theorem 1, sufficiency | — |
| `FF.logExample_isCompleteInterpolating_unconditional`, `FF.landau_sharp_unconditional` | the example of p. 798 and the sharpness of Landau's inequality | — |
| `FF.corollary2_unconditional` | Corollary 2 | — |
| `FF.theorem2_i_unconditional`, `FF.theorem2_i_of_densityBound_unconditional` | Theorem 2 (i), both versions | — |
| `FF.completeInterpolating_zero_set_of_theoremC` | remark p. 797 | `TheoremC` |
| `FF.theorem1_necessity_of_theoremCF`, `FF.theorem1_of_theoremCF` | Theorem 1, necessity; Theorem 1 | `TheoremC`, `TheoremF` |
| `FF.corollary1_of_theoremCF` | Corollary 1 | `TheoremC`, `TheoremF` |
| `FF.landau_inequality_of_theoremCF_pavlov` | the Claim of §4 (Landau's inequality) | `TheoremC`, `TheoremF`, `PavlovBMO` |

`FF.logExample_count` and `FF.theorem2_ii` need no cited result, so they have no separate version.

## How to run

```sh
lake exe cache get                     # prebuilt Mathlib
python3 scripts/make_challenge.py      # (re)generate FFChallenge.lean, FFSolution.lean, comparator/config.json
lake build FFChallenge FFSolution      # optional: warms the cache
COMPARATOR_BWRAP=$PWD/scripts/bwrap-pkgs lake comparator --config comparator/config.json
```

`lake comparator` builds and exports both modules inside a `bwrap` sandbox and runs the Lean kernel
on the export. The wrapper `scripts/bwrap-pkgs` binds the shared package directory read-only when
`.lake/packages` is a symlink outside the project (as in this project's worktrees). Expected output:

```
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

Obtained on 2026-11-07 with Lean v4.35.0 and Mathlib v4.35.0 for all 33 theorems
(`last_run.log`). The challenge build reports one `declaration uses 'sorry'` warning per theorem
(33), as expected; the solution build has none.
