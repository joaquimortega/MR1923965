# Instructions for implementers

You are proving the `sorry`s of one module of the Lean 4 formalization of Ortega-Cerdà–Seip,
*Fourier frames* (Ann. of Math. 155 (2002)). You work in your own git worktree (path given in your
brief), on branch `impl/<name>`. Lean/Mathlib v4.35.0.

## Read first
- `blueprint/README.md` (conventions, design decisions), your module's blueprint
  `blueprint/MNN_*.md` (the detailed proofs you implement), `blueprint/IMPORTS.md` (interface
  reconciliation: how upstream statements differ from what the blueprints assumed), and the
  referee report covering your module in `reviews/` (R2: M01/M02/M10; R3: M03/M04/M05;
  R4: M06/M07; R5: M08/M09).
- `FourierFrames/Defs.lean` (definitions) and the upstream files you import.

## Rules
1. **Own files only.** Edit only the files listed in your brief. New helper lemmas go in new files
   under a directory named after your module (e.g. `FourierFrames/Theorem2i/Aux.lean`), imported
   by your module file. Do not edit `FourierFrames.lean`, `Defs.lean`, `comparator/`, `NOTEBOOK.md`,
   other modules, or the vendored `OrtegaCerdaSeip/`.
2. **Never change an existing statement** (names, hypotheses, conclusions, definitions). Statements
   are frozen at tag `scaffold-reviewed`; `python3 scripts/check_statements.py scaffold-reviewed`
   must pass. If a helper statement you own is false or unprovable as stated, prove a corrected
   version under a new name in your aux file, use that, leave the original `sorry` with a comment
   `-- FALSE: <reason>`, and report it with a counterexample. If an *upstream* statement you use
   looks false or too weak, report immediately with `SendMessage` to `main` (do not wait until the
   end), and continue with the parts that do not depend on it.
3. **Upstream lemmas are black boxes.** Everything upstream is stated (possibly with `sorry`); use it
   freely as stated. Do not re-prove upstream lemmas.
4. **No cheating.** No `axiom`, `admit`, `native_decide`, `sorry` in definitions, or
   `set_option linter.* false`/`set_option maxHeartbeats 0`. Fix linter warnings by correcting
   the code. Raising `maxHeartbeats` locally for one declaration is acceptable if justified in a
   comment. Do not silence an unused hypothesis of a main statement (e.g. `hlow` in `theorem2_i`,
   `hPW` in `theorem2_ii`); leave that warning, it is handled at the end.  (Done in the final
   lint pass, NOTEBOOK I-03: unused hypotheses are removed from the statements.)
5. **Build** with `lake build FourierFrames.<Module>` in your worktree (it shares the prebuilt
   Mathlib; the first build of the project files takes a few minutes). Keep files compiling.
   Prefer many small lemmas to long proofs; long `simp`/`nlinarith` calls that time out should be
   broken up.
6. **Commit often** on your branch (`git add` your files; messages ending with
   `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>` and
   `Claude-Session: https://claude.ai/code/session_01EGoLKyodh2CU3aBi6Uz5mT`). Do not push, do not
   merge, do not rebase onto main.
7. **Notes.** Record every deviation from the blueprint, every false/changed helper statement and
   every source issue you discover in `blueprint/impl_notes/<name>.md` (create it; it is yours).
8. **Residual `sorry`s are acceptable** when you run out of budget: mark each with a comment
   `-- TODO(<name>): <precise obstacle>` and list them in your report, most important first.

## Report
At the end report: what is proved, the list of remaining `sorry`s with obstacles, any false or
changed statements (with counterexamples), upstream problems, and the last commit hash on your
branch.
