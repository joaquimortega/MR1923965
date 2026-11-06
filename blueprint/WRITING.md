# Instructions for blueprint writers

You are writing one module of the blueprint for the Lean 4 formalization of Ortega-Cerdà–Seip,
*Fourier frames* (Ann. of Math. 155 (2002), 789–806). Repository root:
`/home/quim/cloud/papers/Lean/MR1923965`.

## Read first
1. `blueprint/README.md` (plan, conventions, design decisions, module table, interface names,
   known issues) and `blueprint/M00_Defs.md`.
2. `FourierFrames/Defs.lean` (all statement-level definitions and cited `Prop`s) and
   `comparator/statements.lean` (the main statements).
3. The paper: `literature/ArxivOrtega.tex` (author's source, agrees with the print) and the page
   images `literature/pages/p-NN.png` (journal page `788 + NN`; read them with the Read tool when a
   symbol matters). Never trust OCR text.
4. For modules using [OS99] Lemma 3: `OrtegaCerdaSeip/Lemma3/*.lean` (vendored, namespace `OCS`,
   already built; `OCS.lemma3`, `OCS.multU`, `OCS.multPt`, `OCS.multBary`, …) and
   `OrtegaCerdaSeip/Bernstein/*.lean`, `OrtegaCerdaSeip/Products/Canonical.lean`.

## Deliverables
1. `blueprint/MNN_Name.md`: a *very detailed* proof of everything in your module, written so that a
   Lean implementer can follow it line by line. Structure:
   - header: Lean file(s), paper pages, **Depends on** (modules and the exact lemma names used),
     **Used by**;
   - for each lemma: the Lean statement (in a ```lean block, exactly as in your scaffold file),
     then a detailed proof (every inequality, constant and limit made explicit; which Mathlib
     lemmas are likely useful, with names you have checked exist by grepping
     `.lake/packages/mathlib/Mathlib`);
   - a section **Issues in the source** listing every mistake, gap, typo or possible simplification
     you found in the paper's argument for your module, each with page/line, what the paper says
     (quoted from the tex), what is wrong, and the fix. Mark how sure you are.
2. The Lean scaffold file(s) named in the README module table, under `FourierFrames/`:
   - plain (non-`module`) Lean files: start with `import FourierFrames.Defs` (plus `Mathlib`/OCS
     imports as needed), then `open …`, `namespace FF`, …, `end FF`;
   - every lemma of the blueprint stated, proofs `sorry`; **definitions must be real (no `sorry`
     in definitions)**;
   - if you need a lemma owned by another module that does not exist yet, declare it in a section
     at the top of your file headed `/-! ## Upstream interface (temporary, replaced by imports at
     assembly) -/`, with exactly the name and a faithful statement from the README interface list
     (or a clearly marked new name if the README does not list it), proof `sorry`;
   - main statements from `comparator/statements.lean` that belong to your module must appear
     with *identical* names and statements;
   - compile with `cd /home/quim/cloud/papers/Lean/MR1923965 && lake env lean FourierFrames/<path>.lean`
     (do **not** run `lake build`: other agents work in parallel). The only allowed warnings are
     `declaration uses 'sorry'`. Fix all errors.
3. Do not edit files you do not own (`Defs.lean`, `statements.lean`, other modules, `README.md`).
   If you believe a definition in `Defs.lean` or a main statement is wrong or false, say so
   prominently in your doc (section **Requested changes to M00**) with a counterexample or argument.

## Standards
- Statements must be *true* and *faithful*. Before writing a statement, check edge cases (empty
  sets, zeros of functions, `x/0 = 0` in Lean, `Real.log 0 = 0`, `tsum` of non-summable families
  being `0` in `ℝ` — prefer `ℝ≥0∞`).
- Prefer the weakest hypotheses that make the proof work, and conclusions in the form downstream
  modules need.
- Constants: say explicitly on what each constant depends.
- Keep cited results (`PaleyWienerThm`, `TheoremC/D/E/F`, `PavlovBMO`, `JohnNirenberg`,
  `DSPerturbation`) as explicit hypotheses named `hPW`, `hC`, `hD`, `hE`, `hF`, `hA`, `hJN`, `hDS`.
- Report at the end: files written, compile status, the list of source issues found, and any
  requested changes to M00.
