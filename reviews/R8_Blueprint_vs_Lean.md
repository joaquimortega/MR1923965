# R8 — The blueprint as documentation of the finished formalization; soundness audit

**Referee:** independent review agent, 2026-11-07. **Scope:** `blueprint/README.md`, `blueprint/M00_Defs.md` …
`M10_Frames.md`, `NOTEBOOK.md`, compared with the final Lean code under `FourierFrames/` (tree at commit
`d39797e` plus the uncommitted phase-2 work of other agents in `FourierFrames/Cited/DeBrangesDE*`), and a
soundness audit of the code and of `Defs.lean`. Only this file was written.

**Severity.**
- **High:** the document states something false about the code, or is misleading about what is proved.
- **Medium:** a wrong file or lemma name, a proof route that is not the implemented one, a constant that
  differs, or a stale request or status.
- **Low:** cosmetic.
- **OK:** checked and found consistent, recorded so the check is not repeated.

Line numbers are those of the files at the time of review.

## 0. What was checked mechanically

| check | how | result |
|---|---|---|
| axioms of the 15 main theorems | `#print axioms` in a scratch file importing the module files, run with `lake env lean` | `[propext, Classical.choice, Quot.sound]` for all 15, and for `johnNirenberg_holds`, `dsPerturbation_of_paleyWiener` |
| challenge = Defs + statements | regenerated the text of `scripts/make_challenge.py` into the scratchpad (not in place), `diff` with `FFChallenge.lean` | identical |
| main statements present verbatim | `python3 scripts/check_main_statements.py` | `OK: all 15 main statements present verbatim` |
| no statement changed since the freeze | `python3 scripts/check_statements.py scaffold-reviewed` | `OK: no statement changed` |
| `comparator/config.json` | read | 15 names, permitted axioms the standard three |
| doc Lean blocks vs code | every `theorem`/`def` block of M03–M09 extracted and compared, whitespace-normalised, with `FourierFrames/**` | M03 63/64, M04 32/35, M05 6/6, M06 67/68, M07 79/79 identical (differences listed below; all are renamings or superseded statements); M08/M09 identical except as listed |
| forbidden constructs | `grep -w` over `FourierFrames/`, `OrtegaCerdaSeip/`, `FFChallenge.lean` | see §1 |
| import graph | `make_imports.py` run on a patched scratch copy (see F-74) | 92 files, 1584 declarations, 165 `sorry`, all in `Cited/PaleyWiener*`, `Cited/DeBrangesDE*`, `Cited/DeBrangesFC.lean` |

---

## 1. Soundness audit (task 3)

**F-1 (OK) — axioms and comparator.**
- Evidence: `#print axioms` output (§0), `comparator/config.json`, `comparator/last_run.log`.
- The log shows `FFChallenge` and `FFSolution` building successfully and the export of the 15 theorems. It has no
  explicit verdict line, so the acceptance claim rests on the coordinator's statement together with the axiom and
  statement-identity checks of §0.
- `FFSolution.lean` is `import FourierFrames`.
- `FFChallenge.lean` is exactly what `scripts/make_challenge.py` generates from `Defs.lean` and
  `comparator/statements.lean` (regenerated in the scratchpad and compared with `diff`).

**F-2 (OK) — forbidden constructs.**
- No `axiom`, `admit`, `native_decide`, `unsafe`, `implemented_by`, `opaque`, `@[extern]` or `maxHeartbeats` in
  `FourierFrames/`, the vendored `OrtegaCerdaSeip/`, or `FFChallenge.lean`.
- `OrtegaCerdaSeip/` also has no `sorry` and no `set_option`.

**F-3 (Low) — the one `set_option`.**
- Evidence: `FourierFrames/Theorem1/Necessity.lean:250`, `set_option warn.classDefReducibility false in` before
  `def sampCore : InnerProductSpace.Core ℂ PWFun`.
- It only silences the warning about a `def` whose type is a class. It has no logical effect.
- It does go against the spirit of `IMPLEMENTING.md` rule 4 ("Fix linter warnings by correcting the code").
- Proposed: add a justification comment, or replace the `def` by a `@[reducible] def`/`abbrev` and drop the option.

**F-4 (Medium) — `sorry` is reachable from the root import.** None of the 15 main theorems is affected.
- `sorry` occurs only in `FourierFrames/Cited/`:
  - `PaleyWiener/{Part1,Part2,Spectrum,L2Fourier}.lean`: 32;
  - `DeBrangesDE*`: 110 (work in progress by another agent);
  - `DeBrangesFC.lean`: 23–24.
- `FourierFrames.lean` imports `Cited.PaleyWiener` and `Cited.DeBrangesFC` (`FourierFrames.lean:24-27`).
  So `import FourierFrames` puts four `sorry`-backed proofs of cited `Prop`s in scope.
  - `#print axioms` shows `sorryAx` for `FF.paleyWiener_holds`, `FF.theoremC_holds`, `FF.theoremF_holds` and `FF.theoremD_holds`.
  - The last is the *temporary stub* at `Cited/DeBrangesFC.lean:25`.
- The comparator checks only the 15 names, so its verdict stands. But a downstream composition such as
  `theorem1 paleyWiener_holds theoremC_holds …` would compile silently with `sorryAx`.
- Proposed:
  - (a) Import into `FourierFrames.lean` only those `Cited/*` files that are `sorry`-free (today `Cited/JohnNirenberg`
    and `Cited/DSPerturbation`). Put the scaffolds behind a separate root, e.g. `FourierFrames/Phase2WIP.lean`.
  - (b) Alternatively, have README state explicitly which `*_holds` are `sorry`-free (F-13).

**F-5 (Medium) — the declaration `FF.theoremD_holds` exists twice.**
- Evidence:
  - `FourierFrames/Cited/DeBrangesFC.lean:22-26` ("Upstream interface (temporary, replaced by imports at assembly)",
    `theorem theoremD_holds : TheoremD := by sorry`);
  - `FourierFrames/Cited/DeBrangesDE.lean:28` (the real assembly).
- Today `Cited/DeBrangesDE.lean` is not imported by `FourierFrames.lean`, so the build passes. The first file that
  imports both gets an "already declared" error.
- Proposed: at P3/P4 assembly, delete the stub in `DeBrangesFC.lean` and `import FourierFrames.Cited.DeBrangesDE` there.

**F-6 (Medium, open action from NOTEBOOK I-02) — unused hypotheses of two main statements.**
- Evidence: `comparator/last_run.log` shows "`hlow` is not explicitly referenced" (`FourierFrames/Theorem2i.lean:143`)
  and "`hPW` is not explicitly referenced" (`FourierFrames/Theorem2ii.lean:1171`).
- `theorem2_i` proves `IsSampling` from `hreg` and `hmono` alone (`Theorem2i.lean:141-150`). `theorem2_ii` never uses `hPW`.
- NOTEBOOK I-02 (`NOTEBOOK.md:339-343`) promises that these warnings "are resolved at the end by a deliberate,
  recorded statement change". Phase 1 is finished and the change has not been made.
- Either option is sound:
  - (a) Remove the two hypotheses. This gives strictly stronger theorems, and requires updating `comparator/statements.lean`,
    `FFChallenge.lean`, README §1, M00 §3 and the docstrings.
  - (b) Close I-02 with the decision to keep them. Proposed I-02 text: "**Decision (2026-11-07):** kept, for
    faithfulness to the printed statements. The two unused-variable warnings are accepted. `theorem2_i_of_densityBound`
    is the `hlow`-free form of Theorem 2 (i). `theorem2_ii` holds without `hPW`."
- **Note.** `hlow` is not even needed for the *printed* theorem's proof (N-26). The only role it plays is
  faithfulness.

**F-7 (Low) — unused hypotheses of helper statements are silenced with `have _ :=`.**
- None of these is a main statement, so `IMPLEMENTING.md` rule 4 is respected. The occurrences:
  - `Corollary2.lean:70-71` (`multU_const_mul`: `hg`, `hM`);
  - `Landau.lean:168-169` (`osc_bound_of_JN`: `hD`, *written twice*);
  - `Perturbation.lean:274` (`isSampling_of_replace_finite`: `hsep'`);
  - `Theorem2i/Estimates.lean:34` (`RegData.abs_cellTerm_below`: `hz`);
  - `Theorem2i/Cells.lean:66` (`RegData.hasSum_UPsi`: `hz`);
  - `LogExample.lean:1103` (`integrable_log_mul_sub_one`: `hz`);
  - `Construction.lean:378`, `:557` (`compB_eq_zero_iff`, `compB_mul_Q`: `hN`);
  - `Theorem1/Sufficiency.lean:144` (`exists_noRealZero_hb`: `hEHB`).
- Further unused hypotheses are left visible as warnings:
  - `HB/DeBranges.lean:216` and `HB/Comparable.lean:302` (`hPW`);
  - `Theorem1/Necessity.lean:208-326, 635, 718-719` (`sampInner_*`, `samp_H1`, `samp_H3`, `entSum_eq`).
- Each one means a lemma holds under fewer hypotheses than its frozen statement says. That is harmless, but it
  should be logged (F-73).
- Proposed: delete the duplicate `have _ := hD` at `Landau.lean:169`.

**F-8 (OK) — `@[simp]` lemmas and instances.**
- The `@[simp]` lemmas: `PWFun.val_mk` (`rfl`, `Necessity.lean:169`), `fstar_apply` (`rfl`), `fstar_fstar` (proved,
  `HB/Basic.lean:18-20`), and three vendored OCS lemmas (`csinc_zero` etc.).
- A `@[simp]` lemma is a proved theorem, so it cannot introduce unsoundness.
- The only instances are `inferInstanceAs` transfers to `PWFun` (`Necessity.lean:156-157`).
- No `macro`, `elab`, `notation` or `attribute [...]` changes.

**F-9 (OK) — degenerate behaviour of the definitions in `Defs.lean`.**
- Division by zero (`x/0 = 0`):
  - `orthWeight E x = ofReal (π/(φ'|E|²))` is `0` when `φ' = 0`. It occurs only in `TheoremE`, which is restricted to
    `IsStrictHB E` without real zeros, where `φ' > 0` (proved: `IsStrictHB.phaseDeriv_pos`, `HB/Phase.lean:345`).
  - `MemHE` divides by `E` only on `Im z > 0`, where `IsHB` excludes zeros. `heNormSq` divides by `E` on `ℝ`, and the
    real zeros of `E ≢ 0` are a null set.
  - In `TheoremF`, `E − E^*A ≠ 0`, because `|E^*| < |E|` and `|A| ≤ 1`.
- `Real.log 0`: in `UPsi` the integrand meets it only at `t = z` (for real `z`) and `t = 0`, which are null sets.
  `corollary2`'s approximation hypothesis is multiplicative (README §2.6), so zeros of `f` are excluded, not
  silently allowed.
- Bochner integrals (a non-integrable integrand gives `0`):
  - `UPsi`: the integrand is integrable for every admissible `ψ`, since `ψ'` is continuous and tends to `0`, hence is
    bounded; the log singularities are integrable; and the tail is `O(|z|²/t²)`. For the `ψ` of
    Theorem 2 (i) the code proves it (`RegData.integrable_UPsi`, `Theorem2i/Cells.lean:21`;
    `RegData.integrable_upsiInt`). So `happ` is not satisfied vacuously through a zero integral.
  - `intervalMean`/`meanOsc` appear only under `LocallyIntegrable` (`MemBMO`, `JohnNirenberg`).
  - The integrals in `IsFourierFrame` and `PaleyWienerThm` are over a bounded interval of an `L²` function, hence
    of an `L¹` function.
  - `TheoremD`'s inner-product integral has an integrable integrand when `f, K ∈ H(E)`.
- `tsum`: every `∑'` in `Defs.lean` is `ℝ≥0∞`-valued, so there is no non-summable-gives-`0` collapse. This covers
  `sampleSum`, `IsCompleteInterpolating`, `IsFourierFrame`, `TheoremE`, `IsLogRegularPartition*`.
- `ncard`:
  - `countFn` (used only in `PavlovBMO`, for separated `Γ`, where the intersections are finite).
  - `logExample_count`: there the sets are finite, and an infinite set would make the statement *false*
    (`ncard = 0`), not trivial.
  - `landau_inequality` and `landau_sharp` use `encard`, where an infinite set gives `⊤`, which is the right semantics.
- Non-vacuity of the hypotheses:
  - `theorem1_sufficiency`: `E = e^{-iπz}`, `F = 1`, `Λ = ℤ + 1/2`.
  - `theorem2_i`: a `C¹` modification of `√x` near `0`.
  - `theorem2_i_of_densityBound`: the same `ψ`.
  - `theorem2_ii`: a `C¹` modification of `log log x`.
  - The cited `Prop`s: `JohnNirenberg` and `DSPerturbation` (from `PaleyWienerThm`) are now proved. The others were
    checked in R1 and their restrictions are documented (NOTEBOOK N-02, N-37).
- **No main statement is vacuous or trivially true.**

**F-10 (Low) — weak `tsum`/`ncard` helper statements in M08 (not on the main path).**
- Evidence:
  - `Theorem2i/Estimates.lean:65,75,90` (`card_near_le`, `sum_far_le`, `sum_far_im_le`);
  - `Theorem2i/Assembly.lean:507` (`exists_bound_cellTerm`).
- Real-valued `tsum`s are `0` when the family is not summable, and `Set.ncard` is `0` for an infinite set, so these
  statements hold trivially in the degenerate case.
- They are proved (from finset forms) but used by nothing. The main chain goes through the uniform finset lemmas:
  `RegData.finset_card_near_le`, `finset_sum_far_le` (`Counting.lean:95,137`), `finset_sum_far_im_le` (`Riemann.lean:58`),
  via `D3.exists_finset_bound` (`Assembly.lean:483`) into `exists_approx` (`Assembly.lean:512`).
- Proposed: delete the four unused `tsum` forms, or document them as corollaries. Record the design lesson as an I-entry (F-73).

**F-11 (Low) — the import style of `Theorem2i/NearAux.lean`.** It imports `Mathlib` without `module`, which gives a
module-system warning in `last_run.log`. Cosmetic.

**F-12 (Low) — stale comments in the code.** They do not affect soundness, but a reader of the Lean files is misled.
- **`Theorem2i.lean:10-15`.** It says: "`theorem2_i` (identical to `comparator/statements.lean`) has no honest proof
  from the paper's argument unless `DensBound` can be derived or added to the hypotheses". But `theorem2_i` *is* proved:
  `hmono` gives `DensBound` by `RegData.densBound_of_antitoneOn`.
  - Replace with: "`theorem2_i` assumes in addition `hmono` (`ψ'` eventually nonincreasing), which gives `DensBound`
    (`RegData.densBound_of_antitoneOn`). `theorem2_i_of_densityBound` assumes `DensBound` through
    `IsLogRegularPartitionWithDensity`."
- **`Theorem2i/Assembly.lean:18-21`.** "(black boxes; D2 / coordinator to reconcile) TODO(theorem2i): …": these
  lemmas are proved. Remove the TODO.
- **`PW/Basic.lean:275-285`.** The docstrings of `exists_pwFT` ("Easy half of `hPW`") and `memPW_pwFT` ("derives the
  unconditional `⇐`") are stale: `memPW_pwFT` is `hPW.1 g hg` since `PaleyWienerThm` was strengthened.
- **`LogExample.lean:2063`.** The docstring of `landau_sharp` says "the logarithmic term cannot be removed". The
  statement is the strengthened one: no coefficient `A < 1` works.
- **`Corollary2.lean:163-164`.** The docstring of `log_norm_eq_multU_add_affine` describes the holomorphic-log route;
  the proof uses Schwarz reflection.
- **`Corollary2/UCont.lean:6`.** "For a continuous bounded `g`": the file handles measurable `g`.
- **`Construction.lean:23`.** "`E ↦ e^{-κz}E`": it should read `E_κ = e^{-κz}(A − i e^{κ/2}B)`.
- **`Defs.lean:28-29`.** The header lists "de Branges' Theorems C, E, F" and omits D. Optional: `Defs.lean` is copied
  into `FFChallenge.lean`, so the challenge would have to be regenerated.

---

## 2. `blueprint/README.md` (task 2)

**F-13 (High) — The README has no status section.**
- The only status information is the workflow plan (`README.md:17-35`). A reader cannot tell that phase 1 is
  finished, which cited results are proved, or that `sorry` remains under `Cited/`.
- Proposed new section, inserted after the source/project paragraph (after `README.md:15`):

```markdown
## Status (2026-11-07)

**Phase 1 is complete.**
- All 15 main statements of `comparator/statements.lean` are proved, with the cited results as explicit `Prop`
  hypotheses.
- `comparator` accepts `FFChallenge`/`FFSolution`. `#print axioms` of each main theorem shows only `propext`,
  `Classical.choice`, `Quot.sound`.
- No `sorry` outside `FourierFrames/Cited/`.
- `scripts/check_statements.py scaffold-reviewed` passes: no statement changed after the freeze (the
  changes of NOTEBOOK I-01 predate the freeze).
- Open: the hypotheses `hlow` of `theorem2_i` and `hPW` of `theorem2_ii` are unused (NOTEBOOK I-02).

**Phase 2** (`blueprint/PHASE2.md`, files under `FourierFrames/Cited/`):

| `Prop` | Lean | status |
|---|---|---|
| `JohnNirenberg` | `johnNirenberg_holds` (`Cited/JohnNirenberg.lean`) | proved, unconditional |
| `DSPerturbation` | `dsPerturbation_of_paleyWiener : PaleyWienerThm → DSPerturbation` (`Cited/DSPerturbation.lean`) | proved from `PaleyWienerThm` |
| `PaleyWienerThm` | `paleyWiener_holds` (`Cited/PaleyWiener.lean`, `Cited/PaleyWiener/{Part1,L2Fourier,Spectrum,Part2}.lean`) | assembly proved; the parts are scaffolds with `sorry` |
| `TheoremD`, `TheoremE` | `theoremD_holds`, `theoremE_holds` (`Cited/DeBrangesDE.lean` + `Cited/DeBrangesDE/*`) | in progress (`sorry`); not yet imported by `FourierFrames.lean` |
| `TheoremC`, `TheoremF` | `theoremC_holds`, `theoremF_holds` (`Cited/DeBrangesFC.lean`) | scaffold (`sorry`); contains a temporary stub of `theoremD_holds` |
| `PavlovBMO` | — | not feasible (`P5_Pavlov.md`); stays the hypothesis `hA` of `landau_inequality` |

`import FourierFrames` brings the `sorry`-backed `*_holds` declarations into scope. Before using one to discharge
a hypothesis, check it with `#print axioms`.
```

**F-14 (Medium) — The phase plan is stale.**
- `README.md:33-35` says: "Phase 2: discharge cited results, in order of feasibility: Paley–Wiener …, Duffin–Schaeffer,
  John–Nirenberg, then de Branges' Theorems D, E, F, C. Pavlov's theorem is the deepest and may stay a hypothesis."
- Proposed: "*Phase 2*: discharge the cited results that are within reach (plan, assessments and status:
  `blueprint/PHASE2.md` and the Status section above). Pavlov's theorem stays a hypothesis (`P5_Pavlov.md`)."

**F-15 (Low) — The §1 table of main results.**
- Checked against `comparator/statements.lean`: every name and every list of cited hypotheses is correct.
- Two things are missing:
  - (a) where each theorem is proved;
  - (b) that two hypotheses are unused (F-6).
- Proposed: add a column "Lean file" with these entries:

| theorem | Lean file |
|---|---|
| `isFourierFrame_iff_isSampling` | `Frames.lean` |
| `heEqPW_of_comparable` | `HB/Comparable.lean` |
| `theorem1_necessity` | `Theorem1/Necessity.lean` |
| `theorem1_sufficiency` | `Theorem1/Sufficiency.lean` |
| `theorem1` | `Theorem1/Main.lean` |
| `completeInterpolating_zero_set`, `corollary1` | `Corollary1.lean` |
| `landau_inequality` | `Landau.lean` |
| `logExample_isCompleteInterpolating`, `logExample_count`, `landau_sharp` | `LogExample.lean` |
| `corollary2` | `Corollary2.lean` |
| `theorem2_i`, `theorem2_i_of_densityBound` | `Theorem2i.lean` |
| `theorem2_ii` | `Theorem2ii.lean` |

- Proposed changes to the cited-hypotheses column:
  - `theorem2_ii`: "PW (unused, I-02)".
  - `theorem2_i`: row text "Theorem 2 (i), with ψ' eventually nonincreasing (N-22); `hlow` unused".

**F-16 (OK) — The §2 conventions.** All seven items match `Defs.lean`:
- `UPsi`: `Defs.lean:295-296`;
- the multiplicative `happ`: `Corollary2.lean:600`;
- `TheoremF`'s `p ≥ 0`: `Defs.lean:246`;
- the restriction of D/E/F to strict `E` without real zeros: `Defs.lean:217, 229, 243`.

**F-17 (Medium) — §3.2 describes a route the code does not use.**
- `README.md:92-93`: "`φ_F' ≥ 0` … is elementary: `log|F^*| − log|F| ≤ 0` … so its `y`-derivative at `y = 0` … is `≤ 0`."
- The argument is correct, but the code proves `IsHB.phaseDeriv_nonneg` (`HB/Phase.lean:314`) and the strict
  version (`:345`) from one dichotomy, `IsHB.phaseDeriv_pos_or_eventuallyEq` (`HB/Phase.lean:246`): either `E^* = cE`
  near `x`, or `φ'(x) > 0`. That dichotomy is proved with the Hopf-type lemma `hopf_boundary` (`HB/Hopf.lean:74`).
  See `impl_notes/hb.md:11-13`.
- Proposed: append "In Lean both `φ_F' ≥ 0` and the strict `φ_E' > 0` for `E ∈ HB` come from the dichotomy
  `IsHB.phaseDeriv_pos_or_eventuallyEq` (normal form of `E^*/E − c` at `x` plus the Hopf-type boundary lemma of
  `HB/Hopf.lean`). The one-sided derivative argument alone cannot give strictness (`D(y) ≈ −y³`)."

**F-18 (Medium) — §3.6 (Meĭman) describes neither the actual polynomial argument nor the actual limit.**
- `README.md:106-109`: "`A` and `B` are limits of the symmetric partial products … (partial fractions, residues of constant sign)".
- What the code does:
  - The polynomial Hermite–Biehler step is proved by monotonicity of arguments: `PolyHB.arg_sub_strictMono`,
    `sum_bound`, `im_prod_div_pos'` (`Construction/PolyHB.lean:64-129`). There are no partial fractions.
  - The limit is `e^{β + c_R z}(A_R − iλ e^{−c_R/2} B_R) → A − iλB` for every `λ > 0` (`isHB_genA_sub_lam_compB`,
    `Construction.lean:1069`), not the bare symmetric products. Those need not converge (N-35).
- Proposed replacement for the last sentence of 3.6:
  "In Corollary 2, `A` and `B` are locally uniform limits of `e^{β + c_R z}` times the symmetric partial products,
  which are real polynomials with interlacing zeros. For those, `Im(B_R/A_R) > 0` on `ℂ₊`, because the arguments of
  the factors are monotone (`Construction/PolyHB.lean`). The real exponential factors preserve `\overline{HB}`, and
  `\overline{HB}` is closed under locally uniform limits (Hurwitz, `IsHB.of_tendstoLocallyUniformly`). The result is
  `A − iλB ∈ \overline{HB}` for every `λ > 0` (`isHB_genA_sub_lam_compB`)."

**F-19 (Medium) — §3.7 (Levin avoided) names the wrong construction.**
- `README.md:110-113`: "handled by the Corollary 2 construction with `F = 1`: `A` is the generating function,
  `E = A − iB`, … `Λ = {A = 0} = {E + E^* = 0}`".
- What the code does:
  - It uses the construction of M07 §2 directly. There is no Corollary 2 and no perturbation.
  - The step density `logDensity` has barycentres exactly `Λ + 1/2`.
  - `E = compEκ = e^{−κz}(A − i e^{κ/2}B)` with `κ = logKappa` (`LogExample.lean:1765-1770`).
  - Theorem E at level `π/2` gives sampling and CIS for `Λ + 1/2 = {E + E^* = 0}` (`logExample_shift_sampling_cis`,
    `LogExample.lean:2035`). Translating by `−1/2` finishes (`:2042-2048`).
- Proposed replacement:
  "The example `{k + log⁺|k|}` uses the construction of M07 §2 with a step density whose barycentres are exactly
  `Λ + 1/2`, and `E = e^{−κz}(A − i e^{κ/2}B)` with `κ = logKappa`. The sine-type estimate `|E| ≃ e^{π Im z}`,
  which the paper asserts without proof, is proved. Theorem E at level `π/2` shows that `Λ + 1/2 = {E + E^* = 0}`
  is sampling and complete interpolating. Translating by `−1/2` gives the claim."

**F-20 (OK) — §3.1, 3.3, 3.4, 3.5 and 3.8 match the code.**
- 3.1: Theorem D is a hypothesis only of `completeInterpolating_zero_set` (`Corollary1.lean:270`). The bounds on
  `φ'|E|²` use Theorem E, a dense set of non-exceptional points and continuity (`HEEqPW.exists_phase_data`,
  `HB/DeBranges.lean:193-212`).
- 3.4: the kernel `hk x z = 1/(x − z) − x/(1+x²)` (`Necessity.lean:575`).
- 3.5: `plancherelPolya_tail_union` (`PW/PlancherelPolya.lean:378`, used at `Theorem1/Sufficiency/Limit.lean:94`).
  Suggest naming it in 3.5.
- 3.8: `levelSet_separated` uses Theorem E and `pw_deriv_bound` (`Theorem1/Sufficiency/LevelSet.lean:53-73`).

**F-21 (Medium) — §3 is missing the design decisions taken during implementation.**
- These are now part of the formalization, and §3 is where a reader looks for them.
- Proposed additions:

```markdown
9. **Theorem 2 (i) needs a local density bound** `ψ' ≲ 1/d_n` on each cell (N-22). Two main statements:
   `theorem2_i_of_densityBound` assumes it, through `IsLogRegularPartitionWithDensity`, and does not
   assume `ψ' = 1/O(x)`. `theorem2_i` keeps the printed hypotheses and adds `hmono` (`ψ'` eventually
   nonincreasing), which implies the bound (`RegData.densBound_of_antitoneOn`).
10. **Theorem 2 (ii) has a new proof** (N-21, M09): a test function built from [OS99] Lemma 3 for a
    window-dependent density, with constants uniform in the density (`lemma3_estimate_uniform`,
    `Lemma3Uniform.lean`).
11. **Removing the real zeros of `F`** (N-32): a Weierstrass product of variable genus
    `p_a = m(a) + rank(a) + 1`, with `rank` an injection of the real zero set into `ℕ`
    (`Theorem1/Sufficiency/RealFactor/*`). It needs no separation.
12. **Complete interpolating ⇒ sampling** (p. 791, used in Corollary 1 and in the remark of p. 797): the closed
    graph theorem for `ℓ²(Λ) → L²(ℝ)` (`Corollary1/ClosedGraph.lean`).
13. **The phase construction** is `E_κ = e^{−κz}(A − i e^{κ/2} B)` (`compEκ`). The plain twist `e^{−κz}(A − iB)`
    has the right modulus but the wrong phase. The first version of `exists_hb_of_density`, which had a phase
    clause for every `m → 1`, is false. See §4 and `IMPORTS.md`.
14. **`log|f| = (1/π) ∫ log|1 − z/t| φ_f'(t) dt + b Re z + c`** (N-36) is proved by Schwarz reflection of
    `Φ = e^{iφ(0)} f e^{−P}`, which is real on `ℝ`, followed by Borel–Carathéodory. No holomorphic logarithm is
    used (`Corollary2/{Reflection,Affine,LogNorm}.lean`). Continuity of potentials of bounded measurable
    densities uses Vitali's theorem (`Corollary2/UCont.lean`).
15. **No real-valued `tsum` or `ncard` in helper statements on the main path.** They are `0` when the series
    diverges or the set is infinite. The M08 estimates are proved in uniform finset form.
```

**F-22 (Medium) — The §4 module table lists only the scaffold files.**
- `README.md:120-132` lists the scaffold files. None of the helper directories created during implementation
  appear, nor any phase-2 module.
- Proposed "Lean" column:

| # | Lean |
|---|---|
| M01 | `PW/{Basic,Bounds,PlancherelPolya,Complete}.lean` |
| M02 | `HB/{Basic,Phase,H2,DeBranges,Comparable}.lean`; helpers `HB/{Hopf,MeanValue}.lean` |
| M03 | `Theorem1/Necessity.lean`; helper `Theorem1/Necessity/Sep.lean` |
| M04 | `Theorem1/Sufficiency.lean`, `Theorem1/Main.lean`, `Corollary1.lean`; helpers `Theorem1/Sufficiency/{Interlace,Limit,LevelSet,Phase}.lean`, `Theorem1/Sufficiency/RealFactor/{Elem,LUProd,Zeros,Product,Main}.lean`, `Corollary1/{Rotate,Kernel,ClosedGraph}.lean` |
| M05 | `Landau.lean` |
| M06 | `LogExample.lean`; helpers `LogExample/{Basic,Phase,Potential}.lean` |
| M07 | `Construction.lean`, `Perturbation.lean`, `Corollary2.lean`; helpers `Construction/{Gaps,Comparable,PolyHB,Limits,Rigidity,Translate}.lean`, `Corollary2/{Affine,Kernel,Density,LogInt,Reflection,PotC,PotCDiff,PotCCont,UCont,LogNorm}.lean` |
| M08 | `Theorem2i.lean`; helpers `Theorem2i/{Basic,Product,PhaseDecay,Cells,CellsAux,Taylor,CellAux,BelowAbove,FarAux,NearAux,Near,Counting,Riemann,Estimates,Assembly}.lean` |
| M09 | `Theorem2ii.lean`, `Lemma3Uniform.lean`; helpers `Theorem2ii/{Window,UOne,Ramp,Mass,Cells}.lean` |
| M10 | `Frames.lean` |

- Proposed phase-2 rows:

| # | Doc | Lean | Content |
|---|---|---|---|
| P1 | `P1_PaleyWiener.md` | `Cited/PaleyWiener.lean`, `Cited/PaleyWiener/{Part1,L2Fourier,Spectrum,Part2}.lean` | Paley–Wiener theorem |
| P2 | `P2_DS_JN.md` | `Cited/DSPerturbation.lean`, `Cited/JohnNirenberg.lean` | Duffin–Schaeffer, John–Nirenberg |
| P3 | `P3_DeBrangesDE.md` (not yet in `blueprint/`) | `Cited/DeBrangesDE.lean`, `Cited/DeBrangesDE/{Cauchy,Kernel,Space,EntireHerglotz,Orthogonal,Complete}.lean` | de Branges D, E |
| P4 | `P4_DeBrangesFC.md` | `Cited/DeBrangesFC.lean` | de Branges C, F |
| P5 | `P5_Pavlov.md` | — | assessment only |

**F-23 (Low) — The claim about the root file is wrong.**
- `README.md:134`: "`FourierFrames.lean` imports every one of them."
- In fact it imports the module files (helpers come in transitively) and four of the `Cited/*` roots, but not
  `Cited/DeBrangesDE.lean`.
- Proposed: "`FourierFrames.lean` imports the module files of the table (helper files transitively) and
  `Cited/{DSPerturbation,JohnNirenberg,PaleyWiener,DeBrangesFC}.lean`."
- See also F-4: the root should probably not import scaffolds.

**F-24 (Medium) — The regeneration instruction is broken.**
- `README.md:135-137`: "(regenerate with `python3 scripts/make_imports.py`)".
- On the current tree the script stops with `KeyError: 'Cited/DSPerturbation'`, and it would also fail on every helper
  file such as `Theorem2i/Assembly`. Details and a fix in F-74.

**F-25 (Medium) — The dependency graph is wrong.**
- The graph at `README.md:145-153`:
  - places M09 under M07 (M09 imports only `Defs`, `Lemma3Uniform` and OCS);
  - places M07 directly under M02 (`Corollary2.lean` imports `Theorem1.Sufficiency`, i.e. M04, and `Perturbation`
    imports M01);
  - omits that M06 imports M04 (`Theorem1.Sufficiency`) and M02 (`HB.Comparable`);
  - lists OCS only for M07 and M09 (M01, M03, M06 and M08 also import it);
  - has no phase 2.
- Proposed graph, computed from the actual `import` lines and checked with a patched `make_imports.py` (F-74):

```
M00 ── M01 ─┬─ M10
            └─ M02 ─┬─ M03 ─────────────┐
                    └─ M04 Sufficiency ─┴─ M04 Main, Corollary1 ── M05
                         └─ M07 (Construction ← M02; Perturbation ← M01; Corollary2 ← M04 Sufficiency)
                              ├─ M06 (also ← M02 HB.Comparable, M04 Sufficiency)
                              └─ M08
M00 ── M09 (with Lemma3Uniform; no project module besides Defs)
OCS: Bernstein → M01, M07, P1; Products.Canonical → M03, M08; Lemma3 → M06, M07, M09
Phase 2: M00 ── P1, P4;  M01 ── P2 (DSPerturbation; JohnNirenberg ← M00 only);  M02 ── P3
```

**F-26 (Low) — The §4 interface names for M01/M02.**
- Missing: `plancherelPolya_tail_union (hPW)`, the tail bound uniformly over unions of two `δ`-separated sets
  (`PW/PlancherelPolya.lean:378`, consumed by M04).
- `pw_deriv_bound` is pointwise with the explicit constant `(πe)²`, not "some `C`".
- `memHE_sAlpha_unique` needs only `IsHB E`, not "`E` strict" (`README.md:193`).
- `HEEqPW.isStrictHB` and `HEEqPW.ne_zero_ofReal` take no `hPW`.
- `HEEqPW.phaseDeriv_mul_sq_ge` does not use its `hPW` (F-7).
- `MemPW.isH2Upper_mul_exp` is proved but used by no module.
- Proposed: correct the bullets at `README.md:172-173, 190-193` accordingly.

**F-27 (OK) — The §4 M07 construction block.**
- `exists_hb_of_density` (`Construction.lean:1201`) and `exists_hb_of_density_phase` (`:2002`) agree with the
  README statements; the README makes `{m a b}` explicit where the code uses section variables.
- Corollary 2 uses the phase version with `κ = 0` (`Corollary2.lean:625-627`). M06 uses it with `κ = logKappa`
  (`LogExample.lean:1766`).
- `IsSampling.of_perturbation` (`Perturbation.lean:343`) matches the description.

**F-28 (Medium) — §4a ("Known issues in the source (seeds …; each to be verified)") is superseded by NOTEBOOK and partly wrong.**
- `README.md:236`: "(Placeholder: check the definition of `PW` norm.)" is a placeholder.
- `README.md:238` says "p. 794, display after (2)", while N-05 (print-checked) says "p. 796, display after (5)".
- `README.md:241` ("`φ_{EF} = φ_E + φ_F ≥ φ_E` should be about derivatives") was **withdrawn** in N-10: the print
  has primes (`literature/ArxivOrtega.tex:515`).
- The pp. 804–805 bullet is now N-21.
- Proposed: replace §4a by
  "## 4a. Issues in the source — see `NOTEBOOK.md` (N-01 … N-38, all verified against the print or the tex). The
  seeds that were here became N-05, N-07, N-09, N-11, N-12, N-14–N-16, N-18–N-21 and N-35/N-36. The seed about
  `φ_{EF}` was withdrawn (N-10)."

---

## 3. Module documents (task 1)

**Common to all module docs (Low).**
- Every doc still opens with a scaffold-era status line:
  - M01:4 "(all compile with `sorry` only)";
  - M02:8 "All files compile (only `declaration uses 'sorry'` warnings)";
  - M03:25-27; M04:3-4; M06:3; M07:3-6, 1169; M08:3; M09:3; M10:3.
- Most Lean blocks still end in `:= by sorry` or `sorry`.
- Several docs refer to "Upstream interface" sections that were deleted at assembly: M02:13-15, M03 §13 (:962-976),
  M04:3-4, 10, 18-19, M06 §8 (:913-915), M07:104, M08:7, M09:22-23, 91.
- Proposed, once per doc:
  - Replace the status clause with "proved (no `sorry`); helper files: … (list as in F-22)".
  - Add under the header: "Lean blocks show the statements; all are proved. The routes actually implemented, where
    they differ from the text, are marked *Implemented:* below (source: `impl_notes/<module>.md`)."
  - Delete the paragraphs about the upstream-interface sections, or replace them with "imported (see `IMPORTS.md`)".

### M00 — `M00_Defs.md`

**F-29 (Medium) — The §1 table lacks `IsLogRegularPartitionWithDensity`.**
- The definition was added at I-01 (`Defs.lean:313-321`) and is a hypothesis of the main statement
  `theorem2_i_of_densityBound`. The table ends at `M00_Defs.md:39` with `IsLogRegularPartition`.
- Proposed row: "| `IsLogRegularPartitionWithDensity ψ` | p. 802 ("the smoothness of `ψ`") | `IsLogRegularPartition` plus
  `ψ' ≤ K/d_n` on each cell `[t_{n-1}, t_n]` (the local density bound the proof of Theorem 2 (i) uses; N-22). |"

**F-30 (Medium) — §2 reports a phase-2 plan that has been overtaken.**
- `M00_Defs.md:51-53` (PaleyWienerThm): "To be proved in phase 2 from Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ`; …".
  Proposed: "Phase 2 (P1, `Cited/PaleyWiener*`): assembly `paleyWiener_holds` proved; parts 1 and 2 are scaffolds."
- `M00_Defs.md:79-80` (DSPerturbation): "Proof (phase 2): Bernstein's inequality and Taylor expansion."
  The proof is `dsPerturbation_of_paleyWiener : PaleyWienerThm → DSPerturbation` (`Cited/DSPerturbation.lean:330`),
  by `L²` Bernstein plus FTC and Cauchy–Schwarz plus finite overlap. The file header says "No Taylor series"
  (`Cited/DSPerturbation.lean:6-8`). Proposed: "Proved in phase 2 from `PaleyWienerThm`
  (`dsPerturbation_of_paleyWiener`): `L²` Bernstein inequality, FTC and Cauchy–Schwarz on
  `f(γ+δ) − f(γ) = ∫ f'`, finite overlap of `[γ − L, γ + L]`."
- `M00_Defs.md:75-77` (JohnNirenberg): add "Proved in phase 2 (`johnNirenberg_holds`, `Cited/JohnNirenberg.lean`),
  with `C = 2`, `c = log 2/4`, by a dyadic stopping-time argument."

**F-31 (Medium) — §3 does not mention the second Theorem 2 (i) statement or `hmono`.**
- `M00_Defs.md:94-95`.
- Proposed: "`theorem2_i`: '`ψ'(x) = 1/O(x)`' is `ψ'(x) ≥ c/x` for large `x` (`hlow`, unused by the proof, N-26);
  in addition `hmono`: `ψ'` eventually nonincreasing (N-22). `theorem2_i_of_densityBound`: the hypotheses the
  proof uses, `IsLogRegularPartitionWithDensity`, without `hlow`. `theorem2_ii`: '`ψ'(x) = o(1/x)`' is
  `x ψ'(x) → 0`; `hPW` is not used (I-02)."
- Also worth one sentence, from R2-11 (never applied): `IsPhaseFunction` requires `E(x)e^{iφ(x)} ≥ 0`, not just real
  as in the paper. The two differ by a shift by `π`. The level sets `{φ ∈ α + πℤ}` are the same, so `TheoremE` is
  still implied by the paper's Theorem E.

### M01 — `M01_PW.md` (PW toolkit)

Mechanical check: all 55 Lean blocks match the code. The exception is the obsolete `PaleyWienerThm` proposal of §7.

**F-32 (High) — M01 §0, §1.7 and §7 describe the obsolete `PaleyWienerThm`.**
- `M01_PW.md:21-41` says the cited `Prop` is `MemPW f ↔ ∃ g, … ∧ pwNormSq f = 2π‖g‖²` with a vacuous `⇐`.
- `M01_PW.md:309-311` says `exists_pwFT` is "`(hPW f).1 hf` … Literally `hPW`".
- `M01_PW.md:320-357` gives a five-step Parseval/density proof of `memPW_pwFT`.
- `M01_PW.md:727-744` (§7) "requests" the strengthening.
- The frozen `Defs.lean:181-187` is already the strong form in part 1, with no norm identity in part 2.
  `memPW_pwFT` is `hPW.1 g hg` (`PW/Basic.lean:286-290`). `exists_pwFT` combines `hPW.2` with `hPW.1`
  (`PW/Basic.lean:277-281`).
- Proposed:
  - Replace §0 by: "`PaleyWienerThm` (Defs) is the Paley–Wiener–Plancherel theorem. Part 1 gives `F_g ∈ PW` and
    `‖F_g‖² = 2π‖g‖²` for every `g ∈ L²(−π,π)`. Part 2 represents every `f ∈ PW` as `F_g` (without a norm identity,
    which follows from part 1). `memPW_pwFT` is `hPW.1`; `exists_pwFT` is `hPW.2` plus `hPW.1`."
  - Replace the proof at :309-311 by "`obtain ⟨g, hg, hrep⟩ := hPW.2 f hf`; `f = pwFT g` by `funext`; norm identity
    `(hPW.1 g hg).2`."
  - Replace :320-357 by "*Proof.* `hPW.1 g hg`."
  - Mark §6 item 4 (:722-723) and §7 as "Resolved before the freeze (option A, part 2 without norm identity)".
- Same staleness in M10 (F-62) and in the docstrings at `PW/Basic.lean:275, 283-285` (F-12).

**F-33 (Medium) — Interface lemmas present in the code but absent from M01.**
- `plancherelPolya_tail_union` (`PW/PlancherelPolya.lean:378`; added at I-01; consumed by
  `Theorem1/Sufficiency/Limit.lean:94`).
- `sampleSum_mono`, `sampleSum_eq_tsum_indicator` (`PW/PlancherelPolya.lean:235-242`).
- `MemPW.eq_zero_of_pwNormSq_eq_zero` (`PW/Basic.lean:524`), `IsSeparated.finite_inter_Icc` (`PW/Basic.lean:505`),
  `IsSepBy.mono` (`PW/Basic.lean:38`).
- Proposed: add a list "Added during assembly/implementation" to M01 §1/§3 with these statements.
  For `plancherelPolya_tail_union`: "the tail bound of `plancherelPolya_tail`, uniformly over unions `A ∪ B` of two
  `δ`-separated sets".

**F-34 (Low) — Dead code presented as part of the route.**
- `pwFT_sub`, `tsum_enorm_sq_pwFT_int`, `l2piSq_eq_of_pwFT_eq`, `fourierCoeffOn_pwFT` (`PW/Basic.lean:102-217`) and
  `MemPW.isH2Upper_mul_exp`, `MemPW.lintegral_mul_exp_le` (`PW/Bounds.lean:157,183`) are proved but used nowhere.
  The first four were the §1.7 route, now obsolete. Mark them "(proved; unused)", or delete them in a clean-up.
- The "Used by" header (`M01_PW.md:13-15`) is wrong:
  - M02 does not use `mul_div_sub`, `isH2Upper_mul_exp` or `pw_deriv_bound`;
  - M04 does not use `pw_eval_lower`;
  - `pw_normal_family` is used only by M07 (`Perturbation.lean`).
- The sharpness claim "constant exactly `1`" (`M01_PW.md:411, 419-420, 725`; docstring `PW/Bounds.lean:97`) should
  read: "constant `1`, sharp only at `y = 0` (the best constant is `sinh(2π|y|)/(2π|y|)`); the exponent `2π|y|` is
  sharp". This is R2-03, never applied.
- Two route details. `pwNormSq_pwBump_pos` (:505) is proved through `MemPW.eq_zero_of_pwNormSq_eq_zero`
  (`PW/Bounds.lean:304`), not by a local lower bound. `pw_complete` re-indexes as `m ↦ f(m+N) − f n` (R2-04).

### M02 — `M02_HB.md` (HB, phase, `H(E)`, evident fact)

Mechanical check: all 42 Lean blocks match.

**F-35 (Medium) — The header file list and import chain are wrong.**
- `M02_HB.md:3-8`: "Import chain: `Defs ← Basic ← Phase ← DeBranges ← Comparable`, `H2` is imported by `DeBranges`",
  and "(contains the temporary upstream-interface section)".
- Actual imports: `Phase ← Basic, Hopf`; `H2 ← Defs, MeanValue`; `DeBranges ← Phase, H2, PW.Complete`;
  `Comparable ← DeBranges, MeanValue`.
- The helper files are not mentioned: `HB/Hopf.lean` (`hopf_trig`, `hopf_boundary`) and `HB/MeanValue.lean`
  (`area_ge`, `circle_lintegral_ge`, `lintegral_strip`).
- Proposed: replace the import-chain sentence by the four lines above and list the two helper files.

**F-36 (Medium) — §5.1 `IsHB.phaseDeriv_nonneg` takes a route the code does not.**
- `M02_HB.md:411-423` uses a one-sided extremum of `D(y)`.
- The code proves both `phaseDeriv_nonneg` (`HB/Phase.lean:314`) and `phaseDeriv_pos_of_exists_lt` (`:333`) from
  `IsHB.phaseDeriv_pos_or_eventuallyEq` (`:246`): the normal form of `Θ − c` at `x` plus `hopf_boundary`.
- Proposed: insert before the proof "*Implemented:* both `φ' ≥ 0` and the strict case come from the dichotomy
  `IsHB.phaseDeriv_pos_or_eventuallyEq` (either `E^* = cE` near `x`, so `φ'(x) = 0`, or `φ'(x) > 0`), proved with
  `hopf_boundary` (`HB/Hopf.lean`). The `D(y)` argument below is a valid alternative for `≥ 0` but is not formalized."
- `M02_HB.md:713` lists `HasDerivAt.norm_sq` and `IsLocalMaxOn…` among the Mathlib names used; they are not used.

**F-37 (Medium) — §4 `exists_isPhaseFunction` takes a route the code does not.**
- `M02_HB.md:344-359` differentiates `‖E‖`.
- The code (`HB/Phase.lean:71-140`) shows that `M = E·e^{iΦ − R}`, with `R = ∫₀ˣ Re(E'/E)`, has derivative `0`, so
  `E = |E(0)| e^{R} e^{−iΦ}`. It never differentiates `|E|` (`impl_notes/hb.md:14`).
- Proposed: replace steps (2)–(4) with that sentence.

**F-38 (Medium) — §10 contradicts NOTEBOOK N-05.**
- `M02_HB.md:610`: "the first `|f(x)|` is missing its square".
- N-05 (print-checked) and M02 §12.4 (:684) say it is the *middle* `sup |f(x)|` over `‖f‖²_E ≤ 1`.
- Proposed: "the middle `sup |f(x)|` is missing its square (NOTEBOOK N-05)".

**F-39 (Low) — Other M02 discrepancies.**
- §1.2 (:119-135) says "area average of `G`, then Cauchy–Schwarz". The code does Cauchy–Schwarz on circles, then
  polar coordinates (`MeanValue.area_ge`).
- The same sub-mean-value inequality is proved twice: `enorm_sq_le_lintegral_ball` (`PW/PlancherelPolya.lean:75`)
  and `enorm_sq_le_setLIntegral_ball` (`HB/H2.lean:117`).
- §11 Step 2 (:654): delete "For `s = 0`: `L(f,0) ≤ C² M₁`". The code uses only lines `0 < |s| < 2`, because `{0}` is
  null (`HB/Comparable.lean:137-160`; `impl_notes/hb.md:16`).
- §0 (:32) lists `hPW` for `phaseDeriv_mul_sq_ge`. It is unused there and in `memPW_of_memHE`
  (`HB/DeBranges.lean:216`, `HB/Comparable.lean:302`); add "(unused; kept, statement frozen)".
- Interface lemmas added at assembly are missing from §0: `IsStrictHB.mul_isHB`, `IsHB.rotate`,
  `IsPhaseFunction.rotate`, `HEEqPW.exists_phase_data` (`HB/DeBranges.lean:193`), `countable_real_zeros`.
- Code module docstrings cite the wrong sections:
  - `HB/DeBranges.lean:8` says "§6–§8"; the file holds §7–§10.
  - `HB/Comparable.lean:7` says "§9"; it should say §11.
  - `HB/Phase.lean:7` omits §6.

### M03 — `M03_Necessity.md`

Mechanical check: 63 of 64 Lean blocks identical. The exception is `IsSeparated.finite_inter_Icc`, whose binder
`r` became `R` and which moved to `PW/Basic.lean`.

**F-40 (Low) — M03 is accurate apart from scaffold wording.**
- `M03_Necessity.md:25-27`, `:869` ("The proof in the scaffold is complete modulo the lemmas above") and §13
  (:962-976) are stale.
- `:21` "**new name requested** `MemPW.eq_zero_of_pwNormSq_eq_zero`": it now exists in `PW/Basic.lean:524`.
- Constant: `:141` "`1/(1+x²) ≤ 5/(1+n²)`". The code proves `≤ 3/(1+n²)` (`Theorem1/Necessity/Sep.lean`,
  `one_add_sq_floor_le`). Both are valid.
- Helpers not mentioned: `Necessity/Sep.lean`, `PWFun.mk`, `PWFun.val_mk`, `IsSeparated.eventually_le_abs`.
- Proposed header line: "All declarations proved; helper file `Theorem1/Necessity/Sep.lean`. §13 is obsolete:
  the interface block was replaced by imports (`IMPORTS.md`)."

### M04 — `M04_Sufficiency.md` (Theorem 1 ⇐, `theorem1`, Corollary 1, remark p. 797)

Mechanical check: 32 of 35 blocks identical. `sepBy_mono`/`sepBy_subset` (:114-122) do not exist; use
`IsSepBy.mono`, as :38 already says. `sampleSum_mono`/`sampleSum_union_le` use binders `Λ₁ Λ₂`.

**F-41 (Medium) — M04 relies on a lemma that was never created.**
- `exists_HB_of_sampling` at `M04_Sufficiency.md:29` and `:708`. The code uses `exists_E hPW hC hs`
  (`Theorem1/Necessity.lean:434`, used at `Corollary1.lean:274`). Its conclusion has the extra conjunct
  `∀ f, MemHE E f ↔ MemPW f`, and it needs no separation hypothesis.
- README:141 and IMPORTS.md:157 already note this.
- Proposed:
  - :29 "the new name `exists_HB_of_sampling`" → "`exists_E` (`Necessity.lean`)".
  - :708 "`exists_HB_of_sampling` (M03) gives" → "`exists_E hPW hC hs` (M03) gives".

**F-42 (Medium) — The construction of `exists_realFactor` differs.**
- `M04_Sufficiency.md:183-195`: enumerate `a_n`, choose `p_n` with `m_n 2^{−p_n} ≤ 2^{−n}`, use Rudin 15.8.
- The code (`Theorem1/Sufficiency/RealFactor/{Elem,LUProd,Zeros,Product,Main}.lean`):
  - It indexes the nonzero real zeros by a subtype `Zr F`, with `genus a = m(a) + rank(a) + 1`, where `rank` is
    an injection into `ℕ` (`RealFactor/Product.lean:23-43`).
  - The bound is `‖E_p(w)^m − 1‖ ≤ 4m‖w‖^{p+1}` for `‖w‖ ≤ 1/2` and `2m‖w‖^{p+1} ≤ 1`, proved from the tail of the log
    series (`RealFactor/Elem.lean:36,65`).
  - Convergence goes through the abstract `LUProd`.
  - `G = F/S` is extended by `limUnder` and shown entire by the local factorisation `quotG_local`
    (`analyticOrderAt`).
- Proposed: add "*Implemented:*" with these four points. Both routes need no separation.

**F-43 (Medium) — M04 asserts a source error that NOTEBOOK N-10 withdrew.**
- `M04_Sufficiency.md:378`: "(derivatives, not the phases as printed on p. 796)".
- Issue 4 at `:735-737`: "p. 796, '`φ_{EF} = φ_E + φ_F ≥ φ_E`' … (*certain*)".
- The print and the tex have primes (`literature/ArxivOrtega.tex:515`). N-10 is "*Withdrawn*".
- Proposed: at :378 "(as printed on p. 796)"; Issue 4 "*Withdrawn*: OCR artifact; the print has
  `φ'_{EF} = φ'_E + φ'_F ≥ φ'_E` (NOTEBOOK N-10)". The same applies to README:241 (F-28).

**F-44 (Medium) — Routes and constants of three Theorem 1 ⇐ lemmas differ.**
- **`HEEqPW.phase_tendsto` (`:279-300`).**
  - The doc uses `eventually_not_exceptional`, `g` with `g(0) = 1`, and a finite-part/tail split.
  - The code (`Theorem1/Sufficiency/Phase.lean:71-150`) uses `Suff.exists_not_exceptional` and `pwBump`. The norm
    identity gives a uniform lower bound `ε₀ ≤ sampleSum Γ (g(· − t))` (`translate_lower_bound_aux`). The level set
    is bounded on one side (`bddAbove_phaseLevel`), and the Plancherel–Pólya tail (`translate_tail`) gives a
    contradiction for far translates. There is no `ℤ`-indexing and no finite-part split.
- **`levelSet_limit` (`:393-436`).**
  - The doc uses `plancherelPolya_tail` twice and gets `C₀(T + 3η)`.
  - The code (`Theorem1/Sufficiency/Limit.lean:94`) uses `plancherelPolya_tail_union` once and gets `C₀(T + 2η)`,
    with the limit taken along `η_m = (m+1)⁻¹` in `ℝ≥0∞`.
- **`levelSet_separated` (`:257-260`).**
  - The doc has `1/max(Θ,1)`, `Θ = √(C_B K₁)`.
  - The code (`LevelSet.lean:53-55`) has `1/(Θ+1)`, `Θ = √((πe)² max(K,0))`, `K = π/(c c₁)`.
- Proposed: one "*Implemented:*" line per lemma, with these constants. Source: `impl_notes/sufficiency.md:15-19`.

**F-45 (Low) — Other M04 discrepancies.**
- **Rotation lemmas.** `:609` "*New M02 lemmas used below* (statements in `Corollary1.lean`)". `IsHB.rotate` is in
  `HB/Basic.lean:234` and `IsPhaseFunction.rotate` in `HB/Phase.lean:433`. Only `HEEqPW.rotate` is in
  `Corollary1.lean:140`, proved by `Corollary1/Rotate.lean`.
- **Corollary 1, step 2.** Uses `exists_not_exceptional` (`Corollary1.lean:78`).
- **Corollary 1, step 3.** The code shows `φ_E(γ_{k+1}) − φ_E(γ_k) ≥ π`, not `= π`, because the enumeration
  `exists_levelSet_enum` is abstract (`Corollary1.lean:96-104`; `impl_notes/sufficiency_cor1_landau.md:10-12`).
- **`isSampling_of_isCompleteInterpolating`.** Uses `LinearMap.continuous_of_seq_closed_graph`
  (`Corollary1/ClosedGraph.lean:140`).
- **`kernel_orthogonal`.** Uses `uv ≤ (u²+v²)/2` (`Corollary1/Kernel.lean:88`), not Hölder.
- **"Used by" (`:31-32`).** It says "M06/M07/M09 (`theorem1_sufficiency` …)". In fact only `Corollary2.lean:708` (M07)
  calls `theorem1_sufficiency`. M06 imports `Theorem1.Sufficiency` for helpers. M09 does not import it.
- **`Suff.sampleSum_mono` (`:233`).** It is now `sampleSum_mono`.
- **Stale remarks.** Delete "(Proved in the scaffold …)" at `:124, 145, 485, 515, 533, 574`.

### M05 — `M05_Landau.md`

**F-46 (OK / Low) — M05 matches `Landau.lean` exactly.**
- All 6 blocks are identical.
- The constants agree: `M = max M₀ 1`, `A₁ = 2M/c`, `L₀ = max 2 (C+1)`, `A = 2A₁`,
  `B = max(2(K+D), K L₀ + D)`, `K = 1 + 1/q`, `D = 1`, and the final `B + 1`.
- Only cosmetic: the `:= sorry` placeholders, and the fact that `hD` of `osc_bound_of_JN` is unused. Add
  "(`hD` is not needed)".

### M06 — `M06_LogExample.md`

Mechanical check: 67 of 68 blocks identical. The exception is `landau_sharp`.

**F-47 (High) — M06 states and proves the superseded `landau_sharp`.**
- `M06_LogExample.md:891-911` gives `… ∧ ¬ ∃ B, ∀ a b, a < b → ofReal (b − a − B) ≤ …`, with the proof
  "`log R ≤ B + 2`".
- `:961` says "Formalised as `landau_sharp` in the weakest reasonable form (no constant `B` works)".
- The main statement (I-01; `LogExample.lean:2064-2099`) is the strengthened `∀ A < 1, ¬ ∃ B, … − A·posLog(b − a) − B …`.
- Proposed:
  - Replace the block by the text of `comparator/statements.lean:77-82`.
  - Replace the proof by "Take `a = 0`, `b = R = e^x` with `x = (|B| + C + 1)/(1 − A) + 1` (`C` from
    `logExample_count`). Then `R − A x − B ≤ ncard ≤ R − x + C`, i.e. `(1 − A)x ≤ B + C`, a contradiction."
  - At :961, write "in the strengthened form: no coefficient `A < 1` of `log⁺(b − a)` works (NOTEBOOK I-01)".

**F-48 (Medium) — Several M06 proofs take other routes** (`impl_notes/logexample.md:6-40`).
- **`not_memHE_sAlpha` (`:807-811`).**
  - Doc: disjoint intervals `J_k`.
  - Code: `∫_0^T cos²φ ≥ (m₁T/2 − 1/2)/M₁` (`LogEx.integral_cos_sq_phase_ge`, `LogExample/Phase.lean:11`; used at
    `LogExample.lean:1868`). This needs `phaseDeriv E` continuous.
- **`multU_model` (`:545`).** Doc: `Complex.log`. Code: the real primitive `logPrimD` (`LogExample/Potential.lean:108`).
- **`integral_log_mul_sub_one_eq` (`:612`).**
  - Doc: absolutely continuous integration by parts on `[ε,R]`.
  - Code: `integral_eq_of_hasDerivAt_off_countable_of_le` on `[−R,R]` (`LogExample.lean:1300`).
- **`abs_integral_posLog_mul_logKernel_le` (`:652`).**
  - Doc: the `Q_R` splitting.
  - Code: integration by parts with the primitive `log D(t)/2 − log t` (`LogExample/Potential.lean:501, 574`).
- **`integral_abs_rho_logKernel_le` (`:672-682`).**
  - Doc: three regions.
  - Code: `|K| ≤ 1/|t − z| + 1/|t|` and Young's inequality `uv ≤ u³/3 + 2v^{3/2}/3`.
- **Strip estimate.** The exact constant is `20π`, via `∫ log(1+1/s²) = 2π`.
- `LogExample/Potential.lean` is missing from both the doc and `impl_notes/logexample.md:3-4`.
- §8 (`:913-915`) "Upstream interface used (temporary declarations …) … signatures are my guesses" should become
  "Upstream lemmas used (imported)".

**F-49 (Medium) — The κ normalisation is misdescribed in M06 and M07.**
- Places:
  - M06:38 "It is removed by `E ↦ E e^{−κ z}`";
  - M06:752-760 "the normalisation `E = E₀ e^{−κ z}` … is now inside M07";
  - M07:53-54 "after the normalisation `E ↦ e^{−κ z} E`";
  - code docstring `Construction.lean:23`.
- The construction is `compEκ = e^{−κz}(A − i e^{κ/2} B)` (`Construction.lean:183-187`). README §4 explains why the
  plain twist has the wrong phase.
- Proposed for all four: "removed by `E_κ = e^{−κ z}(A − i e^{κ/2} B)` (`compEκ`, M07); `e^{−κ z}(A − iB)` has the
  right modulus but not the right phase".

### M07 — `M07_Corollary2.md` (construction, perturbation, Corollary 2)

Mechanical check: all 79 blocks identical. The only differences are the binder renaming `β → θ` in the rotate
lemmas and their move to `HB/*`.

**F-50 (Medium) — §2.5 cites a lemma whose use would create an import cycle.**
- `M07_Corollary2.md:566`: "`e^{U(z − 1/2)}` is bounded above and below there (`abs_multU_le_of_bdd`, §3.1)".
- `abs_multU_le_of_bdd` is in `Corollary2.lean`, which imports `Construction.lean`.
- The code uses `expU_bounds_on_compact` (`Construction.lean:886`): `Comparable.comparable_on_compact` (an entire
  function with simple zeros has `|F| ≃ min(1, d(z, Z))` on compacts) plus `norm_genA_comparable`. No continuity of
  `U` is used.
- Proposed: replace "(`abs_multU_le_of_bdd`, §3.1)" by "(`expU_bounds_on_compact`, via
  `Construction/Comparable.lean`; no continuity of `U`)".

**F-51 (Medium) — §2.4, §2.6 and §2.7 take other routes** (`impl_notes/construction.md:8-29`).
- **§2.4 `tendsto_polyB` (`:507`).** "Small circle about `a`" → `Limits.tendstoLU_of_mul_prod` (maximum modulus on
  a large circle).
- **§2.6 (`:581`).** "Take `N` from `exists_gap_index`" → `Gaps.exists_gap_index_strong` (gap `> 3/4`), which gives
  `dist(Γ, Γ_B) ≥ η > 0` (`exists_eta`; `Construction.lean:1158, 1214, 2015`).
- **§2.7(b) (`:665-670`).** The connectedness argument is factored into `Rigidity.phase_drift_small`
  (`Construction/Rigidity.lean:112`), applied through `tendsto_compEκ_translate`.
- **§2.7(c) (`:686-689`).** Strictness is proved via `IsHB.isStrictHB_or_fstar_eq` (`E^* = cE` would force `A ≡ 0`) and
  `IsPhaseFunction.strictMono_of_isStrictHB` (`isStrictHB_compEκ`, `Construction.lean:1413`), not by the identity
  theorem.
- **§2.7(a).** It is `Translate.translate_limit`: nonvanishing of the limit at `θ + 1/2`, then `sin_lower`, a
  removable singularity and Liouville. Consistent; naming only.
- **The PolyHB argument.** It goes through arguments (F-18), not partial fractions.

**F-52 (Medium) — Three proof routes in §3 differ** (`impl_notes/corollary2.md:16-34`).
- **`continuous_multU_of_bdd` (`:773-775`).**
  - Doc: dominated convergence.
  - Code: Vitali (`tendsto_Lp_finite_of_tendsto_ae` + `unifIntegrable_of`, `Corollary2/UCont.lean:529-589`), with a
    window split. This is needed because `g` is only measurable.
- **`multU_one` (`:780-788`).**
  - Doc: explicit computation.
  - Code: a corollary of `log_norm_eq_multU_add_affine` for `f = e^{−iπz}`, plus evenness and `U_1(0) = 0`
    (`Corollary2/LogNorm.lean:214`).
- **`log_norm_eq_multU_add_affine` (`:913-924`).**
  - Doc: "`f'/f` has a primitive `L`".
  - Code: Schwarz reflection of `Φ = e^{iφ(0)} f e^{−P}`, real on `ℝ` (`exists_entire_reflection`,
    `Corollary2.lean:143`, via the Morera argument of `Corollary2/Reflection.lean`). Then `Φ̂ = e^{G}` with `|Re G| ≲ |z|^{3/2}`, so `G` is affine (Borel–Carathéodory,
    `Corollary2/Affine.lean`) and the slope is real.
- **Frozen definitions.** `argUp`, `potC` are duplicated as `argUp'`, `potC'` in the helper files (transfer by `rfl`).
- Proposed: one "*Implemented:*" line per lemma.

**F-53 (Low) — M07 file lists and stale claims.**
- `:3-6` lists three files, and says they "compile with `lake env lean` directly". Add the helper files from F-22.
- `:104` "Upstream interface (declared at the top of the file …)" is obsolete.
- §1.1 places `sampleSum_mono` and `IsSeparated.finite_inter_Icc` in `Perturbation.lean`; they are in `PW/*`.
- §3.6 places the rotate lemmas in Corollary 2; they are in `HB/*`.
- `:1161` "The three files are independent of `FourierFrames.HB.*` except through the declared upstream lemmas" is false:
  `Construction.lean` imports `HB.Phase`, and `Corollary2.lean` imports `HB.Comparable`.
- `:1169` "compile with only `declaration uses 'sorry'` warnings" should read "proved; no `sorry`".
- §1.3: `hsep'` of `isSampling_of_replace_finite` is unused (`Perturbation.lean:274`).
- §3.1: `multU_compact_sub_linear` holds for all `z` (`Im z ≥ 0` unused).

### M08 — `M08_Theorem2i.md`

Mechanical check: statement blocks match, but the files moved (see F-55).

**F-54 (High) — The "READ FIRST — status" box says `theorem2_i` has no proof.**
- `M08_Theorem2i.md:13-24`: "`theorem2_i` (statement identical to `comparator/statements.lean`, no honest proof from
  the paper's argument). **Requested change to M00 / `statements.lean`:** add `DensBound` …".
- Both main statements are proved:
  - `theorem2_i` has `hmono` and goes through `RegData.densBound_of_antitoneOn` (`Theorem2i.lean:63, 141-150`);
  - `theorem2_i_of_densityBound` (`Theorem2i.lean:132-139`) uses the new `IsLogRegularPartitionWithDensity`.
- The same staleness appears in the code docstring `Theorem2i.lean:10-15` (F-12).
- Proposed box:
  "**Status (final).** The paper's argument needs the local bound `DensBound` (`ψ' ≤ K/d_n` on `[t_{n−1}, t_n]`, §A),
  which the printed hypotheses do not imply. Two main statements are proved:
  - `theorem2_i_of_densityBound`, under `IsLogRegularPartitionWithDensity` (regular partition plus `DensBound`;
    no `hlow`);
  - `theorem2_i`, under the printed hypotheses plus `hmono` (`ψ'` eventually nonincreasing), which implies
    `DensBound` (`RegData.densBound_of_antitoneOn`).

  Both reduce to `theorem2_i_of_regular (h : RegData ψ t C M) (hK : DensBound ψ t K)`. Whether (i) holds for spiky
  `ψ` is open (N-22)."
- `:23` cites "§A.4", which does not exist; use "§A".

**F-55 (Medium) — The conclusion, the requested change and the file layout are stale.**
- `:338-339` "`theorem2_i` follows from `theorem2_i_of_regular` once `DensBound` is available": replace by the two
  reductions `RegData.of_isLogRegularPartitionWithDensity` and `RegData.of_isLogRegularPartition` +
  `densBound_of_antitoneOn`.
- `:359` and `:408-412` request a clause in `IsLogRegularPartition`. Instead, a separate definition and a new main
  statement were added (I-01). Mark them "Resolved (I-01)".
- `:3`, `:7` ("`corollary2` copied … upstream-interface section") and `:54` are stale. Proposed:
  "**Lean:** `Theorem2i.lean` (§7 glue, main theorems) and `Theorem2i/`:
  - `Basic` (§1–2), `Product` (§3), `PhaseDecay` (§4), `Cells`/`CellsAux` (§5);
  - `Taylor`, `CellAux`, `BelowAbove`, `FarAux` (§6.2–6.6), `NearAux`/`Near` (§6.7);
  - `Counting`/`Riemann` (§6.8, finset forms), `Estimates` (statements of §6.4–6.8), `Assembly` (§6.9).

  `Basic` imports `FourierFrames.Corollary2`."

**F-56 (Medium) — The §6.8/§6.9 route and one constant differ.**
- **Route.**
  - Doc (`:311-320`): `card_near_le`, `sum_far_le`, `sum_far_im_le`, then `exists_bound_cellTerm`.
  - Code: `exists_approx` (`Assembly.lean:512`) uses `D3.exists_finset_bound` (`:483`), built from
    `RegData.finset_card_near_le`/`finset_sum_far_le` (`Counting.lean:95,137`) and `finset_sum_far_im_le`
    (`Riemann.lean:58`) through the `K0_finset_*` wrappers (`Assembly.lean:23-49`).
  - The `tsum` forms are corollaries that nothing uses (F-10).
  - Proposed: "Implemented in uniform finset form (`RegData.finset_*`, `D3.exists_finset_bound`), because real
    `tsum`/`ncard` statements hold trivially when the series diverges or the set is infinite."
- **Above sum.**
  - Doc (`:272-274`): `(1+C)²/(2|z|)` and `∑_{Above}|j_n| ≤ (log(1+C)+1)(1+C)²`.
  - Code: telescoping gives `(1+C)/(2|z|)` and `(log(1+C)+1)(1+C)` (`above_sum`, `Assembly.lean:92`; `sum_Tabove`,
    `:392`).
  - Proposed: "telescoping `d_n/t_{n−1}² ≤ (1+C)(1/t_{n−1} − 1/t_n)`: `∑_{Above} d_n/t_{n−1}² ≤ (1+C)/(2|z|)`, so
    `∑_{Above}|j_n| ≤ (log(1+C)+1)(1+C)`".

**F-57 (Low) — Smaller M08 differences.**
- **The final constant `B`.**
  - Doc: `:318`, `:322-323`.
  - Code (`Assembly.lean:486-488`): `B = max 0 (a1/2 + a2(1+C)/2 + cnear·3(1+K₀²)M + c1·3(1+K₀⁻²)M + (cnear + c1/K₀²) + 2·(9π/4))`.
- **§4, `φ_f' → 0`.**
  - Doc (`:157-186`): a four-way split.
  - Code (`PhaseDecay.lean:356, 409`): the termwise bound `P_n ≤ E q_n` with `q_n = d_n/((x − t_n)² + d_n²)`, then
    finset sums of `q` on four ranges.
- **The value of `K` (`:355-356`).**
  - Doc: "with `K = C`".
  - Code (`Theorem2i.lean:83`): `K = max(C, max(B₀, 0) · t_{N+1})`, because `ψ'` is antitone only beyond `X`.
- **A stale docstring.** `Theorem2i/Basic.lean:77` says `DensBound` is "(NOT a hypothesis of `theorem2_i`)". It is
  part of `IsLogRegularPartitionWithDensity` and follows from `hmono`.

### M09 — `M09_Theorem2ii.md`

Mechanical check: every statement block (§0.3, A1–A6, B2–B4, C1, C3, D1, D2, E1, main) matches verbatim.
`lemma3_estimate_uniform` (`Lemma3Uniform.lean:132`) matches §0.3.

**F-58 (Medium) — M09 states an equivalence that NOTEBOOK N-38 denies.**
- `M09_Theorem2ii.md:500-503`: "`ψ' = o(1/x)` is *equivalent to the existence, for every `s`, `η`, of arbitrarily far
  windows* …".
- N-38 (referee R5) says "implied by, not equivalent to". The code uses `hsmall` only through `exists_window`
  (`Theorem2ii.lean:1160-1165`).
- Proposed: "`ψ' = o(1/x)` *implies* (the converse fails) the existence, …".

**F-59 (Medium) — The M09 header, interface and §10 are stale.**
- `:3` says "(compiles, only `sorry` warnings)". `:22-23` and `:91` say `lemma3_estimate_uniform` "is declared in the
  'Upstream interface' section of the scaffold". §10 (`:530-533`) is a request to other modules.
- In fact `lemma3_estimate_uniform` is proved in `Lemma3Uniform.lean:132`, via the copied
  `exists_abs_sum_multErr_sub_log_infDist_le_uniform` with `K` fixed from `(a, b)`.
- Wrong OCS name at `:18` and `:146`: `OCS.integrable_multU_integrand` does not exist; the name is
  `OCS.integrable_multUIntegrand`.
- Proposed header: "**Lean:** `Theorem2ii.lean` + `Theorem2ii/{Window,UOne,Ramp,Mass,Cells}.lean`; no `sorry`;
  `lemma3_estimate_uniform` proved in `Lemma3Uniform.lean`." Mark §10 "done".

**F-60 (Medium) — Routes A2 and A4 differ** (`impl_notes/theorem2ii.md:16-27`).
- **A2 `multUIntegrand_one` (`:145-169`).**
  - Doc: the explicit antiderivative `A(s)`.
  - Code (`Theorem2ii/UOne.lean`): reduces to `x = 0` by a shift (`shift_eq`, `abs_shift_le`, an `O(x²/R)` error),
    then uses the antiderivative `t log(t²+c²) − 2t log t + 2c arctan(t/c)` (`:139`).
- **A4 `rampPot_estimate` (`:191-206`).**
  - Doc: three cases with `log 6`.
  - Code (`Theorem2ii/Ramp.lean:100, 178`): rescales to `∫_1^2 log|1 − ξ/s|`, splits `|ξ| ≤ 3` / `|ξ| ≥ 3`, and uses
    `min(0, log|v|)` with integral `−2` and `log 3 < 1.11`.
- **Parsing of the A4 statement (`:188-189`; `Theorem2ii.lean:190-192`).** In
  `|(1/a) * ∫ t in a..2*a, log ‖…‖ − log (max …)| ≤ 4` the `∫` binder extends over `− log(max …)`. The statement is
  therefore `(1/a)∫(g − ℓ)`. This equals `R − ℓ` because the interval has length `a`, so it is harmless.
  `T2ii.rampPot_estimate'` (`Ramp.lean:217`) is the parenthesised form.
  - Proposed: add after :189 "(Lean parses this as `(1/a) ∫_a^{2a} (log|1 − x/t| − ℓ)`, which equals `R − ℓ`.)"

**F-61 (Low) — M09 constants.**

| where | doc | code |
|---|---|---|
| points per unit cell (`:348`) | at most `2 + B` | `⌊1+B⌋₊ + 1` (`Theorem2ii/Cells.lean:92`) |
| constant of D2 (`:387`) | — | `C = 20(⌊1+B⌋₊+1)C₁²` (`Theorem2ii.lean:961`) |
| intermediate value lemma (`:425`) | `intermediate_value_Ici` | `intermediate_value_Icc` (`Window.lean:85`) |
| window length (`:59`) | `a₂ − 3 = x₀e^{s}` | E1 and the code use `s' = max(s+1, 3)` |

### M10 — `M10_Frames.md`

The three statement blocks and the main proof match `Frames.lean:16-76` line by line:
- `A' = K·A`, `A = A'/K` with `K = (2π).toNNReal`;
- `exists_pwFT`, `memPW_pwFT`, `memL2pi_reflect`, `l2piSq_reflect`, `tsum_fourierCoeff_eq_sampleSum`.

**F-62 (Medium) — The PW remarks are obsolete (same cause as F-32).**
- `M10_Frames.md:3`: "compiles with `sorry` only".
- `:69`: "(M01, the unconditional `⇐` of Paley–Wiener, §0–§1.7 of M01)". `memPW_pwFT` takes `hPW` and *is* `hPW.1`.
- `:82-83`: "with the literal `PaleyWienerThm` of Defs.lean the latter is derived in M01 §1.7 — see M01 §0 for why
  the literal `⇐` is not sufficient".
- `:93-95` (§5): requests the strengthening, which was done before the freeze.
- Proposed:
  - :3 "proved".
  - :69 "(`memPW_pwFT`, i.e. part 1 of `hPW`)".
  - :82-83 "(i) `hPW` is used through `exists_pwFT` (part 2, with the norm identity from part 1) and `memPW_pwFT`
    (part 1)."
  - Delete §5, or mark it "Resolved before the freeze".
- Also note R2-10: `FF.fourierCoeff` shadows Mathlib's `fourierCoeff`. It cannot be renamed while the statement is
  frozen (`impl_notes/pw.md:20`).

---

## 4. `NOTEBOOK.md` (task 4)

### 4.1 Entries that no longer match the Lean

**F-63 (Medium) — N-22 names an internal lemma instead of the main statement.**
- `NOTEBOOK.md:196-199`: "**Formalization:** `theorem2_i` assumes in addition that `ψ'` is eventually nonincreasing,
  … `theorem2_i_of_regular` assumes `DensBound` directly."
- `theorem2_i_of_regular` (`Theorem2i.lean:45`) is an internal lemma on `RegData`. The main statement is
  `theorem2_i_of_densityBound` (`Theorem2i.lean:132`), with the new `Defs` predicate `IsLogRegularPartitionWithDensity`.
- Proposed:
  "- **Formalization:** two main statements.
  - `theorem2_i_of_densityBound` assumes `IsLogRegularPartitionWithDensity` (the regular partition plus `ψ' ≤ K/d_n`
    on each cell; `Defs.lean`) and not `ψ' = 1/O(x)`.
  - `theorem2_i` keeps the printed hypotheses and adds `hmono` (`ψ'` eventually nonincreasing). This covers the
    paper's example `√x` and implies the density bound (`RegData.densBound_of_antitoneOn`). Its hypothesis `hlow`
    is not used (N-26).

  Both are proved through `theorem2_i_of_regular`. Whether (i) holds without such a regularity assumption is open."

**F-64 (Medium) — N-26 and I-02 describe an end state that did not happen.**
- `NOTEBOOK.md:219-221` says the hypothesis "is kept … unless the linter forces its removal". `:339-343` (I-02)
  says the warnings are resolved "at the end … by a deliberate, recorded statement change".
- Final state: both warnings remain (`comparator/last_run.log`, F-6), and no statement was changed.
- Proposed: after the decision of F-6, append to N-26 "`hlow` is unused by `theorem2_i`; `theorem2_i_of_densityBound`
  omits it". Append the decision to I-02.

**F-65 (Medium) — N-32's genus formula is not the one formalized.**
- `NOTEBOOK.md:258-260`: "A Weierstrass product of variable genus (`p_x ≥ m_x + |x|`) works; … the formalization
  constructs it."
- The formalization uses `p_a = m(a) + rank(a) + 1`, with `rank` an injection of the real zero set into `ℕ`
  (`Theorem1/Sufficiency/RealFactor/Product.lean:23-43`; `impl_notes/sufficiency.md:21-22, 26-33`).
- The choice `p_x ≥ m_x + |x|` works only because the real zeros lie in the separated `Λ`, and `exists_realFactor`
  is stated without separation. `exists_noRealZero_hb` does not even use `E ∈ \overline{HB}`: the factorisation
  `F = SG` depends on `F` alone.
- Proposed replacement of the sentence:
  "A Weierstrass product of variable genus works. The formalization constructs it (Mathlib has no Weierstrass
  factorization theorem) for any `F ∈ \overline{HB}`, `F ≢ 0`, with `p_a = m(a) + rank(a) + 1`, where `rank` injects
  the real zero set into `ℕ`. This needs no separation. Because the zeros lie in the separated `Λ`,
  `p_x ≥ m_x + |x|` would also do."

**F-66 (Low) — N-35's last bullet understates the κ issue.**
- `NOTEBOOK.md:288-289`: "the [OS99] function carries a factor `e^{−κz}` (as does `OCS.multF`), which is harmless".
- It is harmless only with the rescaling `B ↦ e^{κ/2}B`. With a linear drift `κ`, `A` and `B = A(· − 1/2)P/Q` have
  amplitude ratio `e^{−κ/2}`, so `e^{−κz}(A − iB)` has the right modulus but the wrong phase. The formal function is
  `E_κ = e^{−κz}(A − i e^{κ/2}B)` (`compEκ`, `Construction.lean:183`). The first interface version, with a phase
  clause for every `m → 1`, was false (IMPORTS.md "Suspected false statements"; `impl_notes/construction.md:32-33`).
- Proposed: append to N-35 "… which is harmless after rescaling `B ↦ e^{κ/2}B`: the formal phase function is
  `E_κ = e^{−κz}(A − i e^{κ/2}B)`. Without the rescaling the modulus is right but the phase drifts."

**F-67 (Low) — N-17 omits the exponential normalisation.**
- `NOTEBOOK.md:142-145`: "the symmetric partial products are real polynomials with interlacing zeros … `\overline{HB}`
  is closed under locally uniform limits".
- The products converge only after multiplication by real exponential factors `e^{β + c_R z}` (N-35;
  `tendsto_polyA`, `isHB_genA_sub_lam_compB`).
- Proposed: insert "after multiplication by real exponential factors `e^{β + c_R z}` (which preserve
  `\overline{HB}`; the bare products need not converge, N-35)". The rest of N-17 is substantiated: no sign choice
  (`P ↦ −P`), and `A − iλB ∈ \overline{HB}` for every `λ > 0`.

**F-68 (Low) — In N-21 the quantity `L` is undefined, and one hypothesis of the reconstruction is not recorded.**
- `NOTEBOOK.md:185` reads "`‖f‖² ≳ a log(L)` while `∑_Λ |f|² ≲ a(1 + η² log L)`".
- Formally, `pwNormSq_testFn_ge` gives `c a₁ log(a₂/(4a₁))` and `sampleSum_testFn_le` gives
  `C a₁ (1 + η² log(a₂/a₁))`. The last steps are in `theorem2_ii` (`Theorem2ii.lean:1171-1229`).
- Proposed: "with `L = a₂/a₁` the length ratio of the window: `‖f‖² ≳ a₁ log(L/4)` while `∑_Λ|f|² ≲ a₁(1 + η² log L)`".
- Add a bullet: "The construction applies [OS99] Lemma 3 to a density that depends on the window. This needs the
  constants of Lemma 3 to depend only on the bounds `a ≤ m ≤ b`. That is true by inspection of the proof, but not
  stated in [OS99] (`lemma3_estimate_uniform`, `Lemma3Uniform.lean`)."
- The rest of N-21 matches the code: two ramps of mass `−1/2`, zeros `ℤ`/`ℤ + 1/2`/`ℤ`, `f = 0` on `ℤ_{≤0}`, and the
  window lemma `exists_window`.

**F-69 (Low) — N-33 and N-34 describe mechanisms other than the formal ones.**
- N-33 (`:265-267`) says "a level set bounded on one side would contradict the interpolation property". Formally, the
  *norm identity* of Theorem E gives a uniform lower bound for the sampling sums of translates of a fixed PW function,
  and the Plancherel–Pólya tail bound gives the contradiction (`Theorem1/Sufficiency/Phase.lean:71-150`).
  - Proposed: "would contradict the norm identity of Theorem E for far translates of a fixed `g ∈ PW` (by the
    Plancherel–Pólya tail bound)".
  - The `α_n = π/2 + π/(n+2)` part matches `eventually_not_exceptional` (`Sufficiency.lean:57`).
- N-34 (`:276-277`) says "(… open mapping theorem)". The code uses the closed graph theorem
  (`Corollary1/ClosedGraph.lean:140`); the two are equivalent.
  - Proposed: "(closed graph theorem)".

**F-70 (Low) — Smaller notebook points.**
- **N-02 (`:43-44`).** "appears as a hypothesis of exactly the main theorems that use it". `hPW` of `theorem2_ii` is
  unused. Add "(except `hPW` in `theorem2_ii`, I-02)".
- **N-13 (`:114-116`).** Add "The formalization proves `φ_F' ≥ 0`, and `φ_E' > 0` for strict `E`, from one
  dichotomy via a Hopf-type boundary lemma (`HB/Hopf.lean`). Strictness cannot be obtained from the derivative
  argument alone." This also answers N-28's "`φ_E + φ_F` strictly increasing".
- **N-38 (`:313`).** "N-38 (T) — p. 801, Theorem 2 (ii) proof sketch". The proof is on pp. 804–805, and the entry is a
  remark, not a typo. Proposed header: "N-38 (S) — pp. 804–805: what `ψ' = o(1/x)` is used for". M09:500-503 still
  says "equivalent" (F-58).
- **Status tags.** The "referee-confirmed" tags cite R1–R5 only. This report re-checked N-06, N-12, N-16–N-19,
  N-21–N-25, N-30–N-36 against the code; R8 can be added where useful.

**F-71 (OK) — Entries consistent with the code.**
- N-01 to N-04: `Defs.lean`.
- N-06: Theorem D only in `Corollary1*`; `HEEqPW.exists_phase_data`.
- N-07: `hk`, `Necessity.lean:575`.
- N-12: `plancherelPolya_tail_union` at `Limit.lean:94`.
- N-16, N-30: `compEκ` plus Theorem E; no Levin.
- N-18, N-36: `exists_modified_density`: `∫ h = 0`, linear term cancelled.
- N-19: `translate_limit` (Liouville), a single `k₀` in `phase_levels`, both ends.
- N-23: `RegData.abs_cellTerm_far` carries `2d_n y/|z − r_n|²`, summed with `≤ 9π/4`.
- N-24: window `K0 C = 8 + 4(1+C)`.
- N-25: `tendsto_phaseDeriv_fProd`, `integrable_upsiInt`.
- N-27: frame bounds `= 2π ×` sampling bounds, `Frames.lean:46, 63`.
- N-28, N-29: `HEEqPW.ne_zero_ofReal`, `memPW_of_memHE`.
- N-31: `exists_F`, `isHB_F`.
- N-37: `TheoremF` restricted.

### 4.2 What the implementers found that the notebook does not record

`NOTEBOOK.md` has only two I-entries, and `impl_notes/*.md` record many more deviations.

**F-72 (Medium) — Paper-relevant observations from implementation notes and blueprints that have no N-entry.**
- (a) **The `e^{κ/2}` rescaling and the nonzero drift of the example.** See F-66. For N-30: the potential of the
  example's density has a linear drift `κ Re z`, with `κ = ∫_{|t|>1}(m − 1)/t ≈ −1.352` (numerical; M06:36, 729). It
  is an artefact of the `Re(z/t)` normalisation and is absorbed by `E_κ`.
- (b) **The uniform constants in [OS99] Lemma 3** (F-68). Add to N-21.
- (c) **Corollary 1 (p. 798).** "`Λ` consists of those points such that `φ_{EF}(λ) = π/2 + kπ`" holds only after
  removing the real zeros of `F`. The formal proof uses `G` from `exists_noRealZero_hb` and needs only `Λ ⊇ Λ₁`.
  "`φ_E` grows more slowly than `φ_{EF}`" is to be read as "`φ_{EF} − φ_E = φ_G` is nondecreasing", which gives each
  `[γ_k, γ_{k+1})` a `ψ`-image of length `≥ π` (`Corollary1.lean:96-104`; M04 Issues 10–11). Add to N-34, or as N-39 (G).
- (d) **S-entries.**
  - The example needs no perturbation or Kadec/Avdonin argument, because the density can be chosen with barycentres
    exactly `Λ + 1/2` (M06:965; `LogExample.lean:2035`).
  - Corollary 2 does not use `ψ(∞) − ψ(−∞) = ∞` (M07:1131-1133: true for `ψ = 0`, `f = 1`, `Λ = ℤ`).
- (e) **D-entry (R2-11, never applied).** `IsPhaseFunction` requires `E(x)e^{iφ(x)} ≥ 0`, not just real as on p. 794.
  Same level sets; the uniqueness modulo `2πℤ` is finer than the paper's.

**F-73 (Medium) — The implementation log is missing.** Proposed new I-entries, condensed from `impl_notes/*.md`
and the checks above:

```markdown
### I-03 — Helper statements with superfluous hypotheses (frozen, kept)
These helper lemmas hold under fewer hypotheses than their frozen statements say. The hypotheses are kept, either
silenced with `have _ :=` or left as linter warnings:
- `isSampling_of_replace_finite` (`hsep'`)
- `multU_const_mul` (`hg`, `hM`)
- `multU_compact_sub_linear` (holds for all `z`)
- `osc_bound_of_JN` (`hD`)
- `exists_noRealZero_hb` (`hEHB`)
- `compB_eq_zero_iff`, `compB_mul_Q` (`hN`)
- `integrable_log_mul_sub_one` (`hz`)
- `RegData.abs_cellTerm_below`, `RegData.hasSum_UPsi`, `sum_far_im_le` (`0 ≤ Im z`)
- `HEEqPW.phaseDeriv_mul_sq_ge`, `memPW_of_memHE` (`hPW`)
- `sampInner_*`, `samp_H1`, `samp_H3`, `entSum_eq` (Necessity)
- `volume_dyadic` (`_hab`; phase 2)

None of them is a main statement (see I-02 for those).

### I-04 — No real-valued `tsum`/`ncard` statements on the main path (M08)
A real `tsum` is `0` for a non-summable family, and `ncard` is `0` for an infinite set. So `card_near_le`,
`sum_far_le`, `sum_far_im_le` and `exists_bound_cellTerm`, as scaffolded, hold trivially in the degenerate case.
The proof of Theorem 2 (i) uses uniform finset forms instead (`RegData.finset_*`, `D3.exists_finset_bound`). The
`tsum` forms are proved corollaries and are unused.

### I-05 — How `rampPot_estimate` parses (M09)
In `|(1/a) * ∫ t in a..2*a, log ‖1 - x/t‖ - log (max 1 (|x|/a))| ≤ 4` the binder of `∫` extends over
`- log (max …)`. Since the interval has length `a`, the two readings agree. The proof treats both
(`T2ii.rampPot_estimate'`).

### I-06 — Proof routes different from the blueprint
- `φ' ≥ 0` and `φ' > 0`: Hopf dichotomy (`HB/Hopf.lean`).
- `exists_isPhaseFunction`: `E e^{iΦ−R}` is constant.
- `exists_realFactor`: genus `m(a) + rank(a) + 1`, log-series bound.
- `levelSet_limit`: `plancherelPolya_tail_union`, `C₀(T + 2η)`.
- `phase_tendsto`: translates plus tails, no `ℤ`-indexing.
- CIS ⇒ sampling: closed graph theorem.
- `log_norm_eq_multU_add_affine`: Schwarz reflection.
- `multU_one`: a corollary of that identity.
- `continuous_multU_of_bdd`: Vitali.
- `norm_compB_comparable`: compactness lemma, no continuity of `U`.
- `phase_rigidity`: `Rigidity.phase_drift_small`.
- `not_memHE_sAlpha`: `∫ cos² φ`.
- LogExample §4: integration by parts and Young's inequality.
- `multUIntegrand_one`: shift trick.
- `rampPot_estimate`: rescaled, `|ξ| ≤ 3` split.

Details: `blueprint/impl_notes/*.md`.

### I-07 — The construction interface (M07)
The first interface `exists_hb_of_density`, with a phase clause for every `m → 1`, was false. It was replaced
before implementation by `exists_hb_of_density` (no phase clause, `hshift`) and `exists_hb_of_density_phase`
(drifted `hU`), with `E_κ = e^{−κz}(A − i e^{κ/2}B)`. The proof confirms that `λ e^{−κ/2} = 1` is exactly what
makes the translates converge to `i c e^{−iπ(z−θ)}`.

### I-08 — Duplications
- The frozen definitions `argUp`, `potC` are copied as `argUp'`, `potC'` in `Corollary2/*` (transfer by `rfl`).
- `U_1 = π|Im z|` is proved three times (`LogExample.multU_model`, `Corollary2.multU_one`, `Theorem2ii/UOne.lean`).
- The sub-mean-value inequality is proved twice (`PW/PlancherelPolya.lean`, `HB/H2.lean`).
- Unused proved lemmas: `pwFT_sub`, `tsum_enorm_sq_pwFT_int`, `l2piSq_eq_of_pwFT_eq`, `fourierCoeffOn_pwFT`,
  `MemPW.isH2Upper_mul_exp`, `MemPW.lintegral_mul_exp_le`, and the `tsum` forms of I-04.
```

---

## 5. Other documents

**F-74 (Medium) — `IMPORTS.md` is a scaffold-era snapshot, and its generator crashes.**
- The generated block of `IMPORTS.md` (`:43-127`) says "Total: 23 files, 491 declarations, 342 `sorry`". The tree
  now has 92 files, 1584 declarations and 165 `sorry`, all in `Cited/`.
- `scripts/make_imports.py` raises `KeyError: 'Cited/DSPerturbation'`, and would also fail on every helper file
  (e.g. `Theorem2i/Assembly`). This is because `module_of` (`scripts/make_imports.py:37-42`) matches a prefix
  without a trailing `/` only by equality.
- A copy patched in the scratchpad produces a correct graph, with module reductions identical to `IMPORTS.md` plus
  P1 ← M00, P2 ← M01, P3 ← M02, P4 ← M00. The patch:
  - the condition `r == pr or r.startswith(pr + "/")`;
  - the rows `("P1", …, ["Cited/PaleyWiener"])`, `("P2", …, ["Cited/DSPerturbation", "Cited/JohnNirenberg"])`,
    `("P3", …, ["Cited/DeBrangesDE"])`, `("P4", …, ["Cited/DeBrangesFC"])`.

  Apply it and regenerate.
- Stale prose in `IMPORTS.md`:
  - `:162` ends with the placeholder "M06 uses XX". It should read "M06 uses `exists_hb_of_density_phase` with
    `κ = logKappa`".
  - `:178` "`lemma3_estimate_uniform` (`sorry`)": it is proved.
  - `:200` "`lake build OrtegaCerdaSeip` fails (no root file `OrtegaCerdaSeip.lean`)": the root file now exists.
  - `:3-6` "passes with only `declaration uses 'sorry'` warnings": now only phase-2 scaffolds.

**F-75 (Medium) — `PHASE2.md` has no status, and the P3 document is missing.**
- The table (`PHASE2.md:7-16`) has an "Assessment" column only. For example, D/E are "to assess" although P3 is
  being implemented.
- `:22-23` "all phase-1 modules are proved except `Perturbation`/`Corollary2`" is stale.
- `blueprint/P3_DeBrangesDE.md` is cited by `Cited/DeBrangesDE.lean:8`, by six `Cited/DeBrangesDE/*.lean` headers
  and by `formalization.yaml:70`, but it is not in `blueprint/`. It is presumably in another agent's worktree; it
  must be merged with the code.
- Proposed: add a "Status" column with the values of the F-13 table, and replace `:22-23` by "(all phase-1 modules
  are proved)".

**F-76 (Low) — `P2_DS_JN.md` is stale.**
- `:3-4` says "both compile with `lake env lean` (only `sorry` warnings)". Both are complete.
- `:13` "**Used by.** Theorem 2(i)/Corollary 2 (`hDS`), Theorem 2(ii) (`hJN`)" is wrong: `hJN` is a hypothesis of
  `landau_inequality` only. `theorem2_ii` takes only `hPW`.
- Proposed: "Used by: `corollary2`, `theorem2_i`, `theorem2_i_of_densityBound` (`hDS`); `landau_inequality` (`hJN`)."

---

## 6. Summary

76 findings: 4 High, 42 Medium, 21 Low, 9 OK (checked, consistent).

**Soundness: no problem found.**
- The 15 main theorems depend only on `propext`, `Classical.choice` and `Quot.sound` (re-checked with `#print axioms`).
- `FFChallenge.lean` is exactly `Defs.lean` plus `comparator/statements.lean`. All 15 statements occur verbatim in
  the project, and no statement changed since `scaffold-reviewed`.
- There is no `axiom`, `admit`, `native_decide`, `unsafe`, `opaque` or `maxHeartbeats` anywhere. The one
  `set_option` is a warning switch.
- No definition in `Defs.lean` has degenerate behaviour (`x/0`, `log 0`, non-integrable integrals, `tsum`, `ncard`)
  that makes a main statement vacuous or trivial.

**Hygiene items to act on:**
- the root `FourierFrames.lean` imports `sorry`-backed phase-2 scaffolds, so `paleyWiener_holds`, `theoremC/D/F_holds`
  carry `sorryAx` (F-4);
- `FF.theoremD_holds` is declared twice (F-5);
- the unused `hlow`/`hPW` of `theorem2_i`/`theorem2_ii` are still pending, against NOTEBOOK I-02 (F-6);
- some `tsum`/`ncard` helper statements in M08 are weak but unused (F-10);
- several code docstrings are stale (F-12).

**Blueprint as documentation.** Every Lean statement block of M01–M10 matches the code, up to renamings and moved
declarations. But the documents still read as the pre-implementation plan, with stale status lines, deleted
"upstream interface" sections and `sorry` blocks.

Four places misstate what is proved:
- M01 §0/§1.7/§7 and M10 describe the obsolete `PaleyWienerThm` (F-32, F-62);
- M06 states the superseded `landau_sharp` (F-47);
- M08's status box says `theorem2_i` has no proof (F-54);
- the README has no status section and nothing on phase 2 (F-13).

The Medium findings give file and lemma names and the proof routes and constants that were actually
implemented. In particular:
- the Hopf route for `φ' ≥ 0` (F-17, F-36);
- the Meĭman replacement and Levin avoidance (F-18, F-19);
- `exists_realFactor` (F-42);
- the κ normalisation `E_κ = e^{−κz}(A − i e^{κ/2}B)` (F-49, F-66);
- the Corollary 2 identity via Schwarz reflection (F-52);
- the finset forms in M08 (F-56).

M03, M05 and the M07 statement blocks are accurate.

**README.** Needs:
- a status section (F-13);
- the complete file table with helpers and phase 2 (F-22);
- a corrected dependency graph: M09 depends only on M00, M07 on M04 (F-25);
- the new design decisions 3.9–3.15 (F-21);
- §4a replaced by a pointer to NOTEBOOK; it still lists the withdrawn `φ_{EF}` seed (F-28).

`IMPORTS.md` is stale and its generator crashes on the current tree (F-74).

**NOTEBOOK.** The N-entries are correct as statements about the paper. Four need updating to the final Lean:
- N-22 should name `theorem2_i_of_densityBound` (F-63);
- N-26 and I-02 are still open (F-64);
- N-32's genus formula is not the formal one (F-65);
- N-35 should mention the `e^{κ/2}` rescaling (F-66).

Four implementation findings with paper relevance are unrecorded (F-72):
- the uniform [OS99] Lemma 3 constants;
- the drift `κ ≈ −1.35` of the example;
- the reading of Corollary 1 after removing the real zeros of `F`;
- the R2-11 phase convention.

The implementation log stops at I-02, while `impl_notes/` document many deviations. Proposed I-03…I-08 (F-73).

Priority order for the edits: F-13, F-32/F-62, F-54, F-47, F-6/F-64, F-4/F-5, F-63, F-65, then the Medium route
updates.
