# Blueprint: Ortega-Cerdà–Seip, *Fourier frames* (Ann. of Math. 2002)

**Source.** J. Ortega-Cerdà and K. Seip, *Fourier frames*, Ann. of Math. (2) **155** (2002),
789–806, MR1923965.
- Printed version (primary source, gitignored): `literature/2002Annals.pdf`; page renders at
  150 dpi in `literature/pages/p-01.png … p-18.png` (page `p-NN` is journal page `788 + NN`).
- Author's LaTeX source of the Annals version: `literature/ArxivOrtega.tex` (gitignored). It agrees
  with the print. **The OCR text of the PDF is unreliable** (it drops slashes, bars and primes:
  `∉` becomes `∈`, `φ'` becomes `φ`); always check a claim about the source against the tex or
  the page images.
- Page references `[p. 795]` are to the journal pagination.

**Lean project.** Library `FourierFrames`, namespace `FF`, Lean/Mathlib `v4.35.0`. Vendored:
`OrtegaCerdaSeip/` (subset of MR1682065, [OS99] Lemma 3 and Bernstein-space tools; namespace
`OCS`; do not edit). Selected unchanged Tau Ceti v4.35.0 modules supply
analytic infrastructure for P5 (`TauCeti/VENDORED.md`: 41 modules, 8882 lines,
commit `1f9b4414105d86e487a4ac4c3d3397076a44d0d2`).

## Status (2026-11-07)

**Phase 1 is complete.**

- All 15 main statements of `comparator/statements.lean` are proved, with the cited results as explicit `Prop`
  hypotheses.
- `#print axioms` of each main theorem shows only `propext`, `Classical.choice`, `Quot.sound`.
  The 46-statement comparator target is described below; see `comparator/last_run.log` for verification.
- No `sorry` in the implementation. `FourierFramesScaffold` and
  `Cited/DeBrangesFC/PartF.lean` are import-only compatibility modules for the proved Theorem F.
- `scripts/check_statements.py scaffold-reviewed` passes. The only changes to statements frozen at
  `scaffold-reviewed` are the removals of unused hypotheses in the lint pass, recorded in its `APPROVED` list
  (NOTEBOOK I-03). Among the main statements, `theorem2_i` lost `hlow` (`ψ' = 1/O(x)`), and `theorem2_ii` lost
  `hPW` and is unconditional. The changes of NOTEBOOK I-01 predate the freeze.

**Phase 2** (`blueprint/PHASE2.md`, files under `FourierFrames/Cited/`): P1–P5 proved; all eight cited results are discharged in their formalized forms.

| `Prop` | Lean | status |
|---|---|---|
| `PaleyWienerThm` | `paleyWiener_holds` (`Cited/PaleyWiener.lean`, `Cited/PaleyWiener/{Part1,L2Fourier,Spectrum,Part2}.lean`) | proved, unconditional |
| `JohnNirenberg` | `johnNirenberg_holds` (`Cited/JohnNirenberg.lean`) | proved, unconditional |
| `DSPerturbation` | `dsPerturbation_of_paleyWiener : PaleyWienerThm → DSPerturbation` (`Cited/DSPerturbation.lean`); `dsPerturbation_holds` (`Unconditional.lean`) | proved, unconditional |
| `TheoremD`, `TheoremE` | `theoremD_holds`, `theoremE_holds` (`Cited/DeBrangesDE.lean` + `Cited/DeBrangesDE/*`) | proved, unconditional (`P3_DeBrangesDE.md`, referee R9) |
| `TheoremC` | `theoremC_holds` (`Cited/DeBrangesFC.lean` + `Cited/DeBrangesFC/{Analytic,Space,Kernel}.lean`) | proved, unconditional, through Theorem D (R7 finding 7; `P4_DeBrangesFC.md`, referee R10) |
| `TheoremF` | `theoremF_holds` (`Cited/DeBrangesF.lean` and `Cited/DeBrangesF/*`) | proved, unconditional; elementary normalized-kernel route (`P4F_Elementary.md`, review R11) |
| `PavlovBMO` | `pavlovBMO_holds` (`Cited/Pavlov.lean` and `Cited/Pavlov/*`) | proved, unconditional; BMO necessity only (`P5_Pavlov.md`, reviews R13–R15) |

The implementation uses only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
The comparator target comprises 46 statements: 15 original statements, eight proved cited results,
and 23 discharged versions including historical conditional versions. See `comparator/last_run.log`
for verification.

**Unconditional versions** (`FourierFrames/Unconditional.lean`). All formalized main results have
versions with every cited result supplied, including `landau_inequality_unconditional`.
The new Theorem F proof gives `theorem1_necessity_unconditional`, `theorem1_unconditional`,
`corollary1_unconditional`, and the earlier `landau_inequality_of_pavlov`. The Pavlov proof supplies
its last hypothesis in `landau_inequality_unconditional`. Historical `*_of_theoremC`,
`*_of_theoremCF`, `*_of_theoremF` and Landau variants remain for compatibility.

## 0. Workflow

Same workflow as the companion projects (`../MR1949832`, `../MR1682065`, `../MR2006561`):
1. Blueprint: one Markdown file per module with a detailed proof, the Lean statements and explicit
   dependencies.
2. Scaffold: all statements compiled, proofs `sorry`.
3. Independent agent review of the blueprint and of every statement (`reviews/`).
4. Implementation (git worktrees, `scripts/new_worktree.sh`).
5. `comparator` check of the main results against the self-contained `FFChallenge.lean`.
6. `formalization.yaml`, `NOTEBOOK.md`, and the corrected paper, uploaded to arXiv.

**Phases.**
- *Phase 1*: the paper's own arguments, with the cited results (Paley–Wiener, de Branges C/D/E/F,
  Pavlov's Theorem A, John–Nirenberg, Duffin–Schaeffer Lemma III) as explicit `Prop` hypotheses
  defined in `Defs.lean`. Every main theorem takes exactly the cited `Prop`s it uses.
- *Phase 2*: discharge the cited results that are within reach (plan, assessments and status:
  `blueprint/PHASE2.md` and the Status section above), and state the main results with them supplied
  (`Unconditional.lean`). Theorem F follows the independently reviewed elementary route
  (`P4F_Elementary.md`, R11); Pavlov's BMO necessity follows the completed modular route
  in `P5_Pavlov.md` (R13–R15).

## 1. What is formalized (main results, `comparator/statements.lean`)

| Paper | Lean (namespace `FF`) | Cited hypotheses | Lean file (`FourierFrames/`) |
|---|---|---|---|
| p. 790: Fourier frame ⟺ sampling | `isFourierFrame_iff_isSampling` | PW | `Frames.lean` |
| p. 799: `|E| ≃ e^{π Im z}` on `Im z ≥ 0` ⇒ `H(E) = PW` | `heEqPW_of_comparable` | PW | `HB/Comparable.lean` |
| Theorem 1, ⇒ | `theorem1_necessity` | PW, C, F | `Theorem1/Necessity.lean` |
| Theorem 1, ⇐ | `theorem1_sufficiency` | PW, E | `Theorem1/Sufficiency.lean` |
| Theorem 1 | `theorem1` | PW, C, E, F | `Theorem1/Main.lean` |
| Remark p. 797: CIS ⇒ zero set of `E + E^*` | `completeInterpolating_zero_set` | PW, C, D | `Corollary1.lean` |
| Corollary 1 | `corollary1` | PW, C, E, F | `Corollary1.lean` |
| Claim (Landau's inequality = Theorem B) | `landau_inequality` | PW, C, E, F, A, JN | `Landau.lean` |
| Example p. 798 is CIS | `logExample_isCompleteInterpolating` | PW, E | `LogExample.lean` |
| Example p. 798, counting | `logExample_count` | — | `LogExample.lean` |
| Landau's inequality is sharp (no coefficient `A < 1`) | `landau_sharp` | PW, E | `LogExample.lean` |
| Corollary 2 | `corollary2` | PW, E, DS | `Corollary2.lean` |
| Theorem 2 (i), with ψ' eventually nonincreasing (N-22), without `ψ' = 1/O(x)` (N-26, I-03) | `theorem2_i` | PW, E, DS | `Theorem2i.lean` |
| Theorem 2 (i), with the cell density bound the proof uses | `theorem2_i_of_densityBound` | PW, E, DS | `Theorem2i.lean` |
| Theorem 2 (ii) | `theorem2_ii` | — (unconditional, I-03) | `Theorem2ii.lean` |

The cited hypotheses PW, C, D, E, F, A, JN and DS are proved in phase 2; `Unconditional.lean` states each main
result with them supplied (Status section above).

Not formalized: the Proposition on p. 798 (norm equivalence via [Or98]; quoted without proof and
not used), the remarks about [Se95] (Lemma 3.11, Theorems 2.3 and 2.7), the
"Λ = Λ' ∪ (Λ∖Λ')" remark of p. 797.

## 2. Conventions and divergences (details in `M00_Defs.md`)

1. **Sequences are sets.** `Λ : Set ℝ`. Theorem 1 is about separated sequences, whose points are
   distinct.
2. **`ℝ≥0∞`-valued sums and integrals** (`sampleSum`, `pwNormSq`, `heNormSq`).
3. **Closed Hermite–Biehler class.** `IsHB` is the paper's `\overline{HB}`: `|E(z̄)| ≤ |E(z)|`
   on `Im z > 0`, no zeros there, real zeros allowed. The non-strict inequality is essential:
   in Theorem 1 the function `F` can be (a unimodular constant times) a real entire function,
   e.g. `F = 1` when `Λ` is a complete interpolating sequence. `IsStrictHB` is de Branges' class.
4. **Phase functions** enter through `phaseDeriv E x = -Im(E'(x)/E(x))` and `IsPhaseFunction`.
5. **`U_ψ`.** The paper's principal value `∫ Re(z/t) dψ(t)` need not exist for `ψ ∈ C¹`;
   `UPsi` keeps `Re(z/t)` only for `|t| > 1` (as `OCS.multU`). This changes `U_ψ` by a real
   linear function `c Re z`, which is absorbed by `f ↦ f e^{-cz}` in Corollary 2 (this preserves
   `\overline{HB}` and the phase).
6. **Corollary 2's approximation hypothesis** is stated multiplicatively,
   `e^{U_ψ - C} ≤ |f| ≤ e^{U_ψ + C}` on `Im z ≥ 0`, which is `|U_ψ - log|f|| ≤ C` and excludes
   zeros (`Real.log 0 = 0` would not).
7. **Cited `Prop`s in the weakest form used.** Theorem F allows an extra term `p y`, `p ≥ 0`;
   Theorems D, E, F are stated for `E` in the strict class without real zeros; Theorem A only
   in its BMO necessity part.

## 3. Design decisions (simplifications and repairs found while writing the blueprint)

1. **Theorem D is not needed for Theorem 1 or Corollary 1.** The bound `φ_E'|E|² ≃ 1` on `ℝ` when
   `H(E) = PW` (the display after (5), p. 796) follows from Theorem E alone:
   - lower bound: `‖f‖²_E ≥ π|f(x)|²/(φ'(x)|E(x)|²)` from the norm identity at the level set
     through `x`, applied to a translate of a fixed `g ∈ PW` with `g(0) ≠ 0`;
   - upper bound: the interpolant of `δ_x` on that level set has `‖f‖²_E = π/(φ'(x)|E(x)|²)` and
     `1 = |f(x)|² ≲ ‖f‖²_PW ≲ ‖f‖²_E`.
   The exceptional `α` is avoided by continuity of `φ`. Theorem D is only used for the remark
   on p. 797 (`completeInterpolating_zero_set`).
2. **`φ_F' ≥ 0`** for `F ∈ \overline{HB}` without real zeros is elementary: `log|F^*| - log|F| ≤ 0`
   on `Im z > 0` and `= 0` on `ℝ`, so its `y`-derivative at `y = 0`, which is `-2 φ_F'`, is `≤ 0`.
   In Lean both `φ_F' ≥ 0` and the strict `φ_E' > 0` for `E ∈ HB` come from the dichotomy
   `IsHB.phaseDeriv_pos_or_eventuallyEq` (normal form of `E^*/E − c` at `x` plus the Hopf-type boundary
   lemma of `HB/Hopf.lean`). The one-sided derivative argument alone cannot give strictness
   (`D(y) ≈ −y³`).
3. **`G = (EF + E^*F^*)/2` (p. 796)** follows by adding `M + 1 = EF/G` and `M - 1 = -E^*F^*/G`;
   the "real part on the real axis" argument is not needed.
4. **Herglotz normalisation.** In (3) the paper uses `1/(z - λ_k) + 1/λ_k`, undefined if
   `0 ∈ Λ`. Use `1/(λ_k - z) - λ_k/(1 + λ_k²)` and constants: `M` is
   `(-i/π) ∑ c_k (1/(λ_k - z) - λ_k/(1+λ_k²)) - ipz + ia` with `c_k = |E(λ_k)|²`, and the
   canonical product `G` of genus one handles `0 ∈ Λ` with a factor `z`.
5. **The limit `α → π/2` (p. 797).** "By (4) we may apply dominated convergence" is not a
   domination. Use the local Plancherel–Pólya inequality: the tails
   `∑_{|λ_{α,k}| > R} |f(λ_{α,k})|²` are bounded by `C ∫∫_{|x| > R-1, |y| < 1} |f|²`, uniformly in
   `α`, and this tends to `0`. In Lean: `plancherelPolya_tail_union` (`PW/PlancherelPolya.lean`), the
   tail bound uniformly over unions of two `δ`-separated sets, used in `Theorem1/Sufficiency/Limit.lean`.
6. **Meĭman's theorem is replaced.** As usually quoted (interlacing zeros + exponential type) it is
   false: `A = cos πz`, `B = e^{az} sin πz` have interlacing zeros, but for `a ≠ 0` neither
   `A - iB` nor `A + iB` is in `\overline{HB}`. In Corollary 2, `A` and `B` are locally uniform limits
   of `e^{β + c_R z}` times the symmetric partial products, which are real polynomials with
   interlacing zeros. For those, `Im(B_R/A_R) > 0` on `ℂ₊`, because the arguments of the factors are
   monotone (`Construction/PolyHB.lean`). The real exponential factors preserve `\overline{HB}`, and
   `\overline{HB}` is closed under locally uniform limits (Hurwitz, `IsHB.of_tendstoLocallyUniformly`).
   The result is `A − iλB ∈ \overline{HB}` for every `λ > 0` (`isHB_genA_sub_lam_compB`). See M07.
7. **Levin's theorem is avoided.** The example `{k + log⁺|k|}` uses the construction of M07 §2 with
   a step density whose barycentres are exactly `Λ + 1/2`, and `E = e^{−κz}(A − i e^{κ/2}B)` with
   `κ = logKappa`. The sine-type estimate `|E| ≃ e^{π Im z}`, which the paper asserts without proof,
   is proved. Theorem E at level `π/2` shows that `Λ + 1/2 = {E + E^* = 0}` is sampling and complete
   interpolating (`logExample_shift_sampling_cis`). Translating by `−1/2` gives the claim.
8. **Separation of `Γ_α` in Corollary 1** (needed to apply Pavlov's theorem, which is stated for
   separated sequences) follows from Theorem E: the interpolant `f_γ` of `δ_γ` has norm
   `≲ 1`, and the Bernstein/Cauchy bound `|f'| ≲ ‖f‖_PW` on `ℝ` gives `|γ - γ'| ≳ 1`.

Design decisions taken during implementation:

9. **Theorem 2 (i) needs a local density bound** `ψ' ≲ 1/d_n` on each cell (N-22). Two main statements:
   `theorem2_i_of_densityBound` assumes it, through `IsLogRegularPartitionWithDensity`. `theorem2_i`
   keeps the printed hypotheses except `ψ' = 1/O(x)`, which the proof does not use (N-26; removed in
   I-03), and adds `hmono` (`ψ'` eventually nonincreasing), which implies the bound
   (`RegData.densBound_of_antitoneOn`).
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
    `Φ = e^{iφ(0)} f e^{−P}`, which is real on `ℝ`, followed by Borel–Carathéodory. No holomorphic logarithm of `f`
    on the closed half-plane is needed (`Corollary2/{Reflection,Affine,LogNorm}.lean`). Continuity of potentials of bounded measurable
    densities uses Vitali's theorem (`Corollary2/UCont.lean`).
15. **No real-valued `tsum` or `ncard` in helper statements on the main path.** They are `0` when the series
    diverges or the set is infinite. The M08 estimates are proved in uniform finset form (NOTEBOOK I-04).

## 4. Modules

| # | Doc | Lean | Content | Paper |
|---|---|---|---|---|
| M00 | `M00_Defs.md` | `Defs.lean` | definitions, cited `Prop`s, main statements | — |
| M01 | `M01_PW.md` | `PW/{Basic,Bounds,PlancherelPolya,Complete}.lean` | Paley–Wiener space toolkit from `PaleyWienerThm` | §1 |
| M02 | `M02_HB.md` | `HB/{Basic,Phase,H2,DeBranges,Comparable}.lean`; helpers `HB/{Hopf,MeanValue}.lean` | `f^*`, `\overline{HB}`, phase, `H(E)`, "evident fact" | §2, p. 799 |
| M03 | `M03_Necessity.md` | `Theorem1/Necessity.lean`; helper `Theorem1/Necessity/Sep.lean` | Theorem 1 ⇒ | §3 |
| M04 | `M04_Sufficiency.md` | `Theorem1/Sufficiency.lean`, `Theorem1/Main.lean`, `Corollary1.lean`; helpers `Theorem1/Sufficiency/{Interlace,Limit,LevelSet,Phase}.lean`, `Theorem1/Sufficiency/RealFactor/{Elem,LUProd,Zeros,Product,Main}.lean`, `Corollary1/{Rotate,Kernel,ClosedGraph}.lean` | Theorem 1 ⇐ (`Sufficiency`), `theorem1` (`Main`), Corollary 1 and remark p. 797 (`Corollary1`) | §3–4 |
| M05 | `M05_Landau.md` | `Landau.lean` | Claim (Landau from John–Nirenberg + Pavlov) | §4 |
| M06 | `M06_LogExample.md` | `LogExample.lean`; helpers `LogExample/{Basic,Phase,Potential}.lean` | the example `{k + log⁺|k|}` and sharpness | §4 |
| M07 | `M07_Corollary2.md` | `Construction.lean`, `Perturbation.lean`, `Corollary2.lean`; helpers `Construction/{Gaps,Comparable,PolyHB,Limits,Rigidity,Translate}.lean`, `Corollary2/{Affine,Kernel,Density,LogInt,Reflection,PotC,PotCDiff,PotCCont,UCont,LogNorm}.lean` | phase construction `E = A - iB`, perturbation lemma, Corollary 2 | §5 |
| M08 | `M08_Theorem2i.md` | `Theorem2i.lean`; helpers `Theorem2i/{Basic,Product,PhaseDecay,Cells,CellsAux,Taylor,CellAux,BelowAbove,FarAux,NearAux,Near,Counting,Riemann,Estimates,Assembly}.lean` | Theorem 2 (i): the Lyubarskii–Malinnikova approximation | §5 |
| M09 | `M09_Theorem2ii.md` | `Theorem2ii.lean`, `Lemma3Uniform.lean`; helpers `Theorem2ii/{Window,UOne,Ramp,Mass,Cells}.lean` | Theorem 2 (ii); the uniform-in-`m` form of [OS99] Lemma 3 (2) | §5 |
| M10 | `M10_Frames.md` | `Frames.lean` | Fourier frame ⟺ sampling | §1 |

Phase 2 (`PHASE2.md`):

| # | Doc | Lean | Content |
|---|---|---|---|
| P1 | `P1_PaleyWiener.md` | `Cited/PaleyWiener.lean`, `Cited/PaleyWiener/{Part1,L2Fourier,Spectrum,Part2}.lean` | Paley–Wiener theorem (proved) |
| P2 | `P2_DS_JN.md` | `Cited/DSPerturbation.lean`, `Cited/JohnNirenberg.lean` | Duffin–Schaeffer, John–Nirenberg (proved) |
| P3 | `P3_DeBrangesDE.md` | `Cited/DeBrangesDE.lean`, `Cited/DeBrangesDE/{Cauchy,Kernel,Space,EntireHerglotz,Orthogonal,Complete}.lean`; helpers `Cited/DeBrangesDE/{CauchyAux/Basic,EAux/KernelSymm}.lean` | de Branges D, E (proved) |
| P4 | `P4_DeBrangesFC.md`, `P4F_Elementary.md` | `Cited/DeBrangesFC.lean`, `Cited/DeBrangesFC/{Analytic,Space,Kernel}.lean`; `Cited/DeBrangesF.lean`, `Cited/DeBrangesF/*` | de Branges C and F (proved) |
| P5 | `P5_Pavlov.md`, `P5_Statements.md` and specialized `P5_*` notes | `Cited/Pavlov.lean`, `Cited/Pavlov/*` | Pavlov's BMO necessity consequence (proved) |
| — | `PHASE2.md` | `Unconditional.lean` | the main results with the proved cited results discharged |

All Lean files are under `FourierFrames/`. `FourierFrames.lean` imports the module files of the
table (helper files transitively), `Cited/{DSPerturbation,JohnNirenberg,PaleyWiener,DeBrangesDE,DeBrangesFC,DeBrangesF,Pavlov}.lean`
and `Unconditional.lean`; `Cited/DeBrangesFC/PartF.lean` and `FourierFramesScaffold.lean` are compatibility imports of the proved Theorem F. The
file-level import DAG, the interface reconciliation done at assembly (every temporary "Upstream
interface" block was replaced by imports; the last one, the stub `theoremD_holds` of the P4 scaffold, was
deleted at the P4 merge) and the module graph computed from the actual imports are in `IMPORTS.md`.
`scripts/make_imports.py` regenerates that graph (with the fix of R8 F-74 and rows for P1–P4 and
`Unconditional.lean`; regenerated after the P4 merge). Helper lemmas added or moved
at assembly: `IsStrictHB.mul_isHB`, `IsHB.rotate` (`HB/Basic.lean`); `IsPhaseFunction.rotate`
(`HB/Phase.lean`); `IsSeparated.finite_inter_Icc`, `MemPW.eq_zero_of_pwNormSq_eq_zero`
(`PW/Basic.lean`); `sampleSum_mono`, `sampleSum_eq_tsum_indicator` (`PW/PlancherelPolya.lean`).
M03's first half is exported as `exists_E` (`Necessity.lean`), not `exists_HB_of_sampling`.

### Dependency graph

Computed from the actual `import` lines (`IMPORTS.md`):

```
M00 ── M01 ─┬─ M10
            └─ M02 ─┬─ M03 ─────────────┐
                    └─ M04 Sufficiency ─┴─ M04 Main, Corollary1 ── M05
                         └─ M07 (Construction ← M02; Perturbation ← M01; Corollary2 ← M04 Sufficiency)
                              ├─ M06 (also ← M02 HB.Comparable, M04 Sufficiency)
                              └─ M08
M00 ── M09 (with Lemma3Uniform; no project module besides Defs)
OCS: Bernstein → M01, M07, P1; Products.Canonical → M03, M08; Lemma3 → M06, M07, M09
Phase 2: M00 ── P1;  M01 ── P2 (DSPerturbation; JohnNirenberg ← M00 only);  M02 ── P3 ── P4
P1, P2, P3, P4-C, M04 Corollary1, TauCeti → P5
Unconditional ← M02 (HB.Comparable), M04 (Main, Corollary1), M05, M06, M07 (Corollary2), M08, M10, P1, P2, P3, P4, P5
```

### Interface names (the exported lemmas other modules may rely on)

All in namespace `FF`; `hPW : PaleyWienerThm` etc. are explicit hypotheses.

**M01 (PW)**
- `MemPW.add`, `MemPW.sub`, `MemPW.const_mul`, `memPW_zero`, `MemPW.comp_sub_ofReal`
  (translation by a real `a`, with `pwNormSq_comp_sub_ofReal`), `MemPW.fstar`
  (with `pwNormSq_fstar`), `MemPW.mul_div_sub` (`f(z)(z-b)/(z-a)` when `f(a) = 0`, with the value
  at `a` given by `dslope`).
- `pw_norm_sq_le (hPW) : MemPW f → ‖f z‖ ^ 2 ≤ exp (2π |Im z|) * (pwNormSq f).toReal` and
  `pwNormSq_ne_top`.
- `pw_line_integral_le (hPW)`: `∫⁻ x, ‖f (x + iy)‖ₑ² ≤ ofReal (exp (2π|y|)) * pwNormSq f`.
- `plancherelPolya (hPW) (δ) : 0 < δ → ∃ C, ∀ Λ δ-separated, ∀ f ∈ PW, sampleSum Λ f ≤ C * pwNormSq f`.
- `plancherelPolya_tail (hPW)`: for `δ`-separated `Λ` and `f ∈ PW`, the tail sums
  `∑_{λ ∈ Λ, R ≤ |λ|} |f(λ)|²` tend to `0` as `R → ∞`, uniformly over all `δ`-separated `Λ`.
- `plancherelPolya_tail_union (hPW)`: the same tail bound uniformly over unions `A ∪ B` of two
  `δ`-separated sets (I-01; consumed by M04, `Theorem1/Sufficiency/Limit.lean`).
- `exists_memPW_eval_ne_zero : ∃ g, MemPW g ∧ g 0 = 1`, and `pw_eval_lower` (a uniform `c > 0`
  with: for every real `x` some `f ∈ PW` has `c * pwNormSq f ≤ ‖f x‖ₑ²`, `pwNormSq f ≠ 0, ⊤`).
- `pw_deriv_bound (hPW)`: `‖deriv f x‖ ^ 2 ≤ (π e)² * (pwNormSq f).toReal` for real `x` (pointwise,
  explicit constant).
- `MemPW.isH2Upper_mul_exp (hPW)`: `f ∈ PW ⇒ f(z) e^{iπz} ∈ H²(ℂ₊)` with
  `∫|f(x+iy)e^{iπ(x+iy)}|²dx ≤ ‖f‖²` (proved; used by no module).
- `pw_complete (hPW)`: an `L²`-Cauchy sequence in `PW` converges in `L²` and locally uniformly to
  some `f ∈ PW`.
- `pw_normal_family (hPW)`: a norm-bounded sequence in `PW` has a subsequence converging locally
  uniformly to some `f ∈ PW` with `pwNormSq f ≤ liminf pwNormSq f_n`.

**M02 (HB)**
- `fstar_fstar`, `fstar_mul`, `fstar_add`, `fstar_sub`, `fstar_const_mul`,
  `Differentiable.fstar`, `fstar_ofReal` (`fstar f x = conj (f x)` for real `x`).
- `IsHB.mul`, `isHB_one`, `IsHB.of_tendstoLocallyUniformly` (Hurwitz).
- `IsHB.phaseDeriv_nonneg`, `IsStrictHB.phaseDeriv_pos`, `phaseDeriv_mul`.
- `exists_isPhaseFunction`: `E` entire without real zeros has a phase function `φ` with
  `HasDerivAt φ (phaseDeriv E x) x`; phase functions are unique up to `2πℤ`.
- `zero_set_eq_phaseLevel`: for `E` strict, `F ∈ \overline{HB}`, both without real zeros, with
  phase functions `φ_E`, `φ_F`: `E z F z + E^* z F^* z = 0 ↔ z ∈ ofReal '' phaseLevel (φ_E + φ_F) (π/2)`.
- `MemHE.mul_isHB` and `heNormSq_mul`: `f ∈ H(E)`, `F ∈ \overline{HB}` ⇒ `F f ∈ H(EF)`, same norm.
- `HEEqPW.isStrictHB`, `HEEqPW.ne_zero_ofReal` (an `E` with `H(E) = PW` is strict, has no real
  zeros; no `hPW`).
- `HEEqPW.phaseDeriv_mul_sq_ge (hE : TheoremE)` and `..._le (hPW) (hE : TheoremE)`: `φ_E'(x)|E(x)|² ≃ 1`.
- `memHE_sAlpha_unique`: `S_α, S_β ∈ H(E)` ⇒ `β - α ∈ πℤ` (needs only `IsHB E`).
- `heEqPW_of_comparable` (main result).

**M07 (construction, `Construction.lean`)** — consumed by M06 and M07 (Corollary 2). The statement
of the first version (phase asymptotics for every `m → 1`) is not provable (`M07_Corollary2.md` §0.2);
it is replaced by two theorems. With `U = OCS.multU m 0`, `Γ = OCS.multGamma m`, `M = OCS.multPrim m`:
```lean
/-- Without phase asymptotics: `E = A - iB` of p. 801.  `hshift` is `U(z - 1/2) - U(z) = O(1)`. -/
theorem exists_hb_of_density {m : ℝ → ℝ} {a b : ℝ} (hm : Measurable m) (ha : 0 < a)
    (hlow : ∀ t, a ≤ m t) (hup : ∀ t, m t ≤ b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1))
    (hshift : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → |OCS.multU m 0 (z - 1 / 2) - OCS.multU m 0 z| ≤ C) :
    ∃ E : ℂ → ℂ, IsHB E ∧ (∀ x : ℝ, E x ≠ 0) ∧
      (∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
        c * Real.exp (OCS.multU m 0 z) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (OCS.multU m 0 z)) ∧
      (∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ OCS.multGamma m, z = (γ : ℂ))

/-- With phase asymptotics.  `hU`: `U = π Im z + κ Re z + O(1)` on `Im z ≥ 0` for some real `κ`
(`κ ≠ 0` in general, e.g. the example of p. 798).  The linear drift is absorbed by the real
entire factor `e^{-κ z}` *together with the rescaling `B ↦ e^{κ/2} B`*: `E = e^{-κ z}(A - i e^{κ/2} B)`
(the plain twist `e^{-κ z}(A - iB)` has the right modulus but not the right phase, since `A` and
`B = A(· - 1/2) P/Q` have amplitude ratio `e^{-κ/2}`).  Conclusion: `|E| ≃ e^{π Im z}`,
`E + E^* = 2 e^{-κ z} A`, phase with `φ' = phaseDeriv E` and `φ - π M → c₀`. -/
theorem exists_hb_of_density_phase {m : ℝ → ℝ} {a b : ℝ} (hm : Measurable m) (ha : 0 < a)
    (hlow : ∀ t, a ≤ m t) (hup : ∀ t, m t ≤ b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1))
    (hU : ∃ κ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C) :
    ∃ E : ℂ → ℂ, IsHB E ∧ (∀ x : ℝ, E x ≠ 0) ∧
      (∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
        c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) ∧
      (∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ OCS.multGamma m, z = (γ : ℂ)) ∧
      ∃ φ : ℝ → ℝ, IsPhaseFunction E φ ∧ (∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x) ∧
        StrictMono φ ∧ ∃ c₀ : ℝ,
        Tendsto (fun x ↦ φ x - Real.pi * OCS.multPrim m x) (cocompact ℝ) (𝓝 c₀)
```
M06 uses `exists_hb_of_density_phase` with `κ = logKappa`; M07's Corollary 2 uses it with the density
`m` of its §3.3 (for which the linear terms are cancelled, `κ = 0`). M07 also exports
`IsSampling.of_perturbation (hPW) (hDS)`: a separated sampling `Γ` and an injective perturbation
`γ ↦ γ + δ(γ)` with `δ → 0` along `Γ` (finitely many arbitrary moves allowed) give a sampling
sequence. M08 consumes the main statement `corollary2`; M09 consumes `OCS.lemma3` directly and
`lemma3_estimate_uniform` (`Lemma3Uniform.lean`).

## 4a. Issues in the source — see `../NOTEBOOK.md`

The seeds listed here during the blueprint phase were verified against the print or the tex and became
NOTEBOOK entries N-03, N-05, N-07, N-09, N-11, N-12, N-14–N-21 and N-35 (N-01 … N-45 in all; N-43–N-45
come from the "Issues in the source" of `P3_DeBrangesDE.md`). The seed
about `φ_{EF}` was withdrawn (N-10: an OCR artifact; the print has primes), and the placeholder about the
`PW` norm was dropped.
