# Phase 2: proving the cited results

Phase 1 formalized every argument of the paper with the cited results as explicit `Prop`
hypotheses (`FourierFrames/Defs.lean`). Phase 2 proves as many of these `Prop`s as feasible, so that
the main theorems become unconditional (`theorem1_unconditional := theorem1 paleyWiener_holds …`).

| `Prop` | Result | Source | Module | Assessment |
|---|---|---|---|---|
| `PaleyWienerThm` | Paley–Wiener + Plancherel | classical | P1 | feasible (~1300 lines): part 1 by Parseval on `[-π,π]`; part 2 by Gaussian regularisation, the `L²` Fourier isometry (plus the missing `L¹∩L²` agreement lemma) and Phragmén–Lindelöf (`blueprint/P1_PaleyWiener.md`) |
| `DSPerturbation` | Duffin–Schaeffer Lemma III | [DS52] | P2 | feasible: `L²` Bernstein + FTC (`blueprint/P2_DS_JN.md`), `PaleyWienerThm → DSPerturbation` |
| `JohnNirenberg` | John–Nirenberg inequality | [JN61], [Ga81] | P2 | feasible: dyadic stopping time + Lebesgue differentiation (`blueprint/P2_DS_JN.md`) |
| `TheoremD` | reproducing kernel of `H(E)` | [dB68, Thm 19] | P3 | to assess |
| `TheoremE` | orthogonal sampling | [dB68, Thm 22] | P3 | to assess |
| `TheoremF` | isometric measures | [dB60], [dB68, Thm 32] | P4 | to assess |
| `TheoremC` | axiomatic de Branges spaces | [dB68, Thm 23] | P4 | to assess |
| `PavlovBMO` | CIS ⇒ `n_Γ - t ∈ BMO` | [Pa79], [HNP81] | P5 | **not feasible**: needs the Hilbert transform, Muckenhoupt weights and BMO conjugation, none in Mathlib (est. 6–10k lines; `blueprint/P5_Pavlov.md`). Kept as the cited hypothesis `hA` of `landau_inequality`. |

Conventions: Lean files under `FourierFrames/Cited/`, one blueprint `blueprint/P*_*.md` per module,
same standards as `blueprint/WRITING.md`. Each module ends with a theorem
`<prop>_holds : <Prop>` (e.g. `paleyWiener_holds : PaleyWienerThm`). The statements of the `Prop`s
in `Defs.lean` are frozen; if one turns out to be unprovable as stated (too strong), report it.
Writers may use any already-proved project lemma (`FourierFrames/**`, all phase-1 modules are
proved except `Perturbation`/`Corollary2`), but must not create import cycles: `Cited/*` files may
import `Defs`, `PW/*`, `HB/*` only when the corresponding `Prop` is not a hypothesis of the lemma
used (e.g. a proof of `PaleyWienerThm` must not use lemmas taking `hPW`).
