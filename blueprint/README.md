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
`OCS`; do not edit).

## 0. Workflow

Same workflow as the companion projects (`../MR1949832`, `../MR1682065`, `../MR2006561`):
1. Blueprint: one Markdown file per module with a detailed proof, the Lean statements and explicit
   dependencies.
2. Scaffold: all statements compiled, proofs `sorry`.
3. Independent agent review of the blueprint and of every statement (`reviews/`).
4. Implementation (git worktrees, `scripts/new_worktree.sh`).
5. `comparator` check of the main results against the self-contained `FFChallenge.lean`.
6. `formalization.yaml`, `NOTEBOOK.md`, and the corrected paper in `fixed/` (local only, not
   committed).

**Phases.**
- *Phase 1*: the paper's own arguments, with the cited results (Paley–Wiener, de Branges C/D/E/F,
  Pavlov's Theorem A, John–Nirenberg, Duffin–Schaeffer Lemma III) as explicit `Prop` hypotheses
  defined in `Defs.lean`. Every main theorem takes exactly the cited `Prop`s it uses.
- *Phase 2*: discharge cited results, in order of feasibility: Paley–Wiener (Mathlib has the
  `L²` Fourier transform as an isometry), Duffin–Schaeffer, John–Nirenberg, then de Branges'
  Theorems D, E, F, C. Pavlov's theorem is the deepest and may stay a hypothesis.

## 1. What is formalized (main results, `comparator/statements.lean`)

| Paper | Lean (namespace `FF`) | Cited hypotheses |
|---|---|---|
| p. 790: Fourier frame ⟺ sampling | `isFourierFrame_iff_isSampling` | PW |
| p. 799: `|E| ≃ e^{π Im z}` on `Im z ≥ 0` ⇒ `H(E) = PW` | `heEqPW_of_comparable` | PW |
| Theorem 1, ⇒ | `theorem1_necessity` | PW, C, F |
| Theorem 1, ⇐ | `theorem1_sufficiency` | PW, E |
| Theorem 1 | `theorem1` | PW, C, E, F |
| Remark p. 797: CIS ⇒ zero set of `E + E^*` | `completeInterpolating_zero_set` | PW, C, D |
| Corollary 1 | `corollary1` | PW, C, E, F |
| Claim (Landau's inequality = Theorem B) | `landau_inequality` | PW, C, E, F, A, JN |
| Example p. 798 is CIS | `logExample_isCompleteInterpolating` | PW, E |
| Example p. 798, counting | `logExample_count` | — |
| Landau's inequality is sharp | `landau_sharp` | PW, E |
| Corollary 2 | `corollary2` | PW, E, DS |
| Theorem 2 (i) | `theorem2_i` | PW, E, DS |
| Theorem 2 (ii) | `theorem2_ii` | PW |

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
3. **`G = (EF + E^*F^*)/2` (p. 796)** follows by adding `M + 1 = EF/G` and `M - 1 = -E^*F^*/G`;
   the "real part on the real axis" argument is not needed.
4. **Herglotz normalisation.** In (3) the paper uses `1/(z - λ_k) + 1/λ_k`, undefined if
   `0 ∈ Λ`. Use `1/(λ_k - z) - λ_k/(1 + λ_k²)` and constants: `M` is
   `(-i/π) ∑ c_k (1/(λ_k - z) - λ_k/(1+λ_k²)) - ipz + ia` with `c_k = |E(λ_k)|²`, and the
   canonical product `G` of genus one handles `0 ∈ Λ` with a factor `z`.
5. **The limit `α → π/2` (p. 797).** "By (4) we may apply dominated convergence" is not a
   domination. Use the local Plancherel–Pólya inequality: the tails
   `∑_{|λ_{α,k}| > R} |f(λ_{α,k})|²` are bounded by `C ∫∫_{|x| > R-1, |y| < 1} |f|²`, uniformly in
   `α`, and this tends to `0`.
6. **Meĭman's theorem is replaced.** As usually quoted (interlacing zeros + exponential type) it is
   false: `A = cos πz`, `B = e^{az} sin πz` have interlacing zeros, but for `a ≠ 0` neither
   `A - iB` nor `A + iB` is in `\overline{HB}`. In Corollary 2, `A` and `B` are limits of the
   symmetric partial products, which are real polynomials with interlacing zeros; for those the
   polynomial Hermite–Biehler theorem is elementary (partial fractions, residues of constant
   sign), and `\overline{HB}` is closed under locally uniform limits (Hurwitz). See M07.
7. **Levin's theorem is avoided.** The example `{k + log⁺|k|}` is handled by the Corollary 2
   construction with `F = 1`: `A` is the generating function, `E = A - iB`,
   `|E| ≃ e^{π Im z}` on `Im z ≥ 0` (the "sine-type" estimate, which the paper asserts without
   proof), and Theorem E gives that `Λ = {A = 0} = {E + E^* = 0}` is complete interpolating.
8. **Separation of `Γ_α` in Corollary 1** (needed to apply Pavlov's theorem, which is stated for
   separated sequences) follows from Theorem E: the interpolant `f_γ` of `δ_γ` has norm
   `≲ 1`, and the Bernstein/Cauchy bound `|f'| ≲ ‖f‖_PW` on `ℝ` gives `|γ - γ'| ≳ 1`.

## 4. Modules

| # | Doc | Lean | Content | Paper |
|---|---|---|---|---|
| M00 | `M00_Defs.md` | `Defs.lean` | definitions, cited `Prop`s, main statements | — |
| M01 | `M01_PW.md` | `PW/*.lean` | Paley–Wiener space toolkit from `PaleyWienerThm` | §1 |
| M02 | `M02_HB.md` | `HB/*.lean` | `f^*`, `\overline{HB}`, phase, `H(E)`, "evident fact" | §2, p. 799 |
| M03 | `M03_Necessity.md` | `Theorem1/Necessity.lean` | Theorem 1 ⇒ | §3 |
| M04 | `M04_Sufficiency.md` | `Theorem1/Sufficiency.lean`, `Corollary1.lean` | Theorem 1 ⇐, Corollary 1, remark p. 797 | §3–4 |
| M05 | `M05_Landau.md` | `Landau.lean` | Claim (Landau from John–Nirenberg + Pavlov) | §4 |
| M06 | `M06_LogExample.md` | `LogExample.lean` | the example `{k + log⁺|k|}` and sharpness | §4 |
| M07 | `M07_Corollary2.md` | `Construction.lean`, `Perturbation.lean`, `Corollary2.lean` | phase construction `E = A - iB`, perturbation lemma, Corollary 2 | §5 |
| M08 | `M08_Theorem2i.md` | `Theorem2i.lean` | Theorem 2 (i): the Lyubarskii–Malinnikova approximation | §5 |
| M09 | `M09_Theorem2ii.md` | `Theorem2ii.lean` | Theorem 2 (ii) | §5 |
| M10 | `M10_Frames.md` | `Frames.lean` | Fourier frame ⟺ sampling | §1 |

### Dependency graph

```
M00 ── M01 ─┬─ M02 ─┬─ M03 ──┐
            │       ├─ M04 ──┴── M05
            │       └─ M07 ─┬─ M06
            │               ├─ M08
            │               └─ M09
            └─ M10
OCS (vendored Lemma 3) ── M07, M09
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
- `exists_memPW_eval_ne_zero : ∃ g, MemPW g ∧ g 0 = 1`, and `pw_eval_lower` (a uniform `c > 0`
  with: for every real `x` some `f ∈ PW` has `c * pwNormSq f ≤ ‖f x‖ₑ²`, `pwNormSq f ≠ 0, ⊤`).
- `pw_deriv_bound (hPW)`: `‖deriv f x‖ ^ 2 ≤ C * (pwNormSq f).toReal` for real `x`.
- `MemPW.isH2Upper_mul_exp (hPW)`: `f ∈ PW ⇒ f(z) e^{iπz} ∈ H²(ℂ₊)` with
  `∫|f(x+iy)e^{iπ(x+iy)}|²dx ≤ ‖f‖²`.
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
  zeros).
- `HEEqPW.phaseDeriv_mul_sq_ge (hPW) (hE : TheoremE)` and `..._le`: `φ_E'(x)|E(x)|² ≃ 1`.
- `memHE_sAlpha_unique`: `S_α, S_β ∈ H(E)` ⇒ `β - α ∈ πℤ` (`E` strict).
- `heEqPW_of_comparable` (main result).

**M07 (construction, `Construction.lean`)** — consumed by M06 and M07 (Corollary 2):
```lean
/-- The phase construction of p. 801: for a density `m ≃ 1` with `m → 1` at `±∞`, the generating
function `A` of the [OS99] barycentre sequence `Γ = OCS.multGamma m`, a companion `B` with
interlacing zeros, and `E = A - iB`. -/
theorem exists_hb_of_density {m : ℝ → ℝ} (hm : Measurable m) {a b : ℝ} (ha : 0 < a)
    (hlow : ∀ t, a ≤ m t) (hup : ∀ t, m t ≤ b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    ∃ E : ℂ → ℂ, IsHB E ∧ (∀ x : ℝ, E x ≠ 0) ∧
      (∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
        c * Real.exp (OCS.multU m 0 z) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (OCS.multU m 0 z)) ∧
      (∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ OCS.multGamma m, z = (γ : ℂ)) ∧
      ∃ φ : ℝ → ℝ, IsPhaseFunction E φ ∧ ∃ c₀ : ℝ,
        Tendsto (fun x ↦ φ x - Real.pi * OCS.multPrim m x) (cocompact ℝ) (𝓝 c₀)
```
(The M07 writer may strengthen this; any change must keep it usable by M06.) M07 also exports
`IsSampling.of_perturbation (hPW) (hDS)`: a separated sampling `Γ` and an injective perturbation
`γ ↦ γ + δ(γ)` with `δ → 0` along `Γ` (finitely many arbitrary moves allowed) give a sampling
sequence. M08 consumes the main statement `corollary2`; M09 consumes `OCS.lemma3` directly.

## 4a. Known issues in the source (seeds for `../NOTEBOOK.md`; each to be verified)

- p. 790, l. 4 of §1 "1)": fine. (Placeholder: check the definition of `PW` norm.)
- p. 793, Theorem E as printed in the tex/print has "∉" (correct); the OCR shows "∈".
- p. 794, display after (2): `sup |f(x)|` should be `sup |f(x)|²` in the middle term (p. 796).
- p. 795, (3): `1/λ_k` undefined when `0 ∈ Λ`; normalisation constants (`π`) to check against
  Theorem F.
- p. 796: "`φ_{EF} = φ_E + φ_F ≥ φ_E`" should be about derivatives.
- p. 796, (5) and the display before it: the factor `π` of Theorem E is missing (harmless).
- p. 796, end of §3 proof: "`α ∈ (0, π]`" then "`α ∈ [0, π)`".
- p. 797: dominated convergence is not justified by (4) (§3.5 above).
- p. 799, proof of the Claim: "`h'(t) = -1` for `t ∉ Λ`" should be "`t ∉ Γ`", and "the separation
  distance of `Λ`" should be "of `Γ`" (`h = n_Γ - t`); `log|I|` needs `|I| > 1`.
- p. 798: "is a sine-type function" is asserted without proof.
- p. 800: `U_ψ` principal value need not exist (§2.5).
- p. 800, proof of Corollary 2: Meĭman's theorem as quoted (§3.6); "we may assume `ω' ≃ 1`";
  normal-family step only treats `x → +∞`.
- p. 802: `log|f(z)| = ∑ ∫_{r_{n-1}}^{r_n} …` should integrate over `[t_{n-1}, t_n]` (mass 1 per
  zero); the same in (10).
- pp. 804–805, Theorem 2 (ii): `ψ_n(t)` should be `ψ(t)`; "the assumption `φ_n'(t) = o(1/t)`"
  should be `ψ'`; `ε_n → 0` is false in general (for `ψ = log log x`, the defining equation gives
  `ε_n ≈ 0.37`); the claims `U_n(x) + ½ log x ≃ 1` and (11) do not follow as written. The proof of
  (ii) must be reconstructed (M09).
