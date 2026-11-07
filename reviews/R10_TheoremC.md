# R10 — Referee report: P4 Part C, de Branges' Theorem C (blueprint and scaffold)

**Referee:** independent review agent, 2026-11-07.
**Scope:** worktree `wt-ff/cited-p4`, branch `impl/cited-p4`, commit `f0e379f`:
* `blueprint/P4_DeBrangesFC.md`, §0–§1 (Part C) and §3–§5;
* `FourierFrames/Cited/DeBrangesFC.lean`: the 43 Part C `sorry` lemmas, the definitions, and the assembly `theoremC_holds`;
* Part F, skimmed for the truth of its statements only;
* checked against `FourierFrames/Defs.lean` (`TheoremC`, `deBrangesKernel`, `MemHE`, `heNormSq`, `IsHB`), the proved P3 files `Cited/DeBrangesDE/{Cauchy,Kernel,Space}.lean`, `HB/{H2,Comparable,DeBranges}.lean`, `reviews/R7_Cited.md` (findings 6–15) and `reviews/R9_DeBrangesDE.md` (F5).

**Write policy.** This is the only file written; the worktree was not modified.
* Lean checks ran on a copy of the worktree in the session scratchpad: `rsync` without `.git`, then a fresh `lake build FourierFrames.Cited.DeBrangesFC`, 9072 jobs, which succeeded with only `declaration uses 'sorry'` warnings. Scratch files were then run with `lake env lean`.
* Numerical checks ran as scratch Python scripts.

**Severity.**
* *Critical:* a false Lean statement, or a proof step that cannot work.
* *Major:* a gap that needs a new idea.
* *Minor:* a wrong name, stale text, or a simplification.
* *OK:* checked and correct.

---

## Summary

* **Part C: no false statement and no broken proof step.**
  * All 43 sorried Part C statements, the definitions (`UHP`, `thetaFn`, `divExt`, `DBAxioms`, `IsKernelFamily`, `kernelE`, `kernelSpan`) and the assembly were checked by hand. All are true as stated, with the hypotheses given.
  * Every proof step named in the brief was re-derived and is correct:
    * `‖k ζ‖ > 0` by induction on the order of vanishing;
    * the unitary `T` from (H1) and the identity (★), including the degenerate cases `w = ζ` and `w = ζ̄`;
    * the formula `E = √π (z+i) K(i,z)/√K(i,i)` and strictness of `E`;
    * density of the kernel span;
    * Fatou on lines, the upgrade to an isometry, and surjectivity via Riesz;
    * the order lemma and the `IsH2Cont` extension.
  * Part C uses no P3 lemma that assumes `h0 : ∀ x, E x ≠ 0`, and there is no circularity.
* **Numbers.** Formula (★), `kernel_mul_eq`, `fstar_kernelE` and strictness were checked numerically on two spaces, to relative error ≤ 5·10⁻¹⁵:
  * on `PW` itself;
  * on `{f ∈ PW : f(0) = 0}`, where the constructed `E` satisfies `E(0) = 0`. This confirms that real zeros of `E` really occur and that §1.2–1.3 are needed.
* **One critical finding, in deferred Part F: `division_lemma` is false as stated** (finding 1). It has a sorry-free Lean disproof (Appendix A) and was sent to `main` by `SendMessage`. It does not affect Theorem C:
  * no Part C lemma and not `theoremC_holds` refers to it;
  * `theoremF_holds` is still `sorry`;
  * `DeBrangesFC` is imported only by `FourierFramesScaffold.lean`.
* **Counts:** 1 critical (Part F), 0 major, 5 minor, plus OK records.

---

## 0. Mechanical checks

| check | how | result |
|---|---|---|
| Scaffold compiles | fresh `lake build FourierFrames.Cited.DeBrangesFC` on a scratch copy of `f0e379f` | OK; only `sorry` warnings; 43 sorries in Part C (the 44th `sorry` before `end PartC` is in the module docstring), 8 + `theoremF_holds` in Part F |
| Assembly | `#print axioms FF.theoremC_holds` | `[propext, sorryAx, Classical.choice, Quot.sound]`: the only gap is the Part C `sorry`s |
| P3 signatures used by Part C | `#check` (see §3) | as the blueprint assumes; none takes `h0` |
| Mathlib names in the blueprint | `#check` on 40 names (meromorphic normal form API, `toDual_symm_apply`, polarization, `topologicalClosure_eq_top_iff`, `Tendsto.inner`, `mkContinuous`, Hölder, `Continuous.ext_on`, `dense_compl_singleton`, `lintegral_liminf_le`, …) | all exist with the stated shape, except `analyticOrderAt_eq_top_iff_eq_zero` (finding 2) |
| `division_lemma` | Lean disproof of its statement, copied word for word | **false**; axioms `[propext, Classical.choice, Quot.sound]` (Appendix A) |
| Kernel algebra | Python, sinc kernel of `PW`, and the kernel of `{f ∈ PW : f(0)=0}` | (★), `kernel_mul_eq`, `fstar_kernelE`, strict HB: residual ≤ 5·10⁻¹⁵; `E(0) = 0` in the second space |

*Note on stale builds.* While this review ran, the worktree's own `.lake/build` held a **pre-merge** `DeBrangesFC.olean`. `lake env lean` against it reported `FF.divExt`, `FF.IsH2Cont` and `FF.heInner` as unknown, and showed the deleted stub `FF.theoremD_holds`. Rebuild before running scratch checks in the worktree.

---

## 1. Truth of the statements (item a)

### 1.1 `TheoremC` (Defs) and its encoding — OK

* **(H1), pointwise off `ζ`.** `ι g` is entire, and the right side `ι h z (z-ζ̄)/(z-ζ)` has a removable singularity at `ζ`, because `ι h ζ = 0`. So `ι g` is determined everywhere, and the off-`ζ` form is equivalent to de Branges'.
* **(H2):** evaluation is continuous at nonreal points, exactly as in de Branges.
* **(H3):** `ι g = fstar (ι h)` as functions, with the same norm.
* **Data.**
  * `Function.Injective ι` makes `H` a space of functions.
  * `ι : H →ₗ[ℂ] (ℂ → ℂ)` is linear for the pointwise structure.
  * `H : Type` with `InnerProductSpace ℂ H` ties the norm to the inner product.
  * `∃ h ≠ 0` is the nontriviality hypothesis.
* **Conclusion.** Only the closed class `IsHB` is required, and that is necessary: in `{f ∈ PW : f(0)=0}` every admissible `E` vanishes at `0` (R7-6, and confirmed numerically here). `MemHE` and `heNormSq` handle real zeros correctly:
  * the `H²` conditions live on `ℂ₊`;
  * the norm integral ignores the countable zero set.
* `TheoremC` is true (de Branges 1968, Thm 23).

### 1.2 Part C lemmas — all true

| group | lemmas | verdict and remarks |
|---|---|---|
| §1.1 helpers | `eq_of_eqOn_upper`, `analyticOrderAt_eq_of_mul_div`, `lintegral_line_le_liminf` | true. In the second, `(z-ζ̄)` does not vanish at `ζ` because `ζ - ζ̄ = 2i Im ζ ≠ 0`. In the third, the left integrand need not be measurable: `∫⁻` is congruence-invariant, and Fatou needs only measurability of the `F n` lines. |
| §1.2 real zeros | `IsHB.ae_ne_zero`, `analyticOrderAt_le_of_isH2Upper_div`, `divExt` + `divExt_eq_of_ne`, `analyticAt_divExt`, `isH2Cont_divExt`, `exists_isH2Cont_of_memHE`, `heNormSq_eq_lintegral_divExt` | true; see §1.3 for `divExt`. Order lemma: if `ord f = k < m = ord E` at `x₀`, then near `x₀` we have `‖f/E‖² ≍ ‖z-x₀‖^{-2(m-k)}`, so `∫ ‖f/E (x+iy)‖² dx ≳ y^{1-2(m-k)} → ∞` as `y → 0`. `ord E = ⊤` is excluded because `E(i) ≠ 0`, and `ord f = ⊤` is trivial. |
| §1.3 `_of_isHB` | 10 lemmas | true for `E ∈ \overline{HB}` without `h0`: everything goes through `divExt`, which is `IsH2Cont` and equals `f/E` a.e. on `ℝ`. `heInner_kernel_upper_of_isHB` is P3's `heInner_kernel_upper_of_isH2Cont`, whose hypotheses (`IsHB`, `E ≠ 0` a.e., `IsH2Cont` `A, B`) are exactly what `exists_isH2Cont_of_memHE` supplies. Strictness is not needed. |
| C.1–C.4 | `eq_zero_of_upper`, `exists_kernel`, `kernel_diag`, `kernel_norm_pos`, `kernel_symm`, `exists_conjMap`, `kernel_fstar` | true. Convention: `ι h ζ = ⟪k ζ, h⟫` is linear in `h`, so `K(w,z) = ι (k w) z = ⟪k z, k w⟫`, which agrees with `heInner` being linear in its first slot (`⟨ι h, K_w⟩_E = ι h w = ⟪k w, h⟫`). `S` from (H3) is conjugate-linear (by injectivity), so `⟪S x, S y⟫ = ⟪y, x⟫`. I checked the polarization bookkeeping in the blueprint term by term: `‖y ∓ I•x‖ = ‖x ± I•y‖`. |
| C.5–C.8 | `exists_mulMap`, `kernel_identity`, `differentiable_kernelE`, `fstar_kernelE`, `kernel_mul_eq`, `kernel_eq_deBrangesKernel`, `isStrictHB_kernelE` | true (§2.2). |
| C.9–C.14 | `memHE_kernel`, `memHE_of_mem_kernelSpan`, `heInner_iota_of_mem_kernelSpan`, `heNormSq_iota_of_mem_kernelSpan`, `kernelSpan_topologicalClosure`, `exists_seq_kernelSpan`, `memHE_iota`, `heNormSq_iota`, `mem_range_of_memHE` | true (§2.3). |
| assembly | `theoremC_holds` | complete and correct given the lemmas (it compiles). |

### 1.3 `divExt` via `toMeromorphicNFOn` — OK, hypotheses exactly right

From `#print toMeromorphicNFOn` and `#print toMeromorphicNFAt` (current Mathlib):
* `toMeromorphicNFOn φ univ z = toMeromorphicNFAt φ z z`. This holds because `φ = f/E` is `MeromorphicOn univ`: `MeromorphicAt.div` of two analytic functions works even at zeros of `E`, and even when `E ≡ 0`. Without `MeromorphicOn`, the whole function would be replaced by `0`; that case cannot occur here.
* `toMeromorphicNFAt φ x` is `Function.update φ x v`, where `v` depends on the meromorphic order of `φ` at `x`:
  * **order = 0:** `v` is the value of the nonvanishing analytic factor;
  * **order ≠ 0:** `v = 0`. This covers positive order, order `⊤`, and **negative order**.

Consequences:
* Where `E(x) ≠ 0`, `φ` is analytic, so `divExt = φ` there (`divExt_eq_of_ne`).
* At a real zero of `E` where `ord f ≥ ord E`, the order of `φ` is `≥ 0`. The value is then the limit: the analytic factor when the order is `0`, and `0` when it is `> 0` or `⊤`. So `divExt` is **the continuous (indeed analytic) extension** of `f/E` (`analyticAt_divExt`).
* **At a pole** (`ord f < ord E`), `divExt E f x = 0` is a junk value, not a limit, and `divExt` is discontinuous there.
* Hypotheses of the lemmas:
  * every lemma that asserts analyticity or continuity of `divExt` either carries `ord E ≤ ord f` (`analyticAt_divExt`) or derives it from `IsH2Upper (f/E)` through `analyticOrderAt_le_of_isH2Upper_div` (`isH2Cont_divExt`, `exists_isH2Cont_of_memHE`, §1.3);
  * `divExt_eq_of_ne` (pointwise where `E ≠ 0`) and `heNormSq_eq_lintegral_divExt` (a.e.) need no order hypothesis and correctly have none.

So poles cannot leak into any statement.

---

## 2. The proofs (item b)

### 2.1 C.1–C.4 — OK
* **`kernel_norm_pos`.** Suppose `k ζ = 0`; then every `ι h` vanishes at `ζ`. Induction on `n` shows `∀ h, ord_ζ (ι h) ≠ n`:
  * `n = 0`: `analyticOrderAt_eq_zero` would give `ι h ζ ≠ 0`;
  * step: if `ord = n+1`, then (H1) gives `g` with `ord_ζ (ι g) = n` (`analyticOrderAt_eq_of_mul_div`), contradicting the induction hypothesis.

  A nonzero `h` has `ι h ≠ 0` (injectivity), hence finite order: contradiction. The norm clause of (H1) is not used, as the blueprint says.
* **`exists_kernel`.** Riesz (`toDual_symm_apply : ⟪(toDual ℂ H).symm y, x⟫ = y x`) gives the right side of the convention.
* **`kernel_fstar`.** The chain `⟪S(k w), v⟫ = ⟪S(k w), S(S v)⟫ = ⟪S v, k w⟫ = conj (ι (S v) w) = ι v (w̄)` is correct.

### 2.2 C.5–C.8 — OK
* **`exists_mulMap`.**
  * `T` is defined by choice on `H_ζ`.
  * Linearity on `H_ζ` follows from injectivity plus equality of entire functions off `ζ`.
  * `⟪T f, T f'⟫ = ⟪f, f'⟫` follows by polarization: `H_ζ` is closed under `f ± f'` and `f ± I•f'`.
  * Onto `H_ζ̄`: (H1) at `ζ̄` gives `g'` with `ι g' ζ = ι g ζ · 0/(ζ - ζ̄) = 0`, and `T g' = g` because both sides are entire and agree off `{ζ, ζ̄}`.
* **`kernel_identity` (★).** Re-derived.
  * `p = k w − (K(w,ζ)/K(ζ,ζ)) • k ζ` and `q` (the same with `ζ̄`) are the reproducing vectors of `H_ζ` and `H_ζ̄` at `w`.
  * For `f ∈ H_ζ`: `⟪q, T f⟫ = (Tf)(w) = c₀ ι f w = ⟪conj c₀ • T p, T f⟫`, with `c₀ = (w−ζ̄)/(w−ζ)`. So `q − conj c₀ • Tp ∈ H_ζ̄ ∩ H_ζ̄^⊥ = 0`.
  * Evaluating at `z ≠ ζ` gives `(z−ζ)(w̄−ζ̄) ι q z = (w̄−ζ)(z−ζ̄) ι p z`, which is exactly the Lean statement.
  * Degenerate cases, checked by hand: for `w = ζ`, `p = 0` and `w̄ − ζ̄ = 0`; for `w = ζ̄`, `c₀ = 0`, `q = 0` and `w̄ − ζ = 0`; for `z = ζ`, both factors vanish. So no extra hypothesis is needed.
  * Numerical check at generic points on `PW`: residual 3·10⁻¹⁶.
* **`kernel_mul_eq` (formula for `E`).** Take `ζ = i`.
  * The coefficient of `K(w,z)` is `(z+i)(w̄−i) − (z−i)(w̄+i) = −2i(z−w̄)`.
  * `(w̄−i)K(w,i) = conj((w+i)K(i,w))` and `(w̄+i)K(w,−i) = conj((w−i)K(−i,w))` (`kernel_symm`).
  * `K(−i,−i) = conj K(i,i) = K(i,i) =: a > 0` (`kernel_fstar`).
  * Hence `−2i(z−w̄)K(w,z) = (P₀(z) conj P₀(w) − Q₀(z) conj Q₀(w))/a`, with `P₀ = (z+i)K(i,·)` and `Q₀ = (z−i)K(−i,·) = P₀^*`.
  * With `E = √π P₀/√a`: `kernelNum E w z = (π/a)(…)`, so `K(w,z) π(z−w̄) = kernelNum/(−2i) = (i/2) kernelNum`. **Correct.**
  * **Recomputed on `PW`.** With `K(i,z) = sin π(z+i)/(π(z+i))` and `K(i,i) = sinh 2π/(2π)`, `kernelE = √(2/sinh 2π) sin π(z+i)`. Using `sin A sin B = (cos(A−B) − cos(A+B))/2`, the numerator is `E(z)Ē(w) − E^*(z)Ē^*(w) = −2i sin π(z−w̄)`. Then `(i/2)(−2i) sin π(z−w̄)/(π(z−w̄))` is the sinc kernel. **`√π` is the right normalisation**, in agreement with R7-6; also checked numerically.
* **`kernel_eq_deBrangesKernel`.** Both sides are continuous; they agree on `{w̄}ᶜ` by `kernel_mul_eq` and P3's `deBrangesKernel_mul`, which holds for all `z`; `Continuous.ext_on` concludes. OK.
* **`isStrictHB_kernelE`.** For `z ∈ ℂ₊`, `0 < ‖k z‖² = K(z,z) = (‖E z‖² − ‖E z̄‖²)/(4π Im z)` (P3 `deBrangesKernel_diag`, unconditional). This gives strictness, hence `E ≠ 0` on `ℂ₊` and the `≤` of `IsHB`. OK.

### 2.3 C.9–C.14 — OK
* **Span lemmas.** `memHE_kernel` comes from P3 `memHE_deBrangesKernel_of_isHB hE (Or.inl hw)`, which holds with real zeros. Span induction then gives `ι x ∈ H(E)` and `⟨ι h, ι x⟩_E = ⟪x, h⟫` whenever `ι h ∈ H(E)`:
  * generators: the reproducing formula at `w ∈ ℂ₊` plus `kernel_eq_deBrangesKernel`;
  * sums: `heInner_add_right_of_isHB`; the `span_induction` motive carries `x ∈ span`, so `MemHE` of the summands is available;
  * scalars: `heInner_smul_right` gives `conj c`, matching `inner_smul_left`.
* **Density.** If `h ⊥ k w` for all `w ∈ ℂ₊`, then `ι h = 0` on `ℂ₊`, so `h = 0` by the identity theorem and injectivity. With `CompleteSpace H`, `Submodule.topologicalClosure_eq_top_iff` applies. OK.
* **Contraction, `memHE_iota`.** Take `x_n → h` in the span.
  * (H2) gives `ι x_n → ι h` pointwise at every nonreal point, so also `fstar (ι x_n) → fstar (ι h)` on `ℂ₊`, through `z̄ ∈ ℂ₋`.
  * Line bounds: `∫ ‖ι x_n/E‖² ≤ ‖ι x_n‖²_E = ‖x_n‖²`, and the same for `fstar` (`memHE_fstar`, `heNormSq_fstar`).
  * Fatou on each line gives `≤ liminf ‖x_n‖² = ‖h‖²`, so both `H²` conditions hold with constant `‖h‖²`.
  * Fatou at the boundary (`heNormSq_le_of_lines_of_isHB`, through `divExt` and `lintegral_real_le_of_isH2`) gives `‖ι h‖_E ≤ ‖h‖`.
  * Correct, with no completeness of `H(E)`.
* **Isometry, `heNormSq_iota`.** `‖⟪x_n,h⟫‖ = ‖⟨ι h, ι x_n⟩_E‖ ≤ √a ‖x_n‖`. Letting `n → ∞` gives `‖h‖² ≤ √a ‖h‖`, so `‖h‖² ≤ a ≤ ‖h‖²`, with the case `‖h‖ = 0` handled. OK, and not circular: `memHE_iota` does not use it.
* **Onto, `mem_range_of_memHE`.**
  * `Λ h = ⟨ι h, f⟩_E` is linear (`heInner_add_left_of_isHB` with `memHE_iota`, then `heInner_smul_left`) and bounded by Cauchy–Schwarz.
  * Riesz gives `u` with `⟪u,h⟫ = Λ h`.
  * For `z ∈ ℂ₊`: `ι u z = conj ⟪u, k z⟫ = conj ⟨K_z, f⟩_E = ⟨f, K_z⟩_E = f(z)`, using P3 `heInner_conj_symm`, which holds unconditionally.
  * The identity theorem concludes. OK.

### 2.4 §1.2 proofs — OK
* **`analyticOrderAt_le_of_isH2Upper_div`.**
  * Suppose `k₀ < m₀`.
  * Set `f₁ = update (f/(z−x)^{k₀}) x (u x)` and `E₁ = update (E/(z−x)^{k₀}) x 0`. Both are entire: off `x` they are quotients, and near `x` they coincide with `u` and `(z−x)^{m₀−k₀} v`, using `m₀ − k₀ ≥ 1` at `x`.
  * Then `f₁ x ≠ 0`, `E₁ x = 0`, `E₁ ≠ 0` on `ℂ₊`, and `f₁/E₁ = f/E` on `ℂ₊`.
  * This contradicts `not_isH2Upper_div_of_zero` (`HB/H2.lean:236`, whose hypotheses match exactly).
  * Sound. Step 1 cites a wrong lemma name (finding 2).
* **`analyticAt_divExt`.** The proof via `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`, `meromorphicOrderAt_div` and `AnalyticAt.meromorphicOrderAt_eq` works, and the names exist. The case `ord E = ord f = ⊤` gives `⊤ − ⊤` in `WithTop ℤ`; the blueprint's case split ("`ord f = ⊤` ⇒ `φ = 0` near `z`") sidesteps it.

---

## 3. P3 dependency audit (item c) — OK, nothing circular, nothing `h0`-gated

The P3 lemmas Part C calls, with their checked signatures. None takes `h0`:
* `heInner_kernel_upper_of_isH2Cont` (`IsHB E`, `∀ᵐ t, E t ≠ 0`, `IsH2Cont A B`, …);
* `memHE_deBrangesKernel_of_isHB` (`IsHB E`, `w.im ≠ 0 ∨ E w ≠ 0`);
* the unconditional kernel algebra: `deBrangesKernel_mul`, `deBrangesKernel_diag`, and `differentiable_deBrangesKernel` (`Differentiable E` only);
* `IsH2Cont.lintegral_line_le`, `.lintegral_real_lt_top`, `.memLp_real`;
* from `Space.lean` §4.1–4.2: `MemHE.add/const_mul`, `memHE_zero`, `memHE_fstar`, `heNormSq_fstar`, `heInner_conj_symm`, `heInner_smul_left/right`.

Also h0-free, and usable:
* `heInner_self` and `measurable_div_real`, which need `hE : IsHB E` only (finding 3);
* `lintegral_enorm_sq_le_of_tendsto`, a general Fatou lemma with no hypothesis on `E`.

Correctly avoided because they take `h0`: `isH2Cont_of_memHE`, `MemHE.heNormSq_lt_top`, `integrable_heInner`, `heInner_kernel_upper/lower/real`, `heInner_kernel`, `memHE_deBrangesKernel`, `deBrangesKernel_diag_nonneg`, `heInner_add_left/sub_*`, `norm_heInner_sq_le`, `MemHE.lintegral_line_le`, `memHE_of_cauchy`, and the rest of §4.3–4.4.

`theoremD_holds` and `TheoremD` are not used by Part C, which matters because `TheoremD` assumes no real zeros. P3 does not import P4. No cycle.

---

## 4. Part F (skimmed for statement truth)

| lemma | verdict |
|---|---|
| `isometric_moment` (F.1) | true: `‖K(i,t)/E(t)‖ ≥ (‖E(i)‖−‖E^*(i)‖)/(2π√(1+t²))` with a strict inequality between the two terms |
| `herglotzG_spec` (F.2) | true: the integrand is `(1+tz)/((t−z)(1+t²)) = O_z(1/(1+t²))`, and its real part is the Poisson kernel |
| `cauchy_pairing_zero` (F.3) | true (re-derived: `K_v/E = (i/2π) Ē(v)/(t−v̄)` when `E^*(v) = 0`) |
| `cauchy_pairing_general` (F.4) | true with the R7-11 hypothesis `‖Θ(z)‖ ≤ 1/2`: the error is `Θ(z)·∫ conj Θ dμ/((t−w̄₀)(t−z))`, and `P ≤ 3` |
| `poisson_diag_estimate` (F.5) | true: `(1−s)/(1+s) ≤ P ≤ (1+s)/(1−s)`; finiteness of `poissonInt` comes from F.1, so `toReal` is safe |
| `exists_imag_limit` (F.6) | true (even with `a' = a`): gradient bound on unit discs, then Cauchy–Riemann |
| `inner_factorization` (F.7) | true: the classical factorization of a meromorphic inner function plus Blaschke division |
| **`division_lemma` (F.8)** | **FALSE**: finding 1 |
| `theoremF_holds` | true (R7-9) |

---

## 5. Findings

### 1. [critical — Part F only; does not affect Theorem C] `division_lemma` is false as stated
*Evidence.* The only link between `(a, θ, B)` and `Θ` is `hfac : Θ = e^{i(az+θ)} B` on `ℂ₊`. That hypothesis is satisfied by **every** real `a`: take `B := Θ e^{−i(az+θ)}`. Choosing `a` below the true exponential type of `Θ` weakens `hdec` until the conclusion fails.

*Counterexample.*
* Let `E(z) = e^{−iz/2}`. Then `|E(x+iy)| = e^{y/2}`, so `E` is strict HB with no zeros, and `Θ = E^*/E = e^{iz}`: true type `1`, no zeros.
* Take `a = θ = 0`, `B = Θ` and `Ξ ≡ 1/2`.
* Every hypothesis holds:
  * `hfac` is trivial;
  * `‖Ξ‖ ≤ 1`;
  * `hz` is vacuous, since `Θ` has no zeros;
  * `hdec`: for `a' < 0` and `Im z ≥ 1`, `1/2 ≤ 1·e^{−a' Im z}`.
* The conclusion at `z = 10i` would give `1/2 ≤ |Θ(10i)| = e^{−10}`, which is false.
* The same works for any `a` strictly below the true type, for example `a = 1/2` with `Ξ = e^{iz/2}/2`.
* The sorry-free Lean proof of `¬ DivisionLemmaStmt` (the statement copied word for word) is in Appendix A; axioms `[propext, Classical.choice, Quot.sound]`.

*Cause.* The blueprint's proof of F.8 applies F.7's division clause to *this* `B`. That is valid only for the `B` that `inner_factorization` produces, and the Lean statement does not record that.

*Fix.* Add the rest of `inner_factorization`'s conclusion as hypotheses:
```lean
    (ha : 0 ≤ a) (hB1 : ∀ z ∈ UHP, ‖B z‖ ≤ 1)
    (hdiv : ∀ (Ψ : ℂ → ℂ) (M : ℝ), DifferentiableOn ℂ Ψ UHP → (∀ z ∈ UHP, ‖Ψ z‖ ≤ M) →
      (∀ z ∈ UHP, thetaFn E z = 0 → analyticOrderAt (thetaFn E) z ≤ analyticOrderAt Ψ z) →
      ∀ z ∈ UHP, ‖Ψ z‖ ≤ M * ‖B z‖)
```
* `ha` and `hB1` alone do **not** repair the lemma: the counterexample satisfies both.
* `hdiv` is what pins `a`. Write `Θ = c e^{ia₀z} B₀` with `a₀` the true type and `B₀` the Blaschke product. Then `hfac` forces `B = c' e^{i(a₀−a)z} B₀`. Applying `hdiv` to `Ψ = B₀` (or `Ψ ≡ 1` when `Θ` has no zeros) gives `|B₀| ≤ e^{−(a₀−a)y}|B₀|`, hence `a ≥ a₀`. For `a ≥ a₀` the lemma is true.
* With `hdiv` the blueprint's F.8 argument goes through:
  1. `Ξ e^{−ia'z}` is bounded;
  2. so `|Ξ| ≤ M' e^{(a−a')y}|Θ|`;
  3. `Ξ/Θ` is holomorphic, with `limsup ≤ 1` at `ℝ` because `|Θ| → 1` there;
  4. Phragmén–Lindelöf, then `a' → a`.
* Alternatively, merge F.7's division clause into F.8, as R7-12 suggests, so that `B` is never exposed.

F.9 applies F.8 only to the `(a, θ, B)` of F.7, so nothing downstream changes. `SendMessage` was sent to `main`.

### 2. [minor] Wrong Mathlib name in the blueprint: `analyticOrderAt_eq_top_iff_eq_zero`
*Evidence.* §1.2 (order lemma, step 1) and §1.4 (`kernel_norm_pos`) cite `analyticOrderAt_eq_top_iff_eq_zero`. In Mathlib the lemma is `AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (z : 𝕜) (hf : ∀ z₀, AnalyticAt 𝕜 f z₀) : analyticOrderAt f z = ⊤ ↔ f = 0` (`Analysis/Analytic/Order.lean:720`, inside `namespace AnalyticOnNhd`). The root name does not resolve. *Fix.* Use the namespaced name with `fun z ↦ hE.analyticAt z`. Alternatively, use `analyticOrderAt_eq_top` together with the identity theorem.

### 3. [minor] Stale text about P3 in the blueprint
*Evidence.*
* "Depends on" says that P3's lemmas "are `sorry` and are being proved in parallel", and §5 says that `heInner_kernel_upper_of_isH2Cont`, … "are `sorry` today". P3 is fully proved: `grep sorry` finds nothing in `Cited/DeBrangesDE/**`, and `DeBrangesDE.lean` assembles D and E.
* The "not usable" list includes `heInner_self`, but `FF.heInner_self : IsHB E → MemHE E f → heInner E f f = ↑(heNormSq E f).toReal` takes no `h0`. Likewise `measurable_div_real` needs only `hE`.

*Fix.*
* Update the status text.
* Prove `heInner_self_of_isHB` as `heInner_self hE hf`. It is redundant, not wrong.
* Reuse P3's `norm_heInner_sq_le` proof for `norm_heInner_le_of_isHB`: it uses `h0` only through `MemHE.heNormSq_lt_top`, which can be replaced by `MemHE.heNormSq_lt_top_of_isHB`.

### 4. [minor] Small simplifications (optional)
* `mem_range_of_memHE` needs only the contraction `heNormSq (ι h) ≤ ‖h‖²` from `memHE_iota` to bound `Λ`, not the isometry `heNormSq_iota`. This removes one dependency.
* P3's `lintegral_enorm_sq_le_of_tendsto` (a general Fatou lemma with an eventual bound) is available. `lintegral_line_le_liminf` is fine as it stands and is already proved in the implementer's draft.

### 5. [minor, coordination] Implementer's untracked `FourierFrames/Cited/DeBrangesFC/Analytic.lean`
*Evidence.* The file appeared during the review. It redeclares `eq_of_eqOn_upper`, `analyticOrderAt_eq_of_mul_div`, `lintegral_line_le_liminf`, `IsHB.ae_ne_zero`, `divExt`, `divExt_eq_of_ne` and `analyticAt_divExt` under the same names as the scaffold. It also adds `eq_of_eventuallyEq_entire`, `eq_of_eqOn_open`, `eq_of_eq_off_finite`, `sub_conj_ne_zero`, `meromorphicOn_div_entire` and `meromorphicOrderAt_divExt`; none of these clashes with an existing project name.
* Its `divExt` definition is identical to the scaffold's, so no downstream statement changes.
* The proofs read correctly, though I did not compile that file.

*Fix.* Delete the scaffold copies when `DeBrangesFC.lean` imports the new file, to avoid duplicate declarations.

### OK records (so the checks are not repeated)
* `TheoremC` encoding: (H1) pointwise off `ζ` is equivalent to de Branges' form; injectivity, linearity, `Type`, the instances, and the closed class in the conclusion are right (§1.1).
* `divExt` hypotheses: continuity is claimed only under `ord E ≤ ord f` or `IsH2Upper (f/E)`; poles carry the junk value `0` and never reach a statement (§1.3).
* (★) has no missing hypothesis: the degenerate cases `w = ζ`, `w = ζ̄` and `z = ζ` were checked (§2.2).
* `E = √π (z+i)K(i,z)/√K(i,i)` was recomputed on `PW` by hand and numerically, and also checked numerically on `{f ∈ PW : f(0)=0}`, where `E(0) = 0` (§2.2).
* RKHS uniqueness: no completeness of `H(E)` is needed, Riesz is applied in `H`, and there is no circularity among `memHE_iota`, `heNormSq_iota` and `mem_range_of_memHE` (§2.3).
* P3 usage is `h0`-free and acyclic (§3).

---

## Appendix A — Lean disproof of `division_lemma`

Run with `lake env lean` against a fresh build of `f0e379f`. Output: `'FF.not_divisionLemmaStmt' depends on axioms: [propext, Classical.choice, Quot.sound]`.

```lean
import FourierFrames.Cited.DeBrangesFC
open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF

/-- `E(z) = e^{-iz/2}`: strict Hermite–Biehler, no real zeros, `Θ = e^{iz}` (`a = 1`, no zeros). -/
noncomputable def Ecx : ℂ → ℂ := fun z ↦ Complex.exp (-(I * z) / 2)

lemma norm_Ecx (z : ℂ) : ‖Ecx z‖ = Real.exp (z.im / 2) := by
  simp only [Ecx, Complex.norm_exp]
  congr 1
  simp

lemma fstar_Ecx (z : ℂ) : fstar Ecx z = Complex.exp (I * z / 2) := by
  simp only [fstar, Ecx]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_neg, map_mul, Complex.conj_I, Complex.conj_conj, map_ofNat]
  ring

lemma theta_Ecx (z : ℂ) : thetaFn Ecx z = Complex.exp (I * z) := by
  simp only [thetaFn, fstar_Ecx, Ecx]
  rw [div_eq_iff (Complex.exp_ne_zero _), ← Complex.exp_add]
  congr 1
  ring

lemma strict_Ecx : IsStrictHB Ecx := by
  refine ⟨⟨?_, fun z _ ↦ Complex.exp_ne_zero _, fun z hz ↦ ?_⟩, fun z hz ↦ ?_⟩
  · unfold Ecx; fun_prop
  · rw [norm_Ecx, norm_Ecx]; simp only [Complex.conj_im]; gcongr; linarith
  · rw [norm_Ecx, norm_Ecx]; simp only [Complex.conj_im]; gcongr; linarith

/-- The statement of the scaffold's `division_lemma`, verbatim, universally quantified. -/
def DivisionLemmaStmt : Prop :=
  ∀ (E : ℂ → ℂ), IsStrictHB E → (∀ x : ℝ, E x ≠ 0) → ∀ {a θ : ℝ} {B : ℂ → ℂ},
    (∀ z ∈ UHP, thetaFn E z = Complex.exp (I * (a * z + θ)) * B z) → ∀ {Ξ : ℂ → ℂ},
    DifferentiableOn ℂ Ξ UHP → (∀ z ∈ UHP, ‖Ξ z‖ ≤ 1) →
    (∀ z ∈ UHP, thetaFn E z = 0 → analyticOrderAt (thetaFn E) z ≤ analyticOrderAt Ξ z) →
    (∀ a' : ℝ, a' < a → ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im → ‖Ξ z‖ ≤ C * Real.exp (-(a' * z.im))) →
    ∀ z ∈ UHP, ‖Ξ z‖ ≤ ‖thetaFn E z‖

theorem not_divisionLemmaStmt : ¬ DivisionLemmaStmt := by
  intro hstmt
  have hfac : ∀ z ∈ UHP, thetaFn Ecx z =
      Complex.exp (I * (((0 : ℝ) : ℂ) * z + ((0 : ℝ) : ℂ))) * thetaFn Ecx z := by
    intro z _; simp
  have hdec : ∀ a' : ℝ, a' < 0 → ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im →
      ‖(fun _ : ℂ ↦ (1 / 2 : ℂ)) z‖ ≤ C * Real.exp (-(a' * z.im)) := by
    intro a' ha'
    refine ⟨1, fun z hz ↦ ?_⟩
    have h1 : 1 ≤ Real.exp (-(a' * z.im)) := Real.one_le_exp (by nlinarith)
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    simp only [this]
    linarith
  have h := hstmt Ecx (a := 0) (θ := 0) (B := thetaFn Ecx) strict_Ecx
    (fun x ↦ Complex.exp_ne_zero _) hfac (Ξ := fun _ ↦ (1 / 2 : ℂ)) (differentiableOn_const _)
    (fun z _ ↦ by norm_num)
    (fun z _ hz ↦ by rw [theta_Ecx] at hz; exact absurd hz (Complex.exp_ne_zero _))
    hdec (10 * I) (by simp [UHP])
  rw [theta_Ecx, Complex.norm_exp] at h
  have e : (I * (10 * I)).re = -10 := by simp
  rw [e] at h
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  simp only [this] at h
  have h2 : Real.exp (-10) < 1 / 2 := by
    have := Real.exp_one_gt_d9
    have h3 : Real.exp (-10) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by norm_num)
    rw [Real.exp_neg 1] at h3
    have h4 : (Real.exp 1)⁻¹ < 1 / 2 := by
      rw [inv_lt_comm₀ (by positivity) (by norm_num)]; norm_num; linarith
    linarith
  linarith

#print axioms not_divisionLemmaStmt

end FF
```

## Appendix B — numerical checks (Python, `cmath`)

* **On `PW`.** `K(w,z) = sin π(z−w̄)/(π(z−w̄))` and `E = √π(z+i)K(i,z)/√K(i,i)`.
  * Over 20 random `(w, z)` with `w` nonreal: `max |K(w,z)π(z−w̄) − (i/2)(E(z)Ē(w) − E^*(z)Ē^*(w))| / max(1,|lhs|) = 4.0·10⁻¹⁵`.
  * `|E − √(2/sinh 2π) sin π(z+i)| = 1.6·10⁻¹⁷`.
  * `fstar_kernelE` residual `0`.
  * (★) at `ζ = 0.3+0.8i`, `w = −1.1+0.5i`, `z = 0.9−0.7i`: residual `3·10⁻¹⁶`, against `|lhs| = 0.30`.
  * Strict HB holds at the grid points tested.
* **On `{f ∈ PW : f(0)=0}`.** `K₀(w,z) = K(w,z) − K(0,z)K(w,0)/K(0,0)`.
  * `kernel_mul_eq`: max relative error `2.3·10⁻¹⁵` over 30 random pairs.
  * `E(0) = 0` exactly.
  * Strict HB holds on a grid down to `Im z = 0.01`.
