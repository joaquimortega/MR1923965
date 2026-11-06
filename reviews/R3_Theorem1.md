# R3 — Referee report: Theorem 1 (M03 necessity, M04 sufficiency/Corollary 1/remark p. 797, M05 Landau)

Scope: `blueprint/M03_Necessity.md`, `M04_Sufficiency.md`, `M05_Landau.md`; scaffolds
`FourierFrames/Theorem1/{Necessity,Sufficiency,Main}.lean`, `FourierFrames/Corollary1.lean`,
`FourierFrames/Landau.lean`; cited `Prop`s of `FourierFrames/Defs.lean`; main statements of
`comparator/statements.lean`. Sources: page images `literature/pages/p-03, p-06 … p-11` (journal pp. 791,
794–799) and `literature/ArxivOrtega.tex`. All scaffolds are still `sorry`-filled (Necessity 63, Sufficiency 33,
Corollary1 40, Landau 7; compile status taken from the blueprints and sorry counts, no build run); the report therefore judges the *statements* and the *proof plans*.

## Summary verdict

No critical or major mathematical defect found. Every Lean statement in scope is true as stated (checked
against edge cases: empty/finite Λ, `Real.log 0`, `tsum` of non-summable families, `deriv`/`dslope` at the node,
`ENNReal` division, `ncard` of infinite sets). The proof plans of M03, M04, M05 are, in my reading, complete and
correct, including the points the brief singles out (details below). The findings are minor: two partial refutations/refinements of doc claims (R3-1, R3-2), a few imprecisions, and integration risks. Source issues and notebook
entries are almost all confirmed.

## Numbered findings

### R3-1 (minor, doc) — M05 Issue 4 and N-34 first bullet say "the paper never says Γ is separated": refuted
Journal p. 791 (`p-03.png`), right after the definition of `n_Λ`: "It is plain that all complete interpolating
sequences are separated." (tex: "It is plain that all complete interpolating sequences are separated.") So the
paper *asserts* separation of CIS (without proof), which is what Theorem A needs. What is true: Corollary 1 does
not restate it, and the Lean `PavlovBMO` takes `IsSeparated Γ` as a hypothesis, so the formalization must *prove*
that the `Γ` of Corollary 1 is separated — which `corollary1_strong` does via Theorem E + Bernstein
(`HEEqPW.levelSet_separated`). Fix: reword M05 Issue 4 / N-34 bullet 1 to "asserted as plain on p. 791, not proved;
the formal chain needs `corollary1_strong`".

### R3-2 (minor, doc) — N-34 bullet 2: "CIS ⇒ sampling" is also taken for granted in the paper
p. 791 defines CIS "equivalently, if it is sampling but fails to be so on the removal of any one of the points".
So "CIS ⇒ sampling" is implicitly used by the paper (the remark on p. 797 "follows from Theorems C and E" uses it
to apply Theorem C). The gaps listed (orthogonality via Theorem D, completeness, rotation) remain genuine. Note also
that the remark can be derived from E (as the paper says) only after one adds the explicit kernel formula (1)
(= Theorem D) to identify the kernel at `λ` with the interpolant of `δ_λ`; the plan (Theorem D) is the right one.

### R3-3 (minor, doc) — M03 Issue 3 / N-07: the printed convergence factor is legitimate
M03 §11.3 says `∑|E(λ_k)|²/λ_k` need not converge, which is why a convergence factor is needed. That is correct; the
paper does have one: the printed kernel `1/(z-λ_k) + 1/λ_k = z/(λ_k(z-λ_k))` is `O(1/λ²)` and converges once
`∑|E(λ_k)|²/(1+λ_k²) < ∞`. It differs from the Lean factor `λ/(1+λ²)` by `1/(λ(1+λ²))`, which is summable against
`|E(λ)|²`. So the genuine defects of (3) are exactly: the global sign, the missing `1/π`, and `λ_k = 0`. Small nit
in M03 §11 item 1: "`+i∑|E|²(1/(z-λ_k) - …)`" has a stray minus (`-i·hk = i/(z-λ) + iλ/(1+λ²)`). No effect on the
plan (`hk` is correct; `re_neg_I_mul_hk` check `z=i, λ=0 ↦ 1` is right).

### R3-4 (minor) — `TheoremF` in the p-term form: justified, but note the one place p enters
`M(z) = (-i/π)S(z) - i p z + i a` has `M^* = -M` and `Re(-i p z) = p y`, so the plan is unchanged. Nothing in the
paper's text shows `p = 0`; the paper's printed Theorem F (p. 794) has none, and for non-strict `E` (e.g. `E = 1`,
`H(E) = {0}`) the printed "iff" is actually false (hypothesis vacuous, conclusion forces a finite Poisson integral),
so the Lean restriction to strict `E` without real zeros is needed, as claimed in N-02. No action.

### R3-5 (minor, integration) — Interface drift of M04 scaffolds against M02/M03 real lemmas
`Sufficiency.lean`/`Corollary1.lean` "upstream interface" still declare `MemHE.mul_isHB (hE hF hF0 hf)`,
`heNormSq_mul (hF0)`, `memHE_sAlpha_unique (hE : IsStrictHB E)` and `HEEqPW.isStrictHB (hPW)`, while
`HB/DeBranges.lean` has `MemHE.mul_isHB (hF) (hf)`, `heNormSq_mul (hF : IsHB F)`, `memHE_sAlpha_unique (hE : IsHB E)`
(about `sAlpha`) and `HEEqPW.isStrictHB` without `hPW`. All real versions are true (I checked: `heNormSq_mul` with only
`F ∈ \overline{HB}` is true because `F ≢ 0` has countably many real zeros, a null set), i.e. stronger, so the
consumer just adapts; `blueprint/IMPORTS.md` already tracks most of this (and `exists_HB_of_sampling` → `exists_E`).
Suggested fix: update M04 text/scaffolds to the owner signatures; `Exceptional E α` is `MemHE E (sAlpha E α)` by
`rfl`.

### R3-6 (minor, completeness of the plan) — exceptional `α` and the lower bound on `φ_E'|E|²`
`HEEqPW.phaseDeriv_mul_sq_ge` (M02 §10) handles the exceptional level by density + continuity of `κ = φ'|E|²`
(correct: exceptional `x`'s form a countable set since `φ` is injective). N-06 should mention this, since the claim
"the norm identity at the level set through x" fails when that level is the exceptional one. Only the lower bound
`κ ≥ c` is needed for Theorem 1 (it bounds `orthWeight ≤ π/c`); the upper bound `_le` is not used by necessity,
sufficiency, Corollary 1 or M05.

### R3-7 (minor, note) — Non-circularity of `phase_tendsto`
`HEEqPW.phase_tendsto` uses `levelSet_separated` and Theorem E at a non-exceptional `α`, and `phaseDeriv_mul_sq_ge`;
none of these uses surjectivity of `φ_E`. Checked: no circularity. The argument (finite `Γ∩[0,∞)` if `φ` bounded
above, translates `g(·-R)`, uniform PP tails for the δ-separated `(Γ∩(-∞,0)) - R ⊆ {x ≤ -R}`) is correct.

### R3-8 (minor, constants) — M05 "`C, c` absolute" (Issue 5)
The paper says "for some sufficiently big `A`, with `C, c` absolute", so `A` is allowed to depend on `‖h‖_*`; there is
no error in the paper. Verdict below.

## (a) Truth of the Lean statements (all TRUE)

* `theorem1_necessity`, `theorem1_sufficiency`, `theorem1`, `completeInterpolating_zero_set`, `corollary1`,
  `landau_inequality`: true; none is vacuous or trivial. `IsSampling ∅` is false (a nonzero `PW` function exists),
  so the empty set cannot sneak in; `IsHB 0` fails (zeros in `ℂ₊`), so `F = 0` is excluded; zero sets are of `EF+E^*F^*`
  as a set (multiplicity is lost, harmless: zeros are simple in necessity since `G` has simple zeros, and in
  sufficiency a set hypothesis is weaker).
* `landau_inequality`: `Real.posLog`, `ENNReal.ofReal` of a negative number (= 0) and `encard` cast are handled;
  not trivial for large `A` because the bound `L - A log⁺L - B` is positive for large `L`.
* `PavlovBMO`, `JohnNirenberg` (with `≥ s`, absolute `C, c`), `DSPerturbation` (unused here), `TheoremC/D/E/F`:
  each is true in the weakest form stated (JN: `{|h-h_I| ≥ s} ⊆ {> s'}` for `s' < s` and let `s' ↑ s`).
  `TheoremD` kernel at `z = conj w` is the correct limit of formula (1). `TheoremE`'s interpolation clause follows
  from ONB + `K(γ,γ') = 0` (sine formula), with weights `1/K(γ,γ)`.
* Lemma-level statements spot-checked and true: `exists_realFactor`, `exists_noRealZero_hb`,
  `phaseLevel_sepBy_two` (also for `δ ≤ 0` trivially), `levelSet_limit`, `levelSet_ineq`, `levelSet_separated`,
  `levelSet_cis`, `phase_tendsto`, `phase_mul_bijective`, `eventually_not_exceptional`, `zero_set_single`,
  `deBrangesKernel_real`, `kernel_orthogonal`, `levelSet_eq_of_cis`, `isSampling_of_isCompleteInterpolating`,
  `osc_bound_of_JN`, `ncard_Ioc_ge`, `countFn_sub` (all four sign cases), `ncard_inter_Ioc_le`.

## (b) Correctness and completeness of the proof plans

### M03 (necessity)
* *Sampling Hilbert space and (H1)–(H3).* Correct and complete: `InnerProductSpace.Core` with `conj f(λ) g(λ)`
  (Mathlib's convention), definiteness from the lower bound, completeness through `pw_complete` and the upper bound,
  (H1) pointwise off `ζ` (the Lean form of `TheoremC`'s H1 only constrains `ι g` off `ζ`, which determines it), (H2)
  from `|f(ζ)|² ≤ e^{2π|Im ζ|}‖f‖²` and the lower sampling bound, (H3) because `fstar f = conj f` on `ℝ`. `H : Type`
  is fine (`ℂ → ℂ : Type`). The `def PWFun` trick avoiding the product topology is sound.
* *Use of Theorem C* matches the Lean form (`MemHE E f ↔ f ∈ range ι`, `ofReal ‖h‖² = heNormSq E (ι h)`); `HEEqPW E`
  with `c = A`, `C = B`. Strictness and real-zero-freeness of `E` come from M02 *before* Theorem F is applied.
* *Use of Theorem F* matches (`μ = ∑|E(λ)|²δ_λ`, hypothesis equality via `lintegral_sampMeasure_div`, needs
  `E(λ) ≠ 0`). Extra `p y` term handled (R3-4). Summability of `|E(λ)|²/(1+λ²)` from `z = i`.
* *Herglotz function `M` and normalisation.* Verified by hand: `hk λ z = 1/(λ-z) - λ/(1+λ²)`,
  `Re(-i hk) = y/|λ-z|²`, `M^* = -M`, `D = H - M₀` holomorphic on `ℂ₊` (via `M₀ = W₀/G`, avoiding differentiability of
  the series), `Re D = 0 ⇒ D = ia` (open mapping). The bound `‖hk‖ ≤ 2(1+R)/(1+λ²)` for `|λ| ≥ 2R ≥ 1` is right.
  `entTerm` + `dslope` makes `G·M` entire without simplicity of zeros.
* *`F` and `F ∈ \overline{HB}`.* `Φ = if 0<Im z then QA/E else P/E^*` is entire: on `ℂ₊` use `QA/E` (E ≠ 0), at points
  with `Im ≤ 0` the open set `{E^* ≠ 0}` (which contains the lower closed half-plane because `E` has no zeros in
  `ℂ₊ ∪ ℝ`) where the two formulas agree by `hrel`. Hence zeros of `E^*` in `ℂ₊` are handled with full
  multiplicity automatically. `F := -Φ^*` gives `EF = Q`, `E^*F^* = -P`, `F^* = -AF` on `ℂ₊`; `F(E - E^*A) = 2G` on
  `ℂ₊` gives `F ≠ 0` there (correct replacement for the paper's unjustified claim), `|F(z̄)| = |A||F(z)| ≤ |F(z)|`.
* *`EF + E^*F^* = 2G`.* `Q - P = 2G` identically (replaces the paper's "real part" argument, which is correct but
  imprecise at the poles of `M`). Zero set `= Λ` by `genProd_eq_zero_iff`.
* `genProd` (genus one over `Λ∖{0}`, times `z` if `0 ∈ Λ`), `fstar_genProd`: correct.
  Not found wrong: the bucketing proof of `∑ 1/(1+λ²) < ∞` and the `Λ ∩ [-r,r]` finiteness.

### M04 sufficiency
* *Reduction to `F` without real zeros (the proposed variable-genus Weierstrass product).* **Sufficient and, in
  full generality, needed.** Sufficient: with `E_p(w) = (1-w)exp(w+…+w^p/p)`, `|E_p(w)-1| ≤ |w|^{p+1}` on `|w| ≤ 1`,
  `p_n` with `m_n 2^{-p_n} ≤ 2^{-n}`: for `|z| ≤ R`, `|a_n| ≥ 2R` one has `m_n|E-1| ≤ 2^{-n-1} ≤ 1`, so
  `|E_{p_n}^{m_n} - 1| ≤ 2m_n|E-1| ≤ 2^{-n}`, which sums; only finitely many `n` have `|a_n| < 2R` because
  `Z(F) ∩ ℝ` is discrete (`F ≢ 0`); order of vanishing exact; `S^* = S` since zeros are real. The quotient `G = F/S`
  is entire and zero-free on `ℝ`; `|G(z̄)| ≤ |G(z)|` because `|S(z̄)| = |S(z)| ≠ 0`. And `EF+E^*F^* = S(EG+E^*G^*)`
  needs `S^* = S`. Needed: counter-example with admissible hypotheses (`E = e^{-iπz}`, `F = S` real entire with a
  zero of order `m_n = 2^n` at `a_n = 4n`): `F ∈ \overline{HB}` (real zeros only), `EF+E^*F^* = 2S cos πz`, zero set
  `{4n} ∪ (ℤ+½)` separated. For real `w ∈ (0,1)`, `log E_p(w) = -∑_{k>p} w^k/k < 0` (one sign, no cancellation), so
  `∏ E_p(z/a_n)^{m_n}` converges only if `∑ m_n a_n^{-(p+1)} < ∞`, which fails for every fixed `p` when `m_n = 2^n`
  (a fixed genus, e.g. 1 or 2, is not enough; mere unbounded polynomial multiplicities such as `m_n = n` defeat genus one
  only). `S = ∏ E_{p_n}(z/a_n)^{m_n}` with `m_n 2^{-p_n} ≤ 2^{-n}` does exist. Mathlib (checked in `.lake/packages`)
  has no Weierstrass factorization, so it must be built. Conclusion `Λ₁ ⊆ Λ` suffices (only `⊇` of the paper's
  `Λ = Λ₁ ∪ Z(S)` is used); lower bound by inclusion, upper bound by Plancherel–Pólya for the separated `Λ`.
  A cheaper route (phase of `F` through `F^*/F`, which is analytic across real zeros) does not help because
  Theorem E (Lean form) requires no real zeros of `EF`.
* *Phase of `EG` onto `ℝ`, level sets.* `φ_G' ≥ 0` (checked: `∂_y log|G^*/G| = -2φ_G'`, equality on `ℝ`, `≤ 0`
  inside), `φ_E' > 0` by Hopf for strict `E`; `ψ = φ_E + φ_G` strictly increasing with `ψ ≥ φ_E + φ_G(0)` on `[0,∞)`,
  `≤` on `(-∞,0]`; surjective by `phase_tendsto`. OK.
* *Interlacing.* `phaseLevel_sepBy_two` proof verified (parity argument; both intermediate values `π/2+(k+1)π`,
  `π/2+(k+2)π` lie strictly between `φx` and `φy` because `0 < ε < π`). Separation constant not smaller than that
  of `Λ`, as the paper says.
* *Uniform Plancherel–Pólya and the limit `α → π/2`.* `levelSet_limit` is correct: the PW-tail `Prop`
  `plancherelPolya_tail` (uniform over all δ-separated sets; true by the local PP estimate and dominated convergence
  of `∬_{|y|≤r}|f|²` tails), finite part by continuity of `Ψ`, `κ = ψ(-R) - ψ(-R-1)` handles which indices can enter
  `|x| < R`. Genuinely replaces the paper's "(4) + dominated convergence" (N-12/Issue 6 confirmed: (4) bounds a full
  sum, not terms; upper semicontinuity of the sums along `α_n` needs uniform tails, Fatou gives the wrong direction).
  `α_n = π/2 + π/(n+2)` with at most one exceptional `n` (since `E ∉ H(E)`: `E/E = 1 ∉ H²`) is right; avoids the
  paper's detour.
* *`φ_E` onto ℝ* (N-33): see R3-7. *Theorem E applied to `E' = EG`:* `E'` strict, no real zeros, `G f ∈ H(E')`,
  `‖Gf‖_{E'} = ‖f‖_E`, `φ_{E'}' ≥ φ_E'`; constant `C₀ = c⁻¹ π/c₁` independent of `α, G, ψ`. Correct.
* *Corollary 1.* Interlacing uses only `ψ(γ_{k+1}) - ψ(γ_k) ≥ π` (increments of `φ_G ≥ 0`), IVT on `[γ_k,γ_{k+1}]`
  with target `< ψ(γ_{k+1})` giving `x < γ_{k+1}`; correct, and the paper's phrase "`φ_E` grows more slowly than
  `φ_{EF}`" is the loose form of this. Separation of `Γ_α`: Theorem E datum `δ_γ` has `‖f_γ‖²_E ≤ π/c₁`, Bernstein
  gives a uniform Lipschitz constant, so `|γ-γ'| ≥ 1/Θ`. Correct.
* *Remark p. 797 via Theorem D.* Correct: `K := K_a ∈ H(E)`, `K(a) = ‖K‖² =: k`, Cauchy–Schwarz gives `k ≥ 1`,
  norm identity gives `k ≥ k² + ∑_{γ≠a}|K(γ)|²`, so `k = 1` and `K(b) = 0`; `sin(φb-φa) = 0`; completeness of the
  level set by uniqueness (`K_x ≡ 0` contradicts `f(x) = ⟨f,K_x⟩` for a translate); rotation by `θ = β - π/2`
  (`fstar(e^{iθ}E) = e^{-iθ}E^*`). `isSampling_of_isCompleteInterpolating` by closed graph: correct.

### M05 (Landau)
Complete and correct. `h = n_Γ - t`, `hloc: |h(b)-h(a)| ≤ (1+1/q)(b-a)+1` (from `N ≤ L/q+1`); for `L ≥ L₀ =
max 2 (C+1)`, `s = (2M/c) log L`: `exp(-cs/M) = L⁻²`, `vol J ≤ C/L < 1`, unit window `W ⊆ I` (needs `L ≥ 2`)
cannot lie in `J`; `|h(t)-h_I| ≤ K + D + s`; so `|h(b)-h(a)| ≤ 2(K+D) + 4(M/c) log L`; `L < L₀` absorbed in `B`;
`M := max M₀ 1 > 0`. Jumps of `h` (`+1` at points of `Γ`, derivative `-1` elsewhere) are covered by `hloc`, which is
a cleaner replacement of the paper's "`h'` bounded, separation distance". Counting step `ncard_Ioc_ge` (interior
gaps `J∖{max}`) correct. Final arithmetic `n_Λ(b)-n_Λ(a) ≥ L - |h(b)-h(a)| - 1`, `B = B'+1`. The Lean cast
`(encard : ℝ≥0∞)` of a finite set equals `ncard`.

## (c) Use of cited `Prop`s versus their exact Lean form

| Prop | Used in | Matches? |
|---|---|---|
| `PaleyWienerThm` | via M01 (PW tools, `plancherelPolya`, `pw_complete`) | yes |
| `TheoremC` | `exists_E` (injectivity, differentiability, H1 off `ζ`, H2, H3, nonzero) | yes, exact premises produced by `exists_samplingHilbertSpace` |
| `TheoremF` | `exists_herglotz_data` (strict, no real zeros, `μ`-hypothesis, `poissonInt ≠ ∞`, `+ p y`) | yes |
| `TheoremE` | `levelSet_ineq/separated/cis/phase_tendsto` | yes (strict, no real zeros, `¬ MemHE E S_α`; both clauses used) |
| `TheoremD` | remark only (`kernel_orthogonal`, `levelSet_eq_of_cis`) | yes (for all `w ∈ ℂ`, `K(w,·) ∈ H(E)` and reproducing, conj on the kernel) |
| `PavlovBMO`, `JohnNirenberg` | M05 | yes (`Γ` separated, CIS; `0 < M`, `meanOsc ≤ M` on all bounded intervals, locally integrable) |

`TheoremE` without its "at most one α mod π" clause is compensated by `memHE_sAlpha_unique` (true: two independent
combinations of `E, E^*` in `H(E)` would put `E` itself in `H(E)`, contradicting `E/E = 1 ∉ H²`).

## (d) Verdicts on "Issues in the source"

### M03 §11
| # | Verdict | Remark |
|---|---|---|
| 1 sign of (3) | **confirmed** (p-07: `-i∑|E|²(1/(z-λ)+1/λ)`; `Re(-i/(z-λ)) = -y/|z-λ|² < 0`) | see R3-3 for wording |
| 2 missing `1/π` | **confirmed** (print (3) has none; Theorem F has `y/π`) | |
| 3 `1/λ_k` at `0`; convergence | **confirmed** (`λ = 0`; a convergence factor is indeed needed; the paper's own factor is legitimate) | R3-3 |
| 4 Theorem F without `py`, needs strict `E` | **confirmed** | R3-4 |
| 5 "`M-1` vanishes where `E^*` does" | **confirmed** (needs `E` zero-free on `ℝ`; paper states that only on p. 796 "converse") | |
| 6 `G(M-1)` entire | **confirmed** (tacit) | |
| 7 "`F` has no zeros in `Im z>0`" | **confirmed** (print p-08: asserted from `F^*/F = -A`) | |
| 8 real-part argument | **confirmed** (imprecise at poles of `M`, correct otherwise) | |
| 9 `E(λ_k) ≠ 0` | **confirmed** | |
| 10 Theorem C hypotheses | **confirmed** | |
| 11 `G^* = G` | **confirmed** | |

### M04 "Issues in the source"
1 Weierstrass for `S`: **confirmed** (print p-08: "`S` is an entire function, with real zero set `Z(S)`"; counter-example
above shows infinite real zeros with unbounded multiplicity are admissible). 2 `Λ_α` indexed by `ℤ`: **confirmed**.
3 `(0,π]` vs `[0,π)`: **confirmed** (p-08 "α ∈ (0,π]", p-09 "α ∈ [0,π)"). 4 `φ_{EF}' ≥ φ_E'`: **confirmed**
(print has the derivative version; only the notebook's N-10 misreading was withdrawn). 5 missing square in the `sup`:
**confirmed** (p-08, middle term `sup|f(x)|`). 6 dominated convergence: **confirmed**. 7 "may assume it fails at π/2":
**confirmed** (unnecessary). 8 `g = Ff ∈ H(EF)`: **confirmed** (needs `F ∈ \overline{HB}`). 9 remark "follows from C and E":
**confirmed with the refinement R3-2**. 10 Corollary 1 (i)–(iii): **confirmed**; (iii) partially refuted by R3-1 (the paper
asserts separation of CIS on p. 791). 11 "`φ_E` grows more slowly": **confirmed** (p-10; correct form: increments). 12 real part:
**confirmed**.

### M05 "Issues in the source"
1 `h'(t) = -1` for `t ∉ Λ`, "separation distance of `Λ`": **confirmed** (p-11: "`t ∉ Λ`", "separation distance of `Λ`"; should be `Γ`;
`h` has jumps at `Γ`, the mechanism "measure of `J` < separation" is correct for `Γ` and replaced by `hloc`). 2 small intervals
and `log|I|`: **confirmed**. 3 inequality chain: **confirmed** (second step an equality). 4 Γ separated: **partly refuted** (R3-1).
5 constants: **confirmed but not an error** (R3-8). 6 Lean-specific remark: **confirmed**.

## (d) Verdicts on NOTEBOOK entries

* **N-05** missing square: **confirmed** (print-checked).
* **N-06** (S): **confirmed** that Theorem D is not needed for Theorem 1 and that only the lower bound on `φ'|E|²`
  is needed; add the exceptional-level/density remark (R3-6).
* **N-07**: **confirmed** (sign, `1/π`, `0 ∈ Λ`); add that the printed convergence factor is legitimate (R3-3).
* **N-08**: **confirmed**.
* **N-09**: **confirmed** (the display before (5) and (5) lack `π`; p-08).
* **N-11**: **confirmed**.
* **N-12**: **confirmed** (gap; the blueprint's uniform-tail argument is correct and cleaner than the notebook's `∬` sketch).
* **N-13**: **confirmed** (`φ_F' ≥ 0` is used on p. 796 with no comment; proof via `∂_y(log|F^*| - log|F|) = -2φ_F'`).
* **N-14**: **confirmed** (p-11 prints `Λ`; must be `Γ`).
* **N-15**: **confirmed**.
* **N-28**: **confirmed** (true; blow-up of `f/E` at a real zero; strictness of `E` and `φ_E' > 0` also needed).
* **N-31**: **confirmed** (all four bullets; bullet 1 shows `E` free of real zeros is needed already in necessity).
* **N-32**: **confirmed** (variable genus necessary in general; upper bound for `Λ ⊋ Λ₁` needs PP).
* **N-33**: **confirmed** (surjectivity proof in the blueprint is by norm identity + PP tails, not literally "contradicting
  interpolation" as the one-line note suggests; both fine). "We may assume it fails at π/2" unnecessary: confirmed.
* **N-34**: **bullet 1 partly refuted, bullet 2 refined** (R3-1, R3-2); rest confirmed.
* (Also checked) **N-10** withdrawal: correct (p-08 prints `φ'_{EF} = φ'_E + φ'_F ≥ φ'_E`).

## Suggested minor edits (none blocking)
1. M05 Issue 4, N-34 bullet 1/2, M03 Issue 3, N-06: apply R3-1, R3-2, R3-3, R3-6.
2. M04 scaffolds: adopt owner signatures (R3-5).
3. In the final `exists_realFactor` proof, state the multiplicity-aware convergence lemma separately
   (`|E_p(w)^m - 1| ≤ 2m|w|^{p+1}` when `m|w|^{p+1} ≤ 1`), since `OCS.canonicalProd` only covers simple zeros and `p = 1`.
