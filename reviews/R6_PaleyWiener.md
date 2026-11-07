# Referee report R6: P1 (the Paley–Wiener theorem, phase 2)

Scope: `blueprint/P1_PaleyWiener.md` (proof of `FF.PaleyWienerThm`, `FourierFrames/Defs.lean` l. 181) and the
scaffold `FourierFrames/Cited/PaleyWiener.lean`, `FourierFrames/Cited/PaleyWiener/{Part1,L2Fourier,Spectrum,Part2}.lean`
(master copies), with `blueprint/PHASE2.md` as context. I also inspected the implementer's worktree
`../wt-ff/cited-p1` **read-only**, to check the master statements against the proofs.

Method:
* I recomputed by hand every constant and every step of the blueprint (§A).
* I typechecked scratch files against the master build, covering the `IsExpTypeLE` transfer into
  `OCS.norm_le_mul_exp_abs_im`, `ft = (PaleyWienerThm integrand)` by `rfl`, `PaleyWienerThm ↔ (part1 ∧ part2)` by
  `Iff.rfl`, `𝓕 Φ = F2 Φ` and `𝓕⁻ Φ = F2.symm Φ` by `rfl`, and `#check` of all the load-bearing Mathlib lemmas.
* I ran `#print axioms` in the worktree.
* I did numerical checks in Python (Parseval constant, the Gaussian bound on test functions).
* I diffed every declaration signature between master and worktree.

## Summary verdict

* **Critical: 0. Major: 0. Minor: 6.** No false Lean statement and no broken or incomplete proof step.
* **Machine status at review time (2026-11-07, 09:00).** In the worktree all five files are `sorry`-free.
  * Part1 (277 lines), L2Fourier (117), Spectrum (410) and Part2 (195) total 999 lines; with the 19-line top file
    the total is 1018, against the blueprint's estimate of about 1300.
  * Pinned state (sha256 prefixes): `L2Fourier.lean` `f8bbc4ffe1b9`, `Part1.lean` `651a65a9eab7`, `Spectrum.lean`
    `08240df551a6`, `Part2.lean` `9a5ccfe20f41` (unchanged between the axiom check and the end of the review), top
    file `PaleyWiener.lean` `b3a054726f49`.
  * A scratch copy of the current `Part2.lean` plus `⟨PW1.paleyWiener_part1, PW1.paleyWiener_part2⟩ : PaleyWienerThm`
    elaborates. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for that theorem and for
    `paleyWiener_part1`, `F2_toLp_ae_eq`, `F2_symm_toLp_ae_eq`, `spectrum_vanish`, `norm_integral_gauss_mul_le`,
    `eq_integral_of_spectrum` and `pw_representation_real`.
  * In the worktree, `FourierFrames/Defs.lean`, `OrtegaCerdaSeip/` and `lake-manifest.json` are byte-identical to
    master. So the `PaleyWienerThm` proved there is the master's.
  * The worktree's `Part2.olean` is stale (00:44). I elaborated the source file directly: no errors, no `sorry`.
* **(a) Statements.** Every master statement is true; see §B for each of them.
  * Part1, L2Fourier and Spectrum are now settled by Lean. Their signatures agree with master except for the drift
    listed in R6-02 and R6-04.
  * The master `F2_symm_ae_eq` is also true. It is unused and was deleted in the worktree.
* **(b) Proofs.** Correct and complete. Each step is checked in §A:
  * the `2π` and kernel conventions;
  * the Gaussian bound `2|C|√(π/η) exp((a² − (|ξ|−b)²)/(4η))`;
  * the `L²` limit and the a.e. subsequence;
  * the two-pass crude-spectrum ⇒ bounded ⇒ PL ⇒ sharp-spectrum argument;
  * inversion, rescaling and the identity theorem.
* **(c) `F2_toLp_ae_eq`.** The planned Schwartz-testing proof is sound (§C). The implementer used a shorter route
  through a Mathlib lemma that the blueprint says does not exist (R6-03).
* **(d) No circularity.**
  * Imports:
    * `Part1` and `L2Fourier` import `Defs` only;
    * `Spectrum` imports `L2Fourier`;
    * `Part2` imports `Part1`, `Spectrum` and `OrtegaCerdaSeip.Bernstein.PhragmenLindelof`.
  * `OrtegaCerdaSeip/` never mentions `FourierFrames` and is `sorry`-free (per `VENDORED.md`; grep finds no
    `sorry`).
  * No file mentions `hPW` or takes `PaleyWienerThm` as a hypothesis.
* **Normalisation.** `PaleyWienerThm` is exactly the classical Paley–Wiener theorem with Plancherel's identity (§E).

---

## A. Recomputation of the key constants and arguments

| item | claim | my check |
|---|---|---|
| kernel vs `fourierCoeffOn` | `ft g n = 2π · fourierCoeffOn g (−n)` | Mathlib: `fourierCoeffOn hab f m = (1/(b−a)) • ∫_a^b fourier (−m) x • f x`, and `fourier k x = exp(2πikx/T)` with `T = π − (−π)`. For `m = −n`: `fourier n t = e^{int}`, so `fourierCoeffOn g (−n) = (2π)⁻¹ ∫ g e^{int} = (2π)⁻¹ ft g n`. OK. No hypothesis on `g` is needed: both sides are integrals of pointwise-equal functions. |
| translates | `ft g (x+k) = ft (g e^{ix·}) k` | `e^{i(x+k)t} = e^{ixt}e^{ikt}`, everywhere. OK. |
| Parseval | `∑_k |ft g(x+k)|² = 2π∫|g|²` for **every** real `x` | `(2π)² · (2π)⁻¹ ∫|g e^{ix·}|² = 2π∫|g|²` (unimodular factor, `x` real). Reindexing `k ↦ −k`. OK. Numerically, for `g = 1+t` (closed-form `f`, `K = 2·10⁵` terms) the sums at `x = 0.1, 0.3, 0.77` are `169.3568`, `169.3570`, `169.3570`; the target `2π∫(1+t)² = 169.3572`. |
| unit intervals | `∫_ℝ G = ∫_{[0,1)} ∑_k G(·+k)` | `ℝ = ⊔_k [k,k+1)`, translation invariance, `lintegral_tsum`. OK. Numerically `∫_{−3000}^{3000}|f|² = 169.343` (the tail is O(1/3000)). |
| Gaussian integral | `∫ e^{a|x|−ηx²} ≤ 2√(π/η) e^{a²/(4η)}` | `ax − ηx² = a²/(4η) − η(x − a/2η)²`, so `∫e^{±ax−ηx²} = √(π/η)e^{a²/(4η)}`. Also `e^{a|x|} ∈ {e^{ax}, e^{−ax}}` for **every** `a` (see R6-04). OK. |
| moduli | on `z = x+is` | `|e^{−ηz²}| = e^{−η(x²−s²)}` and `|e^{−iξz}| = e^{ξs}`, so `|H(x+is)| ≤ |C| e^{a|x|−ηx²} e^{ηs² + b|s| + ξs}`. OK. |
| contour choice | `y = −sgn(ξ)·Y`, `Y = κ/(2η)`, `κ = |ξ|−b ≥ 0` | `ξy = −|ξ|Y`, and the exponent is `ηY² + (b−|ξ|)Y = κ²/(4η) − κ²/(2η) = −κ²/(4η)`. OK. |
| bound | `‖∫ f e^{−ηx²} e^{−iξx}‖ ≤ 2|C|√(π/η) exp((a²−κ²)/(4η))` | Product of the two lines above. OK. Numerically (`f = e^{iz}`, `a=0,b=1`; `f = cosh z`, `a=1,b=0`; `f = π·sinc`, `C=π,a=0,b=π`; several `η`, `ξ`) the worst ratio exact/bound is **0.5**. That is the factor 2 from `e^{a|x|} ≤ e^{ax}+e^{−ax}`; the exponent is sharp for `e^{ibz}`. |
| vertical sides | `∫_0^y ‖H(±R+is)‖ ds → 0` | `|s| ≤ Y` gives `≤ Y·|C|e^{ηY² + (b+|ξ|)Y}·e^{aR−ηR²} → 0`. OK. For `y < 0` the signed integral is `≤ 0` and still tends to 0 (R6-05). |
| `η → 0⁺` | `2|C|√(π/η) e^{(a²−κ²)/(4η)} → 0` | `κ > a ≥ 0` gives `c = (κ²−a²)/4 > 0`. With `t = 1/η` the expression is `√π t^{1/2} e^{−ct}`, which → 0. OK. |
| threshold | `a + b < 2π|w| ⇒` spectrum vanishes | `ξ = 2πw` (Mathlib kernel `e^{−2πixw}`). Then `b ≤ |ξ|` and `κ = |ξ| − b > a`. OK. |
| `L²` limit, a.e. | `f e^{−ηₙx²} → f` in `L²` | Dominated convergence with dominating function `‖f‖ₑ²` (since `|e^{−ηx²} − 1| ≤ 1`). `F2` is an isometry ⇒ convergence in `L²` ⇒ convergence in measure ⇒ an a.e. subsequence `ns`. Then `F2(toLp fₙ) =ᵐ 𝓕 fₙ` for each `n` (countably many, `ae_all_iff`). For every `w` past the threshold, `𝓕 f_{ns k} w → 0`. Uniqueness of limits gives `Φ w = 0` a.e. The fixed representative `⇑(F2 …)` is used throughout. OK. |
| crude pass | `a = b = π+1`, `ρ = 1 + 1/π` | `‖z‖ ≤ |x|+|y|` gives `|f| ≤ |C₁| e^{(π+1)(|x|+|y|)}`; `|C₁|` is needed (R6-01). `2πρ = 2(π+1)`. OK. |
| boundedness | `|f(x)| ≤ ∫_{−ρ}^{ρ}|Φ|` | `Φ₀ = 1_{[−ρ,ρ]}Φ ∈ L¹∩L²`, `toLp Φ₀ = F2 u`, `u = F2.symm(toLp Φ₀) =ᵐ 𝓕⁻Φ₀`. Both `f|ℝ` and `𝓕⁻Φ₀` are continuous, so a.e. equality upgrades to everywhere. OK. |
| PL | `|f(z)| ≤ M e^{π|Im z|}` | `OCS.norm_le_mul_exp_abs_im hd he π_pos.le hM z` **typechecks with `he : FF.IsExpTypeLE π f`**. Both definitions are `@[expose]` with identical bodies (verified in a scratch file and in the worktree proof). The result is `hC` for `a = 0, b = π` after `zero_mul, zero_add`. `π < 2π|w| ⟺ |w| > 1/2`. OK. |
| rescaling | `g(t) = Φ(t/2π)/2π` | `2πi(t/2π)x = ixt`. `integral_comp_div` gives `∫_{−π}^{π} F(t/2π) dt = 2π • ∫_{−1/2}^{1/2} F`, and `(2π)⁻¹·2π = 1`. `L2pi g` holds since `∫|Φ(t/2π)|² = 2π∫|Φ|²`. OK. |
| identity theorem | `F = G` on `ℝ` ⇒ on `ℂ` | Accumulation at `0` via `1/(n+1)`. OK. |

---

## B. Truth of each master statement (Lean pitfalls)

Lean pitfalls checked throughout:
* `x/0`: only `2π`, `4η` with `η > 0`, and `π/η` along `𝓝[>] 0`.
* `tsum`: every sum over `ℤ` is either `HasSum` (real) or `∑'` in `ℝ≥0∞`, never a real `∑'` that could silently be 0.
* Junk Bochner integrals: in every statement the integrand is either automatically integrable (a continuous function
  on a compact set, or `L²` on a finite interval), or the claimed inequality also holds at the junk value 0.
* `ℝ≥0∞`: no cancellation; finiteness is proved separately (`memLp_ft_real`).
* a.e. vs everywhere: discussed per statement below.

* **Part1** (13 theorems, plus `def ft` and `abbrev L2pi`): all true; machine-proved with the master signatures (the worktree only adds helper
  lemmas).
  * `ft_intCast_eq_fourierCoeffOn` holds with no hypothesis on `g`.
  * `lintegral_enorm_sq_eq_lintegral_tsum` holds for any measurable `F`.
  * `paleyWiener_part1` is definitionally a conjunct of `PaleyWienerThm`.
* **L2Fourier**:
  * `F2_toLp_ae_eq` and `F2_symm_toLp_ae_eq` are true and machine-proved.
  * `F2_symm_ae_eq` (master only) is true: `F2.symm` is `F2` followed by reflection. Both are continuous and agree on
    `toLp` of Schwartz functions (`toLp_fourierInv_eq`, `fourierInv_eq_fourier_neg`), which are dense. It is not used
    anywhere (grep over the repository), see R6-02.
* **Spectrum**: all 8 theorems are true and machine-proved.
  * `integral_line_shift` is true for `y < 0` as stated: `hR`/`hR'` are signed integrals but are equivalent to the
    absolute ones. Junk values are excluded since `H` is continuous and `hint0`/`hinty` are assumed.
  * `ha` is superfluous in `integral_exp_abs_sub_sq_le` and `norm_integral_gauss_mul_le` (R6-04).
* **Part2**: I walked each of the 8 theorems (and `def specOf`); all are true, and all are now proved in the worktree with
  signatures identical to master.

| Part2 statement | why true |
|---|---|
| `specOf` | a fixed representative; every statement about it is a.e. in `w`, or uses only its integrals. |
| `memLp_specOf` | `Lp.memLp`. |
| `eq_integral_of_spectrum` | Holds for **every** `x`, because both sides are continuous (`hd`; the inverse transform of `Φ₀ ∈ L¹`) and agree a.e. The right side is a genuine integral: `Φ` is in `L²`, hence in `L¹` on `[−ρ,ρ]`, and is strongly measurable. `hρ` is only used for `−ρ ≤ ρ`. |
| `bounded_of_spectrum` | `M = ∫_{−ρ}^{ρ}‖Φ‖`, with a unimodular kernel. |
| `pw_bounded` | Classical: PW functions are bounded on `ℝ` (proof in §A). |
| `pw_spectrum` | Spectrum in `[−1/2, 1/2]` in Mathlib's normalisation, which is type `π`. |
| `pw_representation_real` | §A, rescaling row. |
| `eq_of_eq_on_real` | Identity theorem on the connected set `ℂ`. |
| `paleyWiener_part2` | Literally the second conjunct of `PaleyWienerThm`. |

---

## C. The gap lemma `F2_toLp_ae_eq` (`L¹ ∩ L²` agreement)

**The planned proof (blueprint §2) is sound.** Let `u = ⇑F2(toLp φ)` (locally integrable since it is `L²`) and
`v = 𝓕φ` (continuous since `φ ∈ L¹`). Testing against real `g ∈ C_c^∞` (`ae_eq_of_integral_contDiff_smul_eq`), with
`ψ = g` viewed as a Schwartz function and `χ = 𝓕⁻ψ`:

1. `L2.inner_def`, with `⟪a,b⟫_ℂ = conj a · b`, gives `∫ conj ψ · u = ⟪ψ.toLp, F2 Φ⟫`.
2. `ψ.toLp = F2(χ.toLp)` by `toLp_fourier_eq` and `𝓕𝓕⁻ = id` on `𝓢`.
3. `inner_fourier_eq` then gives `⟪χ.toLp, Φ⟫ = ∫ conj χ · φ`.
4. On the `L¹` side, `integral_fourierIntegral_smul_eq_flip` with `(innerₗ ℝ).flip = innerₗ ℝ` (true on `ℝ`; the
   worktree proves it by `ext; simp`) gives `∫ 𝓕φ · ψ = ∫ φ · 𝓕ψ`.
5. `conj(𝓕⁻ψ) = 𝓕(conj ψ) = 𝓕ψ` because `ψ` is real.

Chaining these gives `∫ g·u = ∫ g·v`. Every identity holds and every lemma cited exists with the stated shape.

**The implementer took a shorter route** (`L2Fourier.lean`, worktree, 117 lines). `Lp.fourier_toTemperedDistribution_eq`
(Mathlib `Analysis/Fourier/LpSpace.lean` l. 121), followed by `TemperedDistribution.fourier_apply` and
`Lp.toTemperedDistribution_apply`, gives `∫ ψ • F2 Φ = ∫ 𝓕ψ • Φ` for all `ψ ∈ 𝓢` in three lines. The inverse version
uses `Lp.fourierInv_toTemperedDistribution_eq` (l. 131). This proves `F2_symm_toLp_ae_eq` directly, which is the
blueprint's "alternative" route, without `F2_symm_ae_eq`.

---

## D. Circularity

Nothing in the import closure of `FourierFrames/Cited/PaleyWiener.lean` lies in `FourierFrames/PW/*` or `HB/*`. The
only non-Mathlib dependency besides `Defs` is the vendored `OrtegaCerdaSeip.Bernstein.PhragmenLindelof` (→ `Basic` →
`OrtegaCerdaSeip.Defs` → Mathlib). That library is `sorry`-free and never refers to `FourierFrames`.
`OCS.norm_le_mul_exp_abs_im` has hypotheses `Differentiable`, `OCS.IsExpTypeLE`, `0 ≤ τ` and a bound on `ℝ`, with no
cited `Prop`. No P1 declaration takes `hPW` or `PaleyWienerThm`. The same holds for the worktree files, which have the
same imports.

---

## E. Is `PaleyWienerThm` the classical theorem?

Yes, with the right normalisations.

* **Part (1):** for `g ∈ L²(−π,π)`, `f(z) = ∫_{−π}^{π} g(t)e^{izt}dt` is entire, of type `≤ π`, in `L²(ℝ)`, and
  `‖f‖²_{L²(ℝ)} = 2π‖g‖²_{L²(−π,π)}`.
  * The constant `ofReal(2π)` is right: it is Plancherel for the kernel `e^{izt}` without a `1/2π`, confirmed
    numerically in §A.
  * The interval integral, the `MemLp` measure and the `∫⁻` all use the same `Ioc (−π) π`. So values of `g` outside
    `(−π, π]` are irrelevant, as they should be.
* **Part (2):** every `f ∈ PW` has this form for **all** `z ∈ ℂ`.
  * The kernel sign `e^{izt}` (rather than `e^{−izt}`) is harmless: the reflection `g ↦ g(−·)` preserves
    `L²(−π, π)` up to the null endpoint.
  * `IsExpTypeLE π` is the limsup notion (`∀ε ∃C, |f| ≤ Ce^{(π+ε)|z|}`). It is weaker than `|f| ≤ Ce^{π|z|}`, so
    part (2) is the strong classical form (see e.g. Boas, *Entire Functions*, §6.8; Young, *Nonharmonic Fourier Series*,
    Ch. 2 §1). This is exactly what the PL lemma accepts.
  * Uniqueness of `g` and the norm identity for part (2) are not stated. Neither is needed: the norm identity follows
    from part (1) applied to the `g` obtained.

---

## F. Findings

Severity legend: critical = false statement or broken proof; major = gap needing new ideas; minor = the rest.

**R6-01 (minor, blueprint §4 `pw_bounded`, l. 354–356).**
* *Problem.* The step "`‖z‖ ≤ |z.re| + |z.im|` ⇒ hypothesis `hC` with `C = C₁`" uses monotonicity of
  `C₁·exp(·)`, which needs `0 ≤ C₁`. `he 1 one_pos` does not supply that.
* *Evidence.* The worktree inserts the lemma `norm_le_exp_re_im` with `|C|` (Part2 l. 94–102).
* *Fix.* In the text, use `|C₁|` (`le_abs_self`), or note that `0 ≤ ‖f 0‖ ≤ C₁`.

**R6-02 (minor, blueprint §2 and master `L2Fourier.lean` l. 29–32).**
* *Problem.* `F2_symm_ae_eq` is dead code. It is true, but no file uses it.
* *Evidence.* The worktree deleted it and proves `F2_symm_toLp_ae_eq` directly (§C). Blueprint §2 still presents
  `F2_symm_ae_eq` plus the density argument (`Lp.compMeasurePreservingₗᵢ`, `DenseRange.equalizer`) as the main route.
* *Fix.* On merge-back, drop it from master and from the §2 statement block. Repository-wide grep: no other references.

**R6-03 (minor, blueprint §0 l. 44–46, §2 header, §6 first bullet).**
* *Problem.* "the agreement with the integral on `L¹ ∩ L²` does **not** [exist] (grep … finds nothing)" is misleading.
  There is no packaged lemma, but `Lp.fourier_toTemperedDistribution_eq` and `Lp.fourierInv_toTemperedDistribution_eq`
  give the Schwartz pairing immediately. The §6 fallback ("density of `C_c^∞` in `L¹∩L²`, heavier") is unnecessary.
* *Fix.* Rewrite §2 around the distributional route and keep the inner-product computation as an alternative. It is
  correct (§C).

**R6-04 (minor, blueprint §3 l. 227, 233, 270; master `Spectrum.lean` l. 35, 47).**
* *Problem.* The hypothesis `ha : 0 ≤ a` is unused in `integral_exp_abs_sub_sq_le` and `norm_integral_gauss_mul_le`.
  The remark "(For `a < 0` the statement is still true with `|a|` …)" is inaccurate: the statement is true **verbatim**
  for every `a`, because `e^{a|x|}` is one of `e^{±ax}` and `a² = |a|²`.
* *Evidence.* The worktree dropped `ha` from both lemmas. This is the only signature drift besides R6-02. Full-signature
  diff: Part1 adds helpers only; L2Fourier removes `F2_symm_ae_eq` and adds helpers; Spectrum changes these two and
  adds helpers; Part2 adds `stronglyMeasurable_specOf` and `norm_le_exp_re_im`. `spectrum_vanish` keeps
  `ha`/`hb` in both copies, so the Part2 callers are unaffected.
* *Fix.* Sync the master signatures and blueprint §3 with the worktree.

**R6-05 (minor, blueprint §3 `integral_line_shift`, l. 259–262, and §6).**
* *Problem.* The hedge "adjust `hR` statement accordingly if implementation prefers `|∫|`", and the alternatives
  (conjugation trick, swapped rectangle), are unnecessary. With the signed hypotheses as stated,
  `intervalIntegral.norm_integral_le_abs_integral_norm` and `Tendsto.abs` handle `y < 0` uniformly.
* *Evidence.* This is what the worktree does, in about 30 lines.
* *Fix.* Replace the hedge with that one-line recipe.

**R6-06 (minor, doc sync with the implementation; blueprint header l. 3, §4, §5, `PHASE2.md` row P1).**
* *Problem.* The blueprint no longer matches the implementation in several places:
  * Header: "only `sorry` warnings" is now false (0 `sorry`).
  * Size: actual 1018 lines vs the estimate of about 1300.
  * `pw_representation_real`: the `Real.map_volume_mul_right` / `memLp_map_measure_iff` / `smul_measure` recipe was
    replaced by `memLp_two_iff_integrable_sq_norm` plus `Integrable.comp_div`.
  * Measurability of `t ↦ Φ(t/2π)`: the implementation uses `Lp.stronglyMeasurable`, i.e. the *everywhere*
    strongly measurable representative, plus `comp_measurable`. This avoids composing an a.e.-measurable function
    with a non-measure-preserving map, a step the blueprint does not address.
  * `eq_integral_of_spectrum`: continuity of `𝓕⁻Φ₀` comes from `fourierIntegral_continuous` with `L = −innerₗ ℝ`
    rather than through `𝓕Φ₀ ∘ neg`. The kernel is matched by `Real.fourierInv_eq_fourier_neg`,
    `fourier_real_eq_integral_exp_smul`, `push_cast` and `ring`.
* *Fix.* When the worktree is merged, update the blueprint and the `PHASE2.md` row ("feasible" → "done") to match.

**Merge-back note (not a finding).** The master copies still contain the `sorry` scaffold. The merge must copy all
four `PaleyWiener/*.lean` files; the top file is identical. Only `F2_symm_ae_eq` and the two `ha` drops change master
signatures, and nothing outside P1 references them.

---

## Summary

The P1 blueprint is mathematically correct and complete. I independently recomputed the following, and the Gaussian
bound and Parseval constant also check out numerically:
* the `fourierCoeffOn` and `e^{izt}` conventions and the `2π` constant;
* the Gaussian contour-shift bound `2|C|√(π/η)exp((a²−(|ξ|−b)²)/(4η))`;
* the `L²` limit with an a.e. subsequence;
* the two-pass spectrum ⇒ bounded ⇒ Phragmén–Lindelöf ⇒ sharp spectrum argument;
* inversion, rescaling and the identity theorem.

`FF.IsExpTypeLE` is accepted verbatim by `OCS.norm_le_mul_exp_abs_im`, and there is no circularity. `PaleyWienerThm`
is the classical Paley–Wiener–Plancherel theorem with the correct `2π`, in its strong form (type in the limsup sense).

As of 09:00 the worktree proves `PaleyWienerThm` with only `propext`, `Classical.choice` and `Quot.sound`, against a
`Defs.lean` identical to master's.

Findings: 0 critical, 0 major, 6 minor. All are documentation or signature-sync items for the merge-back: the `|C₁|`
sign, the dead `F2_symm_ae_eq`, the overlooked `Lp.fourier_toTemperedDistribution_eq`, the unused `ha`, the
`integral_line_shift` hedge, and stale status and recipes.
