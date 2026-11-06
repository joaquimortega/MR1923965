# Referee report R2: M01 (Paley–Wiener toolkit), M10 (Frames), M02 (Hermite–Biehler / de Branges / "evident fact")

Scope: `blueprint/M01_PW.md`, `M10_Frames.md`, `M02_HB.md` and `FourierFrames/PW/*.lean`, `Frames.lean`,
`HB/*.lean`, against `FourierFrames/Defs.lean`, the page images (p-05, p-06, p-08 checked directly; tex
for the rest) and the downstream blueprints M03, M04, M06, M07.
Mathlib facts were checked in `.lake/packages/mathlib` (names cited below exist).
Numerical sanity checks (Python): `∫ (sin(πx/2)/(πx/2))⁴ dx = 4/3`; `C(δ)` vs `4/(πδ)` for small `δ`.

## Summary verdict

* **No false Lean statement found** among the ~110 statements of M01/M10/M02 (I tried the usual edge cases:
  `x/0=0`, `log 0`, `ℝ≥0∞` cancellation, empty/degenerate `Λ`, `E` with real zeros, `ε = ⊤`, `M<0`, junk
  values of `orthWeight`/`phaseDeriv` at real zeros, measurability of non-measurable `g` in
  `l2piSq_reflect`/`pwFT_reflect`).
* **No broken proof** found. Every constant I recomputed agrees with the blueprint (details in §A).
* **Critical: 0. Major: 0. Minor: 14** (stale text, small interface mismatches, small implementer gaps).
* Source-issue verdicts: all items of the three "Issues in the source" sections are **confirmed**, with
  two corrections of wording (M02 §12.4 mislocates the missing square; M02 §12.2 "Theorem E is false"
  should read "meaningless, 0/0"), and one stale item (M01 §6.4: already fixed in `Defs.lean`).

---

## A. Recomputation of the key constants and arguments

| item | claim | my check |
|---|---|---|
| Parseval | `∑_k |F_g(k)|² = 2π‖g‖²` | `fourierCoeffOn g n = (2π)⁻¹F_g(-n)`, Mathlib `hasSum_sq_fourierCoeffOn` has RHS `(b-a)⁻¹ • ∫‖f‖²` (verified in source); `(2π)⁻²∑|F|² = (2π)⁻¹∫|g|²` OK. (Note `b-a = π-(-π)`, needs `two_mul`/`ring` to become `2π` in `fourier_coe_apply`.) |
| Plancherel | `‖F_g‖²_{L²(ℝ)} = 2π‖g‖²` | OK. |
| `norm_pwFT_le` | `|F_g(z)| ≤ e^{π|y|}√(2π)‖g‖` | `‖e^{izt}‖ = e^{-ty} ≤ e^{π|y|}` on `[-π,π]`, Cauchy–Schwarz `(∫|g|)² ≤ 2π∫|g|²`. OK. |
| `pw_norm_sq_le` | `|f(z)|² ≤ e^{2π|y|}‖f‖²` | OK. Constant 1 is sharp on `ℝ` (`K_PW(x,x)=1`), consistent with the paper's "`1 = sup`". Off the axis the sharp constant is `sinh(2π|y|)/(2π|y|)` (0.1→1.067, 1→42.6, vs `e^{2π|y|}` = 1.87, 535). The remark "attained asymptotically by `g` concentrated at `∓π`" is wrong as a mechanism (the extremiser is `g = e^{-\bar z t}`-type), but only the exponent `2π|y|` is sharp; harmless. |
| `pw_line_integral_le` | `∫|f(x+iy)|²dx = 2π∫e^{-2yt}|g|² ≤ e^{2π|y|}‖f‖²` | OK (also for `y<0`). |
| H² estimate | `∫|f(x+iy)e^{iπ(x+iy)}|²dx = 2π∫e^{-2y(t+π)}|g|² ≤ ‖f‖²` for `y>0` | OK; `|e^{iπ(x+iy)}| = e^{-πy}`, `t+π ≥ 0`. Constant 1, uniformly in `y`. |
| `pw_deriv_bound` | `|f'(x)|² ≤ π²e²‖f‖²` | Cauchy on radius `R=1/π`: `|Im w| ≤ R`, `|f(w)|² ≤ e^{2πR}‖f‖² = e²‖f‖²`, `|f'| ≤ eπ‖f‖`. `R=1/π` minimises `e^{πR}/R`. OK. |
| `pwBump` | `csinc(πz/2)²`, type `π`, `‖·‖² ≤ min(1,(2/(π|x|))⁴) ≤ 2/(1+x²)`, norm `4/3` | OK (`1+x² ≤ 2x²`, `(2/π)⁴<1`; `N = (2/π)(2π/3) = 4/3`, numerically 1.33333). Triangle function on `[-π,π]` remark OK. |
| sub-mean-value | `|f(c)|² ≤ (πr²)⁻¹∫_{D(c,r)}|f|²` | `(r²/2)|f(c)|² ≤ (2π)⁻¹∫_D|f|²` gives `(πr²)⁻¹`. OK. `DiffContOnCl.circleAverage` exists (`Analysis/Complex/MeanValue.lean:108`), `Complex.lintegral_comp_polarCoord_symm` exists. |
| strip integral | `∫_{-r}^{r}e^{2π|y|}dy = (e^{2πr}-1)/π` | OK. |
| Plancherel–Pólya | `C(δ) = 4(e^{πδ}-1)/(π²δ²)` | `r=δ/2`, `(πr²)⁻¹ = 4/(πδ²)`, times `(e^{2πr}-1)/π`. OK; `C(δ) ~ 4/(πδ)` (129.3 vs 127.3 at `δ=0.01`). Open balls radius `δ/2` at points `≥ δ` apart are disjoint. |
| union of two separated sets | interlaced `Λ_α` = even ∪ odd index | verified: `a_{k+2}-a_k > λ_{k+2}-λ_{k+1} ≥ δ`. So `C = 2C(δ)`. |
| tail | `R = R'+δ/2`, `|Re z| ≥ |x|-r > R'` | OK. |
| Hurwitz (M02 §3.2) | minimum-modulus argument | correct: `E_i` zero-free on `closedBall ⊆ ℂ₊`, `‖1/E_i‖ ≤ 2/m` on the sphere ⇒ `‖E_i(z₀)‖ ≥ m/2`, contradicting `E_i(z₀) → 0`. Hypothesis `E₀ ≢ 0` is necessary (`E_n = e^{-n}(z+i)`). `E₀` may vanish on `ℝ`. |
| phase existence | `Φ = φ₀ + ∫₀^x ρ`, `ρ = -Im(E'/E)`, `u = E e^{iΦ}`, `n=‖E‖` | `u' = (Re q)u`, `n' = (Re q) n`, `u/n` constant `=1`. Computation correct; sign convention checked on `E = e^{-iπz}` (`φ = πx`, `φ' = π`) and `E = z+i` (`φ' = 1/(1+x²)`). |
| `φ' ≥ 0` | `D'(0) = 4 Im(ā b) = 4‖a‖² Im(b/a)` | recomputed: `D'(0) = 2Re(i a b̄) - 2Re(i ā b) = 2Im(āb)+2Im(āb)`. OK. |
| `φ' > 0` (Hopf-type) | `Θ-c = (z-x₀)^n g`, `n ≥ 2`, `cos(nθ+β) ≤ 0` on `(0,π)` impossible | recomputed `Θ'(x₀) = 2iφ'‖a‖²/a²`, `‖Θ'‖ = 2|φ'|`; the `n ≥ 2` trigonometric contradiction is right (open interval of length `nπ ≥ 2π` meets every residue mod `2π` except at most one endpoint class). Need `E x ≠ 0` only. |
| `HEEqPW ⇒` strict | `E^*=cE` ⇒ `G = g₀/E` entire with bounded `L²` lines on both sides ⇒ `G≡0` | correct (lines `s<0`: `‖G(x+is)‖ = ‖(g₀^*/E)(x+i|s|)‖` since `‖E(z)‖ = ‖E^*(z)‖ = ‖E(z̄)‖`). |
| no real zeros | blow-up `∫|f/E(x+iy)|² ≥ a²/(4L²y)` | recomputed (`‖w-x₀‖ ≤ √2y`, `|f|≥a/2`, `|E| ≤ L‖w-x₀‖`). OK. |
| `φ'|E|² ≃ 1` | lower `κ ≥ πc₀/C₁`, upper `κ ≤ π/c₁`, density argument | recomputed both; exceptional set `X` is countable because `φ` is injective and `memHE_sAlpha_unique` puts `φ(X)` in one coset of `πℤ`; `κ` continuous ⇒ bounds extend. OK. `Set.Countable.dense_compl` needs the field explicit: `Set.Countable.dense_compl ℝ hX` (signature checked). |
| evident fact | `PW ⊆ H(E)` with `c⁻²`, `C⁻²`; `H(E) ⊆ PW` via Fatou on `y=1/n`, strip `|s| ≤ 2`, `r=1` mean-value, `|y| ≥ 1` pointwise `H²` bound | all constants recomputed (`K₀ = C²e^{4π}M`, `K₁ = (2/π)K₀`, `‖f‖ ≤ 2√(M/π)Ce^{π|y|}`); proof complete and correct. |

---

## B. Findings (numbered)

Severity legend: critical = false statement / broken proof; major = gap needing new ideas; minor = the rest.

**R2-01 (minor, stale doc, M01 §0, §1.7, §6.4, §7; M10 §1, §5).** `Defs.lean` already contains the *strong*
`PaleyWienerThm` (part 1: `∀ g ∈ L²(-π,π)`, `pwFT g ∈ PW` and `‖pwFT g‖² = 2π‖g‖²`; part 2: `∀ f ∈ PW`
`∃ g`, `f = pwFT g`). M01 §0 still describes a vacuous `↔`, §1.7 still derives `(PW⇐)` through Parseval +
density + closedness, and §7 "Requested changes to M00" is already executed. Consequences:
(i) `memPW_pwFT` is now literally `(hPW).1 g hg`; (ii) `exists_pwFT` is `obtain ⟨g,hg,hrep⟩ := hPW.2 f hf`,
`f = pwFT g` by `funext`, and the norm identity must be *derived* (`rw [f = pwFT g]; exact (hPW.1 g hg).2`):
Defs part 2 does **not** carry `pwNormSq f = 2π‖g‖²`, contrary to the blueprint's "literally `hPW`";
(iii) the lemmas `pwFT_sub`, `tsum_enorm_sq_pwFT_int`, `l2piSq_eq_of_pwFT_eq` (and Steps 3-5 of §1.7) are
dead weight; an implementer should delete them (or mark optional) to avoid wasted work.
`memPW_of_tendsto` stays (needed by `pw_complete`, `pw_normal_family`). Also the statement in §7 that "Mathlib has no
lemma saying the L¹ and L² Fourier transforms agree" is irrelevant now that `PaleyWienerThm` is a hypothesis.

**R2-02 (minor, M01 `MemPW.fstar` / import order).** The blueprint says "use M02's `Differentiable.fstar` if
available". `PW/Basic.lean` imports only `Defs`; `HB/Basic.lean` imports only `Defs`, so importing it from
`PW/Basic` is cycle-free, but the simplest fix is inline: `fun z => by simpa using (hf (conj z)).conj_conj`
(`DifferentiableAt.conj_conj` exists, `Deriv/Star.lean:117`). Say so in the doc.

**R2-03 (minor, M01 §2.2 remark).** "constant exactly 1; exponent cannot be improved; attained asymptotically
by concentration at `t=∓π`" is inaccurate: the best constant is `sinh(2π|y|)/(2π|y|)` (≤ `e^{2π|y|}`, ratio → ∞
as `|y|` grows only like `4π|y|`), attained by `g = e^{-\bar z t}`; at `y=0` the constant 1 is sharp. Only
the *exponent* is sharp. Purely cosmetic, but the docstring in `Bounds.lean` repeats "constant exactly `1`".

**R2-04 (minor, `pw_complete` via `memPW_of_tendsto`).** `memPW_of_tendsto` assumes `hF`, `hK`, `hM` for *all*
`i`, but in `pw_complete` the family `F_m = f_m - f_n` has `pwNormSq F_m < ε` only for `m ≥ N`. The implementer must reindex
(`m ↦ m+N`, `l = atTop`) or weaken the lemma to "eventually". Also `K = √ε` needs `ε < ⊤` (take `ε` finite first;
`hc` is quantified over all `ε ≠ 0`, so this is fine). Not a gap, but state it.

**R2-05 (minor, `memPW_of_tendsto` Fatou).** The parenthetical "Fatou needs countably generated filter" is
satisfied: Mathlib's `lintegral_liminf_le` (`Lebesgue/Add.lean:233`) is stated for an arbitrary
`[IsCountablyGenerated u]` filter, so no reduction to sequences is required. (Pro-forma confirmation; the
requirement `l.IsCountablyGenerated` in the Lean statement is justified.)

**R2-06 (minor, M01 header "Used by").** The header says M02 uses `isH2Upper_mul_exp`. It does not (M02 §11 uses
`pw_line_integral_le`, "avoids H² of `f e^{iπz}`"). `MemPW.isH2Upper_mul_exp`, `MemPW.lintegral_mul_exp_le`
are used by no module at all; harmless (statements are true, constant 1 verified) but optional. Same for
`exists_memPW_eval_ne_zero` header claims: fine, used.

**R2-07 (minor, `plancherelPolya_tail` for unions).** M04 needs the tail bound for `Λ_α`, a union of two
`δ`-separated sets. The Lean statement is for a single `IsSepBy δ Λ`; the implementer needs the extra
step `(Λ₁∪Λ₂)∩S = (Λ₁∩S)∪(Λ₂∩S)` + `sampleSum_union_le` (the latter is provided) and `ε/2` splitting. Add
a one-line corollary `plancherelPolya_tail_union` to the interface to avoid duplication in M04/M07.
Also `plancherelPolya_tail` gives a single `R`; M04's use for "all `R ≥ R_ε`" needs monotonicity of `sampleSum`
in the set (M04 has its own `sampleSum_mono`; consider exporting it from M01).

**R2-08 (minor, M02 module headers).** `DeBranges.lean` docstring says "§6–§8" but its content is §7–§10;
`Comparable.lean` says "§9" but the evident fact is §11; M02 header mentions a "temporary upstream-interface
section" of `DeBranges.lean` that no longer exists (it now imports `PW.Complete`). Cosmetic.

**R2-09 (minor, interface mismatches with M04/M07).**
(a) M04 §7 step 1 writes `HEEqPW.isStrictHB hPW hEHB hEPW`; the signature is `(hE : IsHB E) (h : HEEqPW E)`, no `hPW`
(M03, M06 use it correctly).
(b) M04 lists `IsStrictHB.mul_isHB` ("new name") as an M02 export, but M02 neither lists nor states it. It is
the one-liner in §6(i): `‖E^*F^*‖ ≤ ‖E(z̄)‖‖F(z)‖ < ‖E(z)‖‖F(z)‖`. Add it to M02 (`HB/Basic.lean`).
(c) M04 re-proves `isPhaseFunction_mul` although M02 exports `IsPhaseFunction.mul`.
(d) M04 and M07 each state `IsHB.rotate` (not an M02 issue; flag for the integrator).

**R2-10 (minor, `fourierCoeff` name).** `Frames.lean` defines `FF.fourierCoeff`, which shadows Mathlib's root
`fourierCoeff` inside `namespace FF`. Compiles, but any later `open AddCircle`/unqualified use will be ambiguous.
Rename to `frameCoeff`.

**R2-11 (minor, `IsPhaseFunction` vs paper).** The paper (p. 794) only requires `φ` continuous with `E(x)e^{iφ(x)}` *real*;
`IsPhaseFunction` requires `E(x)e^{iφ(x)} = |E(x)| ≥ 0`. They differ by a constant shift by `π`; the level sets
`{φ ∈ α+πℤ}` are the same sets, so `TheoremE` (quantified over Lean phase functions only) is implied by the paper's
Theorem E. No action; worth one sentence in M00/M02 since the `2πℤ` uniqueness (`exists_int_eq_add`) is *finer*
than the paper's.

**R2-12 (minor, `Set.Countable.dense_compl` call).** M02 §10 writes `Set.Countable.dense_compl`; the Mathlib lemma takes the
scalar field explicitly: `Set.Countable.dense_compl ℝ hX` (needs `[Nontrivial ℝ]`, fine).

**R2-13 (minor, M02 §3.1 gap-free but terse).** In `isStrictHB_or_fstar_eq` the statement "`E^*-cE` vanishes on `ℂ₊`, hence
everywhere" needs `ℂ₊` to have an accumulation point in `ℂ` (it is open, so trivially), via
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` on `univ`; fine. Implementers should note `‖c‖ = 1`
because `‖Θ(z₀)‖ = 1`.

**R2-14 (minor, M02 §5.1 mechanics).** `HasDerivAt.norm_sq` is for `ℝ → F` with `F` a real inner product space; the
two curves `y ↦ F(x+iy)`, `y ↦ F^*(x+iy)` must be treated as `ℝ → ℂ` with derivatives `i b` and `i b̄`. The blueprint
says `HasDerivAt.scomp`; correct. `IsLocalMaxOn … hasFDerivWithinAt_nonpos` needs the *one-sided* set `Ici 0` and
`1 ∈ posTangentConeAt (Ici 0) 0`; supplied. (No gap; recorded so the implementer does not try to use a two-sided extremum:
`D` is **not** ≤ 0 for `y<0`, in fact `D(-y) = -D(y)`.)

### New observations on the source (not in the docs)

**N-A.** p. 793: the norm `‖f‖²_E = ∫|f(t)|²/|E(t)|² dx` is printed with `dx` instead of `dt` (print and tex agree). Typographical.

**N-B.** p. 796: the display before (5) and (5) omit the factor `π` of Theorem E (already N-09 in NOTEBOOK; confirmed on p-08.png).

---

## C. Statement-by-statement truth check (Lean pitfalls)

All OK unless stated.

*M01 Basic.* `isSeparated_iff_exists_isSepBy` is `Iff.rfl` (definitions unfold identically). `l2piSq_reflect`, `memL2pi_reflect`
true for arbitrary `g` (neg is a `MeasurableEquiv`, no measurability of `g` needed; `Ioc`/`Ico` differ by a null set).
`pwFT_reflect` true for arbitrary `g` (`intervalIntegral.integral_comp_neg`, no integrability). `norm_pwFT_le`:
`(l2piSq g).toReal` finite by hypothesis. `memPW_of_tendsto`: `[l.NeBot]` ⇒ `K ≥ 0`; Fatou applicable;
conclusion `pwNormSq f ≤ liminf` correct since `‖F_i x‖ₑ² → ‖f x‖ₑ²` pointwise. `MemPW.mul_div_sub`: true for every
`a ∈ ℂ` with `f a = 0` (including real `a`, `b` arbitrary): checked the three regimes (`‖z-a‖<1`, `≥1`, and the `L²`
domination by `(1+‖a-b‖)‖f‖ + M_h 1_{[Re a-1,Re a+1]}`). `pwNormSq_mul_div_sub_conj`: true for *any* `f` with `f a = 0`,
`a.im ≠ 0` (pointwise a.e. identity `‖dslope f a x‖‖x-ā‖ = ‖f x‖`); counterexample without `f a = 0` (`f ≡ 1`, `a = i`) is correct
(`0` vs `∞`).

*M01 Bounds/PP/Complete.* As in §A. `pw_normal_family`: the order "extract `ψ₀` realising the liminf, then ultrafilter/first-countable
subsequence" is correct, and `MapClusterPt.tendsto_subseq`-type lemma (`TopologicalSpace.FirstCountableTopology.tendsto_subseq`)
exists. `plancherelPolya_tail` true for `ε = ⊤` trivially. `ppConst δ > 0` for `δ > 0`; `ofReal (ppConst δ)` finite.

*M10.* `isFourierFrame_iff_isSampling` true as stated (both directions verified, constants `(A,B) ↔ (A/2π, B/2π)`,
`ENNReal.ofReal (2π) = ↑(Real.toNNReal (2π))` by definition; `reflect (reflect h) = h` by `neg_neg`; `Λ=∅` fails both sides;
non-separated `Λ` is irrelevant: the proof is an exact termwise identity). Precedence of `∑' … ∧ ∑' …` in `IsFourierFrame`
parses as intended (`∑'` binds tighter than `∧`, `≤`).

*M02.* `IsH2Upper.mul_bounded`, `.const_eq_zero` (`‖c‖ₑ² · ∞ = ∞` for `c ≠ 0`), `enorm_sq_le_of_lines` (case `K = ∞` trivial since
`ofReal(2/(πr)) > 0`), `eq_zero_of_lines_le`, `not_isH2Upper_div_of_zero` (needs `E ≠ 0` on `ℂ₊`, supplied, to rule out `x/0 = 0`)
true. `heNormSq_mul`: pointwise `F t f t/(E t F t) = f t/E t` only for `F t ≠ 0`; at `F t = 0` the left is `0/0 = 0`; zero set of `F` is
countable (`F(i) ≠ 0`), so a.e. equal. `phaseDeriv`/`orthWeight` junk at real zeros is harmless since all uses assume none.
`HEEqPW.isStrictHB`/`ne_zero_ofReal` correct. `zero_set_eq_phaseLevel` verified on `E=F=e^{-iπz}`: zeros `1/4 + k/2`.

---

## D. Do the statements serve downstream modules?

* **M03** (necessity): `pw_complete` (hypothesis shape matches `samp_cauchy_converges` after the `A·ε` trick), `MemPW.mul_div_sub hf hz (conj ζ)`
(implicit `a`, matches), `pw_norm_sq_le`, `exists_memPW_eval_ne_zero`, `HEEqPW.isStrictHB hEHB hEPW`, `ne_zero_ofReal`: all adequate.
* **M04** (sufficiency): `phaseDeriv_mul_sq_ge` (only the lower bound `κ ≥ c₁` is needed for the weights and for separation of level sets),
`pw_deriv_bound`, `plancherelPolya(_tail)`, `memHE_sAlpha_unique`, `MemHE.mul_isHB`/`heNormSq_mul` (argument order `E*F`, `F*f` matches), phase lemmas:
adequate; see R2-07, R2-09. I checked M04's `phase_tendsto` proof against the M01/M02 interface (finite part + tail via `plancherelPolya_tail`,
translation by `Equiv.tsum_eq`): sound.
* **M06**: `heEqPW_of_comparable`, `phaseDeriv_mul_sq_ge/le`, `IsPhaseFunction.hasDerivAt`: adequate. Note `phaseDeriv_mul_sq_ge/le` take `hPW` and `hE : TheoremE`
explicitly (M06 does pass them).
* **M07**: `IsHB.of_tendstoLocallyUniformly` (general filter, `hne`), `heEqPW_of_comparable hPW`, `HEEqPW.phaseDeriv_mul_sq_le`, `pw_normal_family`,
`plancherelPolya`, `IsHB.phaseDeriv_nonneg`, `exists_isPhaseFunction`, `continuous_phaseDeriv`: adequate.
* Nothing needed downstream is missing except `IsStrictHB.mul_isHB` (R2-09b) and a union version of the tail lemma (R2-07).

---

## E. Verdicts on the "Issues in the source"

### M01 §6
1. **p. 790, "By the Paley–Wiener theorem, `Λ` is sampling iff `{e^{iλ_k x}}` is a Fourier frame"** — **Confirmed** (cosmetic). Intro (tex l. 96–116) defines the frame with `∫f e^{-iλ_k x}` and
sampling with `f(λ_k) = ∫ g e^{iλ_k t}`; reflection `t ↦ -t` and the factor `2π` are indeed unmentioned. The set-vs-sequence remark is correct and harmless
(bounded multiplicity is forced by the upper bound).
2. **p. 796, Plancherel–Pólya with `C` independent of `α`** — **Confirmed** (true as printed). Verified the even/odd splitting giving two `δ`-separated sets
(constant `≥ δ`, as printed) and `C = 2C(δ)`. The comment that "[Yo80] is for unit separation" is **unclear** (not checkable here; irrelevant since `ppConst` is proved from scratch).
The unstated premise that `φ_{EF}` is onto `ℝ` (N-33) is outside M01.
3. **p. 797, `α → π/2` by dominated convergence from (4)** — **Confirmed** (gap). (4) bounds `∑_k|f(λ_{α,k})|²` uniformly in `α`; domination needs a summable majorant of
`sup_n|f(λ_{α_n,k})|²` in `k`, which (4) does not give; Fatou goes the wrong way for the upper limit. The fix via `plancherelPolya_tail` (uniform tails + termwise convergence) is correct.
4. **`PaleyWienerThm` makes `⇐` vacuous** — **Stale / withdrawn for the current repository**: true of the old statement, but `Defs.lean` already has the strong form (R2-01).
5. **Explicit constants** — **Confirmed** (all recomputed, §A).

### M10 §4
1. **p. 790 reflection + `2π`** — **Confirmed** (same as M01 §6.1).
2. **sequence vs set** — **Confirmed**, harmless.

### M02 §12
1. **p. 796, "E has no zeros on the real axis since PW = H(E)"** — **Confirmed**: stated without proof (p-08.png, line 441–442), true, and the blow-up argument (§1.5) is a correct proof.
2. **Strictness of `E`, `φ_E' > 0`** — **Confirmed in substance** (Theorem E is quoted for "a de Branges space" with no strictness; strictness of `E` is needed to have `φ' > 0` and
`Γ = {γ_k}_{k∈ℤ}`; the proofs §9, §5.2 are correct). **Wording correction:** for `E^* = cE` the space `H(E)` is `{0}`, `K_E ≡ 0`, `φ' ≡ 0`, so the quoted Theorem E is *meaningless* (`0/0` in the normalised kernels),
not literally false; only the Lean version (interpolation clause with weights `ofReal(π/0) = 0`) is false, which justifies the strictness hypothesis in `TheoremE`.
3. **`φ'_{EF} = φ'_E + φ'_F ≥ φ'_E`, `Λ = Λ_{π/2}`** — **Confirmed**: print has `φ'` (the last sentence of the item, about `φ_{EF} = φ_E+φ_F` in "the README seeds", is the withdrawn N-10 and should be deleted).
`φ_F' ≥ 0` (§5.1) and `zero_set_eq_phaseLevel` (§6) verified.
4. **p. 796 missing square** — **Confirmed, but mislocated.** On p-08.png the *first* sup is squared (`sup |f(x)|²`) and the *middle* one is not (`sup |f(x)|`, over `‖f‖²_E ≤ 1`). M02 §10 and §12.4 say "the first `|f(x)|` is missing its square":
wrong; NOTEBOOK N-05 ("middle term") is right. The claim that `sup_{‖f‖²_{PW}≤1}|f(x)|² = 1` is the sharp form of `pw_norm_sq_le` is correct (`K_PW(x,x) = 1`). "Theorem D not needed": confirmed (the paper uses (2), i.e. (1) at `z = x`, but the Theorem-E route is enough and is correct).
5. **p. 799 "evident fact"** — **Confirmed**: true, not evident. I re-derived the full proof (§A, last row). The paper's route (`f e^{iπz} ∈ H²`, `e^{-iπz}/E` bounded on `ℂ₊`) gives only `PW ⊆ H(E)`; the converse needs a Fatou step and a strip argument or Hardy-space boundary theory.
6. **p. 793 definition of `H(E)` / norm of `Ff`** — **Confirmed**, no gap. (Add N-A: `dx` for `dt`.)
7. **Theorem E "at most one α mod π"** — **Confirmed**; proof via constants in `H²` is correct.

---

## F. Items to fix before implementation (priority order)

1. Update M01 §0/§1.7/§7 and M10 §5 to the strong `PaleyWienerThm` already in `Defs.lean`; delete `pwFT_sub`, `tsum_enorm_sq_pwFT_int`, `l2piSq_eq_of_pwFT_eq` (R2-01).
2. Add `IsStrictHB.mul_isHB` to M02; fix `HEEqPW.isStrictHB hPW …` in M04 (R2-09).
3. Add a union version of `plancherelPolya_tail` and export `sampleSum_mono` (R2-07).
4. State the reindexing needed to use `memPW_of_tendsto` in `pw_complete` (R2-04).
5. Cosmetic: R2-02, 03, 06, 08, 10, 11, 12.
