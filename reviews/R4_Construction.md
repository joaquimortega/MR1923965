# R4 — Referee report: M06 (log example) and M07 (construction, perturbation, Corollary 2)

Scope: `blueprint/M06_LogExample.md`, `blueprint/M07_Corollary2.md`, `FourierFrames/{LogExample,Construction,Perturbation,Corollary2}.lean`,
against pp. 798–801 (page images p-10..p-13), `literature/ArxivOrtega.tex`, `FourierFrames/Defs.lean`, `comparator/statements.lean`,
the vendored `OrtegaCerdaSeip/Lemma3`. Nothing else was edited. Python (numpy, outside the repo) was used for numerical checks.

**Bottom line.** I found no mathematical error in either blueprint: every Lean statement in the four scaffolds is true as stated
(modulo the cited `Prop`s), and the proofs I recomputed are correct. The problems are (i) one false temporary interface lemma in
`LogExample.lean` (M06/M07 mismatch), (ii) one missing upstream lemma in `Corollary2.lean`, (iii) imprecise/obsolete NOTEBOOK entries,
and (iv) a few minor items. Verdict on source issues: all M06 §9 and M07 §4 items are confirmed; N-17 and N-30 are correct, N-16 is
correct but slightly over-sold, N-18 and N-19 are inaccurate/incomplete and should be rewritten.

---------------------------------------------------------------------------------------------------

## A. Findings (numbered, by severity)

### F1 (major; critical for soundness if left in place) — the temporary `exists_hb_of_density` in `LogExample.lean` is FALSE at `m = logDensity`

`FourierFrames/LogExample.lean` lines ~33–43 declare (`sorry`) the README §4 version of `exists_hb_of_density`, with the phase clause
`∃ φ, IsPhaseFunction E φ ∧ ∃ c₀, Tendsto (φ x - π·multPrim m x) (cocompact ℝ) (𝓝 c₀)` and *no* `hshift`/`hU` hypothesis. M07 §0.2 shows this
clause is unprovable for general `m → 1`; it is in fact **false for the very density M06 feeds it**: for `m = logDensity`,
`U = π y + κ x + O(1)` with `κ ≈ -1.3523 ≠ 0`, so locally `A(s+τ) ≈ c e^{κτ} sin π(τ-θ)`, `B(s+τ) ≈ -c e^{κ(τ-1/2)} cos π(τ-θ)`, hence
`E(s+τ) ≈ c e^{κτ}[sin π(τ-θ) + i e^{-κ/2} cos π(τ-θ)]` with amplitude ratio `e^{-κ/2} ≈ 1.97 ≠ 1`, and `φ(s+τ)-φ(s)-πτ` does not tend to 0
(the phase advances non-uniformly inside each period; only the level structure `φ(γ_j)=π/2+π(j+k₀)` survives).
I re-derived this and I agree with M07's analysis (A-translates, `B = A(·-1/2) P/Q`, `P/Q → 1`).
Consequence: the M06 chain as scaffolded depends on a `sorry`ed lemma that is false for its instance.
M06 only uses the first four clauses plus *some* phase function. **Fix:** in `LogExample.lean` replace the temporary lemma by M07's
`exists_hb_of_density` (Construction.lean, with `hshift`); supply `hshift` from `logDensity_U_estimate`:
`|U(z-1/2)-U(z)| ≤ |U(z-1/2)-π y-κ(x-1/2)| + |U(z)-π y-κ x| + |κ|/2 ≤ 2C+|κ|/2` (note `z-1/2` stays in `Im ≥ 0`); obtain `φ` from
`exists_isPhaseFunction` (E has no real zeros). M06 §5 and §8 (and the "verbatim README §4" statements in M06 §0/§8) must be updated;
the blueprint M06 §5 currently never states `hshift`.

### F2 (major, interface) — `Corollary2.lean` lacks `IsPhaseFunction.hasDerivAt`

Step 8 of the proof of `corollary2` (separation of `Γ'`) needs `HasDerivAt φ_E (phaseDeriv E x) x` for the phase function `φ_E` returned by
`exists_hb_of_density_phase` (an existential `φ`), see M07 §3.7 step 8 ("from M02"). The upstream list in `Corollary2.lean`
contains only `exists_isPhaseFunction` (which gives HasDerivAt for *some* phase function) and `IsPhaseFunction.strictMono_of_isStrictHB`, not the
uniqueness-type statement `IsPhaseFunction.hasDerivAt` that M06 already declares (new name). Either add it to M02's list
(it is true: `φ` is a continuous branch of `-arg E`, so `φ' = -Im(E'/E)`) or make `exists_hb_of_density_phase` return `∀ x, HasDerivAt φ (phaseDeriv E x) x`.
Also `φ_f` in `exists_good_density` is taken from `exists_isPhaseFunction`, which is fine.

### F3 (major, design — the requested generalisation of the M07 phase theorem) — correct form of the κ-twist

For `U = π Im z + κ Re z + O(1)` (M06's case, and also what removes the "moment condition" of `exists_modified_density`), the construction
that has `|E| ≃ e^{π Im z}` **and** `φ_E - πM → c₀` is
`E_κ := e^{-κ z} (A - i e^{κ/2} B)`, not `e^{-κ z}(A - iB)`.
Reason: `F_k(z) = A(z+s_k) e^{-κ(z+s_k)}` is entire, `|F_k| ≲ e^{π|y|}` and `|F_k| ≳ e^{π|y|} min(1,d)` (use `U(z̄)=U(z)`), so Liouville gives
`F_k → c sin π(z-θ)` exactly as in §2.7(a); then `e^{-κ(z+s_k)}B(z+s_k) = e^{-κ/2} F_k(z-1/2) R(z+s_k) → -e^{-κ/2} c cos π(z-θ)`, so the
companion must be rescaled by `λ = e^{κ/2}` to get equal amplitudes. `isHB_polyA_sub_polyB` already allows an arbitrary `λ > 0`, and
`E_κ + E_κ^* = 2 e^{-κ z} A` still has zero set `Γ`. With the plain `E₀ e^{-κ z}` of M06 §5 the clauses needed in M06 hold, but the phase clause would not.
Statement to formalise: replace `hU` by `∃ κ C, ∀ z, 0 ≤ Im z → |U z - π Im z - κ Re z| ≤ C`, conclusion `|E| ≃ e^{π Im z}`, same phase clause.
(Bonus: with this version `exists_modified_density` only needs `∫ h = 0`; the linear-moment condition `ℓ = -b₀`, hence §3.2's affine coefficient `b`, would no longer have to be
tracked, because `e^{-κ z}` absorbs it. Optional simplification; the present route is also correct.)

### F4 (minor) — `landau_sharp` is the weakest reading of "best possible"

`¬∃ B, ∀ a<b, ofReal(b-a-B) ≤ encard(Λ∩Ioc a b)` says only that the log term cannot be dropped. The example gives deficiency `log R + O(1)`
(proved count `≤ 2` error), so one can also state `∀ A<1, ∀ B, ∃ a<b, encard < ofReal(b-a-A log⁺(b-a)-B)`. The comparator statement as it stands is true and
matches the paper's wording ("cannot be dropped"); strengthening is optional. The proof in M06 §7 is correct (`ncard ≤ R - log R + 2`, finite set so `encard=ncard`).

### F5 (minor) — M06 §0/§9: the "sine-type" claim for the paper's `F` is asserted, not proved

The formalisation proves `|E| ≃ e^{π Im z}` for an `E` whose `E+E^*` vanishes on `Λ+1/2`; it never shows that the *paper's* symmetric product
(`z ∏_{k≠0, |λ_k|<R}(1 - z/λ_k)`) is sine-type. I checked that the claim is true: symmetric truncation gives
`log|F_sym| = lim ∫_{|t|<R} log|1 - z/t| dn = U - κ x + O(1)`, the shift by 1/2 changes `log|F|` by `O(1)` (`|F'/F|` bounded), and
`∏ λ/(λ+1/2)` over symmetric windows converges, so no exponential factor appears. The remark in M06 §4 is right but unproved; harmless since nothing downstream uses it.

### F6 (minor) — duplicated temporary declarations at assembly

`exists_hb_of_density` (both files), `IsHB.mul`, `heEqPW_of_comparable`, `theorem1_sufficiency`, `HEEqPW.isStrictHB`, etc. are declared (`sorry`) in several files in
namespace `FF`; assembling all four files without deleting the temporary blocks gives name clashes. (Expected, noted in the files; listed for completeness.)
In particular `IsAdmissiblePsi`'s clause `ψ → ±∞` is never used by `corollary2` (see M07 §4 item 9; I agree).

### F7 (minor, documentation) — NOTEBOOK N-18, N-19 are inaccurate (see verdicts below).

---------------------------------------------------------------------------------------------------

## B. Adversarial verification log (what I recomputed; all OK unless flagged)

### M06
* **Gaps.** `g_k ∈ [1-log 2, 1+log 2]` (cases `k ≥ 1`, `k ∈ {0,-1}`, `k ≤ -2`) ✓; `|g_k-1| ≤ 3/(1+|k|)` ✓ (checked `k=-2`: `0.693 ≤ 1`). Numerically `g ∈ [0.30685, 1.69315]`.
* **Two-level density.** With `l_j=g_{j-1}/2, r_j=g_j/2, L_j=(g_{j-1}+g_j)/2`, `u_j=r/(lL)`, `v_j=l/(rL)`: mass `ul+vr = (r+l)/L = 1`, first moment about `β_j` is `(-r l + l r)/(2L)=0` ✓ for all positive `l,r`.
  Numerics (|k| ≤ 3·10⁵): mass error `3·10⁻¹¹`, barycentre error `9·10⁻⁶` (float cancellation at `t² ~ 10¹¹`), `m ∈ [0.4386, 4.9874]` so `1/10 ≤ m ≤ 20` holds with room.
  Lower bound `0.6/5.78 = 0.1038 > 0.1`, upper `3.4/0.18 = 18.9 < 20` ✓. `N = ε_j - 3ε_{j-1} - ε_{j-1}² - ε_{j-1}ε_j` ✓ (expanded), constants 23, 207, 1035 ≤ 1100 ✓ (`1+|t| ≤ 5(1+|j|)` ✓).
* **`W = M - t`.** `W(p_j) = -δ_j`, `δ_j = (log⁺|j-1|+log⁺|j|)/2`; `|ρ| ≲ (1+|t|)^{-1/2}` argument (J<8 / J≥8, constants 352 = 1.7·207, `J - log J ≥ J/2` for `J ≥ 8`) ✓.
* **`multU_model`.** `∫ ½log(1+y²/t²) dt = π y` ✓; the `G(w)=w Log w - w` evaluation is consistent with this.
* **Hilbert-type bound.** `K_z = Re(z/(t(t-z)))` ✓; integration by parts boundary terms vanish (`φ_z(±R)=O(1/R)`, `W = O(log R)`; `φ_z(ε)W(ε) = O(ε log ε)`) ✓;
  `|∫ log⁺|t| K_z| ≤ π²/2 + 1` for `Im z ≥ 1`: symmetric truncation, oddness of `P`, `x<0` by `t→-t`, scale-invariant bound `|P(s)| ≤ 1/s`,
  `c_* = ∫_0^∞ log((1+σ)/|1-σ|)dσ/σ = π²/2`, tail piece `≤ 2x log(2R)/(R-x) → 0` ✓. `∫|ρ||K_z|` three-region estimate ✓ (uniform in `Re z`).
  Strip comparison `|U(x+iy)-U(x+i)| ≤ ½∫ log(1+1/s²)·20 = 20π` ✓.
* **Numerics of the estimate.** Exact piecewise integration gives `κ = -1.35227`; `U(x+iy)-π y-κ x` is bounded: at `y=1` it is `-1.9` (x=-10..-100), `+0.3` (x=0), `+6.8..7.9` (x=10..100) → asymptotes
  `≈ -1.9` and `≈ +7.9`, difference `≈ 9.8 ≈ π²` as predicted (x=±1000 values are polluted by truncation at |t| = 3·10⁵).
* **Counting.** `|N - (R - log R)| ≤ 1`, `-n(-R) - (R+log R) ∈ [-1, 1.7]` ✓ with the convention `Λ∩Ioc 0 R`, `Λ∩Ioc(-R) 0` (0 ∈ Λ counted on the negative side).
* **`E = E₀ e^{-κ z}`:** HB̄, no real zeros, `|E| ≃ e^{π y}`, `E^* = E₀^* e^{-κ z}` (κ real), phase unchanged ✓.
* **Theorem E at `α = π/2`.** `S = iE + iE^*`; `|S/E| = 2|cos φ|`, `φ` strictly increasing with `m₁ ≤ φ' ≤ M₁` so the sets `{|φ - kπ| ≤ π/4}` have length `≥ π/(2M₁)` each: not in `L²` ✓.
  Weights between `π/C_φ` and `π/c_φ` give sampling and CIS (uniqueness via `h ∈ H(E)=PW`, `heNormSq h = 0`) ✓. Translation lemmas ✓.

### M07
* **Lemma H** (`arg(z-t)` increasing, partial sum of arguments in `(0,π)`) ✓; `|P(z)|²-|P(z̄)|² = 4|A|² Im(λB/A)` ✓ (expanded). Orientation `γ_j<β_j<γ_{j+1}` ⇒ `E = A - iB`, no sign choice needed ✓ (`B_R/A_R` is a monic ratio).
* **Zero set of `B = D·P`**: `D(a_j) = A'(γ_j)/Q'(a_j) ≠ 0`; zeros `{γ_k+1/2 : |k| ≥ N} ∪ {β_j : |j|<N}`, one per interval `(γ_k,γ_{k+1})`, simple, even if `β_j = a_j` ✓.
* **`E_R → E`**: `e^{β+c_R z}e^{-c_R/2}B_R = e^{β + c_R(z-1/2)}A_R(z-1/2)·P/Q → B` ✓, Hurwitz + `E ≢ 0` (at a real non-zero of `A`) ✓.
* **Counterexample to Meĭman as quoted.** `A = cos πz`, `B = e^{az} sin πz` (zeros `1/2+ℤ`, `ℤ`, interlaced, real, simple): on `z = iy`, `|A∓iB(iy)|² - |A∓iB(-iy)|² = ±4 cosh πy sinh πy cos(ay)` changes sign when `a ≠ 0`; numerically with `a = 1`,
  `|E(z̄)| > |E(z)|` at 272/663 sample points for `E = A - iB` and at 391/663 for `A + iB` ⇒ neither is in HB̄ ✓. (The claim holds for the actual `A,B` by the polynomial argument.)
* **Phase asymptotics.** Normal-family/Liouville: `|sin π w| ≥ c₀ e^{π|Im w|} min(1,dist(w,ℤ))` (constants checked: `|Im w| ≥ 1/2`: `sinh`; `|Im w|<1/2`: `4 d_x² + π² y² ≥ 4 dist²`) ✓; `R(z+s_k) → 1` since `P,Q` monic of equal degree ✓;
  `E(x+s_k) → i c e^{-iπ(x-θ)}`, `g_k = φ(s_k+·)-φ(s_k)-π·` with `e^{-ig_k} → 1` uniformly and `g_k(0)=0` ⇒ `g_k → 0` ✓. Levels: `σ` strictly increasing bijection of ℤ ⇒ `σ(n)=n-k₀`, a single `k₀` at both ends ✓ (strictness of `φ` via `sin α A - cos α B ≡ 0` ⇒ proportional ⇒ common zeros, contradiction ✓).
  The claim that the phase clause fails for `m → 1` alone (M07 §0.2) is right (see F1/F3 mechanism).
* **Perturbation lemma.** `isSampling_replace_point`: both cases correct (`h = g(z)(z-a)/(z-b) ∈ PW` vanishes on `Γ`; or `g=0` ⇒ `A ≤ sampleSum Γ' f_n + |f_n(a)|² → 0`). `isSampling_of_replace_finite`: induction on `n`; hypothesis `ncard (Γ\Γ') = ncard (Γ'\Γ)` essential:
  `ℤ∖{0}` is not sampling (`sin πz/z` vanishes on it). `of_perturbation`: `δ₁` injective (near/far, using `η/4`), `N∩M = ∅`, `G∩M=∅` by injectivity, `|N\G| = |G\N|` ✓. So "finitely many moves" is handled correctly: counts agree because `x ↦ x+δ x` is injective and the moved points are matched by integer index.
  `DSPerturbation` as stated is true (Duffin–Schaeffer, with `L ≤ η/4` separation of the image is automatic).
* **Reduction "ω' ≃ 1".** `exists_modified_density`: `m = c + s·sgn(t)·1_{1<|t|<R}` on `[-R,R]`, `∫_{-R}^R m = ∫(1+w)`, `∫_{1<|t|<R} m/t = 2 s log R = L_R - β` ⇒ linear moment of `h` equals `-β`;
  bounds (`c ≥ 3/4`, `|s| ≤ 1/8`, `m ≥ 5/8`) ✓. Exact phase identity `π M + φ_f = π(x+ψ)+κ` for `|x| ≥ R` (needs `∫h=0` for equal constants at ±∞) ✓.
* **Potential identity** `log|f| = U_{φ_f'}/π + b Re z + c`: `Im potC(x) = -π(φ(x)-φ(0))` (checked signs of `argUp` for `t<0`, `t>0`, `x<0`, `x>0`), `H = L - Q/π` has `Im H = const` on ℝ, Schwarz reflection `Ĥ = conj H(z̄) + 2ic`
  continuous across ℝ, `|Re Ĥ| ≲ (1+|z|)^{3/2}` ⇒ affine (Borel–Carathéodory + Cauchy), `Im β=0` ✓. `b ≠ 0` can occur (`f ↦ f e^{bz}` stays in HB̄, same phase).
* **Final index matching.** `Θ = φ_E - β + φ_f - π/2`, `β = κ + c₀ - π/2`; zero set of `E_β f + E_β^* f^*` = `{Θ ∈ πℤ}` (real by strictness, level `π/2`); `δ = Ψ^{-1}(Θ/π) - x` with `Ψ = x+ψ` expanding so `Ψ^{-1}` 1-Lipschitz, `|δ| ≤ |Θ/π - Ψ| → 0`, and the image of `Γ'` is exactly `Λ(ψ)` with the *same* integer index ✓. Separation: `Θ' = φ_E' + φ_f' ≤ C_E/c² + M_g` (`|E| ≥ c` on ℝ from `Im z = 0` comparability) ✓.
  The tex proves only (8) and ignores the `π/2` offset between `φ_E+φ_f ∈ π/2+πℤ` and `x+ψ ∈ ℤ`; the blueprint's rotation `e^{iβ}` repairs this (and `e^{iβ}` preserves HB̄, `|E|`, `phaseDeriv`).
* **`UPsi` vs principal value** differ by `c Re z`, absorbed by `f ↦ f e^{cz}` (HB̄-preserving, phase and `phaseDeriv` unchanged) ✓.

---------------------------------------------------------------------------------------------------

## C. Verdicts on the "Issues in the source"

### M06 §9
1. `F` undefined at `λ_0=0` — **Confirmed** (p. 798 shows `∏_{|λ_k|<R}(1 - z/λ_k)`, `λ_0 = 0 + log⁺0 = 0`). Minor.
2. Sine-type claim unproved — **Confirmed** (the claim is true; see F5 for why the symmetric product has no exponential factor; the "naive reading" worry is rightly dismissed: `n(t)-t = -log|t|+O(1)` is even).
3. Levin ⇒ CIS ⇒ sampling — **Confirmed**; the replacement by Theorem E is sound (modulo F1).
4. Counting statements — **Confirmed**, with the `(a,b]` convention; error ≤ 2 proved, ≤ 1.7 sharp-ish numerically.
5. Sharpness not argued — **Confirmed**; see F4 for the reading.
6. Simplification (exact `Λ+1/2` barycentres, no perturbation) — **Confirmed correct**; the two-level density works for any positive `l_j, r_j`.

### M07 §4
1. Meĭman as quoted false — **Confirmed** (my numerical check; also N-17's imaginary-axis computation). `P ↦ -P` unnecessary — **confirmed** (orientation forced).
2. "monomials `P`, `Q`" — **Confirmed** (must be real-rooted polynomials; `z^k` is a monomial with all zeros at 0).
3. Symmetric product need not converge — **Confirmed**: `∑_{|j|≤R} 1/γ_j ≈ ∫_{1<|t|<R} m/t` diverges for `m = 1 + 1/log log t` on `t>t₀`, `m=1` for `t<0` (integral `∫ ds/log s = ∞`).
4. "ω' ≃ 1" gap — **Confirmed**: needs sign/lower bound repair, `∫h = 0`, and the affine coefficient; the tex never mentions them.
5. Potential identity used without proof — **Confirmed**; §3.2 proof is correct (growth hypothesis from `happ` is essential).
6. Normal-family step — **Confirmed**: (a) the tex has `A_k(z) = A(z - x_{2k})`; the correct translate is `A(z + x_{2k})` (zeros `γ_j - x_{2k} → 1/2+ℤ` only for `+`); (b)(i) needs `U - π Im z` bounded; (iv) same shift at ±∞; (v) the printed `E(x) = |E(x)| e^{i(π(x+ψ)-φ_f+o(1))}` has the wrong sign: p. 794 defines `E = |E|e^{-iφ}` and (8) says `φ_E = π(x+ψ)-φ_f+o(1)`, so the exponent should be `-i(...)` (confirmed on p-13 image and tex l. 793). Also the paper's `A_k ≈ c_k cos πx`, `B_k ≈ c_k sin πx` is consistent with `A_∞ = c sin π(z-θ)` after `θ = -1/2`.
7. Separation not mentioned — **Confirmed**; fix via `φ_E'|E|² ≲ 1` correct.
8. "Elementary fact" — **Confirmed**: true only for *replacements* with equal counts; `ℤ∖{0}` counterexample is right; in Corollary 2 the matching by integer index gives equal counts.
9. `ψ(∞)-ψ(-∞)=∞` unused — **Confirmed** (`ψ=0, f=1, Λ=ℤ`).
10. Principal value — **Confirmed**.
11. `|E| ≃ e^{π Im z}` not derived — **Confirmed**; needs `hshift` + `|E|² ≥ |A|²+|B|²` + uniform distance between `Γ` and `Γ_B` (`η₀ > 0`), all in §2.6 ✓.

### NOTEBOOK
* **N-16** (sine-type claim, "open"): the statement is accurate. Suggest closing it with "the claim is true (F5); the formalisation avoids it; only `|E| ≃ e^{π Im z}` for an auxiliary `E` is proved".
* **N-17** (Meĭman): **correct**. The imaginary-axis computation `|cosh πy + e^{iay} sinh πy|` vs `|cosh πy - e^{iay} sinh πy|` is right (difference `4 cosh sinh cos(ay)`); I additionally verified numerically. Status "referee-pending" can be set to "referee-confirmed".
* **N-18** (ω' ≃ 1): **inaccurate and incomplete**. It says the modification "changes `Λ(ψ)` by finitely many points, handled by the perturbation argument". In the blueprint nothing changes `Λ(ψ)`; one changes the density `m` on `[-R,R]` only, and the real issues are (i) `∫h = 0` (equal phase constants at ±∞, otherwise an integer index shift), (ii) the linear term `ℓ Re z` / the affine coefficient `b` of `log|f| - U_g/π`. Rewrite accordingly.
* **N-19** (normal family): **incomplete**. Besides "x → -∞ analogous" and "identify the limits", record: sign `A(z+x_{2k})`, need `U-π Im z = O(1)` (the README phase clause is false in general), the single constant `k₀` at both ends, and the sign of the final exponent.
* **N-30** (p. 798 product): **correct** (`λ_0=0`; sine-type ⇒ CIS ⇒ sampling; boundedness of the conjugate function of `log|t|` — here `π²/2` — is exactly what §4.4 proves).
