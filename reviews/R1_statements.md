# R1 -- Referee report on the statement layer

Scope: `FourierFrames/Defs.lean`, `comparator/statements.lean`, `blueprint/M00_Defs.md`,
`blueprint/README.md`, and NOTEBOOK entries N-01..N-07, N-22, N-27.
Sources: page images `literature/pages/p-06, p-07, p-08, p-12` (journal pp. 794, 795, 796, 800)
read directly; the rest from `literature/ArxivOrtega.tex` (agrees with the print where compared).
I edited nothing except this file.

**Bottom line.** I found no critical (false or vacuous) statement. Every cited-result `Prop` is
true as stated (details below, with edge-case tests). Every definition is faithful up to harmless,
documented deviations. Two statements are weaker than the paper (`theorem2_i` through `hmono`,
`landau_sharp` through its reading of "best possible"). Several smaller observations follow.

---

## A. Definitions in `Defs.lean`

### A1. (minor / OK) Sampling, frame, CIS, separated, `PW`
- `MemPW`: entire, type `<= pi` in the "for every eps, C_eps e^{(pi+eps)|z|}" sense, `f|R in L^2`.
  This is the paper's definition. `MemLp (fun x : R => f x) 2` uses `volume` on `R`.
- `IsSampling`: `exists A B : R>=0, 0 < A`, so B is finite. `sampleSum` is an `R>=0inf` tsum over
  the subtype, so infinite sums stay infinite. Degenerate `Lambda = empty` is correctly not
  sampling (take `sinc`). A finite `Lambda` is not sampling either.
- `IsCompleteInterpolating`: `empty` is not CIS, because the unique-solution clause fails for the
  unconstrained problem in `PW`. Only values on `Lambda` matter, and the cast `x : R -> C` is the
  intended one.
- `IsSeparated`: `empty` and singletons are separated; this is harmless.
- `IsFourierFrame`: `g in L^2(Ioc(-pi,pi))` implies `g in L^1`, so the Bochner integral is
  genuine (no "non-integrable = 0" leak). `intervalIntegral` over `(-pi)..pi` equals the integral
  over `Ioc`, so the two sides are consistent. Same bounds `A > 0`, B finite.
- Sets versus sequences: sequences with repeated points (multiplicity) are not representable.
  The paper's Theorem 1 is only about separated sequences, so there is no effect there. But
  `isFourierFrame_iff_isSampling` is stated only for sets. This is covered by N-01 and I judge it
  a minor loss of generality. Suggested fix: add one sentence to the docstring of
  `isFourierFrame_iff_isSampling` saying "for sets, i.e. sequences without multiplicity".

### A2. (minor / OK) `countFn`, `MemBMO`
- `ncard` of an infinite set is `0`, so `countFn` is wrong for non-locally-finite `Lambda`. It is
  used only in `PavlovBMO` (separated `Gamma`) and nowhere else, so it is harmless. The sign
  convention `n(t) = -#(Lambda ∩ (t,0])` for `t < 0` matches `n(b) - n(a) = #(Lambda ∩ (a,b])`
  and `n(0) = 0` (p. 791).
- `MemBMO`: requires `LocallyIntegrable`, so the Bochner integrals in `meanOsc` are genuine.
  Mean oscillation over bounded intervals is the standard `BMO(R)`.

### A3. (OK) `fstar`, `IsH2Upper`, `IsHB`, `MemHE`, `heNormSq`, `HEEqPW`
- `IsHB` is exactly the paper's `\overline{HB}` (p. 793): entire, no zeros in `Im z > 0`,
  `|E(zbar)| <= |E(z)|`. `E = 0` is excluded (zero in `C+`). Real zeros are allowed, as in the
  paper.
- Closed versus strict: the closed class is *necessary* in `TheoremC`. Example (my check):
  `H = span{z}` with `||z|| = 1` satisfies H1-H3 (no nonreal zeros, `z* = z`). It equals `H(E)`
  for `E(z) = z(z + i*pi)` (`z/E = 1/(z+i*pi) in H^2`, while `1/E` has a pole on `R`). `E` has a
  real zero at `0`. Had `TheoremC` asked for `IsStrictHB` or no real zeros it would be false, so
  `IsHB` is the correct choice.
- `heNormSq` uses `x/0 = 0`. This is harmless: `E` is not identically `0`, so its real zeros form
  a null set. For `HEEqPW` they cannot occur anyway.
- `MemHE`: `f/E` and `f*/E` in `H^2(C+)` as in the paper. On `Im z > 0` there is no division by
  zero, since `IsHB` is assumed wherever `MemHE` matters. (`MemHE E f` for a non-HB `E` is junk,
  but no statement uses it that way. `HEEqPW` always appears next to `IsHB E`.)
- Sanity test: `E = e^{-i*pi*z}` gives `|E(z)| = e^{pi y}`, which is in HB with `H(E) = PW`.
  `E(z) = z + i` gives `H(E)` = constants. `E` real entire (`E* = E`), for example `1` or
  `e^{z^2}`, gives `H(E) = {0}`: with `h = f/E` entire, `h in H^2(C+)` and `h* in H^2(C+)` force
  `h in H^2(C+) ∩ H^2(C-) = {0}`.

### A4. (OK) Phase function, `phaseDeriv`, `phaseLevel`, `orthWeight`, kernel
- `E = |E| e^{-i phi}` gives `E'/E = (log|E|)' - i phi'`, so `phi' = -Im(E'/E)`, which is
  `phaseDeriv`. This holds for every continuous phase `phi` (all are locally `phi_0 + 2 pi k`).
- `IsPhaseFunction` encodes the displayed formula `E(x) = |E(x)| e^{-i phi(x)}`. The paper's
  words ("`E e^{i phi}` real") are slightly weaker, since the sign is not forced; the display is
  what is used. Without a no-real-zero hypothesis `phi` is not unique at a zero of `E`, but every
  use (Theorems E, `orthWeight`) assumes no real zeros.
- Pitfall `phaseDeriv f x = 0` when `f x = 0` (Lean `x/0 = 0`): this can only matter in
  `corollary2`. There `hf` does not exclude real zeros of `f`, but `happ` does: at real `x`,
  `||f x|| >= e^{UPsi ψ x - C} > 0`, and `UPsi ψ x` is a finite real (see A6). So the junk value
  never fires.
- `deBrangesKernel`: formula (1) is correct. The removable-singularity value at `z = conj w` is
  the correct limit. I checked that the numerator vanishes there, because
  `E*(wbar) conj E*(w) = conj E(w) E(wbar)`. For `E = z + i` the kernel is `1/pi` and
  `<f, K> = f(w)` holds.
- `orthWeight = ofReal(pi/(phi'|E|^2))`: positive and finite when `E` is strict without real
  zeros. This is the only place it is used.

### A5. (OK) `poissonInt`, `logExample`
- `poissonInt`: `ofReal` of a nonnegative kernel, so no junk.
- `logExample`: `Real.posLog 0 = 0`, so `k = 0` gives `0`. The map `k -> k + log^+|k|` is strictly
  increasing and injective (minimum gap `0.3069` at `k = -2 -> -1`; checked numerically), hence
  separated.
- `logExample_count` constants (`R >= 1`): numerical check up to `R = 50000` gives deviations in
  `[-0.79, 1.31]`.

### A6. (OK, with remarks) `IsAdmissiblePsi`, `LambdaPsi`, `UPsi`, `IsLogRegularPartition`
- `IsAdmissiblePsi`: for monotone `ψ`, `psi(inf) - psi(-inf) = inf` is equivalent to the
  disjunction `atTop atTop ∨ atBot atBot`. `deriv ψ -> 0` at `cocompact`. This equals p. 800.
  The `ContDiff ℝ 1` assumption is the paper's `C^1`.
  (Note: the paper's own example `ψ = sqrt x` for `x >= 0` is not `C^1` at `0`. This is a
  paper-level looseness; any smooth modification near `0` works.)
- `LambdaPsi`: `x ↦ x + ψ x` is a strictly increasing continuous bijection of `R`, so `Lambda` is
  the paper's `{lambda_k}` and is separated (gaps `>= 1/(1 + sup ψ')`).
- `UPsi` (the N-03 deviation): the integrand `(log|1 - z/t| + [|t|>1] Re(z/t)) ψ'(t)` is
  Lebesgue-integrable for every `z`.
  - Near `t = 0` and `t = z` there are logarithmic singularities, which are integrable.
  - `log|1-w| + Re w = O(|w|^2)` for `|t| > 1`, and `ψ'` is bounded, which gives a `t^{-2}` tail.
  - So the Bochner integral is not the junk value `0` (the concern in N-25).
  - `Re(z/t) = Re z / t` for real `t`.
- `IsLogRegularPartition`: `∃ t` is slightly weaker than "the" `t_n` of the paper if `ψ` is flat
  at an integer level. This only affects finitely many `n` once `ψ' >= c/x`, and the ratio
  constant `C` absorbs it. The tsum is over a finite subtype (`t_n -> ∞`), so there is no junk.
  `d_n` and `d_{n+1}` for `n = 1` use `t 0 = 0`, as in the paper. OK.

---

## B. Cited-result `Prop`s: are they true?

Verdict for each: **true as stated** (no critical issue). Remarks:

- **B1. `PaleyWienerThm`: true.**
  - (a) `f_g(z) = ∫ g e^{izt}` is entire of type `<= pi`, `|f_g(z)| <= ||g||_1 e^{pi|Im z|}`. It
    is in `L^2(R)` with `||f_g||^2 = 2 pi ||g||^2` (Plancherel). `pwNormSq` is `ENNReal`, so there
    are no finiteness leaks.
  - (b) Every `f in PW` is of this form (classical, supp `ĥ ⊂ [-pi, pi]`).
  - The A/B bookkeeping of N-27 follows (`A/(2 pi), B/(2 pi)`), and the reflection `t -> -t`
    turns `e^{-i lambda x}` into `e^{i lambda t}`.
- **B2. `TheoremC`: true** (de Branges 1968, Thm 23, p. 57 in the paper's citation).
  - (H1) as `∃ g, ||g|| = ||h|| ∧ ι g z = ι h z (z - ζbar)/(z - ζ)` for `z ≠ ζ` determines `ι g`
    (entire). (H2) is continuity at nonreal points. (H3) is `ι g = fstar (ι h)`.
  - The conclusion is `E in \overline{HB}` (weaker than de Branges' strict `HB`), `H = H(E)` as
    sets, and isometric. Edge-case test: `span{z}` (see A3) shows the closed class with real
    zeros is needed, and the statement allows it.
  - `heNormSq` uses `x/0 = 0`, harmless.
- **B3. `TheoremD`: true** (Thm 19). `E` strict without real zeros: `K_E(w, .) in H(E)` for all
  `w in C` including real `w`. The inner product integral is absolutely convergent, so
  Bochner-`0` cannot occur. Test: `E = z + i` gives `K ≡ 1/pi`, `∫ c/(pi (x^2+1)) = c`. ✓.
- **B4. `TheoremE`: true** (Thm 22).
  - The norm identity is the printed Theorem E (Parseval for the orthonormal basis of normalised
    kernels).
  - The interpolation clause follows: for `a` with `∑ |a(γ)|^2 / K(γ,γ) < ∞` set
    `f = ∑ a(γ) K(γ,.)/K(γ,γ)`. The kernels are orthogonal and evaluation is continuous, so
    `f(γ') = a(γ')`.
  - `orthWeight = 1/K(γ,γ)`.
  - Edge tests:
    - `E = z + i` has `φ(R) = (-pi, 0)`, so level sets are a single point or empty. The exceptional
      `α ≡ 0` is exactly the one with `E - E* ∈ H(E)` (constants), so the hypothesis excludes it.
      For the others the formula reads `pi|c|^2` on both sides. ✓
    - `E* = cE`, `|c| = 1`: `H(E) = {0}` and the hypothesis `¬ MemHE (e^{iα}E - e^{-iα}E*)`
      holds for `α ≢ 0`, but the conclusion would be false (`phi' = 0`, weights are `ofReal(π/0) = 0`).
      So the strict-class restriction (N-02) is genuinely necessary, and `IsStrictHB` is enforced.
  - Restricting to strict HB without real zeros only weakens the `Prop` (safe).
- **B5. `TheoremF`: true.**
  - The "only if" direction (isometric inclusion implies the existence of `A`) is what the Lean
    statement asserts. It is the printed Theorem F (p. 794, [dB60]).
  - Allowing `p >= 0` only weakens the conclusion, so it is implied by the printed form.
  - With `E` strict, `E - E* A ≠ 0` on `C+` (since `|E*| < |E|`, `|A| <= 1`), so `Re((E + E*A)/(E - E*A))`
    never uses Lean's `x/0 = 0`.
  - Sanity check, `E = z + i`, `μ = pi δ_0` (`∫|f/E|^2 dμ = pi|c|^2 = ||f||_E^2`):
    `A ≡ -1` gives `(1+w)/(1-w) = i/z`, whose real part is `y/|z|^2 = (y/pi) ∫ dμ/((t-x)^2+y^2)`.
    With `A ≡ +1` the right side would be `y`, i.e. `μ = 0, p = 1`, which is *not* isometric. This
    shows the "if" direction is not available for `p > 0`, but the Lean `Prop` only uses "only
    if". So the stated extension is safe but is not needed: for `μ` with `∫ dμ/(1+t^2) < ∞`,
    `Φ = (1+w)/(1-w)` with `w(i) = 0` already has `p = 0` (Schwarz lemma: `A = w/b`).
  - Locally finite `μ` follows from the hypothesis (every real point has an `f in H(E)` with
    `f(x) ≠ 0`), so an arbitrary `Measure ℝ` is not a problem.
- **B6. `PavlovBMO`: true** (necessity half of Theorem A). `h = n_Γ - t` is locally integrable
  (step function minus linear), and `BMO` is stated through the sup of mean oscillations over
  bounded intervals.
- **B7. `JohnNirenberg`: true.** Absolute `C, c`. With `||h||_* <= M`,
  `e^{-c s/||h||_*} <= e^{-c s/M}`. `>= s` versus `> s`: the set `{>= s}` is the intersection of
  `{> s - ε}`, so the same constants work. `Icc` versus open interval: null set. `||h||_* = 0`
  gives `h` constant a.e.
- **B8. `DSPerturbation`: true.** `Gamma` separated sampling gives `∃ L > 0` such that every
  injective perturbation `|δ| <= L` is sampling. Proof: `|(Σ|f(γ+δ)|^2)^{1/2} - (Σ|f(γ)|^2)^{1/2}|
  <= (Σ|f(γ+δ) - f(γ)|^2)^{1/2} <= L C ||f||` by Bernstein and Plancherel-Pólya (needs `Γ`
  separated), so `L < sqrt(A)/C` works for both bounds. `InjOn` makes the image-tsum equal the
  `Γ`-tsum. `L` depends only on `Γ` (and its separation constant).

I tried to build counterexamples to each of these and could not. The conditional main theorems
are therefore not vacuous because of a false cited result.

---

## C. Main statements in `comparator/statements.lean`

- **C1. (minor) `theorem1_*`: multiplicities.**
  - The zero set is stated as a *set* equation, ignoring multiplicities. The paper's "zero
    sequence" has multiplicities.
  - Sufficiency is therefore stronger than the printed statement (a hypothesis weaker in a
    harmless way), and the paper's reduction `F = S F~` handles real zeros of `F` of any
    multiplicity.
  - Necessity is correspondingly weaker than the paper's `G = (EF + E*F*)/2` with simple
    zeros. This is documented in `M00 §3`. The paper's necessity proof does give simple zeros
    (`G` is the genus-one product over the simple points `Λ`).
  - Suggested fix (optional): add `∀ x ∈ Λ, derivative ≠ 0` to the necessity conclusion for full
    fidelity.
  - The sufficiency/necessity pair is not vacuous: `Λ = ℤ + 1/2`, `E = e^{-iπz}`, `F = 1` gives
    `EF + E*F* = 2 cos πz`.
- **C2. (OK) `heEqPW_of_comparable`: true** ("evident fact").
  - For `f in PW`, `∫|f(x+iy)|^2 e^{-2 pi y} dx <= ||f||^2`, and `E ≠ 0` on `Im z >= 0` by the
    lower bound, so `f/E, f*/E in H^2`. On `R`, `|E| ≃ 1`.
  - Conversely `f/E in H^2` gives `|f(z)| ≲ e^{pi y}/sqrt(y)`, and similarly for `f*`, hence type
    `<= pi`, and `f in L^2(R)` since `|E| ≲ 1` on `R`.
  - The inclusion of the closed half-plane (`0 <= z.im`) in `hcomp` is what makes `|E(x)| ≃ 1`
    available.
- **C3. (OK) `corollary1`, `completeInterpolating_zero_set`, `landau_inequality`,
  `logExample_*`.** Statements faithful; `encard` in `ℝ≥0∞` avoids junk. `Γ` separated is not
  asserted in `corollary1`, matching the paper (N-34, correct).
- **C4. (minor) `landau_sharp` is weaker than the paper's "best possible".**
  - The Lean statement says: no constant `B` works with `A = 0`. The example actually proves more
    (`n(R) - n(0) = R - log R + O(1)`), so `A >= 1` is needed: the coefficient of `log^+` cannot be
    lowered below `1`, and no `o(log)` substitute works.
  - Suggested fix: state `∀ A < 1, ¬ ∃ B, ∀ a < b, ofReal(b - a - A·posLog(b-a) - B) ≤ encard(...)`,
    or add it as a second conjunct. This is cheap given `logExample_count`.
- **C5. (OK, documented deviation) `corollary2`.**
  - The multiplicative form `e^{U - C} <= |f| <= e^{U + C}` is equivalent to
    `|U - log|f|| <= C` including `f ≠ 0` (in Lean `log 0 = 0` would let a zero hide). ✓ N-04.
  - With the truncated `UPsi` versus a principal-value `U_ψ`: when the PV exists, `U^{PV} = UPsi + c Re z`
    with `c = PV ∫_{-1}^{1} ψ'/t dt` real. If `f` satisfies the paper's hypothesis, then
    `f e^{-cz}` satisfies the formal one. `e^{-cz}` is zero-free and `|e^{-cz}(z̄)| = |e^{-cz}(z)|`,
    so it stays in HB-bar. It is real and positive on `R`, so the phase and `phaseDeriv` are
    unchanged. So the formal hypothesis is equivalent to the paper's wherever the paper's is
    defined, and the formal version is meaningful where the PV does not exist.
  - Truth of the statement itself rests on the paper's proof (N-17 Meĭman, N-18, N-19 are
    proof-level gaps, not statement-level). I see no statement-level obstruction.
  - `hφ : phaseDeriv f -> 0` with `phaseDeriv` defined through `deriv f / f`: fine because the
    approximation hypothesis excludes real zeros of `f` (A4).
- **C6. (major, documented) `theorem2_i` and `hmono`.** See N-22 verdict below. The comparator
  statement is strictly weaker than the printed Theorem 2(i), because of the extra hypothesis
  `∃ X, AntitoneOn (deriv ψ) (Ici X)`.
  - What `hmono` costs: it excludes natural `ψ` with oscillating `ψ'`, for example
    `ψ = log x + small oscillation`. It covers `√x`, `log^+ x`, `c log x`, `log^{a} x`.
  - What the proof needs is the local density bound `DensBound` (`ψ' <= K/d_n` on `[t_{n-1}, t_n]`).
    I verified the claim in the Lean docstring that `hmono + (cells of mass 1) + (d_n ≃ d_{n+1})`
    gives it: on `[t_{n-2}, t_{n-1}]` (with `t_{n-2} >= X`), `ψ' >= ψ'(t_{n-1})` and the mass is `1`,
    so `ψ'(t_{n-1}) <= 1/d_{n-1} <= C/d_n`.
  - Suggested fix: state `theorem2_i` in the comparator with a hypothesis of the weakest checkable
    form that the proof uses. For example fold `DensBound` into the statement as
    `∃ K, ∀ n >= 1, ∀ x in Icc (t (n-1)) (t n), deriv ψ x <= K / (t n - t (n-1))` next to the
    partition `t` (the partition has to be produced by the same `∃ t`, so this would be a variant
    of `IsLogRegularPartition`), or add `theorem2_i_of_regular` to the comparator list so that the
    reader sees both. `hmono` then becomes a corollary. Keep the docstring warning.
- **C7. (OK) `theorem2_ii`.** Matches the paper (`x ψ'(x) -> 0`, i.e. `ψ' = o(1/x)`). `IsAdmissiblePsi` plus
  `h0` forces `ψ -> ∞` at `+∞`. Consistent: `ψ' = o(1/x)` allows `ψ = log log x`.
- **C8. (minor) Hypothesis lists.** `theorem2_ii` takes only `hPW`. If its proof needs more, the
  hypothesis list is a lower bound of what can be proved, so this is not a statement problem.

---

## D. Verdicts on the NOTEBOOK entries

| Entry | Claim | Verdict |
|---|---|---|
| N-01 | sets, ℝ≥0∞ sums, closed `\overline{HB}` needed in Theorem 1 | **Confirmed.** `F = 1` (or `F` a unimodular constant) for CIS `Λ` is not strict. Also `TheoremC` needs the closed class (A3, `span{z}`). |
| N-02 | cited results as hypotheses, weakest form; strictness necessary for Thm E | **Confirmed.** `E* = cE` gives `H(E) = {0}` (verified: `h = f/E` entire, `h` and `h*` both in `H^2(C+)`); also for zero-free `E = e^{z^2}`. The "no real zeros" restriction is not necessary for D/F, only harmless. |
| N-03 | PV at `0` may not exist for `C^1 ψ` | **Confirmed.** The example `ψ' = 1 + 1/log(1/t)` (`t > 0` small) has `∫_0^ε dt/(t log(1/t)) = ∞`. At infinity no PV is needed (integrand `O(t^{-2})`). The `c Re z` difference and the `e^{-cz}` absorption are right (C5). |
| N-04 | multiplicative form equivalent to `|U - log|f|| ≲ 1`, excludes zeros | **Confirmed.** |
| N-05 | missing square in the display after (5), p. 796 | **Confirmed** (page image p-08: middle term reads `sup |f(x)|`, left term `|f(x)|^2`). Also a trivial `dx` for `dt` in the definition of `||f||_E^2` on p. 793. |
| N-06 | `φ_E'|E|^2 ≃ 1` follows from Theorem E alone | **Confirmed**, though marked *open*. Lower bound: norm identity at the level set through `x`, applied to `f in PW` with `|f(x)|^2 >= c||f||^2` (`ξ_E` equivalence). Upper bound: the interpolant of `δ_x` on that level has `||f||_E^2 = π/(φ'|E|^2)` and `1 = |f(x)|^2 ≲ ||f||_PW^2 ≲ ||f||_E^2`. Needs `E` strict without real zeros (follows from `H(E) = PW`) and a non-exceptional `α`, by continuity of `φ`. Theorem D (formula (2)) is only used for the remark of p. 797. |
| N-07 | (3) has the wrong sign, lacks `1/π`, and `1/λ_k` undefined at `0 ∈ Λ` | **Confirmed** (page image p-07, eq. (3)). `Re(-i/(z - λ)) = -y/|z - λ|^2 <= 0`, but the right side `(1+w)/(1-w)`, `|w| < 1`, has positive real part; and Theorem F's Poisson integral has `1/π`. Correct form: `(i/π) Σ c_k (1/(z - λ_k) + …)` (equivalently `-i/(λ - z)`). Also: the paper omits the linear term `p y`; in the PW setting it vanishes, and Lean's `p ≥ 0` is a harmless slack. Does not affect the argument. |
| N-22 | Theorem 2(i) needs regularity beyond the stated hypotheses | **Confirmed as a gap in the printed proof; the "counterexample" is to the construction only.** p. 802 does say "the smoothness of ψ ensures …", and p. 790 says "ψ sufficiently regular", while the printed theorem has no such hypothesis. The M08 example (unit mass on a spike of length `ℓ_n = log t_n ≪ d_n = √t_n`, satisfying `ψ' -> 0`, `d_n ≃ d_{n+1}`, `ψ' >= c/x` after adding a small baseline, and the sup condition) indeed makes `V(x) ≈ log(ℓ_n/d_n) -> -∞` for the paper's `f` (one zero `z_n` at depth `≈ c d_n` per cell). It does *not* show that `Λ(ψ)` fails to be sampling, so the truth of Theorem 2(i) as printed is open. The stated reason in the Lean docstring is sound; the added hypothesis is a genuine weakening (C6). |
| N-27 | Fourier frame vs sampling needs reflection and `2π` | **Confirmed as a correct remark, but not an error in the paper.** The sentence on p. 790 is true; the reflection `t -> -t` and the factor `2π` (bounds `(A/2π, B/2π)`) are details of the proof, so "(T)" overstates it. Suggest re-labelling as (S)/(G). |

---

## E. Short summary

1. No critical findings: all eight cited `Prop`s are true as stated (edge cases tested: polynomial
   `E`, `E* = cE`, real zeros of `E`, `H(E) = {0}`, `span{z}`), all definitions are faithful, and
   the Lean pitfalls (`x/0`, `log 0`, `ncard`, `tsum`, Bochner junk) are either guarded or only
   reachable in unused regimes.
2. Major (unfaithful weakening, documented and justified): `theorem2_i` assumes `hmono`; the printed
   proof genuinely needs a local density bound, but `hmono` is stronger than needed. Suggested: use
   `DensBound`-type hypothesis or list `theorem2_i_of_regular` in the comparator.
3. Minor: `landau_sharp` only shows the log term is needed, not that its coefficient `1` is optimal;
   `theorem1` zero-set statements ignore multiplicity; `isFourierFrame_iff_isSampling` is for sets
   only; `TheoremF`'s `p ≥ 0` is unnecessary slack.
4. Notebook: N-01..N-07 all confirmed; N-22 confirmed (gap in printed proof, truth of printed
   theorem open); N-27 confirmed but mis-typed.
