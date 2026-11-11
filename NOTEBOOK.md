# Formalization notebook

**Source:** J. Ortega-Cerdà and K. Seip, *Fourier frames*, Ann. of Math. (2) **155** (2002),
789–806, MR1923965. Page numbers are the journal's.

This notebook records what we noticed in the source while formalizing it: mistakes, gaps,
clarifications, simplifications, and every place where the Lean proof deliberately differs from
the paper's argument.

**Verification.** Every claim about what the paper prints is checked against renders of the
printed PDF (`literature/pages/`, 150 dpi) or the author's tex (which agrees with the print). OCR
text is not trusted: it drops slashes, bars and primes (it shows "∈" for the "∉" of Theorem E and
loses the prime in "φ_f'" in Corollary 2).

**Entry types:**
- **E**: erratum (false as printed);
- **G**: gap or implicit step;
- **T**: typo;
- **S**: simplification;
- **D**: divergence of the formalization from the paper (definitions, statements or proofs).

**Status tags:** *print-checked* (verified on the page image), *tex-checked*, *referee-confirmed*
(confirmed by an independent review agent; reports `reviews/R1`–`R5`, blueprint review round,
2026-11-06), *code-checked* (checked against the final Lean code), *numerical*, *open* (not yet
settled). Referee R8 (2026-11-07) re-checked N-06, N-12, N-16–N-19,
N-21–N-25 and N-30–N-36 against the final Lean code; the corrections it asked for are applied below,
and N-39–N-42 record findings of the implementation that it found missing. N-43–N-45 come from the
blueprint of de Branges' Theorems D and E (`blueprint/P3_DeBrangesDE.md`, "Issues in the source"),
confirmed by referee R9 (`reviews/R9_DeBrangesDE.md`) and checked here against the page images.

Sections: N-entries are about the paper; I-entries (end of file) are the implementation log.

---

## Definitions and cited results

### N-01 (D) — Sequences, norms and the closed Hermite–Biehler class
- Sequences `Λ` are sets of reals (`Set ℝ`); Theorem 1 concerns separated sequences, so nothing
  is lost.
- Sums and integrals are `ℝ≥0∞`-valued (`sampleSum`, `pwNormSq`, `heNormSq`).
- `\overline{HB}` is the paper's closed class (`|E(z̄)| ≤ |E(z)|`). The non-strict inequality is
  needed in Theorem 1: `F` may be a real entire function times a unimodular constant (for instance
  `F = 1` when `Λ` is complete interpolating).

### N-02 (D) — Cited results are explicit hypotheses
The paper rests on results it quotes without proof: the Paley–Wiener theorem, de Branges'
Theorems C, D, E, F, Pavlov's Theorem A, the John–Nirenberg theorem, and Lemma III of
Duffin–Schaeffer. Each is a `Prop` in `Defs.lean`, stated in the weakest form the paper uses, and
appears as a hypothesis of exactly the main theorems that use it. None is an axiom.
- Theorem F is stated in the direction used, with an extra term `p·y` (`p ≥ 0`) allowed; the proof
  of Theorem 1 is unchanged.
- Theorems D, E, F are stated for `E` in the strict class without real zeros.
  For Theorem E this restriction is necessary: if `E^* = cE`, then `H(E) = {0}` and the
  interpolation part of the conclusion fails. For Theorem D it is not: de Branges' theorem holds on all
  of `\overline{HB}` (for `E^* = cE` the kernel is `0`). The restriction costs nothing, since the paper
  applies D only to `E` with `H(E) = PW`, which is strict without real zeros (N-28).
- Theorem A enters only through its BMO necessity part (`PavlovBMO`).

### N-03 (D) — `U_ψ` and the principal value (p. 800) — *tex-checked*
The paper defines `U_ψ(z) = ∫ [log|1 - z/t| + Re(z/t)] dψ(t)` "in the principal value sense".
For `ψ ∈ C¹` the principal value at `0` of `∫ Re(z/t) ψ'(t) dt` need not exist: it requires a Dini
condition on `ψ'` at `0`. Example: `ψ'(t) = 1 + 1/log(1/t)` for small `t > 0` and `ψ'(t) = 1` for
`t < 0`. The formalization keeps `Re(z/t)` only for `|t| > 1` (`UPsi`), as `OCS.multU` does. When
the principal value exists, the two potentials differ by `c·Re z` with `c` real. Corollary 2 is
insensitive to this, because `f ↦ f e^{-cz}` preserves `\overline{HB}`, the phase and the zero
set.

### N-04 (D) — Corollary 2's approximation hypothesis
`|U_ψ - log|f|| ≲ 1` is stated as `e^{U_ψ - C} ≤ |f| ≤ e^{U_ψ + C}`. This is the same condition and
also excludes zeros of `f` in `Im z ≥ 0`; in Lean `Real.log 0 = 0` would not.

## Section 2: de Branges spaces

### N-05 (T) — p. 796, display after (5): missing square — *print-checked; referee-confirmed (R1, R2, R3)*
The middle term reads `sup_{f ∈ H(E), ‖f‖²_E ≤ 1} |f(x)|`. It should be `|f(x)|²`, as on the left;
`K_E(x,x)` is the supremum of `|f(x)|²`.

### N-06 (S) — Formula (2) and Theorem D are not needed for Theorem 1 — *referee-confirmed (R1, R2, R3)*
The bound `φ_E'(x)|E(x)|² ≃ 1` when `H(E) = PW` (p. 796) is derived in the paper from (2), i.e.
from Theorem D. It also follows from Theorem E alone:
- the norm identity at the level set through `x` gives the lower bound (the only one Theorem 1
  needs);
- the interpolant of `δ_x` on that level set gives the upper bound.
The exceptional level `α` (where `e^{iα}E - e^{-iα}E^* ∈ H(E)`) is avoided by density: the
exceptional points form one level set, and `φ'|E|²` is continuous. The formalization uses this
route (blueprint README §3.1). Theorem D is only used for the remark on p. 797.

### N-07 (E) — p. 795, (3): sign, factor `1/π`, and `1/λ_k` — *tex-checked; coordinator-checked*
(3) reads `-i ∑_k |E(λ_k)|² (1/(z - λ_k) + 1/λ_k) + ia = (E + E^*A)/(E - E^*A)`.
- **Sign.** `Re(-i/(z - λ)) = -y/|z - λ|² ≤ 0` for `y > 0`, while the right side has positive real
  part (it is the Poisson integral of `μ`). The kernel must be `-i/(λ - z)` (equivalently `i/(z - λ)`).
- **Factor.** Theorem F's Poisson integral carries `1/π`, so the sum needs a factor `1/π`.
- **`0 ∈ Λ`.** `1/λ_k` is undefined if `0 ∈ Λ` (also in `G`), and the convergence of the series is not
  discussed. The formalization uses the kernel `1/(λ_k - z) - λ_k/(1 + λ_k²)`; the series converges
  because `∑ |E(λ_k)|²/(1 + λ_k²)` is the (finite) Poisson integral at `z = i`. `G` is the genus-one
  product over `Λ ∖ {0}`, times `z` if `0 ∈ Λ`.
The printed convergence factor `1/λ_k` is legitimate when `0 ∉ Λ` (R3); the defects are the sign,
the factor and the case `0 ∈ Λ`. None of this affects the argument. *Referee-confirmed (R1, R3).*

### N-08 (S) — p. 796: `G = (EF + E^*F^*)/2` — *print-checked*
The paper argues through real parts on `ℝ`. It follows directly by adding `M + 1 = EF/G` and
`M - 1 = -E^*F^*/G`.

### N-09 (T) — p. 796: missing factor `π` — *print-checked*
In the display before (5) and in (5), the weights should be `π/(|E|²|F|²φ'_{EF})`, as in
Theorem E. This is harmless since only `≃` is used.

### N-10 (T) — p. 796: `φ_{EF} = φ_E + φ_F ≥ φ_E` — *print-checked*
The print has `φ'_{EF} = φ'_E + φ'_F ≥ φ'_E`, which is correct. The OCR reading was wrong.
*Withdrawn.*

### N-11 (T) — p. 796–797: range of `α` — *print-checked*
`α` is taken in `(0, π]` on p. 796 and in `[0, π)` on p. 797. Either works.

### N-12 (G) — p. 797: the limit `α → π/2` — *referee-confirmed (R2, R3)*
"by (4) we may apply Lebesgue's dominated convergence theorem": (4) bounds the sums uniformly in
`α` but is not a domination. A correct argument uses the local Plancherel–Pólya inequality: the
tails `∑_{|λ_{α,k}| > R} |f(λ_{α,k})|²` are bounded by a fixed multiple of
`∫∫_{|x| > R-1, |y| < 1} |f|²` uniformly in `α`, and this tends to `0`.

### N-13 (G) — p. 796: `φ_F' ≥ 0` — *referee-confirmed (R3)*
Used without comment. For `F ∈ \overline{HB}` without real zeros it follows from
`log|F^*| - log|F| ≤ 0` on `ℂ₊`, with equality on `ℝ`.
- **Formalization:** `φ_F' ≥ 0`, and `φ_E' > 0` for strict `E`, both come from one dichotomy (either
  `E^* = cE` near `x`, or `φ'(x) > 0`), proved with a Hopf-type boundary lemma
  (`IsHB.phaseDeriv_pos_or_eventuallyEq`, `HB/Hopf.lean`). Strictness cannot be obtained from the
  derivative argument above alone. This also gives the "`φ_E + φ_F` strictly increasing" of N-28.

## Section 4: Landau's inequality

### N-14 (T) — p. 799, proof of the Claim: `Λ` should be `Γ` — *print-checked; referee-confirmed (R3)*
"`h'(t)` is bounded, in fact equal to `-1` for `t ∉ Λ`, and so if the right-hand side is smaller
than the separation distance of `Λ`". Since `h = n_Γ - t`, both occurrences of `Λ` should be `Γ`.
Separation of `Γ` is needed and holds because `Γ` is complete interpolating.

### N-15 (G) — p. 799: small intervals — *referee-confirmed (R3)*
`J = {t ∈ I : |h(t) - h_I| ≥ A log|I|}` requires `|I| > 1`. Short intervals are absorbed into the
constant `B`.

### N-16 (G) — p. 798: the sine-type claim — *referee-confirmed (R4)*
"`F(z) = lim ∏(1 - z/λ_k)` is a sine-type function" is asserted without proof. The formalization
proves the needed estimate `|E(z)| ≃ e^{π Im z}` for an associated `E`, and avoids Levin's
theorem (blueprint README §3.7). The short justification "`n_Λ(t) - t = -log⁺|t| + O(1)`, and the
conjugate function of `log|t|` is bounded" is not enough. The remainder is a sawtooth with unit jumps
at the `λ_k`, and boundedness alone does not bound its conjugate-type integral (the conjugate function
of a bounded function need not be bounded). What works is the density smoothing of [OS99] Lemma 3.
For `|Im z| ≥ 1`, replace the point masses by a density `m ≃ 1` with the same mass and barycentre on
each interval between the midpoints of consecutive `λ_k`. Then
`∫_0^t (m - 1) = -log⁺|t| + c + O((1 + |t|)^{-1/2})`, and the conjugate function of `log|t|` plus an
`O(1)` remainder give the bound. The formalization also replaces the point masses by a density,
`m ≃ 1` with [OS99] barycentres exactly `Λ + 1/2` (N-30; M06 §3–4). (Found in the second pass of the
corrected paper, whose first pass used the short justification.)

## Section 5: Corollary 2 and Theorem 2

### N-17 (E) — p. 801: Meĭman's theorem as used — *referee-confirmed (R4, numerically)*
The text says: if `A` and `B` have interlacing zeros, then `A - iB` or `A + iB` is in
`\overline{HB}`. Interlacing plus exponential type is not sufficient: `A = cos πz` and
`B = e^{az} sin πz` with `a ≠ 0` have interlacing zeros, and on the imaginary axis
`|A ∓ iB|(iy)` vs `|A ∓ iB|(-iy)` compares `|cosh πy ± e^{iay} sinh πy|` with
`|cosh πy ∓ e^{iay} sinh πy|`, whose order changes with the sign of `cos(ay)`. For the specific `A`, `B`
of the proof the conclusion holds and is proved directly: the symmetric partial products are real
polynomials with interlacing zeros, for which `Im(B_R/A_R) > 0` on `ℂ₊` (sum of arguments of the
factors), and, after multiplication by real exponential factors `e^{β + c_R z}` (which preserve
`\overline{HB}`; the bare products need not converge, N-35), they converge locally uniformly;
`\overline{HB}` is closed under locally uniform limits (Hurwitz). No choice of sign (`P ↦ -P`) is
needed, and `A - iλB ∈ \overline{HB}` for every `λ > 0` (`isHB_genA_sub_lam_compB`).

### N-18 (G) — p. 800: "We may assume `ω' ≃ 1`" — *referee-confirmed (R4)*
`ω' = 1 + ψ' - φ_f'/π → 1` at infinity but may fail to be `≃ 1` on a compact set. Modifying `ω'`
there is harmless only if the modification `h` keeps `∫ h = 0` (the phase count) and cancels the
linear term `∫_{|t|>1} h(t)/t dt` that it adds to the potential (otherwise `|E|` is off by a factor
`e^{b Re z}`); see N-36.

### N-19 (G) — p. 801: the normal-family step — *referee-confirmed (R4)*
"A normal family argument shows that there exists a sequence `c_k ≃ 1` such that
`A_k(x) - c_k cos πx → 0`": the argument needs `U_ω - π Im z` bounded up to a linear term (which rests
on the unproved identity of N-36), the identification of the limits (Liouville applied to
`A_∞/sin π(z - θ)`), the translate `A(z + x_{2k})` (N-35), both `k → ±∞`, and a single global
integer offset in the phase at both ends; the final exponent has the wrong sign (N-35).

### N-20 (E) — p. 802: integration range in `log|f|` and (10) — *print-checked*
`log|f(z)| = ∑_n ∫_{r_{n-1}}^{r_n} (log|1 - z/z_n| + Re(z/t)) dψ(t)` gives the zero `z_n` the
`dψ`-mass `ψ(r_n) - ψ(r_{n-1})`. This is not an integer in general, so this is not `log|f|` for an
entire `f`. The integrals must run over `[t_{n-1}, t_n]`, whose mass is `1`. The same applies to
(10), and in the rewriting of `j_n` on p. 803; only the formula for `V_1` uses `[t_{n-1}, t_n]`.
*Referee-confirmed (R5).*

### N-21 (E) — pp. 804–805: the proof of Theorem 2 (ii) — *reconstructed; referee-confirmed (R5, with numerics)*
- **Typos.** "`φ_n(t) = ψ_n(t) - n - 1/2`" should read `ψ(t)`. "The assumption `φ_n'(t) = o(1/t)`"
  should be about `ψ'`. In the heuristic formula for `U_n`, `∫_0^{|x|}` diverges and should be
  `∫_1^{|x|}`.
- **`ε_n → 0` fails.** The equation `∫_{t_n}^{ξ_n} φ_n(x)/x dx = 0` does not give `ε_n → 0` in
  general. For `ψ = log log x` it gives `ε_n ≈ 0.37` (it reduces to `∫_{-1/2}^{ε} u e^u du = 0`). If
  `ψ` is linear in `log x` on the relevant range it gives `ψ(ξ_n) = n + 1`, contradicting
  `ξ_n < t_{n+1}/2`.
- **The estimates do not follow.** `U_n + ½ log x ≃ 1` fails (on `(t_n, ξ_n)` the slope is
  `ψ - n - 1`, not `-1/2`), and with the paper's heuristic formula one gets
  `U_n(ξ_n) ≈ -½ log ξ_n - ½ log t_n`. Then (11) does not follow, while (12) holds because of the mass
  near the origin.
- **The statement is true; a simpler proof.** The authors' idea (critical decay `|f|² ≈ 1/x` over a
  logarithmically long range) works with a different test function. Since `xψ' → 0`, there are
  arbitrarily long windows `[x₀, x₀e^s]` on which `|ψ - (n + 1/2)| ≤ η`, so `Λ` lies within `η` of
  `ℤ + 1/2` there. Take the [OS99] Lemma 3 function for the density `1 + μ`, where `μ` consists of two
  negative ramps of mass `-1/2` just before and after the window, normalised and shifted so that its
  zeros are `ℤ` on the left, `ℤ + 1/2` on the window and `ℤ` after. Then `f` vanishes on
  `Λ ∩ (-∞, 0] = ℤ_{≤0}`, and, with `L = a₂/a₁` the length ratio of the window `[a₁, a₂]`,
  `‖f‖² ≳ a₁ log(L/4)` while `∑_Λ |f|² ≲ a₁(1 + η² log L)`, so the ratio tends to `0` (blueprint M09;
  `pwNormSq_testFn_ge`, `sampleSum_testFn_le`, `Theorem2ii.lean`).
- The construction applies [OS99] Lemma 3 to a density that depends on the window, so it needs the
  constants of Lemma 3 to depend only on the bounds of the density (N-42).

### N-22 (G/D) — Theorem 2 (i) needs regularity of `ψ` beyond the stated hypotheses — *referee-confirmed (R1, R5); open whether (i) holds without it*
The proof of (i) uses "the smoothness of `ψ` ensures that `∑_{n(z)-1}^{n(z)+1} j_n(z) ≃ 1`"
(p. 802), and the introduction speaks of "`ψ` sufficiently regular" (p. 790), but the statement of
Theorem 2 only assumes `ψ' = 1/O(x)` and the logarithmically regular partition.
- **Counterexample to the construction** (M08 writer): cells with `d_n = √t_n` whose unit mass sits on
  a spike of length `ℓ_n = log t_n` satisfy all stated hypotheses (including `ψ' = o(1)`), but near
  the spike `j_n(x) ≈ log(ℓ_n/d_n) → -∞`, so `|U_ψ - log|f||` is unbounded for the paper's `f`.
  Two half-spikes at the ends of a cell defeat every choice of one zero per cell.
- **What the proof needs:** `ψ' ≤ K/d_n` on `[t_{n-1}, t_n]` (`DensBound`).
- **Formalization:** two main statements.
  - `theorem2_i_of_densityBound` assumes `IsLogRegularPartitionWithDensity` (the regular partition plus
    `ψ' ≤ K/d_n` on each cell; `Defs.lean`) and not `ψ' = 1/O(x)`.
  - `theorem2_i` keeps the printed hypotheses except `ψ' = 1/O(x)` (removed as unused, N-26, I-03) and
    adds `hmono` (`ψ'` eventually nonincreasing). This covers the paper's example `√x` and implies the
    density bound (`RegData.densBound_of_antitoneOn`).

  Both are proved through the internal lemma `theorem2_i_of_regular`. Whether (i) holds without such a
  regularity assumption is open.

### N-23 (E) — p. 804: the bound for `V_2` is false for nonreal `z` — *coordinator-checked; referee-confirmed (R5)*
"`|log|z - r_n| - log|z - z_n|| ≲ d_n²/|z - r_n|²`" fails off the real axis: for `z = i r_n` the
derivative of `θ ↦ log|z - r_n e^{-iθ}|` at `θ = 0` is `1/2`, so the difference is `≈ c d_n/(2 r_n)`,
of first order. The correct bound is `≲ d_n²/|z - r_n|² + d_n Im z/|z - r_n|²`; the extra terms sum
to at most a constant because `∑_n d_n y/|z - r_n|²` is a Riemann sum of a Poisson integral.

### N-24 (G) — p. 802: the window `n(z) - 1, …, n(z) + 1` — *referee-confirmed (R3–R5)*
When `d_n ≃ d_{n+1}` holds only with a constant `C > 1`, the cells within distance `≲ d_n` of `z` are
not confined to three indices; the window must depend on `C`. The far cells (`n > n⁺(z)`,
`n < n⁻(z)`) need the cancellation of the first and second order terms through (9), not a termwise
bound.

### N-25 (G) — Theorem 2 (i): `φ_f' → 0` is not checked — *referee-confirmed (R3–R5)*
Corollary 2 requires `φ_f'(x) = o(1)`; the proof of Theorem 2 (i) does not verify it for its `f`. It
holds: `φ_f'(x) = ∑_n |Im z_n|/|x - z_n|²` with `|Im z_n| ≃ d_n → ∞`. Also, the integrand of `U_ψ`
must be shown integrable (in Lean a non-integrable integral is `0`).

### N-26 (S) — Theorem 2 (i): the hypothesis `ψ' = 1/O(x)` — *referee-confirmed (R3–R5)*
The proof only uses `t_n ≤ (1 + C) t_{n-1}`, which already follows from `d_n ≃ d_{n+1}`. The
hypothesis is kept in the formal statement for faithfulness unless the linter forces its removal
(removing a hypothesis strengthens the theorem). *It did: removed from `theorem2_i` in I-03;
`theorem2_i_of_densityBound` never had it.*

### N-27 (S) — p. 790: Fourier frames and sampling — *tex-checked; referee-confirmed (R2)*
"By the Paley–Wiener theorem, `Λ` is sampling for PW if and only if `{e^{iλ_k x}}` is a Fourier frame":
the correspondence involves the reflection `t ↦ -t` (the frame uses `e^{-iλx}`, the Paley–Wiener
representation `e^{izt}`) and the factor `2π` between the norms. The frame bounds `(A, B)` correspond
to the sampling bounds `(A/2π, B/2π)`.

### N-28 (G) — p. 796: "`E` has no zeros on the real axis since `PW = H(E)`" — *referee-confirmed (R3–R5)*
True but needs an argument: if `E(x₀) = 0` and `f(x₀) ≠ 0` for some `f ∈ H(E)` (a translate of a PW
function), then `∫|f/E(x + iy)|² dx ≳ 1/y`, so `f/E ∉ H²`. Likewise Theorem E is applied without
noting that `E` must be in the strict class (`H(E) = PW ≠ {0}` rules out `E^* = cE`) and that
`φ_E + φ_F` is strictly increasing.

### N-29 (G) — p. 799: the "evident fact" — *referee-confirmed (R3–R5)*
"`H(E) = PW` if `|E(z)| ≃ e^{π Im z}` for `Im z ≥ 0`" is true but not evident: `H(E) ⊆ PW` needs a
Fatou argument for `L²(ℝ)` and a separate bound in the strip `|Im z| ≤ 1`.

### N-30 (T) — p. 798: the product `F` of the example — *tex-checked*
`F(z) = lim ∏_{|λ_k|<R}(1 - z/λ_k)` is undefined because `λ_0 = 0`; it should be `z ∏_{k ≠ 0}`.
"This sequence is sampling, because … sine-type" is really sine-type ⇒ complete interpolating ⇒
sampling. The formalization proves the needed estimate `|E(z)| ≃ e^{π Im z}` (the conjugate function
of `log|t|` is bounded, applied after the density smoothing of N-16) and replaces Levin's theorem by
Theorem E. No perturbation (Kadec/Avdonin) argument
is needed either: the density can be chosen with barycentres exactly `Λ + 1/2` (`LogExample.lean`). Its
potential has a nonzero linear drift (N-41).

### N-31 (G) — pp. 795–796: further gaps in the proof of necessity — *referee-confirmed (R3–R5)*
- "`M - 1` vanishes whenever `E^*` vanishes": this uses that the zeros of `E^*` lie in `ℂ₊`, i.e.
  that `E` has no real zeros, which the paper only states in the converse part, and a multiplicity
  argument. That `G(M - 1)` is entire is also tacit.
- "`F` has no zeros in `Im z > 0`" is not justified as written; it follows from
  `F = 2G/(E - E^*A)` on `ℂ₊`.
- `E(λ_k) ≠ 0` is needed for the isometry with `μ = ∑ |E(λ_k)|² δ_{λ_k}`.
- "PW with the sampling norm is a de Branges space" hides completeness, definiteness and the axioms
  (H1)–(H3); all hold.

### N-32 (G) — p. 796: removing the real zeros of `F` — *referee-confirmed (R3–R5)*
"`F = S F̃`, where `F̃ ∈ \overline{HB}` without real zeros and `S` is an entire function with real
zero set": `S` is not constructed. The real zeros of `F` lie in the separated set `Λ`, but their
multiplicities can be unbounded (e.g. `F` real entire with prescribed multiplicities), so a genus-one
product may not converge. A Weierstrass product of variable genus works. The formalization constructs
it (Mathlib has no Weierstrass factorization theorem) for any `F ∈ \overline{HB}`, `F ≢ 0`, with
`p_a = m(a) + rank(a) + 1`, where `rank` injects the real zero set into `ℕ`
(`Theorem1/Sufficiency/RealFactor/Product.lean`). This needs no separation. Because the zeros lie in
the separated `Λ`, `p_x ≥ m_x + |x|` would also do. The factorisation `F = SG` depends on `F` alone
(`exists_noRealZero_hb` does not use `E`). Also "If we prove that
`Λ₁` is a sampling sequence, then `Λ` is also": the upper bound for `Λ ⊋ Λ₁` needs the
Plancherel–Pólya inequality for the separated `Λ`.

### N-33 (G) — p. 796: the level sets are indexed by `ℤ` — *referee-confirmed (R3–R5)*
`Λ_α = {λ_{α,k}}_{k ∈ ℤ}` presupposes that `φ_{EF}` maps `ℝ` onto `ℝ`. This holds (e.g. since
`φ_E → ±∞`, which follows from Theorem E: a level set bounded on one side would contradict the norm
identity of Theorem E for far translates of a fixed `g ∈ PW`, by the Plancherel–Pólya tail bound;
`HEEqPW.phase_tendsto`), but it is not shown. "We may assume it fails for `α = π/2`" is unnecessary:
along `α_n = π/2 + π/(n+2)` at most one `α_n` is exceptional.

### N-34 (G) — Corollary 1 and the remark of p. 797 — *referee-confirmed with corrections (R3)*
- Pavlov's theorem requires `Γ` separated. The paper covers this on p. 791 ("It is plain that all
  complete interpolating sequences are separated"); the formalization proves it for `Γ_α` from
  Theorem E and the Bernstein bound.
- "If `Λ` is a complete interpolating sequence, then there exists `E ∈ \overline{HB}` such that
  `H(E) = PW` and `Λ` constitutes the zero sequence of `E + E^*`. This follows from Theorems C and
  E": the argument also needs that a complete interpolating sequence is sampling (taken for granted
  on p. 791; closed graph theorem, `Corollary1/ClosedGraph.lean`), Theorem D (orthogonality of the kernels at `Λ` forces `Λ` into
  one phase level set), completeness of the kernels, and a rotation `E ↦ e^{iθ}E`.

### N-35 (T) — p. 801: details of the construction in Corollary 2 — *print-checked; referee-confirmed (R4)*
- "two monomials `P` and `Q` of the same degree and with only real zeros": polynomials are meant
  (a monomial `z^n` has only the zero `0`).
- `A_k(z) = A(z - x_{2k})` looks at `A` near `-x_{2k}`; to compare with `cos πx` near `x_{2k}` the
  translate must be `A(z + x_{2k})` (zeros `γ_j - x_{2k} ≈ j - 2k + 1/2`). Only `k → +∞` is treated;
  `k → -∞` is analogous.
- "`E(x) = |E(x)| e^{i(π(x + ψ(x)) - φ_f(x) + o(1))}`": with the convention `E(x) = |E(x)| e^{-iφ(x)}`
  (p. 794) and (8), the exponent must be `-i(π(x + ψ(x)) - φ_f(x) + o(1))`.
- The symmetric products `lim ∏_{|γ_k|<R}(1 - z/γ_k)` need not converge for a general density
  `ω' ≃ 1`; the [OS99] function carries a factor `e^{-κz}` (as does `OCS.multF`), which is harmless
  after rescaling `B ↦ e^{κ/2}B`: the formal phase function is `E_κ = e^{-κz}(A - i e^{κ/2}B)`
  (`compEκ`, `Construction.lean`). Without the rescaling the modulus is right but the phase drifts,
  since `A` and `B = A(· - 1/2)P/Q` have amplitude ratio `e^{-κ/2}`; a first interface with a phase
  clause for every density `m → 1` was false (I-07).

### N-36 (G) — pp. 800–801: the proof of Corollary 2 — *referee-confirmed (R4)*
- **`|E(z)| ≃ e^{π Im z}`** is asserted ("and `|E(z)| ≃ e^{π Im z}` for `Im z ≥ 0`") but never derived.
  It rests on the identity `log|f(z)| = (1/π) ∫ log|1 - z/t| φ_f'(t) dt + b Re z + c` on `Im z ≥ 0`
  for `f ∈ \overline{HB}` with (7), which is not stated. With it, `|E| ≃ e^{U_ω} = e^{π Im z + U_ψ - log|f| + b Re z + O(1)}`,
  and the linear term `b Re z` must be cancelled when `ω'` is modified on a compact set.
- **"We may assume `ω'(x) ≃ 1`"** hides that modification: it must keep `∫ (ω' - ω'_{new}) = 0` and
  cancel the linear term, and it changes `Λ(ψ)` by finitely many points.
- **The normal-family step** needs `U_ω - π Im z` to be bounded (up to a linear term), which again
  rests on the identity above; and the limits of the translates must be identified (Liouville).
- **The perturbation argument** needs the zero set of `Ef + E^*f^*` to be separated (true: `φ_E'|E|²
  ≃ 1`), and the "elementary fact" concerns moving finitely many points to new distinct positions
  (removing points is not allowed: `ℤ ∖ {0}` is not sampling). It is proved by a normal-family
  argument.
- **The standing assumption `ψ(∞) - ψ(-∞) = ∞`** (p. 799) is not used by the proof of Corollary 2,
  whose conclusion holds for every nondecreasing `C¹` `ψ` with `ψ' → 0` (e.g. `ψ = 0`, `f = 1`,
  `Λ = ℤ`). `IsAdmissiblePsi` keeps it, for faithfulness (blueprint M07, Issues 9). The Lean proof of
  `corollary2` uses only `ψ ∈ C¹`, monotonicity and `ψ' → 0` from it (code-checked).

### N-37 (E) — p. 794: Theorem F as printed fails for non-strict `E` — *referee-confirmed (R3)*
Theorem F is stated for `E ∈ \overline{HB}`. For `E = 1` (in `\overline{HB}`), `H(E) = {0}`, so the
isometry condition holds for every measure `μ`, while the right-hand side `Re((1 + A)/(1 - A))` is
finite, which fails for any `μ` with infinite Poisson integral. de Branges' theorem is for the strict
class; the paper only applies it to `E` with `H(E) = PW`, which is strict (N-28). The formalized
`TheoremF` is restricted to the strict class without real zeros. Similarly, Theorem E is
meaningless (`φ' ≡ 0`) when `E^* = cE`.

### N-38 (S) — pp. 804–805: what `ψ' = o(1/x)` is used for — *referee-confirmed (R5)*
The reconstructed proof (N-21) uses `xψ'(x) → 0` only through the existence of arbitrarily long
logarithmic windows where `ψ` stays within `η` of a half-integer; this is implied by, not equivalent
to, `ψ' = o(1/x)`.

## Found during implementation (recorded after referee R8)

### N-39 (G) — p. 798, proof of Corollary 1 — *code-checked; R8; tex-checked*
"If `Λ` is a sampling sequence, then `Λ` consists of those points such that
`φ_{EF}(λ) = π/2 + kπ`" is false as printed when `F` has real zeros. Such a zero is a zero of
`EF + E^*F^*`, hence a point of `Λ`, but the phase condition does not describe it. The sentence must
read "contains", after the real zeros of `F` are removed as in the proof of Theorem 1 (N-32). With
`F = SG`, the zero set `Λ₁` of `EG + E^*G^*` consists of the points where `φ_{EG} ∈ π/2 + πℤ`,
`Λ₁ ⊆ Λ`, and only `Λ ⊇ Λ₁` is needed. The corrected paper (second pass) writes `F = S F̃` and
"contains". "`φ_E` is an increasing
function which grows more slowly than `φ_{EF}`" is to be read as "`φ_{EG} - φ_E = φ_G` is
nondecreasing" (`φ_G' ≥ 0`, N-13). Then each `[γ_k, γ_{k+1})` (consecutive points of the level set
`{φ_E ∈ α + πℤ}`) has a `φ_{EG}`-image of length `≥ π`, so it contains a point of
`{φ_{EG} ∈ π/2 + πℤ} ⊆ Λ` (`corollary1_strong`, `Corollary1.lean`; the enumeration of `Γ` is abstract, so only
`φ_E(γ_{k+1}) - φ_E(γ_k) ≥ π` is used).

### N-40 (D) — p. 794: the phase function — *tex-checked; R2-11, R8*
The paper writes `E(x) = |E(x)|e^{-iφ(x)}` with `φ` continuous "such that `E(x)e^{iφ(x)}` is real".
`IsPhaseFunction` requires `E(x)e^{iφ(x)} = |E(x)| ≥ 0` (`Defs.lean`). For `E` without real zeros the
two differ by a constant shift of `φ` by `π`; the level sets `{φ ∈ α + πℤ}` are the same, so `TheoremE`
(quantified over Lean phase functions) is implied by the paper's Theorem E. The uniqueness of Lean phase
functions modulo `2πℤ` is finer than the paper's.

### N-41 (G) — p. 798: the example's potential has a linear drift — *numerical; code-checked; R8*
The density of the example (barycentres `Λ + 1/2`, N-30) has potential
`U = π Im z + κ Re z + O(1)` on `Im z ≥ 0` with `κ = ∫_{|t|>1} (m(t) - 1)/t dt ≈ -1.352 ≠ 0`
(`logKappa`; numerical value from the blueprint M06). The linear term comes with the normalisation of
the potential (`Re(z/t)` kept for `|t| > 1`, N-03), and the paper does not mention it. It is absorbed by
`E_κ = e^{-κz}(A - i e^{κ/2}B)` (N-35), which still has `|E| ≃ e^{π Im z}` and zero set `{A = 0}`.

### N-42 (G) — [OS99] Lemma 3 with constants uniform in the density — *code-checked; R8*
The reconstructed proof of Theorem 2 (ii) (N-21) applies [OS99] Lemma 3 to a density that depends on the
window. It needs the constants of Lemma 3 (2) to depend only on the bounds `a ≤ m ≤ b`. This is true by
inspection of the proof, but not stated in [OS99]. Formalized as `lemma3_estimate_uniform`
(`Lemma3Uniform.lean`), by re-running the proof of the vendored `OCS.multF_estimate_two` with the
constant `K` of `OCS.exists_abs_sum_multErr_sub_log_infDist_le` fixed from `(a, b)`.

## Found in phase 2 (blueprint of de Branges' Theorems D and E, referee R9)

### N-43 (T) — p. 793: `dx` for `dt` in the norm of `H(E)` — *print-checked; tex-checked; R9*
The norm is printed `‖f‖²_E = ∫_{-∞}^{∞} |f(t)|²/|E(t)|² dx` (tex l. 307–309). The integration variable is
`t`, so `dx` should be `dt`. Harmless.

### N-44 (G) — p. 794, Theorem E: `Γ` indexed by `k ∈ ℤ` — *print-checked; R9*
"let `Γ = {γ_k}` be the sequence of real numbers such that `φ(γ_k) = α + kπ`, `k ∈ ℤ`" presupposes that
the phase function `φ` maps `ℝ` onto `ℝ`. For a strict `E` without real zeros, `φ` is strictly
increasing, but its range is an open interval that may be bounded. For `E(z) = z + i` (`H(E)` = the
constants), `φ(x) = -arg(x + i) ∈ (-π, 0)`: then `Γ = {0}` for `α = -π/2`, and `Γ = ∅` for `α = 0`
(where `E - E^* = 2i ∈ H(E)`, so the theorem does not apply). In general `Γ` can be finite, one-sided or
empty. The formal `TheoremE` sums over the set `Γ = phaseLevel φ α = {x : φ(x) ∈ α + πℤ}`, which is the
paper's statement when `φ` is onto; `theoremE_holds` proves it in general. In the paper's application
(`H(E) = PW`) `φ` is onto, so nothing is affected. N-33 is the same presupposition at the point of use
(p. 796), where the formalization proves that `φ` is onto (`HEEqPW.phase_tendsto`).

### N-45 (G) — p. 793, formula (1) at `z = ζ̄` — *print-checked; R9*
"The kernel has the following representation, which also defines it for real `ζ`": formula (1),
`K_E(ζ, z) = (i/2)(E(z)conj E(ζ) - E^*(z)conj E^*(ζ))/(π(z - ζ̄))`, is `0/0` at `z = ζ̄` for every `ζ`,
real or not, since `E^*(ζ̄) = conj E(ζ)`. The value there is the limit, which (2) uses for real `ζ = x`
(`K_E(x, x) = φ'(x)|E(x)|²/π`). `deBrangesKernel` (`Defs.lean`) takes the derivative form at `z = ζ̄`,
and `deBrangesKernel_eq_dslope` (`Cited/DeBrangesDE/Kernel.lean`) shows that this is the entire
extension of (1). Harmless.

---

## Implementation log

(I-entries: divergences decided during implementation, removed or changed helper statements, and
anything an implementer had to do differently from the blueprint.)

### I-01 — statement changes after the review round (2026-11-06)
Made by the coordinator at the referees' request, after the reviews and before the freeze tag
`scaffold-reviewed`; not themselves re-reviewed:
- **`theorem2_i_of_densityBound`** (new main statement, R1, R5): Theorem 2 (i) under the hypothesis
  the proof uses, `IsLogRegularPartitionWithDensity` (new definition in `Defs.lean`: the
  logarithmically regular partition together with `ψ' ≤ K/d_n` on each cell), without the
  hypothesis `ψ'(x) = 1/O(x)`, which the proof does not use (N-26). `theorem2_i` (with
  `ψ'` eventually nonincreasing) is kept.
- **`landau_sharp`** (R1, R4): strengthened from "the logarithmic term cannot be removed" to "no
  coefficient `A < 1` of `log⁺(b - a)` works".
- **`plancherelPolya_tail_union`** (R2): new helper, the tail bound for a union of two
  `δ`-separated sets, which Theorem 1 sufficiency uses.
- `Suff.SepBy` (a duplicate of `IsSepBy`) removed from `Theorem1/Sufficiency.lean`.

### I-02 — unused hypotheses in main statements
`theorem2_i` has the hypothesis `hlow` (`ψ'(x) ≥ c/x`) and `theorem2_ii` has `hPW`; neither is
used by the proofs. They are kept for faithfulness during implementation; the linter warnings are
resolved at the end by a deliberate, recorded statement change (removing a hypothesis strengthens
the theorem), not by suppression. *Carried out in I-03 (2026-11-07): both hypotheses
removed.*

### I-03 — lint pass: unused hypotheses removed (2026-11-07)
Final lint pass on master: `lake build` now has no warning other than `declaration uses 'sorry'`
in `FourierFrames/Cited/`. Every unused hypothesis was removed from its statement (this
strengthens the lemma) and all call sites updated; no `set_option`, `_`-prefixed binder or dummy
`have _ := h` remains (the earlier `have _ := h` lines and `_h…` binders were removed with their
hypotheses). Where the dropped hypothesis was the only binder fixing an implicit variable, that
variable became explicit (noted "explicit `x`" below). Changes recorded in `APPROVED` of
`scripts/check_statements.py` for the declarations frozen at `scaffold-reviewed`.

**Main statements** (`comparator/statements.lean`, re-checked by comparator):
- `theorem2_i`: `hlow` (`ψ'(x) ≥ c/x` for large `x`, the printed `ψ' = 1/O(x)`, cf. N-26)
  removed; `theorem2_i` no longer assumes it (it keeps `hmono`, N-22).
- `theorem2_ii`: `hPW` removed; `theorem2_ii` is now unconditional (no cited hypothesis).

**Helpers** (declaration: hypothesis removed):
- HB: `memPW_of_memHE`: `hPW`; `HEEqPW.phaseDeriv_mul_sq_ge`: `hPW` (the upper bound `_le`
  keeps it).
- Theorem 1, sufficiency (cascade from `phaseDeriv_mul_sq_ge`): `Suff.levelSet_ineq_aux`,
  `Suff.levelSet_data_aux`, `Suff.levelSet_cis_aux`, `Suff.translate_lower_bound_aux`,
  `HEEqPW.levelSet_ineq`, `HEEqPW.levelSet_cis`: `hPW` (`levelSet_separated(_aux)`,
  `phase_tendsto(_aux)` still use it); `Suff.exists_noRealZero_hb`: `hEHB`.
- Theorem 1, necessity: `sampInner_self`: `hf` and the section variable `hs`;
  `sampInner_conj_symm`, `sampInner_smul_left`: `hf`, `hg`, `hs` (these three now precede
  `section Sampling`, with explicit `Λ f g`); `samp_H1`: `hs` (`omit hs in`); `samp_H3`: `hf`,
  `hs` (`omit hs in`); `summable_norm_herglotz`: `hz` (explicit `z`); `entSum_eq`: `hΛ`, `hcs`;
  `herglotzEnt_eq`: `hΛ`, `hcs` (cascade). Also `sampCore` became an `abbrev` (a `def` of class
  type must be reducible), replacing `set_option warn.classDefReducibility false`.
- Landau: `osc_bound_of_JN`: `hD` (`0 ≤ D`).
- Example: `integrable_log_mul_sub_one`: `hz` (explicit `z`).
- Corollary 2: `multU_const_mul`: `hg`, `hM` (explicit `g`); `isSampling_of_replace_finite`:
  `hsep'` (separation of the new set `Γ'`).
- Construction: `compB_eq_zero_iff`, `compB_mul_Q`: `hN`, and by cascade `tendsto_polyB`,
  `range_compBeta_eq`, `tendsto_compB_translate`, `tendsto_compEκ_translate` (explicit `N` in
  these six), `phase_rigidity`, `phase_asymptotics`: `hN`.
- Theorem 2 (i): `RegData.hasSum_UPsi`: `hz` (explicit `z`); `RegData.abs_cellTerm_below`,
  `RegData.abs_cellTerm_above`, `D1.abs_cellTerm_above`: `hz` (`0 ≤ z.im`); `D1.zPt_re_im`: `h`,
  `hn` (explicit `n`); `D2.integrableOn_log_abs_sub`: `hab` (explicit `a b`);
  `D2.deficit_integrable`: `hd` (explicit `d`). `Theorem2i/NearAux.lean` imports
  `FourierFrames.Defs` instead of all of `Mathlib`.
- Cited (John–Nirenberg): `volume_dyadic`: `hab` (explicit `a b`).

### I-04 — no real-valued `tsum`/`ncard` statements on the main path (M08)
A real `tsum` is `0` for a non-summable family, and `ncard` is `0` for an infinite set. So
`RegData.card_near_le`, `RegData.sum_far_le`, `RegData.sum_far_im_le` (`Theorem2i/Estimates.lean`) and
`RegData.exists_bound_cellTerm` (`Theorem2i/Assembly.lean`), as scaffolded, hold trivially in the
degenerate case. The proof of Theorem 2 (i) uses uniform finset forms instead
(`RegData.finset_card_near_le`, `RegData.finset_sum_far_le` in `Counting.lean`, `RegData.finset_sum_far_im_le`
in `Riemann.lean`, combined in `D3.exists_finset_bound`, `Assembly.lean`). The `tsum` forms are proved
corollaries and are used by nothing (R8 F-10). Design rule since then: no real `tsum` or `ncard` in a
helper statement on the main path (blueprint README §3.15).

### I-05 — how `rampPot_estimate` parses (M09)
In `|(1/a) * ∫ t in a..2*a, log ‖1 - x/t‖ - log (max 1 (|x|/a))| ≤ 4` the binder of `∫` extends over
`- log (max …)`, so the statement is `|(1/a) ∫_a^{2a} (log|1 - x/t| - ℓ)| ≤ 4`. Since the interval has
length `a`, this equals the intended `|(1/a) ∫_a^{2a} log|1 - x/t| - ℓ|`; the proof treats both
(`T2ii.rampPot_estimate'` is the parenthesised form, `Theorem2ii/Ramp.lean`). Harmless; noted because the
frozen statement reads differently from the blueprint formula.

### I-06 — proof routes different from the blueprint
The implemented route, where it differs from the blueprint text (details in `blueprint/impl_notes/*.md`
and the "*Implemented:*" lines of the module documents):
- `φ' ≥ 0` and `φ' > 0`: the Hopf dichotomy `IsHB.phaseDeriv_pos_or_eventuallyEq` (`HB/Hopf.lean`), N-13.
- `exists_isPhaseFunction`: `E e^{iΦ - R}` has derivative `0`; `|E|` is never differentiated.
- `exists_realFactor`: genus `m(a) + rank(a) + 1`, bound from the tail of the log series, abstract
  locally uniform products (`RealFactor/LUProd.lean`), N-32.
- `levelSet_limit`: one application of `plancherelPolya_tail_union`, constant `C₀(T + 2η)`.
- `HEEqPW.phase_tendsto`: translates of a fixed `g ∈ PW` and the tail bound, no `ℤ`-indexing (N-33).
- Complete interpolating ⇒ sampling: closed graph theorem (`Corollary1/ClosedGraph.lean`).
- `log_norm_eq_multU_add_affine`: Schwarz reflection of `e^{iφ(0)} f e^{-P}` and Borel–Carathéodory
  (`Corollary2/{Reflection,Affine,LogNorm}.lean`); `multU_one` is a corollary of it.
- `continuous_multU_of_bdd`: Vitali's theorem, since `g` is only measurable (`Corollary2/UCont.lean`).
- `norm_compB_comparable`: `expU_bounds_on_compact` (compactness lemma of `Construction/Comparable.lean`),
  no continuity of `U`.
- Polynomial Hermite–Biehler step: monotone arguments (`Construction/PolyHB.lean`), not partial fractions.
- `phase_rigidity`: the abstract `Rigidity.phase_drift_small`.
- `not_memHE_sAlpha`: a lower bound for `∫ cos² φ` (`LogExample/Phase.lean`) instead of disjoint intervals.
- The potential estimates of M06 §4: integration by parts with real primitives and Young's inequality
  (`LogExample/Potential.lean`).
- `multUIntegrand_one`: shift to `x = 0`, then an explicit antiderivative (`Theorem2ii/UOne.lean`).
- `rampPot_estimate`: rescaling to `∫_1^2` and a split at `|ξ| = 3` (`Theorem2ii/Ramp.lean`).

### I-07 — the construction interface (M07)
The first interface `exists_hb_of_density`, with a phase clause for every density `m → 1`, was false
(for the example's density `κ ≈ -1.35 ≠ 0`, N-41). Before implementation it was replaced by
`exists_hb_of_density` (no phase clause, hypothesis `hshift`) and `exists_hb_of_density_phase` (drifted
hypothesis `hU`), with `E_κ = e^{-κz}(A - i e^{κ/2}B)` (`compEκ`). A first generalisation
`e^{-κz}·(A - iB)` was also false (wrong phase, N-35). The proof confirms that `λ e^{-κ/2} = 1` is exactly
what makes the translates `E_κ(z + s_k)` converge to `i c e^{-iπ(z - θ)}` (`impl_notes/construction.md`;
`IMPORTS.md`, "Suspected false statements").

### I-08 — duplications and unused lemmas
- The frozen definitions `argUp`, `potC` are copied as `argUp'`, `potC'` in `Corollary2/PotC.lean`
  (transfer by `rfl`).
- `U_1 = π|Im z|` is proved three times (`multU_model` in `LogExample.lean`, `multU_one` in
  `Corollary2.lean`, and in `Theorem2ii/UOne.lean`).
- The sub-mean-value inequality is proved twice (`enorm_sq_le_lintegral_ball`,
  `PW/PlancherelPolya.lean`; `enorm_sq_le_setLIntegral_ball`, `HB/H2.lean`).
- Proved but unused: `l2piSq_eq_of_pwFT_eq` with its helpers `pwFT_sub`, `tsum_enorm_sq_pwFT_int`,
  `fourierCoeffOn_pwFT` (`PW/Basic.lean`; the obsolete route of M01 §1.7), `MemPW.isH2Upper_mul_exp` with
  `MemPW.lintegral_mul_exp_le` (`PW/Bounds.lean`), and the `tsum` forms of I-04.

### I-09 — phase 2: implementation of P1 and P2 (2026-11-07)
- **P1** (`paleyWiener_holds`, proved; `blueprint/P1_PaleyWiener.md`, `impl_notes/cited-p1.md`,
  referee R6): `F2_symm_ae_eq` (true, but only a step towards `F2_symm_toLp_ae_eq`) was removed; both
  `L¹ ∩ L²` agreement lemmas are proved by pairing with Schwartz functions through Mathlib's
  `Lp.fourier_toTemperedDistribution_eq` and `Lp.fourierInv_toTemperedDistribution_eq`. The unused
  hypothesis `ha : 0 ≤ a` was dropped from `integral_exp_abs_sub_sq_le` and `norm_integral_gauss_mul_le`
  (true for every real `a`). These are phase-2 scaffold statements, not covered by the freeze.
- **P2** (`dsPerturbation_of_paleyWiener`, `johnNirenberg_holds`, proved; `impl_notes/cited-p2.md`,
  referee R7): `enorm_sq_sub_le` lost its unused `hPW`; `volume_dyadic` lost `hab` (I-03).
- **Root imports.** `FourierFrames.lean` imports `Cited/DeBrangesFC.lean`, whose `theoremC_holds`,
  `theoremF_holds` and temporary stub `theoremD_holds` are `sorry`-backed (R8 F-4); `#print axioms` shows
  `sorryAx` for them. The stub has the same name as P3's `theoremD_holds` (`Cited/DeBrangesDE.lean`, not
  imported by the root), and must be deleted when P3 is merged (R8 F-5, R7 finding 8). None of this
  affects the 15 main theorems, which take the cited results as hypotheses. *Superseded in I-10: the
  root no longer imports `Cited/DeBrangesFC.lean`; and in I-11: the stub is deleted, Theorem C is
  proved, and the root imports `Cited/DeBrangesFC.lean` again.*

### I-10 — phase 2: de Branges' Theorems D and E proved; `Unconditional.lean` (2026-11-07)
- **P3** (`theoremD_holds`, `theoremE_holds`, proved; `blueprint/P3_DeBrangesDE.md`, implementers' notes
  `impl_notes/cited-p3d.md` and `cited-p3e.md`, referee R9 on the blueprint and scaffold: no false statement,
  0 critical, 0 major, 8 minor). Implemented in two parallel worktrees: Theorem D (`Cauchy`, `Kernel`, helper
  `CauchyAux/Basic`) and Theorem E (`Space`, `EntireHerglotz`, `Orthogonal`, `Complete`, helper
  `EAux/KernelSymm`); 3726 lines in 9 files against an estimate of 4.3–6.2k. Both depend only on `propext`,
  `Classical.choice` and `Quot.sound` and use no cited `Prop`. Theorem D goes through a half-plane
  Cauchy–Goursat theorem for `H²` functions continuous up to `ℝ`, without boundary values. Theorem E is
  not proved by de Branges' route through his Theorems 20–21 (P3 "Issues in the source" 5). The proof is
  elementary: the reproducing kernel `Q` of the orthogonal complement of `{K_γ}` satisfies
  `Q(w,z)π(z - w̄) = S(z)conj S(w)(h(z) - conj h(w))` with `h` entire, real on `ℝ` and `Im h ≥ 0` on `ℂ₊`.
  So `h = pz + q`, and `p = 0` unless `S_α ∈ H(E)`.
- **Changed statements** (unused hypotheses removed; phase-2 scaffold statements, not covered by the
  freeze; no statement was false): `conj_deBrangesKernel`, `fstar_deBrangesKernel` (`hE`, R9 F7; `E` now
  explicit); `IsH2Cont.exists_side_seq` (`hY`); `IsH2Cont.tendsto_integral_line_of_dominated` (`hc`);
  `heInner_self` (`h0`); `fstar_dFun`, `defectKer_diag` (`D : DBData E φ`).
- **Routes different from the blueprint** (the "*Implemented:*" notes of P3): the vertical sides of the
  contour shift are bounded in `ℝ≥0∞` (R9 F1); `im_hFun_nonneg` needs only `Re Q(w,w) ≥ 0` (R9 F2); one
  AM–GM lemma `le_of_dom` serves all domination estimates; the upper and lower reproducing formulas share
  `heInner_kernel_eq_of_ae`, which P4 can reuse; `heNormSq_partialSum` comes from `heInner_partialSum`,
  without the double sum. The deprecated `if_pos`/`if_neg` are replaced by `ite_eq_left`/`ite_eq_right`
  (R9 F8).
- **Duplication.** Theorem E was written against the scaffold signature of `conj_deBrangesKernel`, which the
  Theorem D branch changed, so it uses an identical copy, `deBrangesKernel_conj_symm`
  (`Cited/DeBrangesDE/EAux/KernelSymm.lean`).
- **Root imports.** `FourierFrames.lean` imports only sorry-free modules, now including
  `Cited/DeBrangesDE.lean` and `Unconditional.lean`. The P4 scaffold `Cited/DeBrangesFC.lean` moved to the
  separate Lake target `FourierFramesScaffold` (`lake build FourierFramesScaffold`). It is the only file with
  `sorry`, and it still declares the temporary stub `theoremD_holds` (`sorry`). That stub no longer clashes
  with P3's theorem, since no module imports both. P4 is to replace it by
  `import FourierFrames.Cited.DeBrangesDE` (R7 finding 8, R9 F4). Theorem C is being revised along the route
  through Theorem D (R7 finding 7); Theorem F is deferred. *Done in I-11.*
- **`Unconditional.lean`** supplies `paleyWiener_holds`, `theoremD_holds`, `theoremE_holds`,
  `johnNirenberg_holds` and `dsPerturbation_holds` (new, `:= dsPerturbation_of_paleyWiener
  paleyWiener_holds`). Unconditional: `isFourierFrame_iff_isSampling_unconditional`,
  `heEqPW_of_comparable_unconditional`, `theorem1_sufficiency_unconditional`,
  `logExample_isCompleteInterpolating_unconditional`, `landau_sharp_unconditional`,
  `corollary2_unconditional`, `theorem2_i_unconditional`, `theorem2_i_of_densityBound_unconditional`.
  Conditional on the unproved cited results only: `completeInterpolating_zero_set_of_theoremC` (C);
  `theorem1_necessity_of_theoremCF`, `theorem1_of_theoremCF`, `corollary1_of_theoremCF` (C, F);
  `landau_inequality_of_theoremCF_pavlov` (C, F, Pavlov's A).
- **Comparator.** `comparator/statements.lean` lists 33 theorems: the 15 main statements, the five
  proved cited results (`paleyWiener_holds`, `johnNirenberg_holds`, `theoremD_holds`, `theoremE_holds`,
  `dsPerturbation_holds`) and the 13 versions above. `lake comparator` accepts them (2026-11-07,
  `comparator/last_run.log`); `lake build` has no warning.
- **Notebook.** N-43–N-45 record the issues in the source found by the P3 blueprint (items 1, 2, 4 of its
  list). Items 3 and 6 are covered by N-02, N-28 and N-37, and item 5 is this entry.
- **Tooling.** `scripts/make_imports.py` has no row for `Unconditional.lean` and stops with
  `KeyError: 'Unconditional'`, so the generated part of `blueprint/IMPORTS.md` predates the P3 merge.
  *Fixed right after this entry (commit 65da4ff); see I-11.*

### I-11 — phase 2: de Branges' Theorem C proved; Part F split off (2026-11-07)
- **P4-C** (`theoremC_holds`, proved; `blueprint/P4_DeBrangesFC.md`, implementer's notes
  `impl_notes/cited-p4.md`, referee R10 on the blueprint and scaffold: no false Part C statement,
  0 critical, 0 major, 5 minor). The proof goes through Theorem D (R7 finding 7). The kernel of `H` is
  built from (H1)–(H3), with the explicit strict `E = √π (z+i) K(i,z)/√K(i,i)` and
  `ι(k_w) = K_E(w,·)`. Then RKHS uniqueness, without completeness of `H(E)`: Fatou along a sequence
  from the span of the kernels, and Riesz in `H`. This `E` can have real zeros (e.g. for
  `{f ∈ PW : f(0) = 0}`). `f/E` is extended across them with Mathlib's meromorphic normal form
  (`divExt`), so P3's kernel layer is used unchanged. The proof has 1046 lines in 4 files
  (`Cited/DeBrangesFC.lean`, `DeBrangesFC/{Analytic,Space,Kernel}.lean`), against an estimate of
  1.6–2.5k; standard axioms only. The stub `theoremD_holds` is deleted and P3 is imported
  (R7 finding 8, R9 F4).
- **Changed statements** (phase-2 scaffold statements, not covered by the freeze; no Part C statement
  was false). `[CompleteSpace H]` is no longer a section variable of Part C: it was unused in most
  lemmas and was being auto-included. It is an explicit instance argument only of `exists_kernel`,
  `kernelSpan_topologicalClosure`, `exists_seq_kernelSpan`, `memHE_iota`, `heNormSq_iota` and
  `mem_range_of_memHE`, the six declarations that use Riesz or the orthogonal complement. `TheoremC`
  and the assembly are unchanged.
- **Part F split off.** `theoremF_holds` and the Part F lemmas moved to `Cited/DeBrangesFC/PartF.lean`.
  This file is built only by `FourierFramesScaffold`, and it is now the only file with `sorry`.
  `Cited/DeBrangesFC.lean` (Theorem C) is in the default target and is imported by the root and by
  `Unconditional.lean`.
- **`division_lemma` (F.8) is false as stated** (R10 finding 1, with a Lean disproof). It is a helper
  statement of the deferred Part F scaffold, not a statement of the paper or of de Branges, so it has
  no N-entry. Its hypothesis `Θ = e^{i(az+θ)}B` holds for every real `a`. Counterexample: `E = e^{-iz/2}`,
  `a = θ = 0`, `B = Θ = e^{iz}`, `Ξ ≡ 1/2`. Repair: add `0 ≤ a`, `‖B‖ ≤ 1` on `ℂ₊` and the
  Blaschke-division clause of `inner_factorization` as hypotheses (P4 §2, F.8). The scaffold marks it
  `-- FALSE` and keeps the `sorry`.
- **`Unconditional.lean`** supplies `theoremC_holds` as well. New theorems:
  `completeInterpolating_zero_set_unconditional`; `theorem1_necessity_of_theoremF`,
  `theorem1_of_theoremF`, `corollary1_of_theoremF` (F); `landau_inequality_of_theoremF_pavlov` (F, A).
  The `*_of_theoremC*` versions are kept. The only cited hypotheses left in the project are `TheoremF`
  and `PavlovBMO`.
- **Comparator.** `comparator/statements.lean` lists 39 theorems: the 15 main statements, the six
  proved cited results (now with `theoremC_holds`) and 18 versions with them discharged. `lake comparator`
  accepts them (2026-11-07, `comparator/last_run.log`). `lake build` (default target, now including
  `Cited.DeBrangesFC`) has no warning.
- **Notebook.** The second pass of the corrected paper refined N-39 ("contains" in the proof of
  Corollary 1) and N-16, N-30 (density smoothing in the sine-type estimate). There is no new N-entry.
- **Tooling.** The generated part of `blueprint/IMPORTS.md` is regenerated after the P4 merge. The
  title of its P4 row, "de Branges C, F (scaffold)", is hard-coded in `scripts/make_imports.py`.

### I-12 — de Branges' Theorem F proved by normalized kernels (2026-11-07)

- **Theorem F is proved.** `FF.theoremF_holds : TheoremF` supplies the exact unchanged
  statement in `Defs.lean`, with the allowed coefficient `p = 0`. The proof is in
  `Cited/DeBrangesF.lean` and 14 supporting files, 2349 lines altogether. Its axiom
  audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- **Simpler proof route.** Normalize the measure by the squared kernel at `i`, obtaining
  a probability measure. The upper and reflected reproducing kernels give the two
  Cauchy-transform identities `F - φH = 1` and `J - c = φF`. Cauchy–Schwarz gives
  `|φH| ≤ |φF|`. The numerator of `φ` is a nonzero entire function, so continuity and
  the identity theorem extend `|H| ≤ |F|` through its zeros. An inverse disk
  automorphism produces the holomorphic contractive parameter, and an explicit
  change of measure gives the original Poisson integral. All complex integrals
  used in the calculation have explicit integrability proofs.
- **Retired scaffold.** The previous route required inner-function factorization,
  Blaschke division, decay estimates, and derivative kernels. None is needed.
  Its false `division_lemma` is removed, rather than assumed or repaired as a
  dependency. `Cited/DeBrangesFC/PartF.lean` and the `FourierFramesScaffold` Lake
  target are retained as import-only compatibility entry points. There are no
  remaining `sorry` proofs in the implementation.
- **Blueprint and independent review.** The detailed proof is in
  `blueprint/P4F_Elementary.md`, with exact Lean statements and dependencies in
  `blueprint/P4F_Statements.md`. `reviews/R11_TheoremF.md` independently checks the
  mathematical proof and the normalization/Cauchy helper plans;
  `reviews/R12_TheoremF_Code.md` checks the resulting implementation and unchanged
  theorem statement. Implementation deviations are recorded under
  `blueprint/impl_notes/theorem-f-*.md`.
- **Discharging the hypothesis.** Added `theorem1_necessity_unconditional`,
  `theorem1_unconditional`, `corollary1_unconditional`, and
  `landau_inequality_of_pavlov`. The last retains only `PavlovBMO`; all older
  forms are kept for compatibility. The frozen statements are unchanged.
  `FFChallenge.lean` and `comparator/config.json` are regenerated with 44
  declarations, including Theorem F and the four new versions.
- **Source corrections.** This is a new proof of a theorem cited by the paper,
  not a change to the paper's own statements. N-37 (strict Hermite–Biehler is
  necessary in Theorem F) remains valid. No additional paper erratum was found,
  so the corrected paper (uploaded to arXiv) needs no new change.
- **Validation.** `lake build FourierFrames FourierFramesScaffold` passes without warnings;
  both statement checkers pass. All five new theorems have only the three standard
  axioms. Comparator accepts all 44 declarations (2026-11-07,
  `comparator/last_run.log`). The initial outer-sandbox run could not create
  bubblewrap's network namespace; rerunning the unchanged comparator command
  outside that outer sandbox succeeded with comparator's own sandbox intact.

### I-13 — Pavlov's BMO necessity theorem proved (2026-11-07)

- **Exact scope.** `FF.pavlovBMO_holds : PavlovBMO` proves the unchanged necessity
  statement used in the paper: a separated complete interpolating sequence has
  `countFn Γ - id ∈ BMO`. This is the BMO consequence of Theorem A, not its full
  Helson–Szegő characterization. `landau_inequality_unconditional` now supplies
  this result and Theorem F, so every formalized main result has a version with
  all cited hypotheses discharged. Earlier conditional versions remain as API
  compatibility statements.
- **External infrastructure.** The earlier infeasibility assessment considered
  the installed Mathlib alone. On the user's suggestion, Tau Ceti was checked.
  Forty-one modules from its `v4.35.0` tag, immutable commit
  `1f9b4414105d86e487a4ac4c3d3397076a44d0d2`, are vendored unchanged (8882 lines),
  with Apache-2.0 headers, license and full provenance in `TauCeti/VENDORED.md`.
  They supply Fourier multipliers, harmonic/Dirichlet/Harnack machinery, and
  holomorphic logarithms. Their original implicit-variable language options
  are scoped to the TauCeti library; the project's options remain unchanged.
  Source comparison confirms all vendored Lean files match upstream byte for
  byte. The version compiles against this project's existing Mathlib pin.
- **Cardinal route to A₂.** Reuse the proved de Branges representation of a
  complete interpolating sequence. The cardinal functions are normalized
  removable quotients of the real generator `G`; their exact sample values
  give uniform norm and finite synthesis bounds. Sampling supplies bounded
  gaps. Harnack estimates on zero-free cell neighborhoods compare shifted
  generator values with derivative weights. Finite Cauchy-matrix tests give
  discrete A₂; a finite-cell cover transfers it to the continuous shifted
  weight. This avoids canonical product construction and the continuous
  weighted Hilbert-transform theorem.
- **Elementary BMO simplification.** For an A₂ weight, normalize by its interval
  arithmetic mean and use `|log s| ≤ s + s⁻¹`. This gives log-weight mean
  oscillation at most `2(1+C)` without Jensen. Logarithmic distance to a
  bounded-gap separated grid is BMO; the cell estimates then give BMO of
  `log|G|` on the real line. The same chosen height is used for the shifted
  weight and the logarithmic cell comparison; unrelated existential heights
  are never identified.
- **Regularized conjugate Poisson route.** Define the L² multiplier
  `-i sign ξ exp(-2πy|ξ|)`. Its inverse Fourier transform is
  `t/(π(t²+y²))`, and its L² convolution realization is proved for all L²
  inputs. John–Nirenberg supplies local square oscillation, dyadic mean
  growth controls the tails, and a near/far decomposition gives a BMO bound
  uniform in `y > 0`. The tail constant in the draft was corrected from
  `28/π` to `40/π` during independent review. No principal-value operator is
  needed. Pairwise oscillation and Fatou pass the uniform bound to an a.e.
  boundary limit without assuming convergence of interval means.
- **Logarithmic dispersion.** The normalized cardinal `exp(iπz)q(z)` is bounded
  and zero-free in the upper half-plane. Compact continuous logarithmic
  cutoffs and a squared-modulus maximum principle give Poisson domination.
  Exact Poisson extension of `log|t-a|` cancels each finite-order real zero;
  odd harmonic reflection and the existing entire-Pick theorem classify the
  defect as `a Im z`, `a ≥ 0`. The outer comparison lies in H² by the
  exponential tangent inequality and Tonelli. If `a > 0`, multiplying the
  real cardinal by a small-frequency sine gives a nonzero PW function
  vanishing on the whole sequence, contradicting interpolation uniqueness.
  Thus `a = 0`, without general Hardy factorization or a type-lowering premise.
- **Counting phase.** A holomorphic logarithm has constant boundary argument
  on each gap and drops by π across each simple real zero. Integer midpoint
  recurrence identifies its boundary value with `-π countFn Γ + constant`.
  The Schwarz identity therefore identifies the conjugate-Poisson limit with
  `-π(countFn Γ - id) + constant`, yielding the exact target BMO statement.
- **Implementation and review.** The proof occupies 6761 lines in 37 files,
  including `Cited/Pavlov.lean`. The detailed module blueprints are `P5_*.md`,
  with all 339 public interfaces and imports in `blueprint/P5_Statements.md`.
  R13 records independent blueprint reviews; R14 and R15 independently audit
  the code and the analytic dispersion route. There are no new axioms,
  implementation `sorry`s, or linter suppressions.
- **Paper artifacts.** This completes another theorem quoted by the paper; it
  introduces no new correction to the paper's own statements. The corrected paper
  (uploaded to arXiv) remains applicable.
- **Validation.** The default and compatibility Lake targets build without
  warnings. The frozen-statement and main-statement checks pass; the
  self-contained challenge now contains 46 declarations. Comparator accepts
  all 46 (2026-11-07, `comparator/last_run.log`). Theorem F, PavlovBMO and the
  unconditional Theorem 1, Corollary 1 and Landau theorem have only the three
  standard axioms.
- **Statement-checker correction.** The checker previously indexed moved
  declarations by short name and kept only the first candidate. The new
  `FF.Pavlov.cell` therefore shadowed the unchanged, moved `FF.cell` from
  Theorem 2(i), producing a false change report. It now checks every exact
  candidate for a moved name, while still preferring the original file.
  No new exception was added. A focused regression check verifies that this
  collision passes and a genuinely changed statement is still rejected.
- **Metadata schema.** `formalization.yaml` validates against the published
  v0.4 JSON schema. The earlier string-only literature dependency lists were
  converted to the schema's statement/source objects, and the source
  relationship for the adapted multiplier lemma uses the allowed `adapts`
  value. These are metadata corrections, not mathematical statement changes.
