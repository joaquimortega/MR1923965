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
(confirmed by an independent review agent), *open* (not yet settled).

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
  interpolation part of the conclusion fails.
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

### N-05 (T) — p. 796, display after (5): missing square — *print-checked*
The middle term reads `sup_{f ∈ H(E), ‖f‖²_E ≤ 1} |f(x)|`. It should be `|f(x)|²`, as on the left;
`K_E(x,x)` is the supremum of `|f(x)|²`.

### N-06 (S) — Formula (2) and Theorem D are not needed for Theorem 1 — *open*
The bound `φ_E'(x)|E(x)|² ≃ 1` when `H(E) = PW` (p. 796) is derived in the paper from (2), i.e.
from Theorem D. It also follows from Theorem E alone:
- the norm identity at the level set through `x` gives the lower bound;
- the interpolant of `δ_x` on that level set gives the upper bound.
The formalization uses this route (blueprint README §3.1). Theorem D is only used for the remark
on p. 797.

## Section 3: Theorem 1

### N-07 (G) — p. 795, (3): normalisation of the Herglotz representation — *tex-checked*
(3) uses the kernel `1/(z - λ_k) + 1/λ_k`, which is undefined if `0 ∈ Λ`. The formalization uses
`1/(λ_k - z) - λ_k/(1 + λ_k²)`, and a genus-one canonical product `G` with a factor `z` when
`0 ∈ Λ`. The constant in front of the sum (the paper has `-i`, while Theorem F's Poisson integral
carries `1/π`) is to be checked (M03).

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

### N-12 (G) — p. 797: the limit `α → π/2` — *open*
"by (4) we may apply Lebesgue's dominated convergence theorem": (4) bounds the sums uniformly in
`α` but is not a domination. A correct argument uses the local Plancherel–Pólya inequality: the
tails `∑_{|λ_{α,k}| > R} |f(λ_{α,k})|²` are bounded by a fixed multiple of
`∫∫_{|x| > R-1, |y| < 1} |f|²` uniformly in `α`, and this tends to `0`.

### N-13 (G) — p. 796: `φ_F' ≥ 0` — *open*
Used without comment. For `F ∈ \overline{HB}` without real zeros it follows from
`log|F^*| - log|F| ≤ 0` on `ℂ₊`, with equality on `ℝ`.

## Section 4: Landau's inequality

### N-14 (T) — p. 799, proof of the Claim: `Λ` should be `Γ` — *print-checked*
"`h'(t)` is bounded, in fact equal to `-1` for `t ∉ Λ`, and so if the right-hand side is smaller
than the separation distance of `Λ`". Since `h = n_Γ - t`, both occurrences of `Λ` should be `Γ`.
Separation of `Γ` is needed and holds because `Γ` is complete interpolating.

### N-15 (G) — p. 799: small intervals — *open*
`J = {t ∈ I : |h(t) - h_I| ≥ A log|I|}` requires `|I| > 1`. Short intervals are absorbed into the
constant `B`.

### N-16 (G) — p. 798: the sine-type claim — *open*
"`F(z) = lim ∏(1 - z/λ_k)` is a sine-type function" is asserted without proof. The formalization
proves the needed estimate `|E(z)| ≃ e^{π Im z}` for an associated `E`, and avoids Levin's
theorem (blueprint README §3.7).

## Section 5: Corollary 2 and Theorem 2

### N-17 (E) — p. 801: Meĭman's theorem as used — *open*
The text says: if `A` and `B` have interlacing zeros, then `A - iB` or `A + iB` is in
`\overline{HB}`. Interlacing plus exponential type is not sufficient. `A = cos πz` and
`B = e^{az} sin πz` with `a ≠ 0` have interlacing zeros, and on the imaginary axis neither
combination satisfies the Hermite–Biehler inequality. For the specific `A`, `B` of the proof the
conclusion holds: they are limits of real polynomials with interlacing zeros, for which the
polynomial Hermite–Biehler theorem is elementary. The precise hypotheses of Meĭman's theorem in
[Le80, p. 314] are to be checked.

### N-18 (G) — p. 800–801: "We may assume `ω' ≃ 1`" — *open*
`ω' = 1 + ψ' - φ_f'/π → 1` at infinity, but it may fail to be `≃ 1` on a compact set. A
modification on a compact set changes `Λ(ψ)` by finitely many points, which is handled by the
perturbation argument.

### N-19 (G) — p. 801: the normal-family step — *open*
Only translates by `x_{2k}` with `k → +∞` are considered; `x → -∞` is analogous. The
identification of the limits (`c_k cos πx`) needs to be justified.

### N-20 (E) — p. 802: integration range in `log|f|` and (10) — *print-checked*
`log|f(z)| = ∑_n ∫_{r_{n-1}}^{r_n} (log|1 - z/z_n| + Re(z/t)) dψ(t)` gives the zero `z_n` the
`dψ`-mass `ψ(r_n) - ψ(r_{n-1})`. This is not an integer in general, so this is not `log|f|` for an
entire `f`. The integrals must run over `[t_{n-1}, t_n]`, whose mass is `1`. The same applies to
(10). The rewriting of `j_n` "by (9)" and the formula for `V_1` already use `[t_{n-1}, t_n]`.

### N-21 (E) — pp. 804–805: the proof of Theorem 2 (ii) — *open*
- **Typos.** "`φ_n(t) = ψ_n(t) - n - 1/2`" should read `ψ(t)`. "The assumption `φ_n'(t) = o(1/t)`"
  should be about `ψ'`.
- **`ε_n → 0` fails.** The equation `∫_{t_n}^{ξ_n} φ_n(x)/x dx = 0` does not give `ε_n → 0` in
  general. For `ψ = log log x` it gives `ε_n ≈ 0.37`. If `ψ` is linear in `log x` on the relevant
  range it would give `ψ(ξ_n) = n + 1`, contradicting `ξ_n < t_{n+1}/2`.
- **The estimates do not follow.** With the paper's heuristic formula for `U_n`, one gets
  `U_n(ξ_n) ≈ -½ log ξ_n - ½ log t_n`, not `-½ log ξ_n + O(1)`. Then (11) does not follow, while
  (12) holds because of the mass near the origin.

The proof has to be reconstructed (blueprint M09). Whether the statement holds is under
investigation.

### N-22 (G/D) — Theorem 2 (i) needs regularity of `ψ` beyond the stated hypotheses — *referee-pending*
The proof of (i) uses "the smoothness of `ψ` ensures that `∑_{n(z)-1}^{n(z)+1} j_n(z) ≃ 1`"
(p. 802), and the introduction speaks of "`ψ` sufficiently regular" (p. 790), but the statement of
Theorem 2 only assumes `ψ' = 1/O(x)` and the logarithmically regular partition.
- **Counterexample to the construction** (M08 writer): cells with `d_n = √t_n` whose unit mass sits on
  a spike of length `ℓ_n = log t_n` satisfy all stated hypotheses (including `ψ' = o(1)`), but near
  the spike `j_n(x) ≈ log(ℓ_n/d_n) → -∞`, so `|U_ψ - log|f||` is unbounded for the paper's `f`.
  Two half-spikes at the ends of a cell defeat every choice of one zero per cell.
- **What the proof needs:** `ψ' ≤ K/d_n` on `[t_{n-1}, t_n]` (`DensBound`).
- **Formalization:** `theorem2_i` assumes in addition that `ψ'` is eventually nonincreasing, which
  covers the paper's example `√x` and gives `DensBound`. `theorem2_i_of_regular` assumes `DensBound`
  directly. Whether (i) holds without such a regularity assumption is open.

### N-23 (E) — p. 804: the bound for `V_2` is false for nonreal `z` — *coordinator-checked*
"`|log|z - r_n| - log|z - z_n|| ≲ d_n²/|z - r_n|²`" fails off the real axis: for `z = i r_n` the
derivative of `θ ↦ log|z - r_n e^{-iθ}|` at `θ = 0` is `1/2`, so the difference is `≈ c d_n/(2 r_n)`,
of first order. The correct bound is `≲ d_n²/|z - r_n|² + d_n Im z/|z - r_n|²`; the extra terms sum
to at most a constant because `∑_n d_n y/|z - r_n|²` is a Riemann sum of a Poisson integral.

### N-24 (G) — p. 802: the window `n(z) - 1, …, n(z) + 1` — *referee-pending*
When `d_n ≃ d_{n+1}` holds only with a constant `C > 1`, the cells within distance `≲ d_n` of `z` are
not confined to three indices; the window must depend on `C`. The far cells (`n > n⁺(z)`,
`n < n⁻(z)`) need the cancellation of the first and second order terms through (9), not a termwise
bound.

### N-25 (G) — Theorem 2 (i): `φ_f' → 0` is not checked — *referee-pending*
Corollary 2 requires `φ_f'(x) = o(1)`; the proof of Theorem 2 (i) does not verify it for its `f`. It
holds: `φ_f'(x) = ∑_n |Im z_n|/|x - z_n|²` with `|Im z_n| ≃ d_n → ∞`. Also, the integrand of `U_ψ`
must be shown integrable (in Lean a non-integrable integral is `0`).

### N-26 (S) — Theorem 2 (i): the hypothesis `ψ' = 1/O(x)` — *referee-pending*
The proof only uses `t_n ≤ (1 + C) t_{n-1}`, which already follows from `d_n ≃ d_{n+1}`. The
hypothesis is kept in the formal statement for faithfulness unless the linter forces its removal
(removing a hypothesis strengthens the theorem).

### N-27 (T) — p. 790: Fourier frames and sampling — *tex-checked*
"By the Paley–Wiener theorem, `Λ` is sampling for PW if and only if `{e^{iλ_k x}}` is a Fourier frame":
the correspondence involves the reflection `t ↦ -t` (the frame uses `e^{-iλx}`, the Paley–Wiener
representation `e^{izt}`) and the factor `2π` between the norms. The frame bounds `(A, B)` correspond
to the sampling bounds `(A/2π, B/2π)`.

### N-28 (G) — p. 796: "`E` has no zeros on the real axis since `PW = H(E)`" — *referee-pending*
True but needs an argument: if `E(x₀) = 0` and `f(x₀) ≠ 0` for some `f ∈ H(E)` (a translate of a PW
function), then `∫|f/E(x + iy)|² dx ≳ 1/y`, so `f/E ∉ H²`. Likewise Theorem E is applied without
noting that `E` must be in the strict class (`H(E) = PW ≠ {0}` rules out `E^* = cE`) and that
`φ_E + φ_F` is strictly increasing.

### N-29 (G) — p. 799: the "evident fact" — *referee-pending*
"`H(E) = PW` if `|E(z)| ≃ e^{π Im z}` for `Im z ≥ 0`" is true but not evident: `H(E) ⊆ PW` needs a
Fatou argument for `L²(ℝ)` and a separate bound in the strip `|Im z| ≤ 1`.

### N-30 (T) — p. 798: the product `F` of the example — *tex-checked*
`F(z) = lim ∏_{|λ_k|<R}(1 - z/λ_k)` is undefined because `λ_0 = 0`; it should be `z ∏_{k ≠ 0}`.
"This sequence is sampling, because … sine-type" is really sine-type ⇒ complete interpolating ⇒
sampling. The formalization proves the needed estimate `|E(z)| ≃ e^{π Im z}` (the conjugate function
of `log|t|` is bounded) and replaces Levin's theorem by Theorem E.

---

## Implementation log

(I-entries: divergences decided during implementation, removed or changed helper statements, and
anything an implementer had to do differently from the blueprint.)
