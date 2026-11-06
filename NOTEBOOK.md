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
2026-11-06), *open* (not yet settled).

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
theorem (blueprint README §3.7).

## Section 5: Corollary 2 and Theorem 2

### N-17 (E) — p. 801: Meĭman's theorem as used — *referee-confirmed (R4, numerically)*
The text says: if `A` and `B` have interlacing zeros, then `A - iB` or `A + iB` is in
`\overline{HB}`. Interlacing plus exponential type is not sufficient: `A = cos πz` and
`B = e^{az} sin πz` with `a ≠ 0` have interlacing zeros, and on the imaginary axis
`|A ∓ iB|(iy)` vs `|A ∓ iB|(-iy)` compares `|cosh πy ± e^{iay} sinh πy|` with
`|cosh πy ∓ e^{iay} sinh πy|`, whose order changes with the sign of `cos(ay)`. For the specific `A`, `B`
of the proof the conclusion holds and is proved directly: the symmetric partial products are real
polynomials with interlacing zeros, for which `Im(B_R/A_R) > 0` on `ℂ₊` (sum of arguments of the
factors), and `\overline{HB}` is closed under locally uniform limits (Hurwitz). No choice of sign
(`P ↦ -P`) is needed.

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
  `Λ ∩ (-∞, 0] = ℤ_{≤0}`, `‖f‖² ≳ a log(L)` while `∑_Λ |f|² ≲ a(1 + η² log L)`, and the ratio tends
  to `0` (blueprint M09).

### N-22 (G/D) — Theorem 2 (i) needs regularity of `ψ` beyond the stated hypotheses — *referee-confirmed (R1, R5); open whether (i) holds without it*
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
(removing a hypothesis strengthens the theorem).

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
of `log|t|` is bounded) and replaces Levin's theorem by Theorem E.

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
product may not converge. A Weierstrass product of variable genus (`p_x ≥ m_x + |x|`) works; Mathlib
has no Weierstrass factorization theorem, so the formalization constructs it. Also "If we prove that
`Λ₁` is a sampling sequence, then `Λ` is also": the upper bound for `Λ ⊋ Λ₁` needs the
Plancherel–Pólya inequality for the separated `Λ`.

### N-33 (G) — p. 796: the level sets are indexed by `ℤ` — *referee-confirmed (R3–R5)*
`Λ_α = {λ_{α,k}}_{k ∈ ℤ}` presupposes that `φ_{EF}` maps `ℝ` onto `ℝ`. This holds (e.g. since
`φ_E → ±∞`, which follows from Theorem E: a level set bounded on one side would contradict the
interpolation property), but it is not shown. "We may assume it fails for `α = π/2`" is unnecessary:
along `α_n = π/2 + π/(n+2)` at most one `α_n` is exceptional.

### N-34 (G) — Corollary 1 and the remark of p. 797 — *referee-confirmed with corrections (R3)*
- Pavlov's theorem requires `Γ` separated. The paper covers this on p. 791 ("It is plain that all
  complete interpolating sequences are separated"); the formalization proves it for `Γ_α` from
  Theorem E and the Bernstein bound.
- "If `Λ` is a complete interpolating sequence, then there exists `E ∈ \overline{HB}` such that
  `H(E) = PW` and `Λ` constitutes the zero sequence of `E + E^*`. This follows from Theorems C and
  E": the argument also needs that a complete interpolating sequence is sampling (taken for granted
  on p. 791; open mapping theorem), Theorem D (orthogonality of the kernels at `Λ` forces `Λ` into
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
  `ω' ≃ 1`; the [OS99] function carries a factor `e^{-κz}` (as does `OCS.multF`), which is harmless.

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

### N-37 (E) — p. 794: Theorem F as printed fails for non-strict `E` — *referee-confirmed (R3)*
Theorem F is stated for `E ∈ \overline{HB}`. For `E = 1` (in `\overline{HB}`), `H(E) = {0}`, so the
isometry condition holds for every measure `μ`, while the right-hand side `Re((1 + A)/(1 - A))` is
finite, which fails for any `μ` with infinite Poisson integral. de Branges' theorem is for the strict
class; the paper only applies it to `E` with `H(E) = PW`, which is strict (N-28). The formalized
`TheoremF` is restricted to the strict class without real zeros. Similarly, Theorem E is
meaningless (`φ' ≡ 0`) when `E^* = cE`.

### N-38 (T) — p. 801, Theorem 2 (ii) proof sketch — *referee-confirmed (R5)*
The reconstructed proof (N-21) uses `xψ'(x) → 0` only through the existence of arbitrarily long
logarithmic windows where `ψ` stays within `η` of a half-integer; this is implied by, not equivalent
to, `ψ' = o(1/x)`.

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
the theorem), not by suppression.

