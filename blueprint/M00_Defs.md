# M00 — Definitions, cited results, main statements

**Lean:** `FourierFrames/Defs.lean` (imports only Mathlib; copied verbatim into `FFChallenge.lean`),
main statements in `comparator/statements.lean`.

**Depends on:** Mathlib only. **Used by:** every module.

## 1. Definitions and how they match the paper

| Lean | Paper | Notes |
|---|---|---|
| `IsExpTypeLE τ f` | "exponential type at most τ" | `∀ ε > 0, |f(z)| ≤ C_ε e^{(τ+ε)|z|}` (same as `OCS.IsExpTypeLE`). |
| `MemPW f` | `PW`, p. 790 | entire, type `≤ π`, `f|ℝ ∈ L²`. |
| `pwNormSq f` | `‖f‖²_{PW}` | `∫⁻ |f(x)|²`, `ℝ≥0∞`. |
| `sampleSum Λ f` | `∑_k |f(λ_k)|²` | `tsum` over the subtype `Λ`, `ℝ≥0∞`; no summability side conditions. |
| `IsSampling Λ` | p. 790 | `A ‖f‖² ≤ ∑ ≤ B ‖f‖²`, `A > 0`, `B < ∞`. |
| `IsSeparated Λ` | p. 791 | `inf_{λ≠λ'} |λ-λ'| > 0`. |
| `IsCompleteInterpolating Λ` | p. 791 | unique interpolation of every `ℓ²(Λ)` datum. Data are functions `ℝ → ℂ`; only values on `Λ` matter. |
| `IsFourierFrame Λ` | p. 789 | the frame inequality for `g ∈ L²(-π,π)` with `∫_{-π}^{π} g(x) e^{-iλx} dx`. |
| `countFn Λ t` | `n_Λ(t)`, p. 791 | `#(Λ∩(0,t])` for `t ≥ 0`, `-#(Λ∩(t,0])` for `t < 0`; `ncard` (finite for separated `Λ`). |
| `intervalMean`, `meanOsc`, `MemBMO` | BMO | mean oscillation over bounded intervals. |
| `fstar f` | `f^*(z) = \overline{f(\bar z)}` | |
| `IsH2Upper g` | `H²(ℂ₊)` | holomorphic on `Im z > 0`, `sup_{y>0} ∫|g(x+iy)|²dx < ∞`. |
| `IsHB E` | `\overline{HB}`, p. 793 | entire, no zeros on `Im z > 0`, `|E(z̄)| ≤ |E(z)|` there. |
| `IsStrictHB E` | de Branges' `HB` | adds `|E(z̄)| < |E(z)|`. |
| `MemHE E f` | `H(E)`, p. 793 | entire, `f/E`, `f^*/E ∈ H²`. |
| `heNormSq E f` | `‖f‖²_E` | `∫⁻ |f(t)/E(t)|² dt`. Lean's `x/0 = 0` is harmless: real zeros of `E ≢ 0` form a null set. |
| `HEEqPW E` | "`H(E) = PW`", p. 794 | same set and equivalent norms. |
| `IsPhaseFunction E φ` | phase function, p. 794 | continuous, `E(x) = |E(x)| e^{-iφ(x)}`. |
| `phaseDeriv E x` | `φ_E'(x)` | `-Im(E'(x)/E(x))`; equals `φ'` for any `C¹` phase function when `E(x) ≠ 0`. |
| `phaseLevel φ α` | `{φ = α + kπ}` | |
| `orthWeight E x` | `π/(φ'(x)|E(x)|²) = 1/K_E(x,x)` | `ENNReal.ofReal`. |
| `poissonInt μ z` | `(y/π)∫ dμ(t)/((t-x)²+y²)` | `ℝ≥0∞`. |
| `deBrangesKernel E w z` | `K_E(w,z)`, formula (1) | extended to `z = w̄` by the limit. |
| `logExample` | `{k + log⁺|k|}`, p. 798 | `Real.posLog`. |
| `IsAdmissiblePsi ψ` | standing assumptions p. 800 | `C¹`, nondecreasing, `ψ(∞)-ψ(-∞) = ∞` (one side unbounded), `ψ' → 0` at `±∞`. |
| `LambdaPsi ψ` | `Λ(ψ)`, p. 800 | `{x : x + ψ(x) ∈ ℤ}`; `x ↦ x + ψ(x)` is a strictly increasing bijection of `ℝ`. |
| `UPsi ψ z` | `U_ψ`, p. 800 | `Re(z/t)` kept only for `|t| > 1` (README §2.5). |
| `IsLogRegularPartition ψ` | p. 801 | existence of `t_n` with `t₀ = 0`, `ψ(t_n) = n`, `d_n ≃ d_{n+1}`, and the sup condition. |

## 2. Cited results (`Prop`s) and why each is implied by the literature

Each `Prop` is a *hypothesis* of the main theorems that use it. It must be a true theorem;
otherwise the conditional results would be vacuous. Weakening a cited statement (more hypotheses,
weaker conclusion) is always safe.

- **`PaleyWienerThm`.** Two parts: (a) for every `g ∈ L²(-π,π)`, `f(z) = ∫_{-π}^{π} g(t)e^{izt}dt`
  is in `PW` with `‖f‖²_{L²(ℝ)} = 2π‖g‖²`; (b) every `f ∈ PW` has this form. This is the
  Paley–Wiener theorem plus Plancherel. (A first version stated `MemPW f ↔ ∃ g, rep ∧ norm identity`;
  its `⇐` half was useless because it assumed the norm identity. Changed on the M01 writer's
  request, before any review.) To be proved in phase 2 from Mathlib's
  `MeasureTheory.Lp.fourierTransformₗᵢ`; Mathlib (v4.35) lacks the lemma that the `L¹` and `L²`
  Fourier transforms agree on `L¹ ∩ L²`, which phase 2 needs.
- **`TheoremC`.** de Branges [dB68, Theorem 23]: a Hilbert space of entire functions satisfying
  (H1)–(H3) and containing a nonzero element is isometrically equal to some `H(E)`, `E ∈ HB`. The
  Lean version quantifies over a complete inner product space `H` with an injective linear map
  `ι : H → (ℂ → ℂ)` into entire functions; (H1) is stated pointwise off `ζ` (the value at `ζ` is
  forced by continuity). The conclusion uses the closed class `IsHB` (weaker than de Branges').
- **`TheoremD`.** de Branges [dB68, Theorem 19], restricted to strict `E` without real zeros.
  Only used for the remark of p. 797.
- **`TheoremE`.** de Branges [dB68, Theorem 22] (the tex and the print have `∉ H(E)`), restricted
  to strict `E` without real zeros (then `φ' > 0`, the level set is discrete and the weights are
  finite). Conclusions: the norm identity (Parseval for the orthonormal basis of normalised
  kernels) and surjectivity of the interpolation (every coefficient sequence in `ℓ²` is attained).
  Restriction to the strict class is necessary: for `E^* = cE` the space `H(E)` is `{0}` and the
  interpolation claim would be false.
- **`TheoremF`.** de Branges [dB60] (also [dB68, Theorem 32]), only the direction used
  (isometric inclusion ⇒ existence of `A`), with an extra term `p·y`, `p ≥ 0`, allowed in the
  Herglotz representation, and restricted to strict `E` without real zeros. With `p` allowed, the
  statement is a consequence of the Herglotz representation of the positive harmonic function
  `Re((E+E^*A)/(E-E^*A))` together with de Branges' theorem; the proof of Theorem 1 is unchanged
  (`M` gains an entire term `-ipz`, and `M^* = -M` still holds).
- **`PavlovBMO`.** Theorem A (Pavlov; Hruščev–Nikol'skiĭ–Pavlov [HNP81, p. 286]) contains: if a
  separated `Γ` is complete interpolating, then `h = n_Γ - t ∈ BMO(ℝ)`.
- **`JohnNirenberg`.** [JN61], [Ga81, Ch. VI]: `|{t ∈ I : |h - h_I| > s}| ≤ C e^{-cs/‖h‖_*}|I|`.
  Stated with any upper bound `M` of the mean oscillations instead of `‖h‖_*`, which is
  equivalent.
- **`DSPerturbation`.** Duffin–Schaeffer [DS52, Lemma III]: if `Γ` is a (separated) frame
  sequence, perturbations `|δ_k| ≤ L` with `L` small (depending on `Γ`) preserve the frame
  property. Proof (phase 2): Bernstein's inequality and Taylor expansion.

## 3. Main statements

See `comparator/statements.lean` and the table in `README.md` §1. Points to note:
- `theorem1` is stated for separated `Λ` (as in the paper, which reduces to this case by
  [Se95, Lemma 3.11]).
- The zero set condition "`Λ` constitutes the zero sequence of `EF + E^*F^*`" is
  `∀ z, E z F z + E^* z F^* z = 0 ↔ ∃ x ∈ Λ, z = x`. Multiplicities are irrelevant: for `E` strict
  and `F ∈ \overline{HB}` without real zeros all zeros are real and simple, and the paper reduces
  to that case.
- `corollary1` enumerates `Γ` increasingly by `ℤ` (`StrictMono γ`, `range γ = Γ`).
- `landau_inequality` uses `encard` in `ℝ≥0∞` and `ENNReal.ofReal` on the left (negative left
  sides are trivially fine).
- `theorem2_i`: "`ψ'(x) = 1/O(x)`" is `ψ'(x) ≥ c/x` for large `x`. `theorem2_ii`:
  "`ψ'(x) = o(1/x)`" is `x ψ'(x) → 0`.
