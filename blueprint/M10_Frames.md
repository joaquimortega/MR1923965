# M10 — Fourier frames ⟺ sampling

**Lean file:** `FourierFrames/Frames.lean` (imports `FourierFrames.PW.Basic`; compiles with `sorry` only).
**Paper:** §1, p. 790 ("By the Paley–Wiener theorem, `Λ` is sampling for PW iff `{e^{iλ_k x}}` is a Fourier frame").
**Depends on:** M01 (`memPW_pwFT`, `exists_pwFT`, `memL2pi_reflect`, `l2piSq_reflect`, `pwFT_reflect`, `pwFT`, `reflect`,
`l2piSq`, `MemL2pi`); M00 (`IsFourierFrame`, `IsSampling`, `sampleSum`, `pwNormSq`, `PaleyWienerThm`).
**Used by:** the main statement `isFourierFrame_iff_isSampling` of `comparator/statements.lean`; every use of Theorem 1 for frames.

## 1. Conventions and the dictionary

`IsFourierFrame Λ` (Defs.lean): `∃ A B : ℝ≥0, 0 < A ∧ ∀ g, MemLp g 2 (volume.restrict (Ioc (-π) π)) →
A ∫⁻_{Ioc(-π,π)}‖g‖² ≤ ∑'_{l:Λ} ‖∫_{-π}^{π} g(x) e^{-i l x} dx‖ₑ² ∧ (same sum) ≤ B ∫⁻_{Ioc(-π,π)}‖g‖²`.
`IsSampling Λ`: `∃ A B : ℝ≥0, 0 < A ∧ ∀ f, MemPW f → A ‖f‖² ≤ sampleSum Λ f ∧ sampleSum Λ f ≤ B ‖f‖²`.

*Conventions to watch.*
1. The frame uses the kernel `e^{-iλx}`, the Paley–Wiener theorem (`hPW`) the kernel `e^{+izt}`. They are related by
   the reflection `g ↦ ǧ := g(-·)` (M01 `reflect`): `∫_{-π}^{π} g(x) e^{-iλx}dx = ∫_{-π}^{π} g(-t) e^{iλt}dt = F_ǧ(λ)`.
2. The frame inequality integrates `‖g‖²` over `Ioc (-π) π`, while `reflect` maps `Ioc` to `Ico`; the two differ by the
   null set `{-π, π}`; this is dealt with in M01 (`l2piSq_reflect`, `memL2pi_reflect`). The coefficient is an *interval integral*
   `∫ x in (-π)..π`, which by `intervalIntegral.integral_of_le` is the integral over `Ioc (-π) π`; `pwFT_reflect` is stated with the interval integral
   (`intervalIntegral.integral_comp_neg`, no measure-theoretic subtlety there).
3. Constants: `‖F_ǧ‖²_{PW} = 2π ‖ǧ‖² = 2π ‖g‖²` (the Paley–Wiener normalisation of `PaleyWienerThm`).
   So **frame bounds `(A, B)` correspond to sampling bounds `(A/2π, B/2π)`** and conversely sampling bounds `(A', B')` give frame bounds `(2πA', 2πB')`;
   the constants are absolute multiples of each other.
4. `Λ` is a *set* here; the paper's sequences may repeat points, which is irrelevant for the separated sequences of Theorem 1. The statement is exactly
   true for sets, including `Λ = ∅` (neither side holds: `g = 1` gives `0 ≥ A·2π`).

## 2. Lemmas

```lean
/-- The Fourier coefficient `∫_{-π}^{π} g(x) e^{-iλx} dx` of `IsFourierFrame`. -/
def fourierCoeff (g : ℝ → ℂ) (l : ℝ) : ℂ :=
  ∫ x in (-Real.pi)..Real.pi, g x * Complex.exp (-(I * (l : ℂ) * x))
```
```lean
/-- `fourierCoeff g l = pwFT (reflect g) l`. -/
theorem fourierCoeff_eq_pwFT_reflect (g : ℝ → ℂ) (l : ℝ) :
    fourierCoeff g l = pwFT (reflect g) (l : ℂ)
```

*Proof.* `fourierCoeff g l = ∫ x in (-π)..π, g x * exp(-(I * l * x))` and by `pwFT_reflect g (l:ℂ)`
(M01) `pwFT (reflect g) (l : ℂ) = ∫ t in (-π)..π, g t * exp(-(I * l * t))`. Same integrand; `rfl` after `pwFT_reflect` (the `Complex.exp (-(I * z * t))`
spelling is identical to that of `IsFourierFrame` up to the cast `((l:ℝ):ℂ)`).

```lean
/-- The sum `∑_{λ ∈ Λ} |∫ g e^{-iλx}|²` of `IsFourierFrame` equals `sampleSum Λ (pwFT (reflect g))`. -/
theorem tsum_fourierCoeff_eq_sampleSum (Λ : Set ℝ) (g : ℝ → ℂ) :
    ∑' l : Λ, ‖∫ x in (-Real.pi)..Real.pi, g x * Complex.exp (-(I * ((l : ℝ) : ℂ) * x))‖ₑ ^ 2 =
      sampleSum Λ (pwFT (reflect g))
```

*Proof.* `sampleSum Λ f = ∑' x : Λ, ‖f ((x:ℝ):ℂ)‖ₑ^2` with `f = pwFT (reflect g)`; `tsum_congr` with
`fourierCoeff_eq_pwFT_reflect`, i.e. the summands agree pointwise (in the statement the summand is literally the
integral occurring in `IsFourierFrame`).

## 3. Main theorem

```lean
/-- **The Paley–Wiener reduction** (p. 790): `{e^{iλx}}_{λ ∈ Λ}` is a Fourier frame if and only if
`Λ` is sampling for `PW`.  Frame bounds `(A, B)` correspond to sampling bounds `(A/2π, B/2π)`. -/
theorem isFourierFrame_iff_isSampling (hPW : PaleyWienerThm) (Λ : Set ℝ) :
    IsFourierFrame Λ ↔ IsSampling Λ
```

*Proof.* Put `κ := ENNReal.ofReal (2π) ∈ (0, ∞)` and `K := Real.toNNReal (2π) > 0` (`κ = (K : ℝ≥0∞)`, `ENNReal.ofReal` of a nonnegative real is the coercion of `toNNReal`).

**(⇐) sampling ⇒ frame.** Let `A, B` be the sampling constants (`0 < A`). Take frame constants `A' := K * A`, `B' := K * B` (`0 < A'`).
Let `g ∈ L²(-π,π)` (`MemL2pi g`; the hypothesis `MemLp g 2 (volume.restrict (Ioc ..))` is by definition `MemL2pi g`).
Put `f := pwFT (reflect g)`. By `memL2pi_reflect` and `memPW_pwFT` (M01, the unconditional `⇐` of Paley–Wiener, §0–§1.7 of M01):
`MemPW f` and `pwNormSq f = κ · l2piSq (reflect g) = κ · l2piSq g` (`l2piSq_reflect`). By sampling,
`A · pwNormSq f ≤ sampleSum Λ f ≤ B · pwNormSq f`, and `sampleSum Λ f = ∑' l:Λ, ‖∫ g e^{-ilx}‖ₑ²`
(`tsum_fourierCoeff_eq_sampleSum`). Since `A · κ · l2piSq g = A' · l2piSq g` (`mul_comm`, `ENNReal.coe_mul`), both frame inequalities follow.
(`l2piSq g` is the `∫⁻ x in Ioc (-π) π, ‖g x‖ₑ ^ 2` of `IsFourierFrame` by definition.)

**(⇒) frame ⇒ sampling.** Let `A', B'` be the frame constants (`0 < A'`); put `A := A' / K`, `B := B' / K` (`NNReal` division, `K ≠ 0`; `0 < A`).
Let `f ∈ PW`. By `exists_pwFT` (M01; uses only the `⇒` half of `hPW`): `f = pwFT h`, `h ∈ L²(-π,π)`, `pwNormSq f = κ · l2piSq h`.
Set `g := reflect h` (`MemL2pi g` by `memL2pi_reflect`); `reflect (reflect h) = h` (`neg_neg`), so
`pwFT h = pwFT (reflect g)`, i.e. `f = pwFT (reflect g)`, and `l2piSq g = l2piSq h` (`l2piSq_reflect`). The frame inequality for `g` reads
`A' · l2piSq g ≤ sampleSum Λ f ≤ B' · l2piSq g` (by `tsum_fourierCoeff_eq_sampleSum`), and `A · pwNormSq f = (A'/K) · K · l2piSq g = A' · l2piSq g`
(`ENNReal.coe_div`, `ENNReal.div_mul_cancel`‑type lemma with `K ≠ 0`, `K ≠ ⊤`; or avoid division: choose `A := A' / K` and verify `A * K = A'` in `ℝ≥0` (`div_mul_cancel₀`), then `ENNReal.coe_mul`). Same for `B`.

*Remarks.* (i) `hPW` is used only through `exists_pwFT` (`⇒`) and `memPW_pwFT` (`⇐` with the norm identity);
with the literal `PaleyWienerThm` of Defs.lean the latter is derived in M01 §1.7 — see M01 §0 for why the literal `⇐` is not sufficient.
(ii) The proof shows more: the *best* frame bounds of `Λ` are `2π` times the best sampling bounds.

## 4. Issues in the source

1. **p. 790 (tex l. 135–137):** "By the Paley–Wiener theorem, `Λ` is sampling for PW if and only if `{e^{iλ_k x}}` is a Fourier frame." True, but the
   frame sum has the kernel `e^{-iλ_k x}` while `f(λ) = ∫ g e^{iλ t}dt`; one needs the reflection `t ↦ -t` (harmless since `L²(-π,π)` is reflection
   invariant) and the factor `2π` between the two norms. Neither is mentioned. Sure (cosmetic).
2. The paper writes the sampling/frame sums over `k ∈ ℤ` for a *sequence* `{λ_k}` (repetitions allowed); the formalisation uses `Set ℝ`. For separated `Λ` (the only case of Theorem 1) no difference. Sure.

## 5. Requested changes to M00

* The strengthening of `PaleyWienerThm` requested in M01 §7 (the current `↔` has a vacuous `⇐`); with it `isFourierFrame_iff_isSampling` needs no extra argument. No change to `IsFourierFrame` or `IsSampling` is needed: the statement is true as written (checked: empty `Λ`, constants in `ℝ≥0`, `Ioc` vs `Ico` null sets, `ℝ≥0∞` arithmetic).
