# M05 — The Claim: Landau's inequality from John–Nirenberg and Pavlov

**Lean:** `FourierFrames/Landau.lean` (namespace `FF`).
**Paper:** §4, "Claim", p. 799 (proof, tex lines 640–681).
**Depends on:**
- M04 `corollary1_strong` (Corollary 1 with `Γ` separated; the statement of `corollary1` in
  `comparator/statements.lean` does *not* record the separation of `Γ`, which Pavlov's theorem
  needs; see M04, §Corollary 1);
- cited `Prop`s `PavlovBMO` (`hA`), `JohnNirenberg` (`hJN`), and, through `corollary1_strong`,
  `PaleyWienerThm`, `TheoremC`, `TheoremE`, `TheoremF`;
- Mathlib only otherwise.

**Used by:** nothing downstream (M06 handles the sharpness example independently).

## 0. Overview of the proof

Let `Λ` be separated and sampling. `corollary1_strong` gives `γ : ℤ → ℝ` strictly increasing,
`Γ = range γ` separated (constant `q > 0`) and complete interpolating, with a point of `Λ` in every
`[γ_k, γ_{k+1})`. `PavlovBMO` gives `h(t) = n_Γ(t) - t ∈ BMO`.

1. **Counting** (§1): `#(Λ∩(a,b]) ≥ #(Γ∩(a,b]) - 1 = (b-a) + h(b) - h(a) - 1`.
2. **Local control of `h`** (§2): `|h(b) - h(a)| ≤ K (b-a) + 1` with `K = 1 + 1/q`.
3. **John–Nirenberg** (§3): from 2 and `h ∈ BMO`, `|h(b) - h(a)| ≤ A log⁺(b-a) + B`.
4. Conclusion (§4).

Throughout `h := fun t ↦ countFn Γ t - t`, `L := b - a`.

## 1. Counting lemmas

```lean
/-- A separated set meets bounded intervals in finite sets. -/
theorem IsSeparated.finite_inter_Ioc {Γ : Set ℝ} (hΓ : IsSeparated Γ) (a b : ℝ) :
    (Γ ∩ Ioc a b).Finite := by
  sorry
```

```lean
/-- A `q`-separated set has at most `(b - a)/q + 1` points in `(a, b]`. -/
theorem ncard_inter_Ioc_le {Γ : Set ℝ} {q : ℝ} (hq : 0 < q)
    (hΓ : ∀ x ∈ Γ, ∀ y ∈ Γ, x ≠ y → q ≤ |x - y|) {a b : ℝ} (hab : a ≤ b) :
    ((Γ ∩ Ioc a b).ncard : ℝ) ≤ (b - a) / q + 1 := by
  sorry
```

*Proof of `ncard_inter_Ioc_le` (and of the finiteness lemma).* Put `S = Γ ∩ (a,b]`. The map
`x ↦ ⌊(x - a)/q⌋ : S → ℤ` is injective: if `x < y` in `S`, then `y - x ≥ q`, so
`(y-a)/q ≥ (x-a)/q + 1` and the floors differ (`Int.floor_le`, `Int.lt_floor_add_one`). Its image
lies in `{0, …, ⌊(b-a)/q⌋}` (because `0 < x - a ≤ b - a`), which has `⌊(b-a)/q⌋ + 1 ≤ (b-a)/q + 1`
elements. Mathlib: `Set.Finite.of_injOn` / `Set.Finite.of_finite_image` for finiteness,
`Set.ncard_le_ncard_of_injOn` (or `Set.InjOn.encard_image` (with `Set.Finite.cast_ncard_eq`) + `Set.ncard_le_ncard`) and
`Set.ncard_Icc`-type cardinalities for `Finset.Icc 0 ⌊·⌋` (`Int.card_Icc`) for the bound.
`finite_inter_Ioc` follows from `IsSeparated` (`δ` from the definition) in the same way. ∎

```lean
/-- `n_Γ(b) - n_Γ(a) = #(Γ ∩ (a, b])` for `a ≤ b`, when `Γ ∩ (a, b]` is finite for all `a, b`. -/
theorem countFn_sub {Γ : Set ℝ} (hfin : ∀ a b : ℝ, (Γ ∩ Ioc a b).Finite) {a b : ℝ}
    (hab : a ≤ b) : countFn Γ b - countFn Γ a = ((Γ ∩ Ioc a b).ncard : ℝ) := by
  sorry
```

*Proof.* `countFn Γ t = ncard(Γ ∩ (0,t])` for `t ≥ 0` and `-ncard(Γ ∩ (t,0])` for `t < 0`.
Cases, with `a ≤ b`; every set is finite by `hfin`, and `Set.ncard_union_eq` (disjoint, finite)
is used with the disjoint decompositions of intervals:
- `0 ≤ a`: `(0,b] = (0,a] ∪ (a,b]`.
- `a < 0 ≤ b`: `(a,b] = (a,0] ∪ (0,b]`; the difference is `ncard(Γ∩(0,b]) + ncard(Γ∩(a,0])`.
- `b < 0`: `(a,0] = (a,b] ∪ (b,0]`; the difference is
  `-ncard(Γ∩(b,0]) + ncard(Γ∩(a,0]) = ncard(Γ∩(a,b])`.
Intersections distribute: `Γ ∩ (s ∪ t) = (Γ∩s) ∪ (Γ∩t)` (`Set.inter_union_distrib_left`). ∎

```lean
/-- `n_Λ(b) - n_Λ(a) ≥ n_Γ(b) - n_Γ(a) - 1` when every `[γ_k, γ_{k+1})` contains a point of `Λ`
(p. 799, first display). -/
theorem ncard_Ioc_ge {Λ : Set ℝ} {γ : ℤ → ℝ} (hγ : StrictMono γ)
    (hΛγ : ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1))
    (hfinΛ : ∀ a b : ℝ, (Λ ∩ Ioc a b).Finite) (hfinΓ : ∀ a b : ℝ, (Set.range γ ∩ Ioc a b).Finite)
    (a b : ℝ) :
    ((Set.range γ ∩ Ioc a b).ncard : ℝ) - 1 ≤ ((Λ ∩ Ioc a b).ncard : ℝ) := by
  sorry
```

*Proof* (the first inequality of the display on p. 799). Let `S := Γ ∩ (a,b]`, `J := {k : ℤ | γ k ∈ (a,b]}`,
so `S = γ '' J` and `ncard S = ncard J` (`γ` injective). `J` is finite (since `S` is) and
*order-convex*: if `k₁ < k < k₂` with `k₁, k₂ ∈ J`, then `a < γ k₁ < γ k < γ k₂ ≤ b`.

- If `J = ∅`, then `ncard S = 0` and `0 - 1 ≤ ncard(Λ ∩ (a,b])`.
- Otherwise let `j₂ := J.max'` and `J' := J \ {j₂}`; then `ncard J' = ncard J - 1`
  (`Set.ncard_diff_singleton_of_mem`). For `j ∈ J'` we have `j + 1 ∈ J` (convexity: `j < j+1 ≤ j₂`).
  By `hΛγ` choose `x_j ∈ Λ` with `γ j ≤ x_j < γ (j+1)` (use `choose` on `hΛγ`, giving `x : ℤ → ℝ`).
  Then `a < γ j ≤ x_j < γ(j+1) ≤ b`, so `x_j ∈ Λ ∩ (a,b]`. The map `j ↦ x_j` is injective on `J'`:
  for `j < j'`, `x_j < γ(j+1) ≤ γ j' ≤ x_{j'}` (strict monotonicity). Hence
  `ncard(Λ∩(a,b]) ≥ ncard J' = ncard S - 1` (`Set.InjOn.encard_image` (with `Set.Finite.cast_ncard_eq`), `Set.ncard_le_ncard`, with
  finiteness `hfinΛ`).
Cast to `ℝ`. ∎

## 2. Local control of `h`

For `a ≤ b` set `N := ncard(Γ∩(a,b])` (a real number `≥ 0`). By `countFn_sub`,
`h(b) - h(a) = N - (b - a)`, and by `ncard_inter_Ioc_le`, `N ≤ (b-a)/q + 1`. Then
`N - L ≤ N ≤ L/q + 1` and `L - N ≤ L`, so
`|h(b) - h(a)| ≤ (1 + 1/q) (b - a) + 1` for `a ≤ b`. This is the hypothesis `hloc` of the next lemma
(with `K = 1 + 1/q`, `D = 1`).

**Remark (the paper's "`h'(t) = -1` for `t ∉ Λ`").** `h` is *not* Lipschitz: it has jumps `+1` at
the points of `Γ`. Its "derivative is `-1` off `Γ`" (not off `Λ`; the paper mixes `Λ` and `Γ`), and
between two points at distance `≤ 1` it can change by at most `1/q + 1`. The paper's phrase "if the
right-hand side is smaller than the separation distance" is replaced by the clean argument below,
in which only *Lebesgue measure `< 1`* of `J` is used.

## 3. The John–Nirenberg step

```lean
/-- **Core of the Claim.** If `h ∈ BMO` has the local growth bound
`|h(b) - h(a)| ≤ K (b - a) + D` (`a ≤ b`), then `|h(b) - h(a)| ≤ A log⁺(b - a) + B`. -/
theorem osc_bound_of_JN (hJN : JohnNirenberg) {h : ℝ → ℝ} (hbmo : MemBMO h) {K D : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hloc : ∀ a b : ℝ, a ≤ b → |h b - h a| ≤ K * (b - a) + D) :
    ∃ A B : ℝ, ∀ a b : ℝ, a < b → |h b - h a| ≤ A * Real.posLog (b - a) + B := by
  sorry
```

*Proof.* `hbmo : MemBMO h` gives `LocallyIntegrable h` and `M₀` with `meanOsc h a b ≤ M₀` for all
`a < b`. Put `M := max M₀ 1 > 0` (the hypothesis `0 < M` of `JohnNirenberg`). Let `C, c > 0` be the
constants of `hJN` (absolute). Define
```
A₁ := 2 M / c,      L₀ := max 2 (C + 1).
```

**Large intervals, `L = b - a ≥ L₀`.** Put `I = [a,b]`, `s := A₁ log L > 0` (as `L ≥ 2`), and
`J := {t ∈ I | s ≤ |h t - intervalMean h a b|}`. `hJN` gives
`volume J ≤ ofReal (C exp(-c s/M) L)`, and
`exp(-c s / M) = exp(-2 log L) = L⁻²` (`Real.exp_neg`, `Real.exp_log`, `pow_two`-type rewriting), so
`volume J ≤ ofReal (C / L)` with `C / L < 1` because `L ≥ C + 1`.

*Claim:* every `t ∈ I` has `t' ∈ I ∖ J` with `|t - t'| ≤ 1`. Indeed, the interval
`W := [t, t+1]` if `t + 1 ≤ b`, `W := [t-1, t]` otherwise, lies in `I` (since `L ≥ 2`) and
`volume W = 1` (`Real.volume_Icc`). If `W ⊆ J` then `1 ≤ volume J < 1`
(`MeasureTheory.measure_mono`), absurd. So some `t' ∈ W ∖ J`; being in `I ∖ J` it satisfies
`|h t' - h_I| < s` (negation of the defining inequality).

Then, using `hloc` for the ordered pair `{t, t'}`,
`|h t - h_I| ≤ |h t - h t'| + |h t' - h_I| ≤ K + D + A₁ log L`
and, for `t = a` and `t = b`, `|h b - h a| ≤ |h b - h_I| + |h a - h_I| ≤ 2(K + D) + 2 A₁ log L`.
Since `L ≥ 1`, `log⁺ L = log L` (`Real.posLog_eq_log`).

**Small intervals, `L < L₀`.** `|h b - h a| ≤ K L + D ≤ K L₀ + D` by `hloc`.

Take `A := 2 A₁` and `B := max (2(K + D)) (K L₀ + D)`; for small intervals use
`A log⁺ L ≥ 0` (`Real.posLog_nonneg`, `A ≥ 0`). **Dependencies of the constants:** `C, c` absolute;
`M` depends on `h` (through `Γ`); `K, D` on the separation constant `q` of `Γ`; hence `A, B` depend
on `Λ` only through `Γ`. ∎

## 4. The Claim

```lean
/-- **Claim** (p. 798): Landau's inequality (Theorem B) follows from the John–Nirenberg theorem,
Pavlov's theorem (Theorem A) and Theorem 1: for a separated sampling sequence `Λ`,
`n_Λ(b) - n_Λ(a) ≥ b - a - A log⁺(b - a) - B`. -/
theorem landau_inequality (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE)
    (hF : TheoremF) (hA : PavlovBMO) (hJN : JohnNirenberg)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ A B : ℝ, ∀ a b : ℝ, a < b →
      ENNReal.ofReal (b - a - A * Real.posLog (b - a) - B) ≤ ((Λ ∩ Ioc a b).encard : ℝ≥0∞) := by
  sorry
```

*Proof.* Let `γ, Γ := range γ, q` be as in the overview (`corollary1_strong`, `hΓ : IsSeparated Γ`
gives `q`). `hA Γ hΓ hcis : MemBMO h`. §2 gives `hloc`, so §3 gives `A', B'` with
`|h b - h a| ≤ A' log⁺(b-a) + B'` for `a < b`. Let `a < b`, `L = b-a`. The sets `Λ ∩ (a,b]` and
`Γ ∩ (a,b]` are finite (`IsSeparated.finite_inter_Ioc`; `Λ` is separated by `hΛ`, `Γ` by
`corollary1_strong`). Then
```
ncard(Λ∩(a,b]) ≥ ncard(Γ∩(a,b]) - 1            (ncard_Ioc_ge)
              = n_Γ(b) - n_Γ(a) - 1            (countFn_sub)
              = L + h(b) - h(a) - 1
              ≥ L - A' log⁺ L - B' - 1.
```
With `A := A'`, `B := B' + 1`: `ofReal(L - A log⁺ L - B) ≤ ofReal(ncard(Λ∩(a,b]))
= (ncard : ℝ≥0∞) = encard` (`ENNReal.ofReal_le_ofReal`, `ENNReal.ofReal_natCast`,
`Set.Finite.cast_ncard_eq` for the last equality). If the left argument is negative the claim is
trivial (`ENNReal.ofReal_of_nonpos`). ∎

## Issues in the source

1. **p. 799, `h'(t) = -1` for `t ∉ Λ`; "separation distance of `Λ`"** (certain). The function is
   `h = n_Γ - t`, so the relevant set is `Γ` (the complete interpolating sequence), not `Λ`. Moreover
   `h` is not differentiable at the points of `Γ`, and not Lipschitz; the argument needs the jump
   bound of §2 (at most `1/q + 1` change over a unit interval). The "separation distance of `Γ`"
   is the constant `q`. Fix: §2 and the unit-interval argument of §3, where only `volume J < 1`
   is used. Not a mathematical gap, a misstatement of the mechanism.
2. **p. 799, `log |I|` and "sufficiently big `A`"** (certain). For `|I| ≤ 1` one has `log |I| ≤ 0`
   and `J` is not controlled; the statement `|J| ≤ C/|I|` needs `|I| > 1` (here `|I| ≥ L₀`) and
   `A ≥ 2‖h‖_*/c` (so that `|I|^{1 - cA/‖h‖_*} ≤ |I|^{-1}`). Small intervals are absorbed in `B`.
3. **p. 799, "`≥ n_Γ(b) - n_Γ(a) - 1 ≥ b - a + h(b) - h(a) - 1`"** (certain): correct; the first
   inequality uses half-open intervals `(a,b]` and `[γ_k, γ_{k+1})` as in §1 (`N - 1` interior
   gaps). The second is an *equality*.
4. **Corollary 1 does not state that `Γ` is separated** (certain), but Theorem A (Pavlov) is
   quoted for separated sequences. The paper never says so; see M04 for the proof (README §3.8).
   In Lean this forces the strong form `corollary1_strong`.
5. **Constants** (certain): the paper says "`C, c` absolute"; but `‖h‖_*` enters, so the final
   `A` depends on `‖h‖_*`, hence on `Λ` via `Γ`. Harmless; Landau's inequality has constants
   depending on `Λ`.
6. **Lean-specific:** `intervalMean`/`meanOsc` use interval integrals over `[a,b]`; `hJN` is stated
   for `LocallyIntegrable h` and `M > 0` bounding `meanOsc` over all bounded intervals; the
   `max M₀ 1` above makes `M` positive even if the BMO bound is `0`.

## Requested changes to M00

None. (Optional: a variant `corollary1` with `IsSeparated (Set.range γ)` in the conclusion would
remove the need for the extra `corollary1_strong`; the current `comparator` statement is true
and sufficient for the project.)
