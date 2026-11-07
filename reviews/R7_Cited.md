# R7 — Independent referee report: the cited results (P2, P4, P5)

Scope: `blueprint/PHASE2.md`; `blueprint/P2_DS_JN.md` with `FourierFrames/Cited/DSPerturbation.lean`
and `FourierFrames/Cited/JohnNirenberg.lean`; `blueprint/P4_DeBrangesFC.md` with the scaffold
`FourierFrames/Cited/DeBrangesFC.lean`; `blueprint/P5_Pavlov.md`; the `Prop`s in `FourierFrames/Defs.lean`
(l. 195 `TheoremC`, 242 `TheoremF`, 253 `PavlovBMO`, 259 `JohnNirenberg`, 267 `DSPerturbation`).

Sources checked: `literature/ArxivOrtega.tex` (Theorem A l. 200–207, Theorems C–F l. 330–410, the Claim
l. 640–676, the perturbation argument l. 741–753); Romanov, arXiv:1408.6022, Theorem 8 (p. 27) and
Appendix II (pp. 54–57), read in full. De Branges' book was not available to me, so Theorems 23 and 32 are
checked through the mathematics: I re-derived every step of Part C.1–C.8 and of Part F. Mathlib
(`.lake/packages/mathlib`) was grepped for Hilbert transform, BMO, Muckenhoupt, John–Nirenberg,
Calderón–Zygmund, Herglotz and Blaschke.

Kernel check (scratch file in the scratchpad, nothing in the repository touched):
```
#print axioms FF.johnNirenberg_holds           -- [propext, Classical.choice, Quot.sound]
#print axioms FF.dsPerturbation_of_paleyWiener -- [propext, Classical.choice, Quot.sound]
```

## Overall verdict

* **P2: accept.** Both statements are faithful. Each is a weaker form of its source, which is what
  "weakest form the paper uses" asks for. Both are proved with standard axioms only. The blueprint's
  mathematics checks line by line. Only documentation errors remain (findings 4–5).
* **P4: the mathematics of Part C is right**, including the formula for `E`, the `K(ζ,ζ) > 0` argument and
  the truth of `TheoremC`/`TheoremF`. The Romanov gap is real, and the writer's repair is correct. Five
  problems remain, none fatal:
  - C.9–C.12 re-prove Theorem D. A much cheaper route goes through P3 (finding 7).
  - The scaffold's `theoremD_holds` stub will clash with P3's theorem of the same name (finding 8).
  - F.4 is stated more strongly than its proof supports (finding 11).
  - The "reflection + one-sided Liouville" step of F.7 does not work as written; P3's entire-Pick lemma
    fixes it (finding 12).
  - The "do C only" recommendation needs its payoff stated honestly (finding 15).
* **P5: the verdict "not feasible, keep `hA`" is correct.** I looked for a cheaper route through
  `completeInterpolating_zero_set` and `H(E) = PW`. It removes two peripheral steps but not the core:
  `A₂`, the Poisson representation of `log|E|`, and conjugation on BMO. I give an example showing that
  the conjugate coupling cannot be avoided (finding 17). One step of the writer's route A is wrong as
  justified (finding 18).

No critical findings. Severity scale: critical, major, medium, minor, info.

---------------------------------------------------------------------------------------------------
## Part 1 — P2: `DSPerturbation` and `JohnNirenberg`

### 1. [info] `DSPerturbation` is faithful to the paper's use of [DS52, Lemma III]
*Evidence.* The paper (tex l. 741–746) uses: "if a separated `Γ` is sampling, then `{γ_k+δ_k}` is
sampling whenever all `γ_k+δ_k` are distinct and `δ_k → 0`", which "follows from Lemma III in [DS52] and
the elementary fact" about finitely many modifications. `Defs.lean:267` gives the first ingredient:
`∃ L > 0` such that every injective perturbation with `|δ| ≤ L` on `Γ` keeps the set sampling.
`Perturbation.lean:343` (`IsSampling.of_perturbation`, now sorry-free) adds the finite-modification step,
in exactly the paper's form (`δ → 0` at infinity, `InjOn`).

The `Prop` is weaker than DS in three harmless ways:
* `L` is only claimed to exist. DS give an explicit bound: `(e^{πL}-1)√B < √A`, i.e.
  `L < π⁻¹ log(1+√(A/B))`. This matches the blueprint and secondary sources; I could not open DS52 to
  confirm the lemma number.
* It assumes `Γ` separated. The classical Taylor argument needs only the upper frame bound `B`, applied
  to `f^{(n)}`.
* It assumes injectivity, which is forced by the set formulation: `sampleSum` sums over the image set.

*Fix.* None.

### 2. [info] `JohnNirenberg` is faithful to p. 799
*Evidence.* The paper applies `|J| ≤ C e^{-cA log|I|/‖h‖_*}|I|` to
`J = {t ∈ I : |h(t)-h_I| ≥ A log|I|}`. `Defs.lean:259` is exactly this, with `s = A log|I|` (`s > 0`
for `|I| > 1`, the only case used), the closed interval `Icc a b`, `≥` (`s ≤ |…|`), and `M` any positive
upper bound for the mean oscillation. Allowing any bound `M ≥ ‖h‖_*` is equivalent: `Landau.lean:170`
takes `M = max M₀ 1`.

The hypothesis `LocallyIntegrable h` is needed. Without it, Lean's junk value `∫ = 0` would make
`meanOsc` meaningless and the statement false. With it, the statement is the classical theorem, and the
constants `C = 2`, `c = log 2/4` are valid.

*Fix.* None.

### 3. [info] The blueprint's mathematics is sound
I re-checked both parts.

*Part A.*
* `|f(γ+δ)-f(γ)|² ≤ |δ|∫_{γ-|δ|}^{γ+|δ|}|f'|²` follows from FTC and Cauchy–Schwarz.
* Overlap count: at most `2L/d+1` points of a `d`-separated set in an interval of length `2L`.
* `L²` Bernstein: `‖f'‖² = 2π∫|t g|² ≤ π²‖f‖²`.
* With `L = min(d, A/(12π²))`, `π²L(2L/d+1) ≤ 3π²L ≤ A/4`. This gives `A' = A/4` and `B' = 2B + A/2`,
  which is what the Lean proof uses (`DSPerturbation.lean:330–401`).

*Part B.*
* Every selected cell has a non-stopping parent with average `≤ λ = 2M` (or the parent is `I₀`, with
  average `≤ M`). So the cell's average is `≤ 2λ`, and `|h_J - h_I| ≤ 4M`.
* Total length of the selected cells: `≤ ∫_I g / λ ≤ |I|/2`.
* Off the selected cells, `g ≤ λ` a.e. by Lebesgue differentiation along the dyadic cells containing
  `t` (closed balls of radius `(b-a)/2^{n+1}`, `K = 1`).
* Induction gives `|{|h-h_I| > 4Mk}| ≤ 2^{-k}|I|`.
* Last step: `k = ⌈s/4M⌉-1` gives `2·2^{-s/(4M)} = 2e^{-(log 2/4)s/M}`.

Route A is not DS's own argument: it uses finite overlap and FTC instead of a Taylor series. The
blueprint says so (Issues 2), and it is legitimate exposition.

### 4. [minor] `DSPerturbation` is unconditional only modulo P1
*Evidence.* `dsPerturbation_of_paleyWiener : PaleyWienerThm → DSPerturbation`. At the time of review,
`FourierFrames/Cited/PaleyWiener/{Part1,Part2,Spectrum,L2Fourier}.lean` still contain 32 `sorry` lines.
`JohnNirenberg.lean` imports only `Defs`, so `johnNirenberg_holds` is unconditional now.

*Fix.* In `PHASE2.md`, say that `theorem2_i`, `theorem2_i_of_densityBound` and `corollary2` lose `hDS`
only once P1 is closed (and lose `hE` only with P3).

### 5. [minor] Documentation errors in P2 / PHASE2
* `P2_DS_JN.md` l. 3–4 says "both compile with `lake env lean` (only `sorry` warnings)". This is stale:
  both are now sorry-free.
* `P2_DS_JN.md` l. 13 says "Used by … Theorem 2(ii) (`hJN`)". This is wrong. `JohnNirenberg` is used
  only by `Landau.lean:165` (`osc_bound_of_JN`, i.e. the Claim of §4), and `theorem2_ii` takes only `hPW`
  (`FFChallenge.lean:443`).
* `PHASE2.md` says "all phase-1 modules are proved except `Perturbation`/`Corollary2`". Both files now
  contain no `sorry`.
* `PHASE2.md` lists P3 as "to assess", but the P3 scaffold `Cited/DeBrangesDE/*` exists.
  `Cited/DeBrangesDE.lean` cites `blueprint/P3_DeBrangesDE.md`, which does not exist in `blueprint/`.

*Fix.* Update the text.

---------------------------------------------------------------------------------------------------
## Part 2 — P4: de Branges' Theorems C and F

### 6. [info] Part C.1–C.8 checks; `TheoremC` is true as stated
I re-derived each step:

* **C.5 (`kernel_identity`).** `T : H_ζ → H_ζ̄`, `Tf = f·(z-ζ̄)/(z-ζ)`, is well defined (H1 and
  injectivity) and onto (H1 at `ζ̄`: the preimage vanishes at `ζ` by continuity of the entire `ι g`). It
  is unitary. From `(Tf)(w) = ⟪K^{ζ̄}_w, Tf⟫ = ((w-ζ̄)/(w-ζ))⟪K^ζ_w, f⟫` one gets
  `K^{ζ̄}_w = T[(w̄-ζ)/(w̄-ζ̄)·K^ζ_w]`. This is exactly the multiplied identity in
  `DeBrangesFC.lean:77–82`. The cases `w = ζ` and `w = ζ̄` hold trivially (both sides are `0`), so the
  statement needs no extra hypothesis.
* **C.6–C.7 (formula for `E`).** With `ζ = i` the bracket is `(z+i)(w̄-i)-(z-i)(w̄+i) = -2i(z-w̄)`. Using
  `K(w,i) = conj K(i,w)` (C.3), `(K(i,·))^* = K(-i,·)` and `K(i,i) = K(-i,-i)` (C.4), this gives
  `K(w,z) = (i/2)(P(z)P̄(w) - P^*(z)P̄^*(w))/(z-w̄)` with `P = (z+i)K(i,z)/√K(i,i)`. So `E = √π P`
  reproduces `deBrangesKernel` (formula (1), `Defs.lean`). **Confirmed.**
* **Independent sanity check on `PW`** (the writer only checked formula (1) for `e^{-iπz}`, not `kernelE`).
  With `K(i,z) = sin π(z+i)/(π(z+i))` and `K(i,i) = sinh 2π/(2π)`, `kernelE` gives
  `E(z) = √(2/sinh 2π)·sin π(z+i)`, i.e. a unimodular multiple of `(e^{π}e^{-iπz} - e^{-π}e^{iπz})`. A
  direct computation gives `(i/2π)(E(z)Ē(w) - E^*(z)Ē^*(w))/(z-w̄) = sin π(z-w̄)/(π(z-w̄))`. So the
  normalisation `√π` is right.
* **C.2 (`K(ζ,ζ) > 0` via (H1)).** If `k_ζ = 0`, every element vanishes at `ζ`. Take `h ≠ 0` of finite
  order `m ≥ 1` at `ζ`. The (H1) image `g` has `‖g‖ = ‖h‖ ≠ 0` and order `m-1` at `ζ`, because
  `(z-ζ̄)` does not vanish at `ζ`. Iterating reaches order `0`, a contradiction. Sound.
* **C.8.** `K(w,w) = (|E(w)|²-|E^*(w)|²)/(4π Im w) > 0` on `ℂ₊`, so `E` is strict and zero-free there.
* **Truth of `TheoremC`.** The conclusion asks only for the closed class `IsHB`. `heNormSq` agrees with
  the `H²` norm of `f/E` because `f/E` has no poles on `ℝ`. The writer's example `{f ∈ PW : f(0) = 0}`
  correctly shows that `E` can have real zeros. Real zeros are intrinsic: any `E` with `H(E) = H` must
  vanish at the common real zeros of `H`, since `K_E(t,t) = φ'(t)|E(t)|²/π > 0` where `E(t) ≠ 0`.
  I agree that the statement is true.

### 7. [medium] C.9–C.12 re-prove Theorem D; route C through P3 instead
*Evidence.* After C.8, the blueprint proves the following from scratch, for `E` in the closed class:
* `K(w,·) ∈ H(E)` and the Gram identity (C.9);
* the isometric extension (C.10);
* the reproducing property in `H(E)` (C.11);
* equality of the spaces (C.12).

This is Theorem D plus a completeness argument, i.e. what P3 is building (`Cited/DeBrangesDE/Kernel.lean`:
`memHE_deBrangesKernel`, `heInner_kernel_nonreal`; `Space.lean`: `memHE_of_cauchy`). C.11 is also left
muddled (l. 108–117: "??", "hmm"). Its clean form has two terms, and both are P3 lemmas:

* `conj(K(w,t)/E(t)) = (-i/2π)(E(w) - E^*(w)·conj Θ(t))/(t-w)`.
* First term: `∫ (f/E)(t)/(t-w) dt = 2πi (f/E)(w)` (`IsH2Cont.cauchy_upper`).
* Second term: on `ℝ`, `(f/E)·conj Θ = f/E^* = conj(f^*/E)`, so it equals
  `∫ conj((f^*/E)(t))/(t-w) dt = 0` (`IsH2Cont.cauchy_conj_upper`).

*Cheaper route (RKHS uniqueness).* By C.7, `ι(k_w) = K_E(w,·)` as entire functions. With Theorem D for
this `E`:
* the Gram matrices `⟪k_w,k_v⟫_H` and `⟨K_E(w,·),K_E(v,·)⟩_E` coincide, so `ι` is isometric on
  `span{k_w}`;
* the span is dense in `H`: `h ⊥ k_w` for all `w` gives `ι h = 0` on `ℂ∖ℝ`, hence `ι h = 0`;
* by completeness of `H(E)` (`memHE_of_cauchy`) and continuity of evaluation at nonreal points,
  `ι(H) ⊆ H(E)` isometrically;
* if `f ∈ H(E)` is orthogonal to `ι(H)`, then `f(w) = ⟨f, K_E(w,·)⟩_E = 0` for nonreal `w`, so `f = 0`.

This replaces C.9–C.12 by roughly 300–500 lines of Hilbert-space bookkeeping.

*Obstacle.* P3's kernel layer assumes `IsStrictHB E` and no real zeros (`Kernel.lean:86, 114–149`,
`Space.lean:41`, `isH2Cont_of_memHE` with `h0`). Theorem C's `E` is strict but may have real zeros, and
this is why the writer rejected D (P4 l. 105).

*Fix.* Generalise P3's internal kernel lemmas (not the frozen `TheoremD`) to strict `E` with real zeros.
Two facts are needed:
* `f ∈ H(E)` vanishes at a real zero `t₀` of `E` to at least its order. This is an order version of
  `not_isH2Upper_div_of_zero`, and it makes `f/E` `IsH2Cont`.
* `Θ = E^*/E` extends analytically across `ℝ` with `|Θ| = 1`, since `E` and `E^*` have the same real
  zeros with the same orders.

The P3 Cauchy layer (`Cauchy.lean`) is already stated for general `IsH2Cont F` and needs no change. The
C-specific cost is then about 1.5–2.5k lines (C.1–C.8, uniqueness, real-zero generalisation), against the
writer's 2.5–4k from scratch. The writer's 2.5–4k is plausible for the from-scratch route, but it counts
the `H²` Cauchy machinery that P3 already budgets.

### 8. [medium] Name clash: scaffold stub `theoremD_holds`
*Evidence.* `DeBrangesFC.lean:25` declares `theorem FF.theoremD_holds : TheoremD := by sorry`, and
`Cited/DeBrangesDE.lean:27` declares `FF.theoremD_holds` too. Today `FourierFrames.lean:27` imports
`Cited.DeBrangesFC` but not `Cited.DeBrangesDE`, so nothing breaks yet. Adding P3 to the root import, or
importing both anywhere, gives a duplicate-declaration error. Meanwhile, every Part F lemma that uses the
stub carries `sorryAx`.

*Fix.* `import FourierFrames.Cited.DeBrangesDE` in `DeBrangesFC.lean` and delete the stub. There is no
cycle, because D does not use C or F.

### 9. [info] `TheoremF` is true as stated
* `p ≥ 0` is slack: Romanov's Theorem 8 (⇒) gives the representation (66) with no `c₀ y` term, i.e.
  `p = 0`.
* The extra hypotheses (strict, no real zeros) only weaken the statement.
* `μ` is automatically locally finite: every real `t₀` has some `f` with `f(t₀) ≠ 0`, since
  `K(t₀,t₀) > 0`, and `∫|f/E|² dμ < ∞`.
* `poissonInt μ z ≠ ∞` follows from F.1.
* `E - E^*A ≠ 0` on `ℂ₊` since `|E^*A| ≤ |E^*| < |E|`.

I agree with the writer.

### 10. [medium] Romanov's gap is real; the writer's repair is correct, but reword it
*Evidence (Romanov p. 54–55).*
* He writes: "if `S(z) = 0` … the r.h.s. in (66) is 1, which implies `Ξ(z) = 0`". This is false as
  stated: `Re((1+Ξ)/(1-Ξ)) = 1` holds exactly on the horocycle `|Ξ - 1/2| = 1/2`, so `Ξ(z) = 0` also needs
  `Im g(z) = 0`.
* The free real parameter of `g` is fixed only later ("Choose this constant to be zero"), by decay at
  `i∞`.

The two requirements (`Im g = 0` on `Z`, `Im g → 0` at `i∞`) are *a priori independent*, not
"incompatible" as P4 §4.1 says. The writer's repair closes the gap:

* **F.3.** Polarising the isometry on `K_w, K_v` with `w, v ∈ Z` gives `∫dμ/((t-v̄)(t-w)) = 2πi/(w-v̄)`.
  I checked the conventions of `cauchy_pairing_zero` against the reproducing property. With the
  `herglotzG` convention,
  `∫dμ/((t-w̄₀)(t-z)) = iπ(g(z) + conj g(w₀))/(z-w̄₀)`,
  so `g(w) + conj g(v) = 2`: `Re g = 1` on `Z` and `Im g` is constant on `Z`.
* **F.4 / F.9.** Pairing `K_{w₀}` with `K_z`, `Im z → ∞`, gives `lim g = 2 - conj g(w₀)`, so the decay
  constant equals the constant on `Z`.

"Root of `W`" should indeed read "root of `W^*`": `‖K_w‖² = |W(w)|²/(4π Im w)` requires `W^*(w) = 0`.
Confirmed.

*Multiplicities* (P4 §5, "unchecked"). The gap can be closed with derivative kernels on one side only.
Let `w₀` be a zero of `E^*` of order `m`. For `k < m`, the kernel of `f ↦ f^{(k)}(w₀)` divided by `E`
has no `Θ`-term, because the derivatives of `Ē^*` up to order `k` vanish at `w₀`. Pairing it with
`K_{w₀}` gives `∂_z^k[(g(z) + conj g(w₀) - 2)/(z-w̄₀)]|_{z=w₀} = 0` for `k < m`. Together with
`g(w₀) = 1`, `g - 1` has a zero of order `m` at `w₀`, i.e. so does `Ξ`. Medium bookkeeping, no
conceptual risk.

*Fix.* Replace "incompatible" by "independent a priori". Write the multiplicity argument into F.3/F.9.

### 11. [medium] F.4 (`cauchy_pairing_general`) is stated more strongly than its proof supports
*Evidence.* `DeBrangesFC.lean:171–177` (`cauchy_pairing_general`) claims the error bound `C|Θ(z)|/√(Im z)` for all `Im z ≥ 1`. The
blueprint's proof uses Cauchy–Schwarz, `∫dμ/|t-z|² = πP(z)/y` and "`P(z) ≤ 2` by F.5". But F.5 (and its
proof) only gives `P ≤ (1+s)/(1-s)`, `s = |Θ(z)|`, which is bounded only where `s ≤ 1/2`.

On `{Im z ≥ 1}`, `P` need not be bounded. For the Clark measure `σ_α` (an isometric measure for a
non-exceptional `α`), `P(z) = (1-|Θ|²)/|α-Θ|²`, and `|Θ(x+i)|` can approach `1` when the zeros of `E^*`
are sparse. So the lemma is unproved as stated, and may be false.

*Fix.* Add the hypothesis `‖thetaFn E z‖ ≤ 1/2`, as in F.5. F.9 uses F.4 only for `y → ∞` with
`|Θ(z)| ≤ e^{-ay}`, so nothing downstream changes.

### 12. [medium] F.7(iii): the reflection step does not end with Liouville; finish it with P3's entire-Pick lemma
*Evidence.* P4 l. 159: a non-positive harmonic `u = log|Θ/B|` on `ℂ₊` with zero boundary values, oddly
reflected, is `≤ 0` on `ℂ₊` and `≥ 0` on `ℂ₋`. It has no one-sided bound on `ℂ`, and Mathlib's
`Harmonic/Liouville.lean:49` covers only *bounded* harmonic functions. So "Liouville with a one-sided
bound" does not apply.

The reflection idea itself is sound if finished differently:
* Let `U` be the odd extension (entire harmonic), `U = Re H` with `H` entire
  (`HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq`, used in the Liouville file).
* Set `G := -iH`. Then `G` is real on `ℝ`, so `G(z̄) = conj G(z)`, and `Im G = -U ≥ 0` on `ℂ₊`. That is,
  `G` is an entire Pick function.
* An entire Pick function is `az + b` with `a ≥ 0`, so `u = -ay`.

P3 already budgets exactly this lemma: `EntireHerglotz.lean:56`, `im_div_im_eq`. For entire `h` with
`h(z̄) = conj h(z)` and `Im h ≥ 0` on `ℂ₊`, it gives `Im h(w)/Im w` constant, via the half-disc Poisson
kernel. Equivalently, reflect the holomorphic `Φ = Θ/B` itself: `Φ(z) := 1/conj Φ(z̄)` on `ℂ₋` gives a
zero-free entire `Φ = e^H`, then apply the same step.

*Limits in F.7 and F.8.* The limsup version of Phragmén–Lindelöf can be avoided by ordering the limits.
For a *finite* Blaschke product `B_n` with zeros `x_j + iy_j`, `|B_n(x+iδ)| ≥ ∏ (y_j-δ)/(y_j+δ)`,
uniformly in `x`. So apply Mathlib's bounded half-plane PL (`right_half_plane_of_bounded_on_real`,
`PhragmenLindelof.lean:717`, after rotation) to `Ξ e^{-ia'z}/B_n` on `{Im z > δ}`. That function is
bounded and `DiffContOnCl` there, and the "bounded on the real ray" hypothesis is automatic. Then let
`δ → 0`, `n → ∞`, `a' → a`. This gives `|Ξ| ≤ e^{-ay}|B| = |Θ|` directly, with constant 1 and without
dividing by `Θ`. It merges F.7's division clause and F.8.

*Fix.* Replace "Liouville for harmonic functions with a one-sided bound" by "entire Pick function is linear
(P3, `im_div_im_eq`)". Add a reflection lemma, roughly 0.3–0.5k lines: odd reflection of `u`, or Schwarz
reflection of `Φ`, which needs `B` continuous up to `ℝ`. Restructure F.7(division) and F.8 as above.

### 13. [minor] F.9, case `a = 0`: "`Z` is then infinite" is false
If `E` is a polynomial with zeros in `ℂ₋`, `Θ` is a finite Blaschke product with `a = 0`. Only `Z ≠ ∅`
is used, and that holds since `Θ` is nonconstant. *Fix.* Delete "is then infinite".

### 14. [info] F.1, F.2, F.3, F.5, F.6 check
* F.1: `|K(i,t)/E(t)| ≥ (|E(i)|-|E^*(i)|)/(2π√(1+t²))`.
* F.2: the real part of the regularised Cauchy kernel is the Poisson kernel; the `t/(1+t²)` term is
  imaginary.
* F.5: `(1-s)²P ≤ 1-s² ≤ (1+s)²P` gives `|P-1| ≤ 4s` for `s ≤ 1/2`.
* F.6: gradient estimate on unit discs plus Cauchy–Riemann. It even holds with `a' = a`.

### 15. [medium, scope] "Do C only": defensible, but state what it buys
*Evidence (`FFChallenge.lean`).* `hC` appears in five places:
* `theorem1_necessity`, `theorem1`, `corollary1`, `landau_inequality`: all four also need `hF`;
* `completeInterpolating_zero_set`: needs `hC` and `hD`.

So proving C (with P1 and P3) makes exactly one paper statement unconditional, the Remark on p. 797. No
part of Theorem 1's necessity becomes unconditional without F.

*Estimates.*
* C: 2.5–4k is plausible for the writer's route; about 1.5–2.5k on top of P3 via finding 7.
* F: 5–8k is plausible, plus the reflection lemma of finding 12. F's half-plane Blaschke and
  inner-factorisation infrastructure is reused nowhere else in the project. Its special-case fallback
  (P4 §5, `E` of exponential type) cannot discharge the frozen general `Prop`.

*Fix.* Say this in `PHASE2.md`. Schedule C *after* P3 and through D, and keep `hF`.

---------------------------------------------------------------------------------------------------
## Part 3 — P5: `PavlovBMO`

### 16. [info] Statement faithful; Mathlib inventory confirmed
`PavlovBMO` (`Defs.lean:253`) is the forward half of Theorem A, weakened to `h ∈ BMO`, which is all the
Claim uses (tex l. 650: "we will only need the fact that `h ∈ BMO`"). `LocallyIntegrable` is automatic
for separated `Γ`.

My grep of Mathlib finds:
* no Hilbert transform, BMO, Muckenhoupt, Calderón–Zygmund or John–Nirenberg;
* Herglotz–Riesz and Poisson kernels for *discs* only (`Analysis/Complex/Poisson.lean`);
* *finite* Blaschke products for discs only (`CanonicalDecomposition.lean`).

### 17. [medium] Route B is undersold, but there is no cheap route; the verdict stands
The task asks whether `φ_E/π - t ∈ BMO` follows cheaply from `H(E) = PW`, given
`completeInterpolating_zero_set`. What route B *does* buy:

* **The counting function is trivial.** `Γ` is exactly a level set `{φ_E ∈ α+πℤ}` of a continuous
  increasing phase, so `|n_Γ(t) - (φ_E(t)-φ_E(0))/π| ≤ 1`. This removes route A's step 2 (the generating
  function) *and* step 6(ii) (see finding 18).
* **`φ'_E ≍ |E|^{-2}` is cheap and already proved.** `K_E(x,x) ≍ K_PW(x,x) = 1` by norm equivalence, and
  `φ'|E|² = πK_E(x,x)`. The project has this as `HEEqPW.phaseDeriv_mul_sq_ge/le`
  (`HB/DeBranges.lean:216, 277`).

What remains, and is the whole difficulty:
1. `|E|² ∈ A₂(ℝ)` from the norm equivalence (the necessity half of Hunt–Muckenhoupt–Wheeden, in
   Lyubarskii–Seip form).
2. `log|E| ∈ BMO` (elementary from `A₂`).
3. The representation `φ_E(x) - πx = -H̃[log|E|](x) + c`. This needs `E` in the Cartwright class and
   Nevanlinna/boundary theory in `ℂ₊`.
4. Conjugation maps BMO to BMO, or `L^∞` to BMO plus a Helson–Szegő decomposition.

**The coupling of step 3 cannot be bypassed.** Information on `φ'` alone, even `φ' ∈ A₂`, does not give
BMO. Take `v(t) = 1 + ½ sin log(1+|t|)`. It is bounded above and below (so in `A₂`), but
`∫_0^t (v-1) ≍ t·(oscillating factor)` is not in BMO. What forces BMO is that `log φ' = -2 log|E| + O(1)`
and `φ - πx` are harmonic conjugates. The brief's suggestion ("`|E(x)|²` comparable to a weight with
bounded conjugate behaviour") is precisely the Helson–Szegő form `log|E|² = u + ṽ`, `‖v‖_∞ < π/2`. That
is the hard direction of Helson–Szegő, not a shortcut.

Route B also makes `PavlovBMO` conditional on `hC` and `hD` (`Corollary1.lean:270`). Net cost: at least
4–5k lines even on route B. The writer's 6–10k is the right order of magnitude.

Finally, replacing `hA` by a weaker `Prop` (the two-sided bound `osc_I h ≤ A log|I| + B`) would amount to
assuming Landau-type estimates and would empty the Claim. Not recommended.

*Fix.* In P5 §2, replace "Not cheaper" by: "Cheaper on the periphery (counting function, `φ' ≍ |E|^{-2}`,
both available), identical on the core (`A₂`, Poisson representation, BMO conjugation)." Keep the
verdict.

### 18. [minor] Route A, step 6(ii) is wrong as justified
*Evidence.* P5 l. 50 claims `|π n_Γ(x) - arg_x G(x+i)| ≤ C`, because "each zero changes arg by `π ± O(1)`".

Exactly, `d/dx arg G(x+i) = -Σ_γ 1/((x-γ)²+1) = -π P_1[dn_Γ](x)`. So `arg G(x+i) = -π P_1[n_Γ](x) + c`,
and `π n_Γ + arg G(x+i) = π(h - P_1[h]) + c`. The per-zero `O(1)` errors have a tail `~ Σ 1/(x-γ)`, which
is a conditionally convergent Hilbert-type sum, not `O(1)`. The bound holds a posteriori, once `h ∈ BMO`,
so using it inside the proof is circular. This is why Theorem A is phrased with `P_1[h]`. Route A needs an
extra lemma: for separated `Γ`, `P_1[h] ∈ BMO ⇒ h ∈ BMO`.

Step 3's weight text ("`|G(x+i)|^{-2}`-type weight (the correct weight is `|G(x+i)|²`…)") is also
garbled.

*Fix.* Correct the step. Note that route B avoids it (finding 17).

---------------------------------------------------------------------------------------------------
## Recommendation for the phase-2 scope

| module | status / action | `FFChallenge` theorems that lose the hypothesis |
|---|---|---|
| P2 `DSPerturbation`, `JohnNirenberg` | **accept** (doc fixes, findings 4–5) | `hJN` in `landau_inequality` can be discharged now by `johnNirenberg_holds` (the statement still carries the parameter). `hDS` in `corollary2`, `theorem2_i`, `theorem2_i_of_densityBound` can be discharged once P1 is closed |
| P1 + P3 (D, E) | finish first: largest payoff | `theorem1_sufficiency`, `corollary2`, `theorem2_i(_of_densityBound)`, `logExample_isCompleteInterpolating`, `landau_sharp` become unconditional |
| P4-C | **do, after P3**, via D and RKHS uniqueness (finding 7). Generalise P3's kernel layer to `E` with real zeros. Fix the stub clash (finding 8) | `completeInterpolating_zero_set` becomes unconditional. No part of Theorem 1 does |
| P4-F | **defer, keep `hF`**. If ever attempted, first fix F.4 (finding 11) and restructure F.7/F.8 (finding 12); budget 5–8k plus about 0.5k | — (`theorem1_necessity`, `theorem1`, `corollary1`, `landau_inequality` stay conditional on `hF`) |
| P5 `PavlovBMO` | **keep `hA`** (finding 17) | — (`landau_inequality` stays conditional on `hF`, `hA`) |

End state of this plan: every cited `Prop` except `TheoremF` and `PavlovBMO` is discharged. The final
conditional theorems are exactly Theorem 1 (necessity half), Corollary 1, and the Claim (Landau via
John–Nirenberg). They should be presented as conditional on these two named, faithful hypotheses.

## Summary

* P2 is done and correct. The `DSPerturbation` and `JohnNirenberg` statements are faithful, weaker-than-source
  forms of the cited results, and their proofs use standard axioms only. The blueprint's dyadic and
  `L²`-Bernstein mathematics checks. Only documentation errors remain, plus the dependence of
  `DSPerturbation` on the unfinished P1.
* P4: the formula `E = √π(z+i)K(i,z)/√K(i,i)` and the `K(ζ,ζ) > 0` argument are correct; I checked the
  formula independently on `PW`. `TheoremC` and `TheoremF` are true as stated. The Romanov gap is real
  and the writer closes it correctly; multiplicities can be handled with one-sided derivative kernels.
  Three problems need fixing: F.4 is overstated, F.7's "reflection + one-sided Liouville" step must end
  instead with P3's entire-Pick lemma, and the `theoremD_holds` stub clashes with P3. Part C should be built on P3's Theorem D plus RKHS uniqueness
  rather than re-proving D; that brings it to about 1.5–2.5k extra lines. "C only" is the right call, but
  it unlocks only `completeInterpolating_zero_set`.
* P5: "not feasible, keep `hA`" is right. Route B via `H(E) = PW` makes the counting step trivial and
  `φ' ≍ |E|^{-2}` is already in the project. Even so, `A₂`, the Poisson representation of `log|E|` and
  BMO conjugation remain, and the example `v = 1 + ½ sin log(1+|t|)` shows the conjugate coupling cannot be
  bypassed. Step 6(ii) of route A is wrong as justified.
