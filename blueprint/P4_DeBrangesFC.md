# P4 — de Branges' Theorems C (book Thm 23) and F (book Thm 32)

**Status: Part C proved; Part F deferred** (Part C merged 2026-11-07 from branch `impl/cited-p4`). Part C has no
`sorry`; `#print axioms FF.theoremC_holds` gives `[propext, Classical.choice, Quot.sound]`. `theoremC_holds` is among
the 39 theorems accepted by comparator, and `FourierFrames/Unconditional.lean` uses it. Part C has 1046 lines in 4
files: `DeBrangesFC.lean` 269, `Analytic` 248, `Space` 140, `Kernel` 389 (estimate in §0: 1.6–2.5k).
Implementer's notes: `impl_notes/cited-p4.md`. Referee report on the Part C blueprint and scaffold:
`reviews/R10_TheoremC.md`. For Part C it found no false statement (0 critical, 0 major, 5 minor), and it found one
critical issue in Part F (below). The statement blocks below match the code, with `sorry` in place of the proofs
(checked mechanically for all 52 declarations). Six of them take `[CompleteSpace H]` explicitly (the *Implemented:*
note of §1.4). The code adds helper lemmas not listed here (`impl_notes/cited-p4.md`). Part F (Theorem 32) is
deferred. Its statements form a scaffold with `sorry`, and its `division_lemma` (F.8) is **false as stated** (R10
finding 1, with a Lean disproof; §2).

**Lean files.**
* `FourierFrames/Cited/DeBrangesFC.lean`: `UHP`, `thetaFn`, `kernelSpan`, C.9–C.14 (§1.6) and the assembly
  `theoremC_holds : TheoremC` (§1.7). It is in the default target `FourierFrames`.
* Subfiles (`FourierFrames/Cited/DeBrangesFC/`): `Analytic.lean` (§1.1–1.2), `Space.lean` (§1.3) and `Kernel.lean`
  (`DBAxioms`, `IsKernelFamily`, `kernelE`, C.1–C.8: §1.4–1.5). Import chain:
  `Cited/DeBrangesDE → Analytic → Space → Kernel → DeBrangesFC`.
* `FourierFrames/Cited/DeBrangesFC/PartF.lean`: Part F (§2): `IsIsometricMeasure`, `herglotzG`, F.1–F.8 and
  `theoremF_holds`, all `sorry`. It imports `DeBrangesFC.lean` and is built only by the separate Lake target
  `FourierFramesScaffold`, so `import FourierFrames` brings no `sorry` into scope.

R10's minor findings were handled as follows:
* finding 2: the Mathlib name `analyticOrderAt_eq_top_iff_eq_zero` is namespaced; fixed below and in the code;
* finding 3: the stale P3 text is updated, and `heInner_self_of_isHB` is P3's `heInner_self`;
* finding 4: the optional simplification of `mem_range_of_memHE` was not adopted;
* finding 5: the draft `Analytic.lean` duplicated declarations of the scaffold; the scaffold copies were removed
  when the scaffold was split into the files above.

**Sources:** de Branges, *Hilbert spaces of entire functions* (1968), Thms 19, 23, 32;
Romanov, *Canonical systems and de Branges spaces* (arXiv 1408.6022), Appendix II = proof of the
direction of "Theorem 8" that is our `TheoremF` (his "⇒"); Remling's book for the kernel route to Thm 23.
Referee reports: `reviews/R7_Cited.md` (findings 6–15), `reviews/R9_DeBrangesDE.md` (F4, F5),
`reviews/R10_TheoremC.md` (Part C; truth of the Part F statements).

**Depends on.**
* P3 (`Cited/DeBrangesDE`, imported and proved; P4 uses its lemmas as black boxes, and only those that do **not**
  assume `∀ x, E x ≠ 0`):
  * `Cauchy.lean`: `IsH2Cont`, `IsH2Cont.lintegral_real_lt_top`, `IsH2Cont.memLp_real`, `IsH2Cont.lintegral_line_le`;
  * `Kernel.lean`: `heInner`, `kernelNum`, `heInner_eq_integral_div`, `deBrangesKernel_mul`,
    `differentiable_deBrangesKernel`, `deBrangesKernel_diag`, `memHE_deBrangesKernel_of_isHB`,
    `heInner_kernel_upper_of_isH2Cont`;
  * `Space.lean` (the `h0`-free ones only): `MemHE.add`, `MemHE.const_mul`, `memHE_zero`, `memHE_fstar`,
    `heNormSq_fstar`, `heInner_conj_symm`, `heInner_smul_left`, `heInner_smul_right`, `heInner_self` (it lost its
    `h0` in the P3 implementation; R10 finding 3);
  * Part F: `theoremD_holds` can be passed for the explicit hypothesis `hD : TheoremD`.
* P3 lemmas **not usable** here because they assume `h0 : ∀ x : ℝ, E x ≠ 0`, while the `E` of Theorem C may have
  real zeros: `isH2Cont_of_memHE`, `MemHE.heNormSq_lt_top`, `integrable_heInner`, `heInner_kernel_upper`,
  `heInner_kernel`, `memHE_deBrangesKernel`, and the rest of `Space.lean` §4.2–4.4
  (`heInner_add_left`, `norm_heInner_sq_le`, `MemHE.lintegral_line_le`, `memHE_of_cauchy`, …). P4 states its own
  `_of_isHB` replacements (§1.3); if P3 later weakens `h0` to `IsHB E`, they become redundant, not wrong.
* Project: `HB/H2` (`IsH2Upper.congr`, `measurable_line_sq`, `not_isH2Upper_div_of_zero`), `HB/Comparable`
  (`lintegral_real_le_of_isH2`), `HB/DeBranges` (`countable_real_zeros`), `HB/MeanValue` (`enorm_sq_eq_ofReal`),
  `HB/Basic` (`fstar_fstar`, `fstar_add`, `fstar_const_mul`, `norm_fstar`, `Differentiable.fstar`).
* Does **not** use `hPW` or any other cited `Prop`: Part C is unconditional modulo P3.

**Used by:** `Theorem1/Necessity` (`exists_E` uses `hC`, `exists_herglotz_data` uses `hF`). By R7-15, `hC` alone
(with P1 and P3) makes only `completeInterpolating_zero_set` unconditional; every other use of `hC` also needs `hF`.
*Implemented* (`Unconditional.lean`): `completeInterpolating_zero_set_unconditional`; `theorem1_necessity_of_theoremF`,
`theorem1_of_theoremF`, `corollary1_of_theoremF` keep `hF`, and `landau_inequality_of_theoremF_pavlov` keeps `hF`, `hA`.

**Blueprint history (2026-11-07).** Part C rewritten on the route recommended by R7 finding 7 (through P3, RKHS uniqueness),
with real zeros of `E` handled as in R9 F5. Part F unchanged except R7-11 (F.4 now assumes `‖Θ(z)‖ ≤ 1/2`); the
stub `theoremD_holds` (R7-8) is deleted and P3 imported.

Notation: `K(w,z) := ι(k w)(z)`; `E^*(z)=conj E(conj z)`; `Θ=E^*/E`; `UHP = ℂ₊ = {Im z>0}`; `⟨f,g⟩_E = heInner E f g
= ∫_ℝ f conj g/|E|²` (linear in `f`, conjugate-linear in `g`); `‖f‖²_E = heNormSq E f` (an `ℝ≥0∞`).
Convention of Mathlib/the project: `⟪x,y⟫` is conjugate-linear in `x`; `ι h ζ = ⟪k ζ, h⟫`.
Hence the Gram identity reads `⟨ι x, ι y⟩_E = ⟪y, x⟫` (order swapped), and the key form used below is
`⟨ι h, ι x⟩_E = ⟪x, h⟫` (`heInner_iota_of_mem_kernelSpan`).

---------------------------------------------------------------------------------------------------
## 0. Summary and honest feasibility

| | route | new infrastructure | est. size | verdict |
|---|---|---|---|---|
| **C** | kernel of `H` from the axioms (C.1–C.8) → `ι(k_w) = K_E(w,·)` for an explicit strict `E` → P3's `K_w ∈ H(E)` and reproducing formula (with real zeros, §1.2–1.3) → RKHS uniqueness: isometric on the span of kernels, Fatou extends to a contraction, reproducing formula upgrades to an isometry, Riesz in `H` gives onto (§1.6) | none beyond P3: Riesz (`InnerProductSpace.toDual`), orthogonal complements, meromorphic normal form (`toMeromorphicNFOn`) are in Mathlib; **no** inner-product-space structure and **no** completeness of `H(E)` needed | **1.5–2.5 k lines on top of P3** (P3's Cauchy + Kernel layer, ≈ 2–2.5 k, is budgeted in P3) | feasible, moderate risk |
| **F** (scaffold; F.8 false as stated, R10) | Romanov's Appendix II (repaired): Herglotz transform `g` of `μ`, `Ξ=(g-1)/(g+1)`, `A = Ξ/Θ`; `|A| ≤ 1` by Blaschke division + Phragmén–Lindelöf | Herglotz transform (explicit, easy), factorization `Θ = e^{i(az+θ)}B` of a meromorphic inner function with Blaschke division (**big, absent from Mathlib**), kernel computations, Phragmén–Lindelöf (Mathlib has half-plane versions) | 5–8 k lines (+0.3–0.5 k, R7-12) | deferred; feasible only as a long project |

Size of Part C by group (Lean lines, estimates):

| group | lemmas | est. lines | main risk |
|---|---|---|---|
| §1.1 helpers | `eq_of_eqOn_upper`, `analyticOrderAt_eq_of_mul_div`, `lintegral_line_le_liminf` | 80–150 | low |
| §1.2 real zeros | `IsHB.ae_ne_zero`, `analyticOrderAt_le_of_isH2Upper_div`, `divExt` + 5 lemmas | 300–500 | moderate: global factorisation at a real zero; first use of Mathlib's meromorphic normal form in the project |
| §1.3 `H(E)` with real zeros | 10 `_of_isHB` lemmas | 250–400 | low–moderate: integrability / Hölder plumbing |
| §1.4 C.1–C.4 | 7 | 250–400 | low: Riesz, order induction, polarization |
| §1.5 C.5–C.8 | 7 | 400–650 | moderate: the unitary `T` of (H1) and the `conj`/`sqrt` algebra of `kernel_mul_eq` |
| §1.6 C.9–C.14 + assembly | 9 + 1 | 300–450 | low–moderate |
| **total** | 43 | **≈ 1.6–2.5 k** | **moderate; no missing deep theory** |

This agrees with R7's 1.5–2.5k. It depends on P3's `Cauchy.lean`/`Kernel.lean` (in particular
`heInner_kernel_upper_of_isH2Cont`, `memHE_deBrangesKernel_of_isHB`, the kernel algebra, and the `IsH2Cont` line and
boundary bounds), which were proved first. Nothing else in P3 (Theorem E, completeness of `H(E)`) is needed.
*Implemented:* 1046 lines, below the estimate. By group: `Analytic` 248 (§1.1–1.2), `Space` 140 (§1.3), `Kernel` 389
(§1.4–1.5), and `DeBrangesFC.lean` 269 (§1.6–1.7 and the shared definitions).

Special cases for the paper: `PW` with the sampling norm (C) and `μ=∑|E(λ)|²δ_λ` with `H(E)=PW` (F).
(a) For C nothing simplifies: one still needs the kernel/`H²` machinery.  (b) For F the measure is discrete
and separated, so local finiteness and the integrability (F.1) are trivial, but the factorization of
`Θ` and the Herglotz/Blaschke-division part are unchanged.  There is **no** substantially cheaper route to
`theorem1_necessity` without `hC, hF`.

---------------------------------------------------------------------------------------------------
## 1. Part C (Theorem 23)

Let `H, ι` satisfy (H1)–(H3) and `H ≠ 0` (structure `DBAxioms`).

### 1.0 Route

1. **Kernel of `H` (C.1–C.4).** Riesz gives `k ζ` with `ι h ζ = ⟪k ζ, h⟫` for nonreal `ζ`; `‖k ζ‖ > 0` by
   iterating (H1); `K(w,z) = conj K(z,w)`; (H3) gives a conjugate-linear isometric involution `S` with
   `S(k w) = k w̄`, so `K(w,·)^* = K(w̄,·)`.
2. **The function `E` (C.5–C.8).** (H1) gives a unitary `T : {f(ζ)=0} → {f(ζ̄)=0}`, `Tf = f(z-ζ̄)/(z-ζ)`; comparing the
   reproducing kernels of the two hyperplanes gives the identity (★); with `ζ = i` it solves to
   `K(w,z) = (i/2π)(E(z)conj E(w) − E^*(z)conj E^*(w))/(z − w̄)`, `E = √π (z+i)K(i,z)/√K(i,i)`. So
   `ι(k w) = deBrangesKernel E w` as functions, and `K(w,w) > 0` gives `E` strict.
3. **Real zeros (§1.2–1.3).** `E` may vanish on `ℝ` (e.g. `H = {f ∈ PW : f(0) = 0}`). For `f ∈ H(E)`, `f` vanishes at a
   real zero of `E` at least to its order, so `f/E` has an `IsH2Cont` extension `divExt E f` (Mathlib's meromorphic
   normal form). With it: `‖f‖_E < ∞`, line bounds, Cauchy–Schwarz, and the reproducing formula at `w ∈ ℂ₊`
   (P3 `heInner_kernel_upper_of_isH2Cont`).
4. **RKHS uniqueness (C.9–C.14), without completeness of `H(E)`.** Let `S₀ = span{k w : w ∈ ℂ₊}`.
   * `ι x ∈ H(E)` and `⟨ι h, ι x⟩_E = ⟪x, h⟫` for `x ∈ S₀` whenever `ι h ∈ H(E)` (reproducing formula + span induction);
     so `ι` is isometric on `S₀`.
   * `S₀` is dense in `H`: its orthogonal complement is `0` (`h ⊥ k w ∀ w ∈ ℂ₊ ⇒ ι h = 0` on `ℂ₊` ⇒ `ι h = 0`).
   * *Contraction:* for `h ∈ H` take `x_n ∈ S₀`, `x_n → h`. (H2) gives `ι x_n → ι h` pointwise on `ℂ ∖ ℝ`; Fatou on each
     line `Im z = y` gives `∫|ι h/E|² ≤ liminf ‖x_n‖² = ‖h‖²` (same for `(ι h)^*`), so `ι h ∈ H(E)`, and Fatou at the
     boundary gives `‖ι h‖_E ≤ ‖h‖`.
   * *Isometry:* `‖h‖² = lim ⟪x_n, h⟫ = lim ⟨ι h, ι x_n⟩_E ≤ ‖ι h‖_E · lim ‖x_n‖ = ‖ι h‖_E ‖h‖`.
   * *Onto:* for `f ∈ H(E)`, `h ↦ ⟨ι h, f⟩_E` is a bounded linear functional on `H`; Riesz gives `u` with
     `⟪u, h⟫ = ⟨ι h, f⟩_E`; at `h = k w` this reads `ι u (w) = ⟨f, K_w⟩_E = f(w)` for `w ∈ ℂ₊`, so `ι u = f`.

   This replaces R7's "complete `H(E)` + orthogonal projection onto `ι(H)`": P3's completeness theorem
   `memHE_of_cauchy` assumes no real zeros, and P3 never builds `H(E)` as a type. Mathlib's RKHS uniqueness
   (`RKHS.equiv` in `Mathlib/Analysis/InnerProductSpace/Reproducing.lean`) was also considered: it needs `H(E)` as a
   complete `InnerProductSpace` type with an `RKHS` instance, i.e. exactly the completeness with real zeros we avoid
   (≈ 0.5 k more lines). The direct argument above uses only the reproducing formula at `ℂ₊`, Cauchy–Schwarz, Fatou and
   Riesz in `H`.

### 1.1 General helpers

Top-level definitions (shared with Part F):
```lean
def UHP : Set ℂ := {z : ℂ | 0 < z.im}
```
```lean
def thetaFn (E : ℂ → ℂ) (z : ℂ) : ℂ := fstar E z / E z
```

```lean
theorem eq_of_eqOn_upper {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ z : ℂ, 0 < z.im → f z = g z) : f = g := by
  sorry
```
*Proof.* `ℂ₊` is open (`isOpen_lt continuous_const Complex.continuous_im`) and contains `I`, so
`f =ᶠ[𝓝 I] g` (`Filter.eventually_of_mem`). Both are `AnalyticOnNhd ℂ · univ` (`hf.analyticAt`,
`Differentiable.analyticAt` in `Analysis/Complex/CauchyIntegral.lean`). Conclude with
`AnalyticOnNhd.eq_of_eventuallyEq` (`Analysis/Analytic/Uniqueness.lean:235`). ∎

```lean
theorem analyticOrderAt_eq_of_mul_div {F G : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G) {ζ : ℂ} (hζ : ζ.im ≠ 0) {n : ℕ}
    (hn : analyticOrderAt F ζ = (n + 1 : ℕ))
    (hFG : ∀ z : ℂ, z ≠ ζ → G z = F z * (z - conj ζ) / (z - ζ)) :
    analyticOrderAt G ζ = n := by
  sorry
```
*Proof.* By `AnalyticAt.analyticOrderAt_eq_natCast` (`hF.analyticAt ζ`) there is `u`, analytic at `ζ`, `u ζ ≠ 0`,
with `F z = (z-ζ)^(n+1) • u z` near `ζ`. Put `v z := u z * (z - conj ζ)`: analytic at `ζ`, and
`v ζ = u ζ · (ζ - conj ζ) ≠ 0` because `ζ - conj ζ = 2i Im ζ ≠ 0` (`Complex.sub_conj`).
For `z ≠ ζ` near `ζ`: `G z = (z-ζ)^(n+1) u z (z-ζ̄)/(z-ζ) = (z-ζ)^n v z` (`field_simp`, `z - ζ ≠ 0`).
So `G =ᶠ[𝓝[≠] ζ] fun z ↦ (z-ζ)^n • v z`; both sides are continuous at `ζ` (`hG`, `v` analytic), hence
`G =ᶠ[𝓝 ζ] …` (`eventuallyEq_nhds_of_eventuallyEq_nhdsNE`, `Topology/NhdsWithin.lean:448`, which takes the
equality at `ζ` as a second argument; that equality follows from `tendsto_nhds_unique` on `𝓝[≠] ζ`, a `NeBot`
filter in `ℂ`). Conclude with `(hG.analyticAt ζ).analyticOrderAt_eq_natCast`. ∎

```lean
theorem lintegral_line_le_liminf {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y)
    (hlim : ∀ x : ℝ, Tendsto (fun n ↦ F n ((x : ℂ) + (y : ℂ) * I)) atTop
      (𝓝 (G ((x : ℂ) + (y : ℂ) * I)))) :
    ∫⁻ x : ℝ, ‖G ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤
      liminf (fun n ↦ ∫⁻ x : ℝ, ‖F n ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2) atTop := by
  sorry
```
*Proof.* Put `φ n x := ‖F n (x+iy)‖ₑ²`, measurable by `measurable_line_sq (hF n) hy` (`HB/H2`). Pointwise
`‖G(x+iy)‖ₑ² = lim φ n x` (continuity of `a ↦ ‖a‖ₑ ^ 2`: `continuous_enorm.pow 2`), hence `= liminf φ n x`
(`Filter.Tendsto.liminf_eq`). Then `lintegral_congr` and Fatou `lintegral_liminf_le` (with `Measurable (φ n)`). ∎

### 1.2 Real zeros of `E` (R9 F5)

The `E` of Theorem C is strict, but can vanish on `ℝ`: for `H = {f ∈ PW : f(0) = 0}` (closed, satisfies (H1)–(H3)),
every `E` with `H(E) = H` vanishes at `0` (R7-6: if `E(0) ≠ 0`, then `K_E(0,·) ∈ H(E) = H`, so
`K_E(0,0) = 0`, while `K_E(0,0) = φ'(0)|E(0)|²/π > 0` for strict `E`). In Lean `f t / E t = 0` at a zero of `E`, which is not the boundary value of `f/E`; P3's reproducing
formula therefore asks for `IsH2Cont` functions `A`, `B` equal to `f/E`, `f^*/E` on `ℂ₊` and a.e. on `ℝ`. They are
built here.

```lean
theorem IsHB.ae_ne_zero {E : ℂ → ℂ} (hE : IsHB E) : ∀ᵐ t : ℝ, E t ≠ 0 := by
  sorry
```
*Proof.* `countable_real_zeros hE.1 ⟨I, hE.2.1 I (by simp)⟩` (`HB/DeBranges.lean:21`) and
`Set.Countable.measure_zero`; `ae_iff`. (Verbatim the argument of `heNormSq_mul`, `HB/DeBranges.lean:82–86`.) ∎

```lean
theorem analyticOrderAt_le_of_isH2Upper_div {E f : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hf : Differentiable ℂ f) (hE0 : ∀ z : ℂ, 0 < z.im → E z ≠ 0)
    (h : IsH2Upper (fun z ↦ f z / E z)) (x₀ : ℝ) :
    analyticOrderAt E (x₀ : ℂ) ≤ analyticOrderAt f (x₀ : ℂ) := by
  sorry
```
(Statement verbatim from R9 F5.)
*Proof.* Write `x = (x₀ : ℂ)`, `m = ord_x E`, `k = ord_x f` (`analyticOrderAt`, values in `ℕ∞`).
1. `m ≠ ⊤`: otherwise `E = 0` (`AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero`,
   `Analysis/Analytic/Order.lean:720`, with `fun z ↦ hE.analyticAt z`; R10 finding 2), contradicting `hE0 I (by simp)`.
2. If `k = ⊤`, done (`le_top`). Otherwise `k = (k₀ : ℕ)`, `m = (m₀ : ℕ)`, and suppose `k₀ < m₀`.
3. *Global division by `(z-x)^k₀`.* `AnalyticAt.analyticOrderAt_eq_natCast` gives `u` analytic at `x`, `u x ≠ 0`,
   `f = (z-x)^k₀ u` near `x`; similarly `E = (z-x)^m₀ v` near `x`, `v x ≠ 0`. Define the entire functions
   `f₁ := Function.update (fun z ↦ f z / (z - x)^k₀) x (u x)` and
   `E₁ := Function.update (fun z ↦ E z / (z - x)^k₀) x 0`.
   They are differentiable away from `x` (quotients), and near `x` they coincide with `u` and with
   `(z-x)^(m₀-k₀) v` respectively (on `𝓝[≠] x` by the factorisations, and at `x` by definition, since `m₀ - k₀ ≥ 1`),
   hence differentiable at `x`. (Alternative: iterate `dslope · x` `k₀` times and use `sub_smul_dslope`,
   `Complex.differentiableOn_dslope`.)
4. `f₁ x = u x ≠ 0`, `E₁ x = 0`, `E₁ z ≠ 0` on `ℂ₊` (there `E z = (z-x)^k₀ E₁ z` and `E z ≠ 0`), and on `ℂ₊`,
   `f₁ z / E₁ z = f z / E z` (cancel `(z-x)^k₀ ≠ 0`). So `IsH2Upper (f₁/E₁)` by `h.congr`, contradicting
   `not_isH2Upper_div_of_zero hE₁ hf₁ hE₁0 (E₁ x = 0) (f₁ x ≠ 0)` (`HB/H2.lean:236`). ∎

*Implemented:* step 3 divides with `divExt (fun z ↦ (z - x)^k₀) f` and `divExt (fun z ↦ (z - x)^k₀) E` (meromorphic
normal form, with the orders computed by the new helper `analyticOrderAt_divExt`) instead of `Function.update`
quotients. `toMeromorphicNFOn` worked without trouble, and the `limUnder` fallback for `divExt` was not needed.

```lean
def divExt (E f : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun z ↦ f z / E z) Set.univ
```
`toMeromorphicNFOn f U` (`Analysis/Meromorphic/NormalForm.lean:830`) changes `f` on a discrete subset of `U` so that
it is in meromorphic normal form; on analytic points it changes nothing. Fallback if this API turns out awkward: define
`divExt E f z := if E z = 0 then limUnder (𝓝[≠] z) (fun u ↦ f u / E u) else f z / E z`; the three lemmas below
then follow from the same local factorisations.

```lean
theorem divExt_eq_of_ne {E f : ℂ → ℂ} (hE : Differentiable ℂ E) (hf : Differentiable ℂ f)
    {z : ℂ} (hz : E z ≠ 0) : divExt E f z = f z / E z := by
  sorry
```
*Proof.* `φ := fun z ↦ f z / E z` is `MeromorphicOn φ univ`: at each point
`(hf.analyticAt z).meromorphicAt.div (hE.analyticAt z).meromorphicAt` (`AnalyticAt.meromorphicAt`,
`MeromorphicAt.div`, `Analysis/Meromorphic/Basic.lean:40, 311`). By `toMeromorphicNFOn_eq_toMeromorphicNFAt`
(`NormalForm.lean:885`), `divExt E f z = toMeromorphicNFAt φ z z`. Since `E z ≠ 0`, `φ` is analytic at `z`
(`AnalyticAt.div`), so `MeromorphicNFAt φ z` (`AnalyticAt.meromorphicNFAt`) and `toMeromorphicNFAt φ z = φ`
(`toMeromorphicNFAt_eq_self`, `NormalForm.lean:578`). ∎

```lean
theorem analyticAt_divExt {E f : ℂ → ℂ} (hE : Differentiable ℂ E) (hf : Differentiable ℂ f)
    {z : ℂ} (hle : analyticOrderAt E z ≤ analyticOrderAt f z) :
    AnalyticAt ℂ (divExt E f) z := by
  sorry
```
*Proof.* `divExt E f` is `MeromorphicNFOn … univ` (`meromorphicNFOn_toMeromorphicNFOn`, `NormalForm.lean:893`), so
by `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt` (`NormalForm.lean:143`) it suffices that
`0 ≤ meromorphicOrderAt (divExt E f) z`. On `𝓝[≠] z`, `divExt E f = φ`
(`MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE`, `NormalForm.lean:861`), so the orders agree
(`meromorphicOrderAt_congr`, `Meromorphic/Order.lean:284`).
* If `ord_z f = ⊤` then `f = 0` near `z`, `φ = 0` near `z`, order `⊤ ≥ 0`.
* Otherwise `ord_z E ≤ ord_z f < ⊤`, both finite; `meromorphicOrderAt φ z = meromorphicOrderAt f z −
  meromorphicOrderAt E z` (`meromorphicOrderAt_div`, `Order.lean:582`), and for analytic functions
  `meromorphicOrderAt = (analyticOrderAt).map (↑)` (`AnalyticAt.meromorphicOrderAt_eq`, `Order.lean:303`); the
  difference of the two naturals is `≥ 0`. ∎

```lean
theorem isH2Cont_divExt {E f : ℂ → ℂ} (hE : IsHB E) (hf : Differentiable ℂ f)
    (h : IsH2Upper (fun z ↦ f z / E z)) : IsH2Cont (divExt E f) := by
  sorry
```
*Proof.* `H²` part: `h.congr` with `divExt_eq_of_ne hE.1 hf (hE.2.1 z hz)` on `ℂ₊`. Continuity at real `t`:
`(analyticAt_divExt hE.1 hf (analyticOrderAt_le_of_isH2Upper_div hE.1 hf hE.2.1 h t)).continuousAt`. ∎

```lean
theorem exists_isH2Cont_of_memHE {E f : ℂ → ℂ} (hE : IsHB E) (hf : MemHE E f) :
    ∃ A B : ℂ → ℂ, IsH2Cont A ∧ IsH2Cont B ∧
      (∀ z : ℂ, 0 < z.im → A z = f z / E z) ∧
      (∀ z : ℂ, 0 < z.im → B z = fstar f z / E z) ∧
      (∀ x : ℝ, E x ≠ 0 → A x = f x / E x ∧ B x = fstar f x / E x) := by
  sorry
```
(Statement verbatim from R9 F5.)
*Proof.* `A := divExt E f`, `B := divExt E (fstar f)`; `isH2Cont_divExt hE hf.1 hf.2.1` and
`isH2Cont_divExt hE hf.1.fstar hf.2.2` (`Differentiable.fstar`, `HB/Basic`); the equalities by `divExt_eq_of_ne`
(on `ℂ₊` since `E ≠ 0` there). ∎

```lean
theorem heNormSq_eq_lintegral_divExt {E f : ℂ → ℂ} (hE : IsHB E) (hf : Differentiable ℂ f) :
    heNormSq E f = ∫⁻ t : ℝ, ‖divExt E f t‖ₑ ^ 2 := by
  sorry
```
*Proof.* `lintegral_congr_ae`; `filter_upwards [hE.ae_ne_zero]`; `divExt_eq_of_ne hE.1 hf`. ∎

### 1.3 `H(E)` for `E ∈ \overline{HB}` with real zeros

`h0`-free replacements of P3's `Space.lean`. Throughout, `u_f := fun t : ℝ ↦ f t / E t` and `A_f := divExt E f`,
so `u_f = A_f` a.e. (`IsHB.ae_ne_zero`, `divExt_eq_of_ne`).

```lean
theorem MemHE.heNormSq_lt_top_of_isHB (hE : IsHB E) {f : ℂ → ℂ} (hf : MemHE E f) :
    heNormSq E f < ⊤ := by
  sorry
```
*Proof.* `heNormSq_eq_lintegral_divExt hE hf.1` and `(isH2Cont_divExt hE hf.1 hf.2.1).lintegral_real_lt_top`. ∎

```lean
theorem MemHE.memLp_div_of_isHB (hE : IsHB E) {f : ℂ → ℂ} (hf : MemHE E f) :
    MemLp (fun t : ℝ ↦ f t / E t) 2 := by
  sorry
```
*Proof.* `(isH2Cont_divExt hE hf.1 hf.2.1).memLp_real` and `MemLp.ae_eq` (`LpSeminorm/Basic.lean:577`) with the a.e.
equality `A_f = u_f`. ∎

```lean
theorem MemHE.lintegral_line_le_of_isHB (hE : IsHB E) {f : ℂ → ℂ} (hf : MemHE E f) {y : ℝ}
    (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ heNormSq E f := by
  sorry
```
*Proof.* On the line `x + iy` (`y > 0`, imaginary part `y` by `simp`), `A_f = f/E` (`divExt_eq_of_ne`, `E ≠ 0` on
`ℂ₊`). `IsH2Cont.lintegral_line_le` (P3) bounds the line integral of `A_f` by `∫⁻ ‖A_f t‖ₑ²`, which is `heNormSq E f`
(`heNormSq_eq_lintegral_divExt`). ∎

```lean
theorem MemHE.heNormSq_le_of_lines_of_isHB (hE : IsHB E) {f : ℂ → ℂ} (hf : MemHE E f)
    {C : ℝ≥0∞} (hC : ∀ y : ℝ, 0 < y →
      ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ C) :
    heNormSq E f ≤ C := by
  sorry
```
*Proof.* Rewrite with `heNormSq_eq_lintegral_divExt`; apply `lintegral_real_le_of_isH2` (`HB/Comparable.lean:82`) to
`G = A_f`: `hd` from `(isH2Cont_divExt …).1.1`, `hcont` from `(isH2Cont_divExt …).2`, and the line bound from `hC`
after rewriting `A_f = f/E` on the line. ∎

```lean
theorem integrable_heInner_of_isHB (hE : IsHB E) {f g : ℂ → ℂ} (hf : MemHE E f)
    (hg : MemHE E g) : Integrable fun t : ℝ ↦ f t * conj (g t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) := by
  sorry
```
*Proof.* Pointwise, for every real `t` (also where `E t = 0`, both sides being `0`):
`f t * conj (g t) / ‖E t‖² = u_f t * conj (u_g t)` (`‖E t‖² = E t * conj (E t)`: `Complex.mul_conj`,
`Complex.normSq_eq_norm_sq`; this is the pointwise content of P3's `heInner_eq_integral_div`).
`u_f`, `u_g` are in `L²` (`MemHE.memLp_div_of_isHB`); `‖u_f conj u_g‖ ≤ (‖u_f‖² + ‖u_g‖²)/2`, integrable by
`memLp_two_iff_integrable_sq_norm`; measurability from `AEStronglyMeasurable.mul` and
`Complex.continuous_conj.comp_aestronglyMeasurable`. `Integrable.mono'`. ∎
*Implemented:* by `MemLp.integrable_mul` (Hölder `2,2`) on `u_f` and `conj u_g`. The pointwise identity is the
helper `heInner_integrand_eq`.

```lean
theorem heInner_add_left_of_isHB (hE : IsHB E) {f g k : ℂ → ℂ} (hf : MemHE E f)
    (hg : MemHE E g) (hk : MemHE E k) :
    heInner E (fun z ↦ f z + g z) k = heInner E f k + heInner E g k := by
  sorry
```
*Proof.* Unfold `heInner`; the integrand of the left side is the sum of the two integrands (`add_mul`, `add_div`);
`integral_add` with `integrable_heInner_of_isHB hE hf hk` and `… hg hk`. ∎

```lean
theorem heInner_add_right_of_isHB (hE : IsHB E) {f g k : ℂ → ℂ} (hf : MemHE E f)
    (hg : MemHE E g) (hk : MemHE E k) :
    heInner E f (fun z ↦ g z + k z) = heInner E f g + heInner E f k := by
  sorry
```
*Proof.* `heInner E f (g + k) = conj (heInner E (g + k) f)` (`heInner_conj_symm`, P3, no hypothesis), then
`heInner_add_left_of_isHB hE hg hk hf`, `map_add`, and `heInner_conj_symm` back. ∎

```lean
theorem heInner_self_of_isHB (hE : IsHB E) {f : ℂ → ℂ} (hf : MemHE E f) :
    heInner E f f = (((heNormSq E f).toReal : ℝ) : ℂ) := by
  sorry
```
*Proof.* Pointwise `f t * conj (f t) / ‖E t‖² = ((‖u_f t‖ ^ 2 : ℝ) : ℂ)` (`Complex.mul_conj`, `norm_div`; both sides `0`
where `E t = 0`). So `heInner E f f = ((∫ ‖u_f‖² : ℝ) : ℂ)` (`integral_ofReal`), and
`∫ ‖u_f‖² = (∫⁻ ofReal (‖u_f‖²)).toReal = (heNormSq E f).toReal` (`integral_eq_lintegral_of_nonneg_ae` with
`sq_nonneg`, measurability from `memLp_div_of_isHB`; `enorm_sq_eq_ofReal`, `HB/MeanValue.lean:50`). ∎
*Implemented* as `heInner_self hE hf`: P3's lemma needs only `IsHB E` (R10 finding 3).

```lean
theorem norm_heInner_le_of_isHB (hE : IsHB E) {f g : ℂ → ℂ} (hf : MemHE E f)
    (hg : MemHE E g) :
    ‖heInner E f g‖ ≤ Real.sqrt (heNormSq E f).toReal * Real.sqrt (heNormSq E g).toReal := by
  sorry
```
*Proof.* `heInner E f g = ∫ u_f conj u_g` (pointwise identity above). `‖∫ u_f conj u_g‖ ≤ ∫ ‖u_f‖‖u_g‖`
(`norm_integral_le_integral_norm`, `norm_mul`, `Complex.norm_conj`) `≤ (∫‖u_f‖²)^{1/2}(∫‖u_g‖²)^{1/2}`
(`integral_mul_le_Lp_mul_Lq_of_nonneg` with `Real.HolderConjugate.two_two`, `Bochner/Basic.lean:1237`; the `rpow 2`
and `rpow (1/2)` become `sq` and `Real.sqrt` by `Real.sqrt_eq_rpow`, `Real.rpow_natCast`), and
`∫‖u_f‖² = (heNormSq E f).toReal` as in `heInner_self_of_isHB`. ∎
*Implemented* through the squared form `norm_heInner_sq_le_of_isHB`. Its proof is P3's `ℝ≥0∞`-Hölder proof of
`norm_heInner_sq_le`, with `MemHE.heNormSq_lt_top_of_isHB` in place of `h0`; square roots follow.

```lean
theorem heInner_kernel_upper_of_isHB (hE : IsHB E) {f : ℂ → ℂ} (hf : MemHE E f) {w : ℂ}
    (hw : 0 < w.im) : heInner E f (deBrangesKernel E w) = f w := by
  sorry
```
*Proof.* `obtain ⟨A, B, hA, hB, hAu, -, hAB⟩ := exists_isH2Cont_of_memHE hE hf`; apply P3's
`heInner_kernel_upper_of_isH2Cont hE hE.ae_ne_zero hA hB hAu _ _ hw`, the two a.e. equalities from `hAB` and
`hE.ae_ne_zero` (`filter_upwards`). ∎

### 1.4 Data, and C.1–C.4: the reproducing kernel of `H`

Section variables: `{H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]`, `{ι : H →ₗ[ℂ] (ℂ → ℂ)}`.
*Implemented:* `[CompleteSpace H]` is not a section variable. It was unused in most lemmas and was being
auto-included. It is an explicit instance argument of exactly the six declarations that use Riesz or the orthogonal
complement: `exists_kernel`, `kernelSpan_topologicalClosure`, `exists_seq_kernelSpan`, `memHE_iota`,
`heNormSq_iota` and `mem_range_of_memHE`. `TheoremC` supplies the instance.

```lean
structure DBAxioms (ι : H →ₗ[ℂ] (ℂ → ℂ)) : Prop where
  inj : Function.Injective ι
  entire : ∀ h : H, Differentiable ℂ (ι h)
  h1 : ∀ h : H, ∀ ζ : ℂ, ζ.im ≠ 0 → ι h ζ = 0 →
      ∃ g : H, ‖g‖ = ‖h‖ ∧ ∀ z : ℂ, z ≠ ζ → ι g z = ι h z * (z - conj ζ) / (z - ζ)
  h2 : ∀ ζ : ℂ, ζ.im ≠ 0 → Continuous fun h : H ↦ ι h ζ
  h3 : ∀ h : H, ∃ g : H, ‖g‖ = ‖h‖ ∧ ι g = fstar (ι h)
  nontrivial : ∃ h : H, h ≠ 0
```
```lean
def IsKernelFamily (ι : H →ₗ[ℂ] (ℂ → ℂ)) (k : ℂ → H) : Prop :=
  ∀ ζ : ℂ, ζ.im ≠ 0 → ∀ h : H, ι h ζ = ⟪k ζ, h⟫_ℂ
```
```lean
def kernelE (ι : H →ₗ[ℂ] (ℂ → ℂ)) (k : ℂ → H) (z : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * (z + I) * ι (k I) z / (Real.sqrt (ι (k I) I).re : ℂ)
```
```lean
def kernelSpan (k : ℂ → H) : Submodule ℂ H :=
  Submodule.span ℂ (k '' UHP)
```

```lean
theorem DBAxioms.eq_zero_of_upper (hax : DBAxioms ι) {h : H}
    (h0 : ∀ z : ℂ, 0 < z.im → ι h z = 0) : h = 0 := by
  sorry
```
*Proof.* `eq_of_eqOn_upper (hax.entire h) (differentiable_const 0) h0` gives `ι h = 0 = ι 0` (`map_zero`); `hax.inj`. ∎

```lean
theorem exists_kernel [CompleteSpace H] (hax : DBAxioms ι) : ∃ k : ℂ → H, IsKernelFamily ι k := by
  sorry
```
*Proof.* For nonreal `ζ`, `Λ_ζ : H →L[ℂ] ℂ`, `Λ_ζ h = ι h ζ`: linear (`map_add`, `map_smul`, `Pi.add_apply`,
`Pi.smul_apply`), continuous by `hax.h2 ζ hζ` (build it as a structure `{ toFun, map_add', map_smul', cont }`).
`k ζ := if ζ.im ≠ 0 then (InnerProductSpace.toDual ℂ H).symm Λ_ζ else 0` (`classical`; `StrongDual ℂ H = H →L[ℂ] ℂ`).
`InnerProductSpace.toDual_symm_apply : ⟪(toDual 𝕜 E).symm y, x⟫ = y x` (`InnerProductSpace/Dual.lean:178`) gives
`⟪k ζ, h⟫ = ι h ζ`. ∎

```lean
theorem kernel_diag {k : ℂ → H} (hk : IsKernelFamily ι k) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    ι (k ζ) ζ = ((‖k ζ‖ ^ 2 : ℝ) : ℂ) := by
  sorry
```
*Proof.* `hk ζ hζ (k ζ)` and `inner_self_eq_norm_sq_to_K`; `push_cast`. ∎

```lean
theorem kernel_norm_pos (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) {ζ : ℂ}
    (hζ : ζ.im ≠ 0) : 0 < ‖k ζ‖ := by
  sorry
```
*Proof.* Suppose `‖k ζ‖ = 0`, so `k ζ = 0` and `ι h ζ = ⟪0, h⟫ = 0` for all `h` (`inner_zero_left`).
Claim: for all `n : ℕ` and `h : H`, `analyticOrderAt (ι h) ζ ≠ n`. Induction on `n`.
* `n = 0`: `analyticOrderAt_eq_zero` (`Order.lean:135`) would give `ι h ζ ≠ 0` (`ι h` is analytic).
* `n+1`: `ι h ζ = 0`, so (H1) gives `g` with `ι g z = ι h z (z-ζ̄)/(z-ζ)` for `z ≠ ζ`;
  `analyticOrderAt_eq_of_mul_div` gives `analyticOrderAt (ι g) ζ = n`, contradicting the induction hypothesis.
Now take `h ≠ 0` (`hax.nontrivial`). `ι h ≠ 0` (`hax.inj`, `map_zero`), so `analyticOrderAt (ι h) ζ ≠ ⊤`
(`AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero`), i.e. `= n` for some `n` (`ENat.ne_top_iff_exists`): contradiction. ∎
(The norm clause `‖g‖ = ‖h‖` of (H1) is not used here.)

```lean
theorem kernel_symm {k : ℂ → H} (hk : IsKernelFamily ι k) {w z : ℂ} (hw : w.im ≠ 0)
    (hz : z.im ≠ 0) : ι (k w) z = conj (ι (k z) w) := by
  sorry
```
*Proof.* `ι (k w) z = ⟪k z, k w⟫ = conj ⟪k w, k z⟫ = conj (ι (k z) w)` (`hk`, `inner_conj_symm`). ∎

```lean
theorem exists_conjMap (hax : DBAxioms ι) :
    ∃ S : H → H, (∀ h : H, ι (S h) = fstar (ι h)) ∧ (∀ x y : H, ⟪S x, S y⟫_ℂ = ⟪y, x⟫_ℂ) ∧
      ∀ h : H, S (S h) = h := by
  sorry
```
*Proof.* `S h := (hax.h3 h).choose`, so `‖S h‖ = ‖h‖` and `ι (S h) = fstar (ι h)`.
* `S (S h) = h`: `ι (S (S h)) = fstar (fstar (ι h)) = ι h` (`fstar_fstar`), `hax.inj`.
* Conjugate-linearity: `ι (S (x + y)) = fstar (ι x + ι y) = ι (S x) + ι (S y)` (`fstar_add`) and
  `ι (S (c • x)) = conj c • ι (S x)` (`fstar_const_mul`); `hax.inj` gives `S (x + y) = S x + S y`,
  `S (c • x) = conj c • S x`.
* `⟪S x, S y⟫ = ⟪y, x⟫`: polarization `inner_eq_sum_norm_sq_div_four` (`InnerProductSpace/Basic.lean:537`,
  `⟪x, y⟫ = (‖x+y‖² − ‖x−y‖² + (‖x − I•y‖² − ‖x + I•y‖²) I)/4`). With `S(I•y) = −I•S y`:
  `‖Sx ± Sy‖ = ‖x ± y‖`, `‖Sx − I•Sy‖ = ‖S(x + I•y)‖ = ‖x + I•y‖`, `‖Sx + I•Sy‖ = ‖x − I•y‖`. On the other side,
  `‖y + x‖ = ‖x + y‖`, `‖y − x‖ = ‖x − y‖`, `‖y − I•x‖ = ‖−I•(x + I•y)‖ = ‖x + I•y‖`, `‖y + I•x‖ = ‖x − I•y‖`.
  So the two polarization expressions coincide. ∎

```lean
theorem kernel_fstar (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) {w : ℂ}
    (hw : w.im ≠ 0) : fstar (ι (k w)) = ι (k (conj w)) := by
  sorry
```
*Proof.* Let `S` be as above. `S (k w) = k (conj w)` by `ext_inner_right ℂ`: for every `v`,
`⟪S (k w), v⟫ = ⟪S (k w), S (S v)⟫ = ⟪S v, k w⟫ = conj ⟪k w, S v⟫ = conj (ι (S v) w) = conj (conj (ι v (conj w)))
= ι v (conj w) = ⟪k (conj w), v⟫` (`(conj w).im = -w.im ≠ 0`). Then
`fstar (ι (k w)) = ι (S (k w)) = ι (k (conj w))`. ∎

### 1.5 C.5–C.8: the identity from (H1) and the function `E`

```lean
theorem exists_mulMap (hax : DBAxioms ι) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    ∃ T : H → H,
      (∀ f : H, ι f ζ = 0 → ∀ z : ℂ, z ≠ ζ → ι (T f) z = ι f z * (z - conj ζ) / (z - ζ)) ∧
      (∀ f f' : H, ι f ζ = 0 → ι f' ζ = 0 → ⟪T f, T f'⟫_ℂ = ⟪f, f'⟫_ℂ) ∧
      ∀ g : H, ι g (conj ζ) = 0 → ∃ f : H, ι f ζ = 0 ∧ T f = g := by
  sorry
```
*Proof.* `T f := if h : ι f ζ = 0 then (hax.h1 f ζ hζ h).choose else 0`. The first clause is `choose_spec`.
*Uniqueness off a point.* Two entire functions equal on `{ζ}ᶜ` (or on the complement of any finite set) are equal:
`Continuous.ext_on` (`Topology/Separation/Hausdorff.lean:518`) with `dense_compl_singleton`
(`Topology/ClusterPt.lean:276`), or `Set.Countable.dense_compl ℝ` (`Topology/Algebra/Module/Cardinality.lean:132`)
for a finite set.
*Linearity on `H_ζ = {f : ι f ζ = 0}`.* For `f, f' ∈ H_ζ`, `c : ℂ`: `ι (T (f + c • f'))` and `ι (T f + c • T f')`
agree off `ζ`, hence everywhere, hence `T (f + c • f') = T f + c • T f'` (`hax.inj`); `‖T f‖ = ‖f‖`.
*Isometry.* Polarization as in `exists_conjMap` (here `T` is linear, so `⟪T f, T f'⟫ = ⟪f, f'⟫`); or bundle
`T` as `LinearMap.ker ((LinearMap.proj ζ).comp ι) →ₗᵢ[ℂ] H` and use `LinearIsometry.inner_map_map`
(`InnerProductSpace/LinearMap.lean:112`).
*Onto `H_ζ̄`.* Given `g` with `ι g ζ̄ = 0`, (H1) at `ζ̄` (`(conj ζ).im ≠ 0`, `conj (conj ζ) = ζ`) gives `g'` with
`ι g' z = ι g z (z − ζ)/(z − ζ̄)` for `z ≠ ζ̄`. At `z = ζ` (`ζ ≠ ζ̄`, since `Im ζ ≠ 0`) this gives `ι g' ζ = 0`, so
`g' ∈ H_ζ`. For `z ∉ {ζ, ζ̄}`: `ι (T g') z = ι g z (z−ζ)/(z−ζ̄) · (z−ζ̄)/(z−ζ) = ι g z`; so `ι (T g') = ι g` and
`T g' = g`. ∎
*Implemented:* "equal off a point" (and off `{ζ, ζ̄}`) uses `DBAxioms.eq_of_eq_off_finite`, i.e. the identity theorem on
the open complement of a finite set (`eq_of_eq_off_finite`), not `Continuous.ext_on`. Linearity on
`H_ζ = ker (proj ζ ∘ ι)` comes from injectivity. `T` is bundled as `H_ζ →ₗᵢ[ℂ] H`, and the second clause is
`LinearIsometry.inner_map_map`, without polarization. `exists_conjMap` is conjugate-linear, so it uses polarization
(`inner_eq_sum_norm_sq_div_four`) as planned.

```lean
theorem kernel_identity (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) {ζ w z : ℂ}
    (hζ : ζ.im ≠ 0) (hw : w.im ≠ 0) :
    (z - conj ζ) * (conj w - ζ) *
        (ι (k w) z - ι (k ζ) z * ι (k w) ζ / ι (k ζ) ζ) =
      (z - ζ) * (conj w - conj ζ) *
        (ι (k w) z - ι (k (conj ζ)) z * ι (k w) (conj ζ) / ι (k (conj ζ)) (conj ζ)) := by
  sorry
```
*Proof.* Let `a := ι (k ζ) ζ`, `b := ι (k ζ̄) ζ̄`, both nonzero (`kernel_diag`, `kernel_norm_pos`). Let
`p := k w − (ι (k w) ζ / a) • k ζ` and `q := k w − (ι (k w) ζ̄ / b) • k ζ̄` (the reproducing kernels at `w` of
`H_ζ` and `H_ζ̄`). Then:
* `ι p z = ι (k w) z − ι (k ζ) z · ι (k w) ζ / a` (the bracket on the left of the statement) and `ι p ζ = 0`;
  similarly for `q` (right bracket) and `ι q ζ̄ = 0`;
* for `f ∈ H_ζ`: `⟪p, f⟫ = ⟪k w, f⟫ − conj(…)⟪k ζ, f⟫ = ι f w` (`inner_sub_left`, `inner_smul_left`, `hk`);
  similarly `⟪q, g⟫ = ι g w` for `g ∈ H_ζ̄`.
*Case `w = ζ`.* `p = 0` (coefficient `a/a = 1`), so the left bracket is `0`; on the right `conj w − conj ζ = 0`.
*Case `w ≠ ζ`.* Let `T` be from `exists_mulMap`, `c₀ := (w − ζ̄)/(w − ζ)` and `d := q − conj c₀ • T p`.
* `d ∈ H_ζ̄`: `ι q ζ̄ = 0` and `ι (T p) ζ̄ = ι p ζ̄ · 0/(ζ̄ − ζ) = 0` (first clause at `z = ζ̄ ≠ ζ`).
* `⟪d, g⟫ = 0` for all `g ∈ H_ζ̄`: write `g = T f`, `f ∈ H_ζ` (onto). Then `⟪q, T f⟫ = ι (T f) w = c₀ · ι f w`
  (first clause at `z = w ≠ ζ`), and `⟪conj c₀ • T p, T f⟫ = c₀ ⟪T p, T f⟫ = c₀ ⟪p, f⟫ = c₀ · ι f w`.
* Hence `⟪d, d⟫ = 0`, `d = 0` (`inner_self_eq_zero`), i.e. `q = conj c₀ • T p`.
* Apply `ι` at `z ≠ ζ`: `ι q z = conj c₀ · ι p z · (z − ζ̄)/(z − ζ)`, with `conj c₀ = (w̄ − ζ)/(w̄ − ζ̄)`
  (`w̄ ≠ ζ̄`). Multiply by `(z − ζ)(w̄ − ζ̄)`: `(z−ζ)(w̄−ζ̄) ι q z = (w̄−ζ)(z−ζ̄) ι p z`, which is the statement
  (`field_simp`, `ring`). At `z = ζ`: `ι p ζ = 0` and the factor `z − ζ = 0`, both sides vanish. ∎

```lean
theorem differentiable_kernelE (hax : DBAxioms ι) (k : ℂ → H) :
    Differentiable ℂ (kernelE ι k) := by
  sorry
```
*Proof.* `((differentiable_const _).mul (differentiable_id.add_const _)).mul (hax.entire _) |>.div_const _`. ∎

```lean
theorem fstar_kernelE (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) :
    fstar (kernelE ι k) =
      fun z ↦ (Real.sqrt Real.pi : ℂ) * (z - I) * ι (k (-I)) z / (Real.sqrt (ι (k I) I).re : ℂ) := by
  sorry
```
*Proof.* `funext z`; `fstar (kernelE ι k) z = conj (√π (z̄ + i) K(i, z̄) / √a)` with `a = (ι (k I) I).re`;
`map_mul`, `map_div₀`, `Complex.conj_ofReal`, `conj (conj z + I) = z − I` (`Complex.conj_conj`, `Complex.conj_I`),
and `conj (ι (k I) (conj z)) = fstar (ι (k I)) z = ι (k (conj I)) z = ι (k (-I)) z` (`kernel_fstar` at `w = I`). ∎

```lean
theorem kernel_mul_eq (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) {w : ℂ}
    (hw : w.im ≠ 0) (z : ℂ) :
    ι (k w) z * (Real.pi * (z - conj w)) = I / 2 * kernelNum (kernelE ι k) w z := by
  sorry
```
*Proof.* Let `a := ι (k I) I`; by `kernel_diag`, `a = ‖k I‖²` is real and `> 0` (`kernel_norm_pos`); `s := √a.re`,
`s² = a`. Also `ι (k (-I)) (-I) = a`: by `kernel_fstar`, `ι (k (-I)) = fstar (ι (k I))`, whose value at `-I` is
`conj (ι (k I) I) = conj a = a`.
`kernel_identity` with `ζ = I` (`conj I = -I`):
`(z + I)(w̄ − I)(K(w,z) − K(I,z)K(w,I)/a) = (z − I)(w̄ + I)(K(w,z) − K(−I,z)K(w,−I)/a)`.
The coefficient of `K(w,z)` is `(z+I)(w̄−I) − (z−I)(w̄+I) = −2I(z − w̄)`. With `K(w,I) = conj K(I,w)`,
`K(w,−I) = conj K(−I,w)` (`kernel_symm`) and `w̄ − I = conj(w + I)`, `w̄ + I = conj(w − I)`:
`−2I(z − w̄) K(w,z) = (1/a)[P₀(z) conj P₀(w) − Q₀(z) conj Q₀(w)]`, `P₀ = (z+I)K(I,z)`, `Q₀ = (z−I)K(−I,z)`.
By the definition of `kernelE` and `fstar_kernelE`, `kernelNum (kernelE ι k) w z = (π/s²)[P₀(z) conj P₀(w) −
Q₀(z) conj Q₀(w)]` (`((√π : ℝ) : ℂ)² = π`, `Real.sq_sqrt`). Hence `K(w,z)·π(z − w̄) = kernelNum/(−2I) = (I/2)·kernelNum`.
(`field_simp` with `s ≠ 0`, then `linear_combination` of the identity.) ∎
*Implemented* with the helpers `kernelE_eq` and `fstar_kernelE_eq` (normalised forms with `√K(i,i) = ‖k i‖`),
`kernel_diag_ne_zero` and `kernel_diag_neg_I` (`K(-i,-i) = K(i,i)`).
*Check* (R7-6): on `PW`, `K(i,z) = sin π(z+i)/(π(z+i))`, `K(i,i) = sinh 2π/(2π)` and `kernelE = √(2/sinh 2π)·sin π(z+i)`,
which reproduces `sin π(z−w̄)/(π(z−w̄))`; so `√π` is the right normalisation.

```lean
theorem kernel_eq_deBrangesKernel (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k)
    {w : ℂ} (hw : w.im ≠ 0) : ι (k w) = deBrangesKernel (kernelE ι k) w := by
  sorry
```
*Proof.* Both sides are continuous in `z` (`hax.entire`; P3 `differentiable_deBrangesKernel (differentiable_kernelE hax k) w`).
On `{conj w}ᶜ`: `kernel_mul_eq` and P3 `deBrangesKernel_mul` (no hypothesis) give
`ι (k w) z · π(z − w̄) = deBrangesKernel E w z · π(z − w̄)`, and `π(z − w̄) ≠ 0`. Conclude with `Continuous.ext_on`
and `dense_compl_singleton (conj w)`. ∎
*Implemented* with `eq_of_eq_off_finite` (off `{w̄}`) instead of `Continuous.ext_on`.

```lean
theorem isStrictHB_kernelE (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) :
    IsStrictHB (kernelE ι k) := by
  sorry
```
*Proof.* Let `z ∈ ℂ₊` (`z.im ≠ 0`). `ι (k z) z = ‖k z‖² > 0` (`kernel_diag`, `kernel_norm_pos`), and
`ι (k z) z = deBrangesKernel E z z = ((‖E z‖² − ‖E (conj z)‖²)/(4π Im z) : ℝ)` (`kernel_eq_deBrangesKernel`, P3
`deBrangesKernel_diag`). So `‖E (conj z)‖² < ‖E z‖²` (`Complex.ofReal_inj`, `div_pos_iff`, `Im z > 0`), hence
`‖E (conj z)‖ < ‖E z‖` (`sq_lt_sq'`/`pow_lt_pow_iff_left₀` with `norm_nonneg`), hence `E z ≠ 0` and the `≤` of `IsHB`.
Differentiability: `differentiable_kernelE`. ∎

### 1.6 C.9–C.14: `H = H(E)` isometrically

Write `E := kernelE ι k` and `hE := (isStrictHB_kernelE hax hk).1 : IsHB E`.

```lean
theorem memHE_kernel (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) {w : ℂ}
    (hw : w.im ≠ 0) : MemHE (kernelE ι k) (ι (k w)) := by
  sorry
```
*Proof.* `kernel_eq_deBrangesKernel` and P3 `memHE_deBrangesKernel_of_isHB hE (Or.inl hw)` (no real-zero
assumption). ∎

```lean
theorem memHE_of_mem_kernelSpan (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k)
    {x : H} (hx : x ∈ kernelSpan k) : MemHE (kernelE ι k) (ι x) := by
  sorry
```
*Proof.* `Submodule.span_induction` (`LinearAlgebra/Span/Defs.lean:137`). Generators `k w`, `w ∈ UHP`:
`memHE_kernel` (`hw.ne'`). Zero: `ι 0 = fun _ ↦ 0` (`map_zero`), P3 `memHE_zero`. Sum: `ι (x + y) = fun z ↦ ι x z + ι y z`
(`map_add`), P3 `MemHE.add`. Scalar: `ι (c • x) = fun z ↦ c * ι x z` (`map_smul`, `smul_eq_mul`), P3 `MemHE.const_mul`. ∎

```lean
theorem heInner_iota_of_mem_kernelSpan (hax : DBAxioms ι) {k : ℂ → H}
    (hk : IsKernelFamily ι k) {h : H} (hh : MemHE (kernelE ι k) (ι h)) {x : H}
    (hx : x ∈ kernelSpan k) : heInner (kernelE ι k) (ι h) (ι x) = ⟪x, h⟫_ℂ := by
  sorry
```
*Proof.* `Submodule.span_induction` on `x`, motive `heInner E (ι h) (ι x) = ⟪x, h⟫` (membership of `ι x` in `H(E)` from
`memHE_of_mem_kernelSpan`).
* `x = k w`, `w ∈ ℂ₊`: `heInner E (ι h) (ι (k w)) = heInner E (ι h) (deBrangesKernel E w)` (`kernel_eq_deBrangesKernel`)
  `= ι h w` (`heInner_kernel_upper_of_isHB hE hh hw`) `= ⟪k w, h⟫` (`hk`).
* `x = 0`: `heInner E f (fun _ ↦ 0) = 0` (unfold, `map_zero`, `mul_zero`, `zero_div`, `integral_zero`), `inner_zero_left`.
* `x + y`: `heInner_add_right_of_isHB hE hh hx' hy'` and `inner_add_left`.
* `c • x`: P3 `heInner_smul_right` (`= conj c * …`, no hypothesis) and `inner_smul_left` (`= conj c * ⟪x, h⟫`). ∎

```lean
theorem heNormSq_iota_of_mem_kernelSpan (hax : DBAxioms ι) {k : ℂ → H}
    (hk : IsKernelFamily ι k) {x : H} (hx : x ∈ kernelSpan k) :
    heNormSq (kernelE ι k) (ι x) = ENNReal.ofReal (‖x‖ ^ 2) := by
  sorry
```
*Proof.* With `hx' := memHE_of_mem_kernelSpan hax hk hx`: `heInner E (ι x) (ι x) = ⟪x, x⟫ = ‖x‖²`
(`heInner_iota_of_mem_kernelSpan hax hk hx' hx`, `inner_self_eq_norm_sq_to_K`) and `= (heNormSq E (ι x)).toReal`
(`heInner_self_of_isHB`). So `(heNormSq E (ι x)).toReal = ‖x‖²` (`Complex.ofReal_inj`); since `heNormSq < ⊤`
(`MemHE.heNormSq_lt_top_of_isHB`), `heNormSq = ENNReal.ofReal ((heNormSq).toReal)` (`ENNReal.ofReal_toReal`). ∎

```lean
theorem kernelSpan_topologicalClosure [CompleteSpace H] (hax : DBAxioms ι) {k : ℂ → H}
    (hk : IsKernelFamily ι k) : (kernelSpan k).topologicalClosure = ⊤ := by
  sorry
```
*Proof.* `Submodule.topologicalClosure_eq_top_iff` (`InnerProductSpace/Projection/Submodule.lean:179`, needs
`CompleteSpace H`): show `(kernelSpan k)ᗮ = ⊥`. If `h ∈ (kernelSpan k)ᗮ` then (`Submodule.mem_orthogonal`,
`Submodule.subset_span ⟨z, hz, rfl⟩`) `ι h z = ⟪k z, h⟫ = 0` for `z ∈ ℂ₊`, so `h = 0`
(`DBAxioms.eq_zero_of_upper`). ∎

```lean
theorem exists_seq_kernelSpan [CompleteSpace H] (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k)
    (h : H) : ∃ x : ℕ → H, (∀ n, x n ∈ kernelSpan k) ∧ Tendsto x atTop (𝓝 h) := by
  sorry
```
*Proof.* `h ∈ ⊤ = (kernelSpan k).topologicalClosure`, whose carrier is `closure (kernelSpan k)`
(`Submodule.topologicalClosure_coe`, `Topology/Algebra/Module/Basic.lean:173`); `mem_closure_iff_seq_limit`
(`Topology/Sequences.lean:108`). ∎

```lean
theorem memHE_iota [CompleteSpace H] (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) (h : H) :
    MemHE (kernelE ι k) (ι h) ∧ heNormSq (kernelE ι k) (ι h) ≤ ENNReal.ofReal (‖h‖ ^ 2) := by
  sorry
```
*Proof.* Take `x_n` from `exists_seq_kernelSpan`; `ι x_n ∈ H(E)` and `heNormSq E (ι x_n) = ofReal ‖x_n‖²` (C.10).
1. *Pointwise convergence.* For `z` nonreal, `ι x_n z → ι h z` (`(hax.h2 z hz).tendsto h` composed with `x_n → h`).
   For `z ∈ ℂ₊`: `ι x_n z / E z → ι h z / E z` (`Tendsto.div_const`) and
   `fstar (ι x_n) z = conj (ι x_n (conj z)) → fstar (ι h) z` (`(conj z).im ≠ 0`, `Complex.continuous_conj`).
2. *Line bounds.* For `y > 0`: `∫⁻ ‖ι x_n/E (x+iy)‖ₑ² ≤ heNormSq E (ι x_n) = ofReal ‖x_n‖²`
   (`MemHE.lintegral_line_le_of_isHB`), and the same for `fstar (ι x_n)` (P3 `memHE_fstar`, `heNormSq_fstar`).
3. *Fatou.* `lintegral_line_le_liminf` with `F n := fun z ↦ ι x_n z / E z` (differentiable on `ℂ₊`: entire over `E ≠ 0`)
   gives `∫⁻ ‖ι h/E (x+iy)‖ₑ² ≤ liminf ofReal ‖x_n‖² = ofReal ‖h‖²` (`Filter.liminf_le_liminf`,
   `Filter.Tendsto.liminf_eq`, `ENNReal.tendsto_ofReal`, `(continuous_norm.tendsto h).comp`, `.pow 2`). Same for `fstar`.
4. So `IsH2Upper (ι h / E)` and `IsH2Upper (fstar (ι h) / E)` with the constant `Real.toNNReal ‖h‖²`
   (`ENNReal.ofReal = ↑(Real.toNNReal ·)`), and `ι h` is entire: `MemHE E (ι h)`.
5. `heNormSq E (ι h) ≤ ofReal ‖h‖²`: `MemHE.heNormSq_le_of_lines_of_isHB` with step 3. ∎

```lean
theorem heNormSq_iota [CompleteSpace H] (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) (h : H) :
    heNormSq (kernelE ι k) (ι h) = ENNReal.ofReal (‖h‖ ^ 2) := by
  sorry
```
*Proof.* Let `a := (heNormSq E (ι h)).toReal`; by `memHE_iota`, `ι h ∈ H(E)`, `heNormSq < ⊤`, `a ≤ ‖h‖²`. Take `x_n`
as above. For each `n`: `⟪x_n, h⟫ = heInner E (ι h) (ι x_n)` (`heInner_iota_of_mem_kernelSpan` with
`hh := (memHE_iota hax hk h).1`), so `‖⟪x_n, h⟫‖ ≤ √a · ‖x_n‖` (`norm_heInner_le_of_isHB`,
`heNormSq_iota_of_mem_kernelSpan`, `ENNReal.toReal_ofReal`, `Real.sqrt_sq`). Let `n → ∞`: `⟪x_n, h⟫ → ⟪h, h⟫ = ‖h‖²`
(`Filter.Tendsto.inner`, `InnerProductSpace/Continuous.lean:71`) and `‖x_n‖ → ‖h‖`; `le_of_tendsto_of_tendsto'` gives
`‖h‖² ≤ √a ‖h‖`. If `‖h‖ = 0`, then `a ≤ 0`, so `a = 0 = ‖h‖²`. Otherwise `‖h‖ ≤ √a`, i.e. `‖h‖² ≤ a`. Hence
`a = ‖h‖²` and `heNormSq E (ι h) = ofReal a = ofReal ‖h‖²` (`ENNReal.ofReal_toReal`). ∎

```lean
theorem mem_range_of_memHE [CompleteSpace H] (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k)
    {f : ℂ → ℂ} (hf : MemHE (kernelE ι k) f) : f ∈ Set.range ι := by
  sorry
```
*Proof.* Let `Λ : H →ₗ[ℂ] ℂ`, `Λ h := heInner E (ι h) f`: additive by `heInner_add_left_of_isHB hE` (with
`(memHE_iota _).1` for both summands, `hf`, and `ι (x + y) = fun z ↦ ι x z + ι y z`), homogeneous by P3
`heInner_smul_left`. Bound: `‖Λ h‖ ≤ √(heNormSq E f).toReal · ‖h‖` (`norm_heInner_le_of_isHB`, `heNormSq_iota`,
`Real.sqrt_sq`). `Λc := Λ.mkContinuous _ bound` (`LinearMap.mkContinuous`,
`Analysis/Normed/Operator/ContinuousLinearMap.lean:55`), `u := (InnerProductSpace.toDual ℂ H).symm Λc`.
For `z ∈ ℂ₊`:
`ι u z = ⟪k z, u⟫ = conj ⟪u, k z⟫ = conj (Λc (k z)) = conj (heInner E (ι (k z)) f) = heInner E f (ι (k z))
= heInner E f (deBrangesKernel E z) = f z`
(`hk`, `inner_conj_symm`, `toDual_symm_apply`, P3 `heInner_conj_symm`, `kernel_eq_deBrangesKernel`,
`heInner_kernel_upper_of_isHB hE hf`). `eq_of_eqOn_upper (hax.entire u) hf.1` gives `ι u = f`. ∎

### 1.7 Assembly (proved)

```lean
theorem theoremC_holds : TheoremC := by
  intro H _ _ _ ι hinj hent h1 h2 h3 hne
  have hax : DBAxioms ι := ⟨hinj, hent, h1, h2, h3, hne⟩
  obtain ⟨k, hk⟩ := exists_kernel hax
  refine ⟨kernelE ι k, (isStrictHB_kernelE hax hk).1, fun f ↦ ⟨fun hf ↦ ?_, ?_⟩,
    fun h ↦ (heNormSq_iota hax hk h).symm⟩
  · exact mem_range_of_memHE hax hk hf
  · rintro ⟨h, rfl⟩
    exact (memHE_iota hax hk h).1
```

---------------------------------------------------------------------------------------------------
## 2. Part F (Theorem 32) — deferred

**Status: deferred** (not attempted; estimate 5–8k lines, §0). The statements are in
`FourierFrames/Cited/DeBrangesFC/PartF.lean` (`section PartF` and `theoremF_holds`, all `sorry`), which is built
only by the Lake target `FourierFramesScaffold`; `TheoremF` stays a hypothesis of the main results.
**`division_lemma` (F.8) is false as stated** (R10 finding 1; see F.8). R10 checked the truth of the other Part F
statements, and they are true.

*Unchanged from the assessment version except the R7-11 note on F.4 and the R10 note on F.8; the R7 corrections in
§6 (items 3–6) supersede the text they refer to. The lemmas take `hD : TheoremD` explicitly, and P3's
`theoremD_holds` (imported) can be supplied.*

Hypotheses: `E` strict, no real zeros; `μ` with `∫⁻‖f/E‖²dμ = ‖f‖_E²` on `H(E)` (`IsIsometricMeasure`).  Conclusion with `p=0`.

### F.1 `isometric_moment`
Apply the isometry to `f=K(i,·)∈H(E)` (TheoremD).  `|K(i,t)/E(t)|² = (1/4π²)|Ē(i)−Ē^*(i)Θ(t)|²/(t²+1)` and `|Θ(t)|=1` (`|E^*(t)|=|E(t)|` on `ℝ`), so
`≥ (|E(i)|−|E^*(i)|)²/(4π²(1+t²))`, `|E(i)|>|E^*(i)|`.  Hence `∫dμ/(1+t²)≤ C·‖K_i‖²<∞`.  Also `μ` is locally finite (not needed).

### F.2 `herglotzG_spec`
`g(z)=−(i/π)∫(1/(t−z) − t/(1+t²))dμ(t)+ic`.  Integrand bounded by `C_z/(1+t²)`, locally uniformly in `z`; holomorphy of parameter integrals
(Mathlib `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, or Morera + Fubini).
`Re(−i/(π(t−z)))=y/(π|t−z|²)`; the second term contributes a purely imaginary number.  So `Re g = poissonInt μ z`
(finite by F.1).  *Only the real part of the Herglotz representation is used; no uniqueness theorem for positive harmonic functions is needed.*

### F.3 `cauchy_pairing_zero` (Romanov (67))
For `w,v∈ℂ₊` with `E^*(w)=E^*(v)=0`: `K(w,t)/E(t)=(i/2π)Ē(w)/(t−w̄)` (no `Θ`-term).  Isometry polarised (TheoremD: `⟨K_v,K_w⟩_E=K(v,w)`):
`(1/4π²)Ē(v)E(w)∫dμ/((t−v̄)(t−w)) = K(v,w) = (i/2π)E(w)Ē(v)/(w−v̄)`, hence the Lean statement `∫dμ/((t−v̄)(t−w)) = 2πi/(w−v̄)`.
(Integrability: Cauchy–Schwarz and F.1.)  Consequence with `1/((t−v̄)(t−w))=(1/(w−v̄))(1/(t−w)−1/(t−v̄))`:
`g(w)+conj g(v) = 2` for the Herglotz transform `g` (with constant `c=0`), i.e. `Re g(w)=1`, `Im g(w)=Im g(v)` on `Z={Θ=0}`.

### F.4 `cauchy_pairing_general`
Pair `K(w₀,·)` (`w₀∈Z`) with `K(z,·)`, `z∈ℂ₊`: `K(z,t)/E(t)=(i/2π)(Ē(z)−Ē^*(z)Θ(t))/(t−z̄)`; the `Θ`-term is bounded in modulus by
`|Ē^*(z)|·(∫dμ/|t−w̄₀|²)^{1/2}(∫dμ/|t−z|²)^{1/2}` and `∫dμ/|t−z|²=πP[μ](z)/y` with `P≲1`.  Dividing by `Ē(z)` (`|Ē^*(z)/Ē(z)|=|Θ(z)|`) gives the stated error `C|Θ(z)|/√y` (use F.5 for `P(z)≤2`).
(*R7-11, applied:* F.5 gives `P(z) ≤ (1+s)/(1−s) ≤ 3` only where `s = |Θ(z)| ≤ 1/2`, so the scaffold statement now
assumes `‖thetaFn E z‖ ≤ 1/2`, and the constant is `C = √(3π)·(∫dμ/|t−w̄₀|²)^{1/2}` (finite by F.1). F.9 uses F.4 only
as `Im z → ∞`, where `|Θ(z)| ≤ e^{−a Im z}`.)
```lean
theorem cauchy_pairing_general (hD : TheoremD) (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0)
    (hμ : IsIsometricMeasure μ E) {w₀ : ℂ} (hw₀ : 0 < w₀.im) (hz0 : fstar E w₀ = 0) :
    ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im → ‖thetaFn E z‖ ≤ 1 / 2 →
      ‖∫ t : ℝ, (((t : ℂ) - conj w₀)⁻¹ * ((t : ℂ) - z)⁻¹) ∂μ - 2 * Real.pi * I / (z - conj w₀)‖ ≤
        C * ‖thetaFn E z‖ / Real.sqrt z.im := by
  sorry
```

### F.5 `poisson_diag_estimate`
Isometry on `K(z,·)`: `‖K_z‖²=K(z,z)=(|E(z)|²−|E^*(z)|²)/(4π y)` and
`∫|K(z,t)|²|E|^{-2}dμ=(1/4π²)|E(z)|²∫|1−Θ̄(z)Θ(t)|²dμ/|t−z̄|²` with `|1−Θ̄(z)Θ(t)|∈[1−s,1+s]`, `s=|Θ(z)|`.  With `∫dμ/|t−z̄|²=πP(z)/y`:
`(1−s)²P ≤ 1−s² ≤ (1+s)²P`... i.e. `(1−s)/(1+s) ≤ P(z) ≤ (1+s)/(1−s)`, so `|P−1|≤4s` for `s≤1/2`.

### F.6 `exists_imag_limit`
`u=Re g−1`, `|u|≤Ce^{−ay}` on `y≥1`.  Cauchy estimates for harmonic derivatives: `|∇u(z)|≤C'e^{−a'y}` on `y≥2` (mean value on the disc of radius 1, `a'<a`).  By Cauchy–Riemann `|∂_y Im g|=|∂_x u|`, `|∂_x Im g|=|∂_y u|`, both `≲e^{−a'y}`.  So `Im g(x+iy)` converges as `y→∞` to some `c` independent of `x` and
`|Im g−c|≲e^{−a''y}`.  (Romanov's "locally uniform in `Re w`" suffices; the version here assumes uniform estimates, which F.5 gives since `|Θ(z)|≤e^{−ay}` uniformly in `x`.)

### F.7 `inner_factorization` (**the hard analytic lemma, not in Mathlib**)
`Θ` is holomorphic on `ℂ₊`, `|Θ|≤1`, continuous on a neighbourhood of `ℝ` with `|Θ|=1` there (no real zeros of `E`).  Claim `Θ=e^{i(az+θ)}B`, `a≥0`, `B` Blaschke product of the zeros of `Θ` (the zeros of `E^*` in `ℂ₊`).
Proof outline: (i) Blaschke condition `∑ Im z_j/(1+|z_j|²)<∞` from boundedness: Jensen on discs/Carleman's formula for the half-plane (Mathlib has `JensenFormula` for discs; map half-plane to disc by Cayley, `Mathlib/Analysis/Complex/UpperHalfPlane`).
(ii) The product `B` converges (standard), `|B|≤1`, `Θ/B` zero-free holomorphic with `|Θ/B|≤1` (finite partial products and maximum principle/PL, as in (iii)).
(iii) `log|Θ/B|` is a non-positive harmonic function on `ℂ₊` with boundary values `0` on `ℝ` (continuity of `Θ` and `|B|→1` at the boundary away from accumulation... careful: `B` has no accumulation on `ℝ` since `Θ` is analytic/unimodular near `ℝ`, so zeros are discrete and bounded away from compacts... needs an argument).  A non-positive harmonic function on `ℂ₊` vanishing on `ℝ` is `−a y` (Herglotz/Poisson representation with zero boundary measure — **or** reflect across `ℝ` using Schwarz reflection (harmonic function vanishing on a line extends oddly), then Liouville for harmonic functions with a one-sided bound: `Mathlib/Analysis/Complex/Harmonic/Liouville.lean`).  This reflection trick avoids Herglotz and is the recommended route.  (*R7-12:* the reflected function has no one-sided bound on `ℂ`; finish instead with the entire-Pick lemma, §6.)  So `Θ/B=e^{−ay+i(\ldots)}=e^{i(az+θ)}`.
Blaschke division (second conjunct): if `Ψ` bounded by `M`, vanishing on zeros of `B` with multiplicity, then `|Ψ|≤M|B|`: for finite sub-products `B_n`, `Ψ/B_n` is holomorphic and `limsup |Ψ/B_n|≤M` at the boundary and at `∞` (the finite Blaschke product is unimodular on `ℝ`, tends to a unimodular limit at `∞`) — maximum principle in `ℂ₊` for bounded functions (Phragmén–Lindelöf, `Mathlib/Analysis/Complex/PhragmenLindelof.lean` has half-plane versions); let `n→∞`.
Orders: `analyticOrderAt`.

### F.8 `division_lemma`
`Ξ_1=Ξe^{−ia'z}` is bounded on `ℂ₊` (by `max(C,e^{a'})`: use `|Ξ|≤1` on `0<y<1`, decay on `y≥1`), vanishes with multiplicity where `Θ` does, so by F.7 `|Ξ_1|≤C_1|B|`, i.e. `|Ξ|≤C_1e^{−a'y}|B|=C_1 e^{(a−a')y}|Θ|`.  Thus `Ψ=Ξ/Θ` (holomorphic: removable singularities at zeros of `Θ`) satisfies `|Ψ|≤C_1e^{(a-a')y}` on `ℂ₊`, and
`limsup |Ψ(z)|≤1` at every real point (`|Ξ|≤1`, `|Θ|→1`).  Apply Phragmén–Lindelöf (bounded version) to `Ψe^{iεz}` with `ε=a−a'`: `|Ψ|≤e^{εy}`; let `ε→0`: `|Ψ|≤1`.

**False as stated (R10 finding 1; Lean disproof in `reviews/R10_TheoremC.md`, Appendix A).** In the Lean statement
the only link between `(a, θ, B)` and `Θ` is `hfac : Θ = e^{i(az+θ)}B` on `ℂ₊`, and every real `a` satisfies it (take
`B := Θe^{−i(az+θ)}`). Counterexample: `E = e^{−iz/2}`, `Θ = e^{iz}`, `a = θ = 0`, `B = Θ`, `Ξ ≡ 1/2`. The
conclusion at `z = 10i` would give `1/2 ≤ e^{−10}`. The argument above applies F.7's division clause to *this* `B`,
which is valid only for the `B` of `inner_factorization`.
*Repair* (before any attempt): add the rest of F.7's conclusion as hypotheses: `0 ≤ a`, `‖B z‖ ≤ 1` on `ℂ₊`, and
the Blaschke-division clause. The division clause pins `a` to the true type; the first two alone do not repair the
lemma. Alternatively, merge the division clause into F.8 (R7-12, §6 item 5). F.9 applies F.8 only to the
`(a, θ, B)` of F.7, so nothing downstream changes. The scaffold keeps the false statement with `sorry`, marked
`-- FALSE`.

### F.9 Assembly (`theoremF_holds`)
Let `Z={z∈ℂ₊: Θ(z)=0}={zeros of E^*}`; `a` from F.7.  Let `g_0=herglotzG μ 0`.
* **Case `a>0`.**  By F.5 (note `|Θ(z)|≤e^{−ay}`), `|Re g_0−1|≤4e^{−ay}` for `y≥y_0`; F.6 gives `c`, `|g_0−1−ic|≲e^{−a'y}`.  If `Z≠∅`: F.4 and the Herglotz formula give for `w₀∈Z`: `g_0(z)+conj g_0(w₀)→2` as `y→∞`, so `g_0(w₀)=1+ic`: **the constant `c` from decay and the constant from `Z` agree** (this repairs a gap in Romanov: he fixes the constant by decay and claims `Ξ(z)=0` on `Z` from `Re g=1` alone).  For zeros of order `m>1` use the same pairings for the derivative kernels `∂_{w̄}^jK(w,·)` (reproducing property of derivatives; `⟨f,∂^jK_w⟩=f^{(j)}(w)`) — **sketch only, to be checked**.
* **Case `a=0`.**  `Θ=e^{iθ}B`, `Re g_0=1` on `Z` (F.3; `Z` need not be infinite, R7-13, but `Z≠∅`); F.3 shows `Im g_0` is the same constant `c_Z` on `Z`, choose `c=−c_Z`... (`Z≠∅` since `Θ` nonconstant by strictness).  No decay is needed: `Ξ/B` is bounded by 1 by Blaschke division, `hdec` is vacuous (`a'<0`... the division lemma with `a=0` follows from F.7 directly with `M=1`).
Set `g=g_0−ic`, `Ξ=(g−1)/(g+1)` (`Re g>0` so `g+1≠0`, `|Ξ|<1`), `A:=Ξ/Θ` (zero set: removable).  By F.8 `|A|≤1`.  `1−ΘA=1−Ξ=2/(g+1)≠0`, `(E+E^*A)/(E−E^*A)=(1+ΘA)/(1−ΘA)=(1+Ξ)/(1−Ξ)=g`,
so `Re(...)=Re g=poissonInt μ z` (F.2) with `p=0`.  `A` is `DifferentiableOn` `UHP`.

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
## 3. Mathlib / project inventory

* Present in Mathlib and used by Part C: `InnerProductSpace.toDual` (+ `toDual_symm_apply`), `ext_inner_right`,
  `inner_eq_sum_norm_sq_div_four`, `LinearIsometry.inner_map_map`, `Submodule.topologicalClosure_eq_top_iff`,
  `Submodule.topologicalClosure_coe`, `mem_closure_iff_seq_limit`, `Filter.Tendsto.inner`, `LinearMap.mkContinuous`,
  `analyticOrderAt` API (`AnalyticAt.analyticOrderAt_eq_natCast`, `analyticOrderAt_eq_zero`,
  `AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero`), meromorphic normal form (`toMeromorphicNFOn`, `meromorphicOrderAt_div`,
  `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`), identity theorem (`AnalyticOnNhd.eq_of_eventuallyEq`),
  Fatou (`lintegral_liminf_le`), Hölder (`ENNReal.lintegral_mul_le_Lp_mul_Lq`, as in P3, in place of the planned
  `integral_mul_le_Lp_mul_Lq_of_nonneg`). Mathlib also has RKHS theory (`Analysis/InnerProductSpace/Reproducing.lean`,
  `RKHS.equiv`), not used (§1.0). `Continuous.ext_on` and `dense_compl_singleton` were planned (§1.5) but not
  used: the identity theorem on the complement of a finite set replaced them.
* Present in Mathlib for Part F: Phragmén–Lindelöf (`Analysis/Complex/PhragmenLindelof`), harmonic functions
  (`HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq`), parametric holomorphic integrals. Absent: half-plane Poisson kernel,
  Herglotz measure representation, Blaschke products, inner–outer factorization.
* From P3 (imported): the `IsH2Cont` Cauchy layer and the kernel layer (see **Depends on**).
* From the project: `HB/H2` (`not_isH2Upper_div_of_zero`, `IsH2Upper.congr`, `measurable_line_sq`), `HB/Comparable`
  (`lintegral_real_le_of_isH2`), `HB/DeBranges` (`countable_real_zeros`), `Theorem1/Necessity` (`samp_H1..3`: the
  hypotheses of Theorem C for the sampling space).
* Missing (must be written for F): Blaschke products with convergence, Blaschke division, factorization of meromorphic
  inner functions (F.7); harmonic derivative estimates (F.6).

## 4. Issues in the source / the statements
1. **Romanov, App. II (⇒)** (the proof we follow): "`Re g=1` at a zero of `S` implies `Ξ(z)=0`" needs `Im g=0` there; the imaginary constant is claimed to be fixed by two requirements (zeros, decay) that are independent a priori (R7-10; "incompatible" in an earlier version of this note was wrong); compatibility is a genuine step (F.4/F.9 above).  Also multiplicities ("easy") are not proved.  Also "`w` a root of `W`" should read root of `W^*` in the upper half-plane (his `W` is HB).  Confidence: high for the first point, medium for the multiplicity gap being real.
2. Romanov's theorem has `c_0≥0` only in the converse; in our direction `p=0` always, so the `p` of `TheoremF` is slack (kept as stated, supply `p=0`).
3. `TheoremC`: statement true; note the conclusion cannot require `E` without real zeros (example `{f∈PW: f(0)=0}`); the project already uses closed `IsHB`.  The `E` produced is even strict on `ℂ₊` (`isStrictHB_kernelE`).  Consequence for the formalization: P3's `TheoremD` (strict, no real zeros) and P3's `h0`-gated `Space.lean` lemmas cannot be applied to this `E`; §1.2–1.3 supply the real-zero versions.  Confidence: certain.
4. `TheoremF` needs `TheoremD` (P3) for `K(w,·)∈H(E)` and its reproducing property; P4 now imports P3 (`theoremD_holds` is available; the Part F lemmas keep `hD : TheoremD` as an explicit hypothesis).  (No cycle: D does not use C or F.)
5. Constant check: with `K` in the norm of `H` and `‖f‖²_E=∫|f/E|²`, `E=√π P` (not `P`), verified on `PW` (also independently by R7-6).
6. **de Branges' proof of Theorem 23 vs. ours.** de Branges (and Remling) identify the spaces through the reproducing kernel and a completeness argument in `H(E)`.  The route here never uses completeness of `H(E)`: the inclusion `H ⊆ H(E)` is obtained by Fatou along a sequence from the span of kernels, and the reverse inclusion by Riesz in `H` together with the reproducing formula of `H(E)` at `ℂ₊` (§1.0, step 4).  This is a simplification for the formalization, not a correction.  Confidence: high.
7. **Superseded statements of the previous scaffold** (all true, replaced by cheaper ones): `kernel_formula` (pointwise, `z ≠ w̄`) by the function equality `kernel_eq_deBrangesKernel`; `isHB_kernelE` by `isStrictHB_kernelE` (same content); `kernel_gram`, `range_subset`, `reproducing_HE`, `range_eq` (the from-scratch `H²` route) by §1.3 + §1.6.  The stub `theoremD_holds` is deleted (R7-8).  **No Part C statement of the scaffold is false** (confirmed by R10). In Part F, `division_lemma` is false as stated (R10 finding 1, §2 F.8). The previous `cauchy_pairing_general` was unproved and possibly false as stated (R7-11) and now carries `‖thetaFn E z‖ ≤ 1/2`.

## 5. Risks
* **Part C (moderate; written before the implementation).** *Outcome:* proved in 1046 lines. P3 was proved first,
  `toMeromorphicNFOn` worked, and the global factorisation went through `divExt` (§1.2).
  * *Dependency on P3.* `heInner_kernel_upper_of_isH2Cont`, `memHE_deBrangesKernel_of_isHB`, the kernel algebra
    (`deBrangesKernel_mul`, `deBrangesKernel_diag`, `differentiable_deBrangesKernel`) and the `IsH2Cont` bounds were
    `sorry` when this was written; Part C could not be unconditional until P3's `Cauchy.lean` and `Kernel.lean` were proved. If P3's
    signatures change (e.g. hypotheses weakened from `IsHB` to `Differentiable`), only the sorried P4 proofs are
    affected; the P4 statements and the assembly are unaffected.
  * *C.5 (`exists_mulMap`, `kernel_identity`).* The heaviest Hilbert-space bookkeeping (choice-defined `T`, linearity
    by injectivity, polarization, surjectivity via (H1) at `ζ̄`); about 250–400 lines.
  * *Meromorphic normal form.* First use of `toMeromorphicNFOn` in the project; if awkward, use the `limUnder`
    fallback (§1.2, `divExt`), at the cost of about 100 more lines.
  * *Global factorisation at a real zero* in `analyticOrderAt_le_of_isH2Upper_div` (`Function.update` quotients).
  * *Integral plumbing* (§1.3): Hölder with `rpow`, `ofReal`/`toReal` conversions; routine.
* **Part F (high; deferred).** F.7 (factorization of a meromorphic inner function) is the largest single missing
  piece; multiplicity-`>1` zeros of `Θ` in F.9 need derivative kernels (R7-10 sketches the fix); F.7(iii) must end with
  the entire-Pick lemma, not Liouville (R7-12); `division_lemma` (F.8) must first be restated (R10 finding 1).
* **Scope (R7-15).** Part C alone (with P1, P3) makes only `completeInterpolating_zero_set` unconditional;
  `theorem1_necessity`, `theorem1`, `corollary1`, `landau_inequality` also need `hF`.

---------------------------------------------------------------------------------------------------
## 6. Referee corrections (R7)

From `reviews/R7_Cited.md`, Part 2 (2026-11-07). R7 confirms C.1–C.8 (including the formula
`E = √π (z+i)K(i,z)/√K(i,i)`, checked independently on `PW`), F.1–F.3, F.5, F.6, and that `TheoremC`
and `TheoremF` are true as stated. The items below supersede the text they refer to.
**Status after the Part C rewrite (2026-11-07):** items 1 and 2 are *applied* (§1 and the scaffold); item 4 is
applied to the scaffold statement of `cauchy_pairing_general`; items 3, 5, 6 concern the deferred Part F and stand
as written; item 7 is reflected in §0 and §5.

1. **[applied in §1] Part C through P3 (R7-7; replaces C.9–C.12).** C.9–C.12 re-prove Theorem D plus a completeness
   argument, which P3 builds. Route: by C.7, `ι(k_w) = K_E(w,·)` as entire functions. With Theorem D for
   this `E`:
   - the Gram matrices `⟪k_w, k_v⟫_H` and `⟨K_E(w,·), K_E(v,·)⟩_E` coincide, so `ι` is isometric on
     `span{k_w}`;
   - the span is dense in `H`: `h ⊥ k_w` for all `w` gives `ι h = 0` on `ℂ ∖ ℝ`, hence `ι h = 0`;
   - by completeness of `H(E)` (P3 `memHE_of_cauchy`) and continuity of evaluation at nonreal points,
     `ι(H) ⊆ H(E)` isometrically;
   - if `f ∈ H(E)` is orthogonal to `ι(H)`, then `f(w) = ⟨f, K_E(w,·)⟩_E = 0` for nonreal `w`, so `f = 0`.

   The clean form of C.11 has two terms: `conj(K(w,t)/E(t)) = (−i/2π)(E(w) − E^*(w) conj Θ(t))/(t − w)`;
   `∫ (f/E)(t)/(t − w) dt = 2πi (f/E)(w)` (P3 `IsH2Cont.cauchy_upper`); on `ℝ`,
   `(f/E)·conj Θ = f/E^* = conj(f^*/E)`, so the second term is `∫ conj((f^*/E)(t))/(t − w) dt = 0`
   (P3 `IsH2Cont.cauchy_conj_upper`).

   *As implemented (§1.0 step 4):* the last two bullets are replaced by Fatou along a sequence of the span
   (no completeness of `H(E)`) and Riesz in `H` (no projection in `H(E)`), because P3's `memHE_of_cauchy` and its
   `heInner` algebra assume no real zeros, and P3 never builds `H(E)` as a type. Of the two facts in the next
   paragraph only the first is needed (`analyticOrderAt_le_of_isH2Upper_div`); the second (`Θ` across `ℝ`) is not,
   since P3's `memHE_deBrangesKernel_of_isHB` already covers `E` with real zeros.

   *Obstacle.* P3's kernel layer assumes `IsStrictHB E` and no real zeros (`isH2Cont_of_memHE`,
   `memHE_deBrangesKernel`, `heInner_kernel_nonreal`); the `E` of Theorem C is strict but may have real zeros
   (C.10). Generalise P3's *internal* kernel lemmas (not the frozen `TheoremD`) to strict `E` with real
   zeros. Two facts are needed: `f ∈ H(E)` vanishes at a real zero `t₀` of `E` to at least its order (an
   order version of `not_isH2Upper_div_of_zero`), which makes `f/E` `IsH2Cont`; and `Θ = E^*/E` extends
   analytically across `ℝ` with `|Θ| = 1` (`E` and `E^*` have the same real zeros with the same orders).
   P3's Cauchy layer (`Cauchy.lean`) is stated for general `IsH2Cont F` and needs no change. Cost: about
   1.5–2.5k lines on top of P3, against 2.5–4k from scratch. (P3 names as in the master scaffold of
   2026-11-07; P3's blueprint `P3_DeBrangesDE.md` is forthcoming.)
2. **[applied] Stub clash (R7-8).** `DeBrangesFC.lean` declares `theorem FF.theoremD_holds : TheoremD := by sorry`,
   and P3 declares the same name. Importing both gives a duplicate-declaration error, and every Part F
   lemma that uses the stub carries `sorryAx`. Fix at P3 assembly: `import FourierFrames.Cited.DeBrangesDE`
   here and delete the stub (no cycle: D uses neither C nor F).
3. **Romanov's gap (R7-10).** The two requirements on the imaginary constant (`Im g = 0` on `Z`,
   `Im g → 0` at `i∞`) are independent a priori, not incompatible; F.3 and F.4/F.9 show that they agree.
   *Multiplicities* (§5 "unchecked"): let `w₀` be a zero of `E^*` of order `m`. For `k < m` the kernel of
   `f ↦ f^{(k)}(w₀)`, divided by `E`, has no `Θ`-term, because the derivatives of `Ē^*` up to order `k`
   vanish at `w₀`. Pairing it with `K_{w₀}` gives
   `∂_z^k[(g(z) + conj g(w₀) − 2)/(z − w̄₀)]|_{z=w₀} = 0` for `k < m`. With `g(w₀) = 1`, `g − 1` has a zero
   of order `m` at `w₀`, and so does `Ξ`. Derivative kernels are needed on one side only.
4. **[applied to the statement] F.4 is overstated (R7-11).** `cauchy_pairing_general` (scaffold) claims the error `C|Θ(z)|/√(Im z)` for
   all `Im z ≥ 1`, but the proof needs `P(z) ≤ 2`, which F.5 gives only where `|Θ(z)| ≤ 1/2`. On
   `{Im z ≥ 1}` the Poisson integral need not be bounded (for a Clark measure,
   `P = (1 − |Θ|²)/|α − Θ|²`, and `|Θ(x + i)|` can approach `1` when the zeros of `E^*` are sparse), so the
   lemma is unproved as stated and may be false. Repair: add the hypothesis `‖thetaFn E z‖ ≤ 1/2`, as in
   F.5. F.9 uses F.4 only for `y → ∞` with `|Θ(z)| ≤ e^{−ay}`, so nothing downstream changes.
5. **F.7(iii): reflection, then the entire-Pick lemma (R7-12).** A non-positive harmonic `u = log|Θ/B|` on
   `ℂ₊` with zero boundary values, reflected oddly, is `≤ 0` on `ℂ₊` and `≥ 0` on `ℂ₋`: there is no
   one-sided bound on `ℂ`, and Mathlib's harmonic Liouville theorem covers only bounded functions. Finish:
   the odd extension `U` is entire harmonic, `U = Re H` with `H` entire
   (`HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq`); `G := −iH` is real on `ℝ` and `Im G = −U ≥ 0` on
   `ℂ₊`, so `G` is an entire Pick function, hence `az + b` with `a ≥ 0` (P3 `im_div_im_eq`,
   `EntireHerglotz.lean`); so `u = −ay`. Equivalently, reflect `Φ = Θ/B` by `Φ(z) := 1/conj Φ(z̄)` on `ℂ₋`,
   which gives a zero-free entire `Φ = e^H`. The reflection lemma costs about 0.3–0.5k lines (it needs `B`
   continuous up to `ℝ`).
   *Limits in F.7 and F.8.* For a finite Blaschke product `B_n` with zeros `x_j + iy_j`,
   `|B_n(x + iδ)| ≥ ∏ (y_j − δ)/(y_j + δ)` uniformly in `x`. Apply Mathlib's bounded half-plane
   Phragmén–Lindelöf (`PhragmenLindelof.right_half_plane_of_bounded_on_real`, after rotation) to
   `Ξ e^{−ia'z}/B_n` on `{Im z > δ}`, then let `δ → 0`, `n → ∞`, `a' → a`. This gives `|Ξ| ≤ e^{−ay}|B| = |Θ|`
   with constant `1` and without dividing by `Θ`, and merges the division clause of F.7 with F.8.
6. **F.9, case `a = 0` (R7-13).** "`Z` is then infinite" is false (if `E` is a polynomial with zeros in
   `ℂ₋`, `Θ` is a finite Blaschke product with `a = 0`). Only `Z ≠ ∅` is used, and it holds since `Θ` is
   nonconstant.
7. **Scope (R7-15).** `hC` occurs in `theorem1_necessity`, `theorem1`, `corollary1` and
   `landau_inequality`, all of which also need `hF`, and in `completeInterpolating_zero_set` (with `hD`).
   So Part C alone (with P1 and P3) makes only `completeInterpolating_zero_set` unconditional. Recommended
   plan (`PHASE2.md`): do C after P3, through Theorem D (item 1); defer F and keep `hF`. If F is ever
   attempted, first apply items 4 and 5; estimate 5–8k lines plus about 0.5k.
