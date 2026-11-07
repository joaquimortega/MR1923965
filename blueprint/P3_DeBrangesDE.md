# P3 — de Branges' Theorems D (book Thm 19) and E (book Thm 22)

**Status: proved** (merged 2026-11-07: branch `impl/cited-p3d` for Theorem D, `impl/cited-p3e` for
Theorem E, developed in parallel). No `sorry`; `#print axioms` of `FF.theoremD_holds` and
`FF.theoremE_holds` gives `[propext, Classical.choice, Quot.sound]`; both are among the 33 theorems
accepted by comparator, and `FourierFrames/Unconditional.lean` uses them. 3726 lines in 9 files:
Theorem D 1647 (`Cauchy` 837, `Kernel` 675, helper `CauchyAux/Basic` 135; estimate below 2–2.5k),
Theorem E 2039 (`Space` 455, `EntireHerglotz` 279, `Orthogonal` 880, `Complete` 383, helper
`EAux/KernelSymm` 42), top file 40 (estimate 4.3–6.2k in all). Implementers' notes:
`impl_notes/cited-p3d.md`, `impl_notes/cited-p3e.md`. Referee report on this blueprint and the scaffold:
`reviews/R9_DeBrangesDE.md` (0 critical, 0 major, 8 minor). The implementers applied F1–F3, F7 and F8
(see the *Implemented:* notes); F4 was done at assembly except for the stub in `DeBrangesFC.lean` (§8);
F5 and F6 are applied in "Issues in the source". No statement was false. The statement blocks below
match the code, with `sorry` in place of the proofs (checked mechanically for all 159 declarations).
Seven of them lost an unused hypothesis during the implementation; each has an *Implemented:* note.
The code adds helper lemmas not listed here.

**Lean files.**
* `FourierFrames/Cited/DeBrangesDE.lean`: assembly, ends with `theoremD_holds : TheoremD` and
  `theoremE_holds : TheoremE`.
* Subfiles (`FourierFrames/Cited/DeBrangesDE/`): `Cauchy.lean` (§1), `Kernel.lean` (§2–3),
  `Space.lean` (§4), `Orthogonal.lean` (§5), `EntireHerglotz.lean` (§6), `Complete.lean` (§7);
  helpers `CauchyAux/Basic.lean` (Tonelli on strips, good abscissae, the rectangle identity, the AM–GM
  form of the domination hypothesis; imports only `HB.MeanValue`) and `EAux/KernelSymm.lean`
  (`deBrangesKernel_conj_symm`, see §2).
  Import chain: `HB.Comparable, CauchyAux/Basic → Cauchy → Kernel (+ HB.Phase) → Space → EAux/KernelSymm →
  Orthogonal → Complete (+ EntireHerglotz, which imports only Defs and uses no project lemma) →
  DeBrangesDE`.

**Paper.** p. 793–794 (tex l. 323–372): Theorem D (formula (1) and the reproducing property),
formula (2) `‖K_E(x,·)‖² = K_E(x,x) = φ'(x)|E(x)|²/π`, Theorem E.
**Sources.** L. de Branges, *Hilbert spaces of entire functions* (1968), Theorem 19 (p. 50) and
Theorem 22 (p. 55).  The proof of E given here is **not** de Branges' (his goes through Theorems
20–21 and Krein's theory of functions of bounded type); it is an elementary Mittag-Leffler /
entire-Pick-function argument (§5–§7), see *Issues in the source* 5.

**Depends on.**
* `Defs`: `TheoremD`, `TheoremE`, `deBrangesKernel`, `MemHE`, `heNormSq`, `IsH2Upper`, `IsHB`,
  `IsStrictHB`, `IsPhaseFunction`, `phaseDeriv`, `phaseLevel`, `orthWeight`, `fstar`.
* `HB/Basic`: `fstar_ofReal`, `norm_fstar`, `Differentiable.fstar`, `deriv_fstar`,
  `deriv_fstar_ofReal`, `fstar_add`, `fstar_const_mul`, `IsHB.norm_fstar_le`, `IsHB.rotate`,
  `isHB_one`.
* `HB/H2`: `IsH2Upper.add/sub/const_mul/congr`, `continuous_line`, `measurable_line_sq`,
  `enorm_add_sq_le`.
* `HB/MeanValue`: `enorm_sq_eq_ofReal`, `lintegral_strip` (as a model for Tonelli on strips).
* `HB/Comparable`: `lintegral_real_le_of_isH2` (Fatou step), `memLp_two_of_lintegral_lt_top`.
* `HB/Phase`: `IsStrictHB.phaseDeriv_pos`, `IsHB.phaseDeriv_nonneg`,
  `IsPhaseFunction.strictMono_of_isStrictHB`, `zero_set_eq_phaseLevel`, `IsPhaseFunction.rotate`.
* No cited `Prop` is used (no `hPW`, no `hC`, …): **P3 is unconditional.**

**Used by.** Every phase-1 lemma taking `hD : TheoremD` or `hE : TheoremE`
(`HB/DeBranges` (`HEEqPW.phaseDeriv_mul_sq_ge/le`), `Theorem1/Sufficiency*`, `Theorem1/Main`,
`Corollary1*`, `Corollary2`, `Landau`, `Theorem2i`, `LogExample`); P4 (`Cited/DeBrangesFC.lean`,
Part F uses `theoremD_holds`; Part C can reuse `Cauchy.lean` and `Kernel.lean`, see §9).

---------------------------------------------------------------------------------------------------

## 0. Summary, route, feasibility

### Notation
`ℂ₊ = {Im z > 0}`, `ℂ₋ = {Im z < 0}`; `f^* = fstar f`; `Θ = E^*/E`; `K_w = deBrangesKernel E w`;
`⟨f, g⟩ = heInner E f g = ∫_ℝ f conj g/|E|²`; `‖f‖² = heNormSq E f` (an `ℝ≥0∞`; we mostly use its
`toReal`).  For Theorem E: `U = e^{iα}E`, `V = e^{-iα}E^* = U^*`, `C = (U+V)/2 = cFun E α`,
`S = (U-V)/(2i) = sFun E α` (so `S_α = e^{iα}E - e^{-iα}E^* = 2iS`), `Γ = phaseLevel φ α`,
`wt(γ) = π/(φ'(γ)|E(γ)|²) = 1/K(γ,γ)`, `c_γ = cLev E γ = 1/(πφ'(γ))`, `d_γ = dslope S γ`
(entire, `d_γ(z) = S(z)/(z-γ)` for `z ≠ γ`, `d_γ(γ) = S'(γ)`).

### Theorem D (route)
1. *Half-plane Cauchy–Goursat* (`Cauchy.lean`): for `F ∈ IsH2Cont` (`H²(ℂ₊)` and continuous at
   every real point) and `G` continuous on `{Im ≥ 0}`, holomorphic on `ℂ₊`, dominated far from a
   point `w₀` by `|F|/|z-w₀| + A/|z-w₀|²`, `∫_ℝ G = 0`.  Proof: rectangles `[-Rₙ,Rₙ]×[0,Y]`
   (Mathlib's Cauchy–Goursat), sides vanish along a sequence `Rₙ` chosen by Tonelli, top line
   integral `→ 0` as `Y → ∞`.  No boundary values: `F` is continuous up to `ℝ`.
2. Cauchy formulas: `∫ F(t)/(t-w) = 2πi F(w)` (`w ∈ ℂ₊`), `= 0` (`w ∈ ℂ₋`), and the **regularized
   formula at a real point** `∫ (F(t) - F(x) i/(t-x+i))/(t-x) dt = 0` (needs `F` differentiable
   at `x`).  All three are `∫ dslope(...) = 0` instances of step 1.
3. `K_w ∈ H(E)`: `K_w/E = (i/2π)(conj E(w) - Θ conj E^*(w))/(z - w̄)` with `|Θ| ≤ 1`, plus an
   elementary decay criterion for `H²`; and `K_w^* = K_{w̄}`.
4. Reproducing formula: on `ℝ`, `f conj K_w/|E|² = (-i/2π)[E(w)(f/E)(t) - E^*(w) conj((f^*/E)(t))]/(t-w)`;
   for `w ∈ ℂ₊` (resp. `ℂ₋`) apply the upper formula to `f/E` (resp. `f^*/E` at `w̄`) and the lower
   formula to the other one; for real `w = x` split off `f(x)·2i/((t-x)²+1)` and use the regularized
   formula for both `f/E` and `f^*/E`.  **No limiting argument in `w`** (the previous plan used
   `K_{x+i/n} → K_x` in norm; replaced).

### Theorem E (route)
1. `Γ` is the zero set of `S` (all zeros real and simple, `S'(γ) = -C(γ)φ'(γ)`);
   `K(γ,·) = -(C(γ)/π) d_γ`; the `K_γ` are orthogonal with `‖K_γ‖² = 1/wt(γ)`.  Bessel's
   inequality, partial sums, Pythagoras.
2. `H(E)` is complete (`memHE_of_cauchy`, via the evaluation bound `|f(z)|² ≤ K(z,z)‖f‖²`, Fatou,
   and the line bound `∫|F(x+iy)|² ≤ ∫|F(t)|²` from the Poisson formula).  Hence every
   `Σ wt|a_γ|² < ∞` defines `g = Σ a_γ wt(γ) K_γ ∈ H(E)` with `g(γ) = a_γ` — this is the
   **interpolation half** of `TheoremE` (no hypothesis on `α` needed).
3. Mittag-Leffler: by Bessel for `K_i`, `Σ c_γ/(1+γ²) < ∞`; `R = Σ c_γ (1+γz)/(1+γ²) d_γ(z)` is
   entire, `D = C + πR` vanishes on `Γ`, so `h = D/S` is entire and real on `ℝ`.
4. The *defect kernel* `Q(w,z) = K(w,z) - Σ_γ K(w,γ)K(γ,z)wt(γ)` (reproducing kernel of the
   orthogonal complement of `{K_γ}`) satisfies `Q(w,z)π(z-w̄) = S(z)conj S(w)(h(z) - conj h(w))`;
   `Q(w,w) ≥ 0` (Bessel) gives `Im h ≥ 0` on `ℂ₊`.
5. An entire function, real on `ℝ`, with `Im h ≥ 0` on `ℂ₊` is `pz + q`, `p ≥ 0`
   (`EntireHerglotz.lean`, Poisson formula on discs from Mathlib).
6. If `p > 0`, then `Q(i,·) = (p/π)conj S(i)·S ∈ H(E)`, so `S_α = 2iS ∈ H(E)`: excluded.  So
   `p = 0`, `Q(w,w) = 0`, and every `f ∈ H(E)` vanishing on `Γ` satisfies
   `|f(w)|² = |⟨f, Q_w⟩|² ≤ ‖f‖²Q(w,w) = 0`.  Applied to `f - Σ f(γ)wt(γ)K_γ` this gives the norm
   identity.

### Feasibility (honest)
| file | content | est. Lean lines | risk |
|---|---|---|---|
| `Cauchy` | explicit integrals; `IsH2Cont` basics; strip contour shift; dominated half-plane Cauchy–Goursat; Cauchy formulas (3 kinds); Poisson; line ≤ boundary | 1100–1500 | moderate (measure-theoretic plumbing: Tonelli on strips, interval/Bochner/lintegral conversions, a.e. congruences) |
| `Kernel` | kernel algebra (dslope form, symmetry, diagonal, local bound); `H²` decay criterion; `K_w ∈ H(E)`; reproducing formula (3 cases) | 800–1100 | low–moderate (algebra with `conj`, `if`-branches of `deBrangesKernel`) |
| `Space` | linear structure; `heInner` algebra, Cauchy–Schwarz; evaluation bound; completeness | 500–750 | moderate (completeness: uniform Cauchy on balls, Fatou twice) |
| `EntireHerglotz` | entire Pick function is linear | 250–400 | low–moderate (Mathlib has the disc Poisson formula for harmonic functions) |
| `Orthogonal` | `C`, `S` algebra; `Γ` = zeros of `S`; orthogonality; Bessel; Mittag-Leffler series and `h = D/S`; defect kernel identity | 1100–1500 | moderate (`tsum` over the subtype `Γ` in `ℂ`; every `tsum` manipulation needs a summability proof) |
| `Complete` | exhaustion, series limits, defect kernel in `H(E)`, key proposition, Theorem E | 600–900 | moderate |
| **total** | | **≈ 4.3–6.2 k** | **moderate; no missing deep theory** |

Theorem D alone (Cauchy + Kernel) is ≈ 2–2.5 k lines and is what P4 needs.  Nothing is
unprovable as stated: both `TheoremD` and `TheoremE` are true; the scaffold statements were checked
against edge cases (`Γ = ∅`, real `w`, junk values at `z = w̄`, `x/0 = 0`).  Examples used to
sanity-check the Mittag-Leffler identities by hand: `E = e^{-iπz}` (`α = 0, π/2`: `R = -C/π`,
`h = 0`, Shannon sampling) and `E = z + i` (`H(E) = ℂ`, `K ≡ 1/π`; `α = 0`: `Γ = ∅`, `h = z`,
`p = 1`, `S = 1 ∈ H(E)`, consistent; `α = -π/2`: `Γ = {0}`, `h = 0`).

Recommended implementation order: `Cauchy → Kernel` (then `theoremD_holds` is done; it does not
need `Space`/`Orthogonal`/`Complete`) `→ Space → Orthogonal → Complete`; `EntireHerglotz` is
independent and can be done in parallel.

---------------------------------------------------------------------------------------------------

## 1. `Cauchy.lean` — Cauchy and Poisson formulas for `IsH2Cont`

```lean
def IsH2Cont (F : ℂ → ℂ) : Prop :=
  IsH2Upper F ∧ ∀ t : ℝ, ContinuousAt F (t : ℂ)
```

`IsH2Cont F` is the hypothesis of every lemma of this section.  It is designed to avoid boundary
values: the "boundary function" of `F` is its restriction to `ℝ`, which is in `L²` by the Fatou
step `lintegral_real_le_of_isH2`.  For `f ∈ H(E)` and `E` without real zeros, `f/E` and `f^*/E`
are `IsH2Cont` (`isH2Cont_of_memHE`).

### 1.1 Explicit integrals

```lean
theorem integrable_inv_sq_add_sq (a : ℝ) {y : ℝ} (hy : y ≠ 0) :
    Integrable fun t : ℝ ↦ ((t - a) ^ 2 + y ^ 2)⁻¹ := by
  sorry
```

*Proof.* For `y ≠ 0`, `((t-a)² + y²)⁻¹ = (y²)⁻¹ · (1 + (y⁻¹(t-a))²)⁻¹` (`field_simp`).
`integrable_inv_one_add_mul_sq (inv_ne_zero hy)` gives integrability of `s ↦ (1 + (y⁻¹ s)²)⁻¹`;
compose with the translation `t ↦ t - a` (`Integrable.comp_sub_right _ a`), multiply by the constant
(`Integrable.const_mul`), conclude with `Integrable.congr`/`funext`. ∎

```lean
theorem integral_inv_sq_add_sq (a : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ t : ℝ, ((t - a) ^ 2 + y ^ 2)⁻¹ = Real.pi / y := by
  sorry
```

*Proof.* Same rewriting; `integral_const_mul`, `integral_sub_right_eq_self` (translation
invariance) and `integral_univ_inv_one_add_mul_sq y⁻¹ : ∫ (1 + (y⁻¹ s)²)⁻¹ = π/|y⁻¹| = π y`.
So the integral is `(y²)⁻¹ · π y = π / y`. ∎

```lean
theorem norm_sq_line_sub (t y : ℝ) (w : ℂ) :
    ‖(t : ℂ) + (y : ℂ) * I - w‖ ^ 2 = (t - w.re) ^ 2 + (y - w.im) ^ 2 := by
  sorry
```

*Proof.* `Complex.sq_norm`/`Complex.normSq_eq_norm_sq` and `Complex.normSq_apply`; the real part
of `t + iy - w` is `t - Re w`, the imaginary part `y - Im w`; `ring`. ∎

```lean
theorem inv_norm_sq_le_of_le {z w : ℂ} {r : ℝ} (hr : 0 < r) (hzw : r ≤ ‖z - w‖) :
    (‖z - w‖ ^ 2)⁻¹ ≤ 2 * ((z.re - w.re) ^ 2 + r ^ 2)⁻¹ := by
  sorry
```

*Proof.* `|Re z - Re w| ≤ ‖z - w‖` (`Complex.abs_re_le_norm`), so `(Re z - Re w)² ≤ ‖z-w‖²`; and
`r² ≤ ‖z-w‖²`.  Adding: `(Re z - Re w)² + r² ≤ 2‖z - w‖²`, both sides positive; take inverses
(`inv_le_inv₀`) and rearrange: `(‖z-w‖²)⁻¹ ≤ 2((Re z - Re w)² + r²)⁻¹`. ∎

### 1.2 Basic facts on `IsH2Cont`

```lean
theorem IsH2Cont.continuousOn {F : ℂ → ℂ} (hF : IsH2Cont F) :
    ContinuousOn F {z : ℂ | 0 ≤ z.im} := by
  sorry
```

*Proof.* Let `0 ≤ Im z`.  If `0 < Im z`, `F` is differentiable on the open set `ℂ₊`
(`isOpen_lt continuous_const Complex.continuous_im`), hence continuous at `z`.  If `Im z = 0`, then
`z = ↑(Re z)` (`Complex.ext`) and `hF.2 (Re z)` gives continuity at `z`.  In both cases
`ContinuousAt.continuousWithinAt`. ∎

```lean
theorem IsH2Cont.exists_bound {F : ℂ → ℂ} (hF : IsH2Cont F) :
    ∃ C : ℝ≥0, ∀ y : ℝ, 0 ≤ y → ∫⁻ x : ℝ, ‖F ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ C := by
  sorry
```

*Proof.* Take `C` from `hF.1 = ⟨_, C, hC⟩`.  For `y > 0` this is `hC`.  For `y = 0` simplify
`↑x + ↑0 * I = ↑x` and apply `lintegral_real_le_of_isH2 hF.1.1 hF.2 (fun y hy ↦ hC y hy)`. ∎

```lean
theorem IsH2Cont.lintegral_real_lt_top {F : ℂ → ℂ} (hF : IsH2Cont F) :
    ∫⁻ t : ℝ, ‖F (t : ℂ)‖ₑ ^ 2 < ⊤ := by
  sorry
```

*Proof.* `exists_bound` at `y = 0` and `ENNReal.coe_lt_top`. ∎

```lean
theorem IsH2Cont.memLp_line {F : ℂ → ℂ} (hF : IsH2Cont F) {y : ℝ} (hy : 0 ≤ y) :
    MemLp (fun x : ℝ ↦ F ((x : ℂ) + (y : ℂ) * I)) 2 := by
  sorry
```

*Proof.* `memLp_two_of_lintegral_lt_top` (HB/Comparable) needs continuity of
`x ↦ F(x + iy)`: `hF.continuousOn.comp_continuous (by fun_prop) (fun x ↦ by simpa using hy)`; and
finiteness from `exists_bound`. ∎

```lean
theorem IsH2Cont.memLp_real {F : ℂ → ℂ} (hF : IsH2Cont F) :
    MemLp (fun t : ℝ ↦ F (t : ℂ)) 2 := by
  sorry
```

*Proof.* `memLp_line` at `y = 0` and `simp`. ∎

```lean
theorem IsH2Cont.add {F G : ℂ → ℂ} (hF : IsH2Cont F) (hG : IsH2Cont G) :
    IsH2Cont (fun z ↦ F z + G z) := by
  sorry

theorem IsH2Cont.const_mul {F : ℂ → ℂ} (hF : IsH2Cont F) (c : ℂ) :
    IsH2Cont (fun z ↦ c * F z) := by
  sorry
```

*Proof.* `IsH2Upper.add`, `IsH2Upper.const_mul` (HB/H2) and `ContinuousAt.add`,
`ContinuousAt.const_mul`. ∎

```lean
theorem IsH2Cont.exists_side_seq {F : ℂ → ℂ} (hF : IsH2Cont F) {Y : ℝ} :
    ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧ ∀ n, ∫⁻ y in Ioc (0 : ℝ) Y,
        (‖F ((R n : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 + ‖F (((-R n : ℝ) : ℂ) + (y : ℂ) * I)‖ₑ ^ 2) ≤ 1 := by
  sorry
```

*Proof.* Let `C` be the bound of `exists_bound` and `H(x) = ∫⁻_{y ∈ (0,Y]} ‖F(x+iy)‖ₑ²`.
1. *Tonelli*: `∫⁻ x, H(x) ≤ Y·C`.  Let `F' = {z | 0 ≤ Im z}.piecewise F 0`; it is measurable
   (`ContinuousOn.measurable_piecewise hF.continuousOn continuousOn_const`, closed set) and equals
   `F` on `{y > 0}`, so `H(x) = ∫⁻_{(0,Y]} ‖F'(x+iy)‖ₑ²`.  The function `(x,y) ↦ ‖F'(x+iy)‖ₑ²` is
   measurable on `ℝ × ℝ` (composition with the continuous `(x,y) ↦ x + y I`), so
   `lintegral_lintegral_swap` (with `volume` and `volume.restrict (Ioc 0 Y)`) gives
   `∫⁻ x, H(x) = ∫⁻_{(0,Y]} ∫⁻ x, ‖F(x+iy)‖ₑ² ≤ ∫⁻_{(0,Y]} C = C·Y` (`setLIntegral_mono`,
   `setLIntegral_const`, `Real.volume_Ioc`).  (Model: `lintegral_strip` in HB/MeanValue.)
2. *Good abscissae*: `∀ a, ∃ x ≥ a, H(x) + H(-x) ≤ 1`.  Otherwise there is `a ≥ 0` with
   `H(x) + H(-x) > 1` for all `x ≥ a`, so `∫⁻_{x ≥ a} (H(x) + H(-x)) ≥ ∫⁻_{x ≥ a} 1 = ∞`; but
   `∫⁻_{x ≥ a}(H(x) + H(-x)) ≤ ∫⁻ H + ∫⁻ x, H(-x) = 2∫⁻ H ≤ 2YC < ∞`
   (`lintegral_add_left`, reflection invariance `lintegral_neg_eq_self`).
3. Choose `R n ≥ n` with `H(R n) + H(-R n) ≤ 1` (`Classical.choose` on step 2 at `a = n`);
   `Tendsto R atTop atTop` by `tendsto_atTop_mono` and `tendsto_natCast_atTop_atTop`.  The
   integrand of the statement is the sum, and `lintegral_add_left` (measurability of the line
   restricted to `y > 0` from `continuous_line`) turns it into `H(R n) + H(-R n)`. ∎

*Implemented:* without the hypothesis `hY : 0 < Y` of the scaffold, which is unused (for `Y ≤ 0` the
strip is empty, and Tonelli gives `C·ofReal Y` for every `Y`); call as `hF.exists_side_seq (Y := Y)`.
Measurability as in R9 F3: `H` is measurable by `Measurable.lintegral_prod_right'` applied to the
measurable extension `F'` (`measurable_lintegral_strip`), and in step 3 the integrand is replaced by
`‖F'‖ₑ²` on `(0, Y]` (`setLIntegral_congr_fun`) instead of using `continuous_line`. Steps 1–2 are the
helpers `lintegral_lintegral_strip_le` and `exists_ge_add_neg_le_one` (`CauchyAux/Basic.lean`).

### 1.3 The half-plane Cauchy–Goursat theorem

```lean
theorem integral_eq_integral_line_of_sides {G : ℂ → ℂ} {Y : ℝ} (hY : 0 < Y)
    (hc : ContinuousOn G {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Y})
    (hd : ∀ z : ℂ, 0 < z.im → z.im < Y → DifferentiableAt ℂ G z)
    (h0 : Integrable fun x : ℝ ↦ G (x : ℂ))
    (h1 : Integrable fun x : ℝ ↦ G ((x : ℂ) + (Y : ℂ) * I))
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop)
    (hside : Tendsto (fun n ↦ ∫⁻ y in Ioc (0 : ℝ) Y,
      (‖G ((R n : ℂ) + (y : ℂ) * I)‖ₑ + ‖G (((-R n : ℝ) : ℂ) + (y : ℂ) * I)‖ₑ)) atTop (𝓝 0)) :
    ∫ x : ℝ, G (x : ℂ) = ∫ x : ℝ, G ((x : ℂ) + (Y : ℂ) * I) := by
  sorry
```

*Proof.* Fix `n`, write `R = R n` (we may assume `R ≥ 0`, true eventually).  Apply
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable G (↑(-R)) (↑R + ↑Y * I) ∅
countable_empty Hc Hd`:
* `Hc`: `[[-R, R]] ×ℂ [[0, Y]] ⊆ {0 ≤ Im ∧ Im ≤ Y}` (`mem_reProdIm`, `uIcc_of_le`), so
  `hc.mono`;
* `Hd`: a point of `Ioo (min ..) (max ..) ×ℂ Ioo (min 0 Y) (max 0 Y)` has `0 < Im < Y`; use `hd`.

After `simp` (`(↑(-R)).re = -R`, `.im = 0`, `(↑R + ↑Y * I).re = R`, `.im = Y`,
`↑x + ↑0 * I = ↑x`) the conclusion reads
`Bₙ - Tₙ + I • Vₙ⁺ - I • Vₙ⁻ = 0` with `Bₙ = ∫_{-R}^{R} G(x)`, `Tₙ = ∫_{-R}^{R} G(x+iY)`,
`Vₙ^± = ∫_0^Y G(±R + iy)`.
* `Bₙ → ∫_ℝ G` and `Tₙ → ∫_ℝ G(·+iY)`: `intervalIntegral_tendsto_integral h0
  (tendsto_neg_atTop_atBot.comp hR) hR` (and the same with `h1`).
* `‖Vₙ⁺‖ + ‖Vₙ⁻‖ → 0`: `intervalIntegral.norm_integral_le_integral_norm hY.le`, then
  `intervalIntegral.integral_of_le` and `integral_norm_eq_lintegral_enorm` (continuity of the
  sides from `hc`) bound it by `(∫⁻_{(0,Y]} (‖G(R+iy)‖ₑ + ‖G(-R+iy)‖ₑ)).toReal`, which tends to
  `0` by `hside` and `ENNReal.tendsto_toReal ENNReal.zero_ne_top`.  (Alternatively:
  `enorm_integral_le_lintegral_enorm` directly.)

Passing to the limit, `∫ G - ∫ G(·+iY) = 0` (`tendsto_nhds_unique` against the constant sequence
`0`). ∎

*Implemented* (R9 F1): the vertical sides stay in `ℝ≥0∞`. `‖I•Vₙ⁺ - I•Vₙ⁻‖ₑ` is bounded by
`∫⁻_{(0,Y]} (‖G(R+iy)‖ₑ + ‖G(-R+iy)‖ₑ)` (`enorm_integral_le_lintegral_enorm`, as the helper
`enorm_intervalIntegral_le`, and `le_lintegral_add`), and `tendsto_zero_iff_enorm_tendsto_zero`
concludes: no `toReal` and no continuity of the sides is needed. The rectangle step is the helper
`rect_identity` (`CauchyAux/Basic.lean`).

**Section variables** for the next four lemmas: `{F G : ℂ → ℂ} {w₀ : ℂ} {A : ℝ}`; the domination
hypothesis is
`hdom : ∀ z, 0 ≤ z.im → 1 ≤ ‖z - w₀‖ → ‖G z‖ ≤ ‖F z‖ / ‖z - w₀‖ + A / ‖z - w₀‖ ^ 2`.
Write `a = Re w₀`, `b = Im w₀`, `d(z) = ‖z - w₀‖`.  Two elementary inequalities are used
repeatedly: (AM–GM) `u/d ≤ (ε u² + ε⁻¹ d⁻²)/2` for `ε > 0`, and `d⁻² ≤ 2((x-a)²+1)⁻¹` when
`d ≥ 1` (`inv_norm_sq_le_of_le` with `r = 1`, `Re z - Re w₀ = x - a`).

*Implemented:* the three domination estimates below use one pointwise lemma, `le_of_dom`
(`CauchyAux/Basic.lean`): `‖G z‖ ≤ (ε/2)‖F z‖² + (1/(2ε) + |A|) d(z)⁻²` when `d(z) ≥ 1`, with `ε = 1`
(integrability on lines), `ε → 0` (top side) and `ε = ρ⁻¹` (vertical sides, `enorm_le_of_dom_side`).

```lean
theorem IsH2Cont.integrable_line_of_dominated (hF : IsH2Cont F)
    (hc : ContinuousOn G {z : ℂ | 0 ≤ z.im})
    (hdom : ∀ z : ℂ, 0 ≤ z.im → 1 ≤ ‖z - w₀‖ → ‖G z‖ ≤ ‖F z‖ / ‖z - w₀‖ + A / ‖z - w₀‖ ^ 2)
    {y : ℝ} (hy : 0 ≤ y) :
    Integrable fun x : ℝ ↦ G ((x : ℂ) + (y : ℂ) * I) := by
  sorry
```

*Proof.* `x ↦ G(x+iy)` is continuous (`hc.comp_continuous`), hence `AEStronglyMeasurable` and
bounded on `[a-1, a+1]` by some `M` (`isCompact_Icc.exists_bound_of_continuousOn`).  Pointwise, with
`z = x + iy`:
* if `d(z) < 1` then `|x - a| ≤ d(z) < 1`, so `x ∈ [a-1,a+1]` and `‖G z‖ ≤ M`;
* if `d(z) ≥ 1`: `‖G z‖ ≤ ‖F z‖/d + |A|/d² ≤ ‖F z‖²/2 + (1/2 + |A|) d⁻²
  ≤ ‖F z‖²/2 + (1 + 2|A|)((x-a)²+1)⁻¹`.

Hence `‖G(x+iy)‖ ≤ b(x) := M·𝟙_{[a-1,a+1]}(x) + ‖F(x+iy)‖²/2 + (1+2|A|)((x-a)²+1)⁻¹`.  `b` is
integrable: indicator of a compact interval (`integrableOn_const`, `integrable_indicator_iff`);
`‖F(·+iy)‖²` by `hF.memLp_line hy` and `memLp_two_iff_integrable_sq_norm`;
`integrable_inv_sq_add_sq a one_ne_zero`.  Conclude with `Integrable.mono'`. ∎

```lean
theorem IsH2Cont.tendsto_integral_line_of_dominated (hF : IsH2Cont F)
    (hdom : ∀ z : ℂ, 0 ≤ z.im → 1 ≤ ‖z - w₀‖ → ‖G z‖ ≤ ‖F z‖ / ‖z - w₀‖ + A / ‖z - w₀‖ ^ 2) :
    Tendsto (fun Y : ℝ ↦ ∫ x : ℝ, G ((x : ℂ) + (Y : ℂ) * I)) atTop (𝓝 0) := by
  sorry
```

*Proof.* Let `C` (real, `≥ 0`) bound the line integrals (`exists_bound`).  For `Y ≥ b + 1` every
point `z = x + iY` has `d(z) ≥ |Y - b| ≥ 1` and, by `norm_sq_line_sub`,
`d(z)² = (x-a)² + (Y-b)²`.  For any `ε > 0`:
`‖G z‖ ≤ (ε/2)‖F z‖² + (1/(2ε) + |A|)·((x-a)² + (Y-b)²)⁻¹`,
so (`norm_integral_le_of_norm_le` with the integrable right side, `integral_inv_sq_add_sq a`)
`‖∫ G(x+iY) dx‖ ≤ (ε/2) C + (1/(2ε) + |A|)·π/(Y - b)`
(`∫ ‖F(x+iY)‖² dx ≤ C` from the `ℝ≥0∞` bound via `integral_eq_lintegral_of_nonneg_ae` and
`ENNReal.toReal_le_of_le_ofReal`).  Given `η > 0`, take `ε = η/(C+1)` and then
`Y ≥ max (b+1) (b + 2π(1/(2ε) + |A|)/η)`: the bound is `< η`.  Conclude with
`Metric.tendsto_atTop`. ∎

*Implemented:* without the hypothesis `hc` (continuity of `G`) of the scaffold, which is unused:
`norm_integral_le_of_norm_le` bounds `‖∫ G‖` by the integral of an integrable bound and needs no
integrability of `G`. The real bound `∫ ‖F(x+iY)‖² dx ≤ C` and the estimate for fixed `ε` are the
helpers `IsH2Cont.integral_sq_le` and `IsH2Cont.norm_integral_line_le`.

```lean
theorem IsH2Cont.exists_sides_of_dominated (hF : IsH2Cont F)
    (hdom : ∀ z : ℂ, 0 ≤ z.im → 1 ≤ ‖z - w₀‖ → ‖G z‖ ≤ ‖F z‖ / ‖z - w₀‖ + A / ‖z - w₀‖ ^ 2)
    {Y : ℝ} (hY : 0 < Y) :
    ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧ Tendsto (fun n ↦ ∫⁻ y in Ioc (0 : ℝ) Y,
      (‖G ((R n : ℂ) + (y : ℂ) * I)‖ₑ + ‖G (((-R n : ℝ) : ℂ) + (y : ℂ) * I)‖ₑ)) atTop (𝓝 0) := by
  sorry
```

*Proof.* Take `R` from `IsH2Cont.exists_side_seq hF hY`.  Eventually `R n ≥ ‖w₀‖ + 1`
(`hR.eventually_ge_atTop`).  For such `n`, `y ∈ (0, Y]` and `z = ±R n + iy`:
`d(z) ≥ |±R n - a| ≥ R n - ‖w₀‖ =: ρₙ ≥ 1`, so by `hdom` and `u ≤ (u² + 1)/2`:
`‖G z‖ ≤ (‖F z‖² + 1)/(2ρₙ) + |A|/ρₙ²`.
Integrating over `(0, Y]` and adding the two sides:
`∫⁻ (‖G(R+iy)‖ₑ + ‖G(-R+iy)‖ₑ) ≤ ofReal((1 + 2Y)/(2ρₙ) + 2Y|A|/ρₙ²)`
(using `∫⁻_{(0,Y]} (‖F(R+iy)‖ₑ² + ‖F(-R+iy)‖ₑ²) ≤ 1` from `exists_side_seq`).
Since `ρₙ → ∞`, the right side tends to `0` (`ENNReal.tendsto_ofReal`, then squeeze
`tendsto_of_tendsto_of_tendsto_of_le_of_le'` with `tendsto_const_nhds` at `0`). ∎

*Implemented:* with `le_of_dom` at `ε = ρₙ⁻¹`; the bound is
`ofReal(ρₙ⁻¹/2 + 2(ρₙ⁻¹/2 + |A|ρₙ⁻²)Y)`, `ρₙ = R n - ‖w₀‖`.

```lean
theorem IsH2Cont.integral_eq_zero_of_dominated (hF : IsH2Cont F)
    (hc : ContinuousOn G {z : ℂ | 0 ≤ z.im}) (hd : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ G z)
    (hdom : ∀ z : ℂ, 0 ≤ z.im → 1 ≤ ‖z - w₀‖ → ‖G z‖ ≤ ‖F z‖ / ‖z - w₀‖ + A / ‖z - w₀‖ ^ 2) :
    ∫ x : ℝ, G (x : ℂ) = 0 := by
  sorry
```

*Proof.* For every `Y > 0`, `integral_eq_integral_line_of_sides hY (hc.mono fun z hz ↦ hz.1)
(fun z h _ ↦ hd z h) h0 h1 hR hside` where `h0` is `integrable_line_of_dominated` at `y = 0`
(after `simp`), `h1` the same at `y = Y`, and `R, hR, hside` come from `exists_sides_of_dominated`.
So `Y ↦ ∫ G(·+iY)` is eventually the constant `∫_ℝ G`, and it tends to `0`
(`tendsto_integral_line_of_dominated`); `tendsto_nhds_unique` gives `∫_ℝ G = 0`. ∎

### 1.4 The Cauchy formulas

```lean
theorem norm_sub_ge_mul_norm_sub {z w c : ℂ} (hz : 0 ≤ z.im) (hc : c.im < 0) (hw : 0 ≤ w.im) :
    min (1 / 2) (-c.im / (2 * ‖w - c‖)) * ‖z - w‖ ≤ ‖z - c‖ := by
  sorry
```

*Proof.* Let `δ = ‖w - c‖`; `δ > 0` since `Im(w - c) = Im w - Im c > 0`; `m = -Im c > 0`.  Then
`‖z - c‖ ≥ Im(z - c) ≥ m` (`Complex.im_le_norm` or `abs_im_le_norm`) and
`‖z - c‖ ≥ ‖z - w‖ - δ` (triangle inequality).  If `‖z - w‖ ≥ 2δ`, then
`‖z - c‖ ≥ ‖z - w‖/2 ≥ κ‖z - w‖` (`min_le_left`).  If `‖z - w‖ < 2δ`, then
`κ‖z - w‖ ≤ (m/(2δ))‖z - w‖ < m ≤ ‖z - c‖` (`min_le_right`). ∎

```lean
theorem IsH2Cont.integrable_div {F : ℂ → ℂ} (hF : IsH2Cont F) {w : ℂ} (hw : w.im ≠ 0) :
    Integrable fun t : ℝ ↦ F (t : ℂ) / ((t : ℂ) - w) := by
  sorry
```

*Proof.* Continuity of `t ↦ F t` (from `hF.continuousOn`) and of `t ↦ (t - w)⁻¹` (`t - w ≠ 0`
since `Im w ≠ 0`) gives measurability.  Bound: `‖F t/(t - w)‖ ≤ (‖F t‖² + ‖t - w‖⁻²)/2` and
`‖↑t - w‖² = (t - Re w)² + (Im w)²` (`norm_sq_line_sub` with `y = 0`); integrable by
`memLp_real` and `integrable_inv_sq_add_sq _ hw`.  `Integrable.mono'`. ∎

```lean
theorem IsH2Cont.integral_div_lower {F : ℂ → ℂ} (hF : IsH2Cont F) {w : ℂ} (hw : w.im < 0) :
    ∫ t : ℝ, F (t : ℂ) / ((t : ℂ) - w) = 0 := by
  sorry
```

*Proof.* `G z = F z/(z - w)`: continuous on `{Im ≥ 0}` (`hF.continuousOn.div`, `z - w ≠ 0` because
`Im z ≥ 0 > Im w`), differentiable on `ℂ₊`, and `‖G z‖ = ‖F z‖/‖z - w‖` (domination with
`w₀ = w`, `A = 0`).  `IsH2Cont.integral_eq_zero_of_dominated`. ∎

```lean
theorem IsH2Cont.integrable_dslope {F : ℂ → ℂ} (hF : IsH2Cont F) {w c : ℂ}
    (hw : 0 ≤ w.im) (hdw : DifferentiableAt ℂ F w) (hc : c.im < 0) :
    Integrable fun t : ℝ ↦ dslope (fun z ↦ F z - F w * ((w - c) / (z - c))) w (t : ℂ) := by
  sorry
```

*Proof.* Let `Φ z = F z - F w·((w-c)/(z-c))` and `G = dslope Φ w`.
1. `Φ w = 0` (`w ≠ c`, `div_self`).
2. *Continuity on `{Im ≥ 0}`*: such `z` is `≠ c`.  If `z ≠ w`: `Φ` is continuous at `z` (`F` is:
   differentiable if `Im z > 0`, `hF.2` if `Im z = 0`), so `(continuousAt_dslope_of_ne hzw).2`.
   If `z = w`: `Φ` is differentiable at `w` (`hdw` and the rational part), so
   `continuousAt_dslope_same.2`.
3. *Domination* with `w₀ = w`: for `‖z - w‖ ≥ 1`, `G z = Φ z/(z - w)` (`dslope_of_ne`,
   `slope_def_field`, step 1) and `‖Φ z‖ ≤ ‖F z‖ + ‖F w‖‖w-c‖/‖z - c‖
   ≤ ‖F z‖ + ‖F w‖‖w-c‖/(κ‖z - w‖)` (`norm_sub_ge_mul_norm_sub`, `κ > 0`), i.e. `hdom` holds with
   `A = ‖F w‖‖w - c‖/κ`.
4. `integrable_line_of_dominated` at `y = 0`, `simp`. ∎

```lean
theorem IsH2Cont.integral_dslope_eq_zero {F : ℂ → ℂ} (hF : IsH2Cont F) {w c : ℂ}
    (hw : 0 ≤ w.im) (hdw : DifferentiableAt ℂ F w) (hc : c.im < 0) :
    ∫ t : ℝ, dslope (fun z ↦ F z - F w * ((w - c) / (z - c))) w (t : ℂ) = 0 := by
  sorry
```

*Proof.* Same `Φ, G` and steps 1–3 above.  *Differentiability on `ℂ₊`*: let `Im z > 0`.  If
`z ≠ w`, `(differentiableAt_dslope_of_ne hzw).2` and `Φ` differentiable at `z` (`F` on the open
`ℂ₊`, `z ≠ c`).  If `z = w` (then `Im w > 0`), `Φ` is differentiable on the open set `ℂ₊ ∋ w`
(`c ∉ ℂ₊`), so `(Complex.differentiableOn_dslope (isOpen.mem_nhds hz)).2` gives differentiability
of `G` on `ℂ₊`, in particular at `w`.  Conclude with `IsH2Cont.integral_eq_zero_of_dominated`. ∎

```lean
theorem integral_cauchy_pair {w : ℂ} (hw : 0 < w.im) :
    ∫ t : ℝ, (w - conj w) / (((t : ℂ) - w) * ((t : ℂ) - conj w)) = 2 * Real.pi * I := by
  sorry
```

*Proof.* With `w = a + ib`: `(t - w)(t - w̄) = ↑((t-a)² + b²)` (`Complex.mul_conj`,
`Complex.normSq_apply`, or `ext; simp; ring`) and `w - w̄ = 2ib` (`Complex.sub_conj`).  So the
integrand is `2ib·↑(((t-a)² + b²)⁻¹)` and the integral is `2ib·↑(π/b) = 2πi`
(`integral_const_mul`, `integral_ofReal`, `integral_inv_sq_add_sq a hw`). ∎

```lean
theorem IsH2Cont.cauchy_upper {F : ℂ → ℂ} (hF : IsH2Cont F) {w : ℂ} (hw : 0 < w.im) :
    ∫ t : ℝ, F (t : ℂ) / ((t : ℂ) - w) = 2 * Real.pi * I * F w := by
  sorry
```

*Proof.* `integral_dslope_eq_zero hF hw.le (hF.1.1.differentiableAt …) (c := conj w)` (`Im c < 0`).
For real `t`, `t ≠ w`, so the integrand is
`Φ(t)/(t - w) = F(t)/(t - w) - F(w)·(w - w̄)/((t - w)(t - w̄))`
(`dslope_of_ne`, `slope_def_field`, `field_simp`).  Both pieces are integrable
(`integrable_div`, and a constant times `integrable_inv_sq_add_sq`), so `integral_sub` and
`integral_const_mul` give `∫ F/(t-w) = F(w)·∫ (w-w̄)/((t-w)(t-w̄)) = 2πi F(w)`
(`integral_cauchy_pair`). ∎

```lean
theorem IsH2Cont.integrable_reg_real {F : ℂ → ℂ} (hF : IsH2Cont F) {x : ℝ}
    (hdx : DifferentiableAt ℂ F x) :
    Integrable fun t : ℝ ↦ (F (t : ℂ) - F x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x) := by
  sorry
```

*Proof.* `integrable_dslope` with `w = ↑x` (`Im = 0`) and `c = ↑x - I` (`Im c = -1`).  For
`t ≠ x`, `dslope Φ x t` equals the displayed integrand since `x - c = I` and `t - c = t - x + I`;
`{x}` is null (`measure_singleton`), so `Integrable.congr` with an a.e. equality. ∎

```lean
theorem IsH2Cont.cauchy_real {F : ℂ → ℂ} (hF : IsH2Cont F) {x : ℝ}
    (hdx : DifferentiableAt ℂ F x) :
    ∫ t : ℝ, (F (t : ℂ) - F x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x) = 0 := by
  sorry
```

*Proof.* `integral_dslope_eq_zero` with the same `w, c`, then `integral_congr_ae` as in the
previous proof. ∎

```lean
theorem integral_two_I_div (x : ℝ) :
    ∫ t : ℝ, 2 * I / ((((t - x) ^ 2 + 1 : ℝ)) : ℂ) = 2 * Real.pi * I := by
  sorry
```

*Proof.* `2I/↑((t-x)²+1) = 2I·↑(((t-x)²+1)⁻¹)`; `integral_const_mul`, `integral_ofReal`,
`integral_inv_sq_add_sq x one_pos` (`1² = 1`). ∎

### 1.5 Poisson formula and the line bound

```lean
theorem IsH2Cont.poisson {F : ℂ → ℂ} (hF : IsH2Cont F) {w : ℂ} (hw : 0 < w.im) :
    F w = ∫ t : ℝ, ((w.im / (Real.pi * ((t - w.re) ^ 2 + w.im ^ 2)) : ℝ) : ℂ) * F (t : ℂ) := by
  sorry
```

*Proof.* `cauchy_upper`: `∫ F(t)/(t-w) = 2πi F(w)`; `integral_div_lower` at `w̄`
(`Im w̄ < 0`): `∫ F(t)/(t - w̄) = 0`.  Subtract (`integral_sub`, both `integrable_div`):
`∫ F(t)[(t-w)⁻¹ - (t-w̄)⁻¹] dt = 2πi F(w)`.  Pointwise
`(t-w)⁻¹ - (t-w̄)⁻¹ = (w - w̄)/((t-w)(t-w̄)) = 2i b/((t-a)² + b²)` (`w = a + ib`).  Hence
`2ib ∫ F(t)/((t-a)²+b²) = 2πi F(w)`, i.e. `F(w) = ∫ (b/(π((t-a)²+b²))) F(t) dt`
(`integral_const_mul`, divide by `2πi ≠ 0`). ∎

```lean
theorem IsH2Cont.lintegral_line_le {F : ℂ → ℂ} (hF : IsH2Cont F) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖F ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ ∫⁻ t : ℝ, ‖F (t : ℂ)‖ₑ ^ 2 := by
  sorry
```

*Proof.* Write `P(x,t) = y/(π((t-x)² + y²)) ≥ 0`.  For each `t`,
`∫⁻ x, ofReal P(x,t) = 1` and for each `x`, `∫⁻ t, ofReal P(x,t) = 1`
(`ofReal_integral_eq_lintegral_ofReal` with `integrable_inv_sq_add_sq`, value
`(y/π)·(π/y) = 1` by `integral_inv_sq_add_sq`; `(t-x)² = (x-t)²`).
1. *Pointwise*: by `poisson` at `w = x + iy` and `enorm_integral_le_lintegral_enorm`,
   `‖F(x+iy)‖ₑ ≤ ∫⁻ t, ofReal P(x,t)·‖F t‖ₑ`.
2. *Cauchy–Schwarz*: `(∫⁻ P‖F‖ₑ)² ≤ (∫⁻ P)(∫⁻ P‖F‖ₑ²) = ∫⁻ P‖F‖ₑ²` —
   `ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2` (`Real.HolderConjugate.two_two`),
   `f = P^{1/2}`, `g = P^{1/2}‖F‖ₑ`, then square.  (Elementary alternative avoiding `rpow`:
   `u ≤ λ/2 + u²/(2λ)` for every `λ > 0`, optimize `λ`.)
3. *Tonelli*: `∫⁻ x, ‖F(x+iy)‖ₑ² ≤ ∫⁻ x ∫⁻ t, P(x,t)‖F t‖ₑ² = ∫⁻ t, ‖F t‖ₑ² ∫⁻ x, P(x,t)
   = ∫⁻ t, ‖F t‖ₑ²` (`lintegral_lintegral_swap`; measurability: `P` continuous, `t ↦ F t`
   continuous). ∎

*Implemented* by the main route: the kernel masses are `lintegral_poissonKernel`, and step 2 is the
helper `sq_lintegral_mul_le` (Cauchy–Schwarz against a probability density in `ℝ≥0∞`, by
`ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2`).

---------------------------------------------------------------------------------------------------

## 2. `Kernel.lean` — algebra of the kernel

```lean
def heInner (E f g : ℂ → ℂ) : ℂ :=
  ∫ t : ℝ, f t * conj (g t) / ((‖E t‖ ^ 2 : ℝ) : ℂ)

def kernelNum (E : ℂ → ℂ) (w z : ℂ) : ℂ :=
  E z * conj (E w) - fstar E z * conj (fstar E w)
```

```lean
theorem heInner_eq_integral_div (E f g : ℂ → ℂ) :
    heInner E f g = ∫ t : ℝ, f t / E t * conj (g t / E t) := by
  sorry
```

*Proof.* Pointwise (`integral_congr`): if `E t = 0`, both integrands are `0` (`div_zero`, `x/0`).
Otherwise `‖E t‖² = E t · conj (E t)` as complex numbers (`Complex.mul_conj`,
`Complex.normSq_eq_norm_sq`), so `f conj g/(E conj E) = (f/E)·conj(g/E)` (`map_div₀`,
`field_simp`). ∎

```lean
theorem kernelNum_conj_self (E : ℂ → ℂ) (w : ℂ) : kernelNum E w (conj w) = 0 := by
  sorry
```

*Proof.* `fstar E (conj w) = conj (E w)` and `conj (fstar E w) = E (conj w)` (unfold `fstar`,
`conj_conj`); then `E(w̄)conj E(w) - conj E(w)·E(w̄) = 0`, `ring`. ∎

```lean
theorem deBrangesKernel_of_ne (E : ℂ → ℂ) {w z : ℂ} (hz : z ≠ conj w) :
    deBrangesKernel E w z = (I / 2) * kernelNum E w z / (Real.pi * (z - conj w)) := by
  sorry
```

*Proof.* `unfold deBrangesKernel kernelNum; rw [if_neg hz]`. ∎

*Implemented* (R9 F8): `rw [ite_eq_right hz]`, since `if_neg` and `if_pos` are deprecated in this
Mathlib (`ite_eq_left` replaces `if_pos` elsewhere in the file).

```lean
theorem deBrangesKernel_eq_dslope {E : ℂ → ℂ} (hE : Differentiable ℂ E) (w : ℂ) :
    deBrangesKernel E w = fun z ↦ (I / (2 * Real.pi)) * dslope (kernelNum E w) (conj w) z := by
  sorry
```

*Proof.* `funext z`.  If `z = conj w`: `dslope_same` gives `deriv (kernelNum E w) (conj w)`, which
equals `deriv E (conj w)·conj (E w) - deriv (fstar E) (conj w)·conj (fstar E w)` (`deriv_sub`,
`deriv_mul_const`; differentiability of `E` and of `fstar E` by `hE.fstar`), i.e. the `if`-branch
of `deBrangesKernel` (`(I/(2π))·…`).  If `z ≠ conj w`: `dslope_of_ne`, `slope_def_field` and
`kernelNum_conj_self` give `dslope = kernelNum E w z/(z - w̄)`; compare with
`deBrangesKernel_of_ne` (`(I/2)·N/(π(z - w̄)) = (I/(2π))·N/(z - w̄)`, `field_simp`). ∎

```lean
theorem differentiable_deBrangesKernel {E : ℂ → ℂ} (hE : Differentiable ℂ E) (w : ℂ) :
    Differentiable ℂ (deBrangesKernel E w) := by
  sorry
```

*Proof.* Rewrite with `deBrangesKernel_eq_dslope`; `kernelNum E w` is entire; `dslope` of an
entire function is entire: `(Complex.differentiableOn_dslope (Filter.univ_mem)).2`
(`s = univ ∈ 𝓝 (conj w)`); multiply by the constant. ∎

```lean
theorem deBrangesKernel_mul (E : ℂ → ℂ) (w z : ℂ) :
    deBrangesKernel E w z * (Real.pi * (z - conj w)) = (I / 2) * kernelNum E w z := by
  sorry
```

*Proof.* If `z = conj w` both sides are `0` (`sub_self`, `kernelNum_conj_self`).  Otherwise
`deBrangesKernel_of_ne` and `field_simp` (`π(z - w̄) ≠ 0`). ∎

```lean
theorem conj_deBrangesKernel (E : ℂ → ℂ) (w z : ℂ) :
    conj (deBrangesKernel E w z) = deBrangesKernel E z w := by
  sorry
```

*Proof.* `z = conj w ↔ w = conj z`.
* Off the diagonal: by `deBrangesKernel_of_ne` twice,
  `conj K(w,z) = (-I/2)·conj N_w(z)/(π(z̄ - w))`; and `conj N_w(z) = conj E(z)E(w) -
  conj E^*(z) E^*(w) = N_z(w)`, `(-I/2)/(z̄ - w) = (I/2)/(w - z̄)` (`map_div₀`, `map_mul`,
  `Complex.conj_I`, `Complex.conj_ofReal`, `ring`).
* On the diagonal `z = w̄`: both values are `if`-branches.  With `deriv_fstar`:
  `(E^*)'(w̄) = conj E'(w)` and `(E^*)'(w) = conj E'(w̄)`, `conj E^*(w) = E(w̄)`,
  `conj E^*(w̄) = E(w)`.  Then `K(w,w̄) = (i/2π)(E'(w̄)conj E(w) - conj E'(w)·E(w̄))` and
  `K(w̄,w) = (i/2π)(E'(w)conj E(w̄) - conj E'(w̄)·E(w))`; the conjugate of the first is the second
  (`ring` after `map_*`). ∎

*Implemented* (R9 F7): without the hypothesis `hE : Differentiable ℂ E` of the scaffold, which is unused
(the diagonal case needs only `deriv_fstar`, which is unconditional); `E` is explicit. Theorem E
(§4–§7) was developed in parallel against the scaffold signature and uses instead an identical copy,
`deBrangesKernel_conj_symm (E) (w z)` (`Cited/DeBrangesDE/EAux/KernelSymm.lean`), wherever this
document cites `conj_deBrangesKernel` in §5–§7.

```lean
theorem fstar_deBrangesKernel (E : ℂ → ℂ) (w : ℂ) :
    fstar (deBrangesKernel E w) = deBrangesKernel E (conj w) := by
  sorry
```

*Proof.* `funext z`; `fstar (K w) z = conj K(w, z̄) = K(z̄, w)` (`conj_deBrangesKernel`).  It remains
`K(z̄, w) = K(w̄, z)`, an instance of the identity `K(b̄, ā) = K(a, b)`: off the diagonal
(`w ≠ z`), `N_{z̄}(w) = E(w)E^*(z) - E^*(w)E(z) = -N_{w̄}(z)` (use `conj E(z̄) = E^*(z)`,
`conj E^*(z̄) = E(z)`) and `w - z = -(z - w)`; on the diagonal `z = w` both sides are `K(w̄, w)`. ∎

*Implemented:* without `hE`, as `conj_deBrangesKernel`; the code rewrites with `conj_deBrangesKernel E`
directly.

```lean
theorem deBrangesKernel_diag (E : ℂ → ℂ) {w : ℂ} (hw : w.im ≠ 0) :
    deBrangesKernel E w w =
      (((‖E w‖ ^ 2 - ‖E (conj w)‖ ^ 2) / (4 * Real.pi * w.im) : ℝ) : ℂ) := by
  sorry
```

*Proof.* `w ≠ conj w` (`Im w ≠ 0`), so `deBrangesKernel_of_ne`; `kernelNum E w w =
‖E w‖² - ‖E^* w‖²` (`Complex.mul_conj`), `‖E^* w‖ = ‖E (conj w)‖` (`norm_fstar`),
`w - conj w = 2i Im w` (`Complex.sub_conj`); `(I/2)·X/(π·2i Im w) = X/(4π Im w)` (`field_simp`,
`push_cast`). ∎

```lean
theorem deBrangesKernel_diag_real (E : ℂ → ℂ) (x : ℝ) :
    deBrangesKernel E x x = ((phaseDeriv E x * ‖E x‖ ^ 2 / Real.pi : ℝ) : ℂ) := by
  sorry
```

*Proof.* `↑x = conj ↑x`, `if`-branch: `(I/2π)(E'(x)conj E(x) - (E^*)'(x)conj E^*(x))`.
`deriv_fstar_ofReal`: `(E^*)'(x) = conj E'(x)`; `fstar_ofReal`: `conj E^*(x) = E(x)`.  So the value
is `(I/2π)(u - conj u) = (I/2π)(2i Im u) = -Im u/π` with `u = E'(x)conj E(x)`.  If `E x ≠ 0`,
`Im u = Im(E'/E)·|E|²` (`u = (E'/E)·(E conj E)`), so `-Im u/π = phaseDeriv E x·|E x|²/π`.  If
`E x = 0`, both sides are `0`. ∎

```lean
theorem deBrangesKernel_diag_nonneg {E : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (w : ℂ) :
    (deBrangesKernel E w w).im = 0 ∧ 0 ≤ (deBrangesKernel E w w).re := by
  sorry
```

*Proof.* Nonreal `w`: by `deBrangesKernel_diag` the value is real, and
`(‖E w‖² - ‖E w̄‖²)/(4π Im w) ≥ 0`: if `Im w > 0`, `‖E w̄‖ ≤ ‖E w‖` (`IsHB`); if `Im w < 0`,
apply `IsHB` at `w̄ ∈ ℂ₊`: numerator `≤ 0`, denominator `< 0`.  Real `w = ↑x`
(`w = ↑w.re`): `deBrangesKernel_diag_real` and `IsHB.phaseDeriv_nonneg hE (h0 x)`. ∎

```lean
theorem exists_bound_deBrangesKernel {E : ℂ → ℂ} (hE : Differentiable ℂ E) (ρ : ℝ) :
    ∃ M : ℝ, ∀ w z : ℂ, ‖w‖ ≤ ρ → ‖z‖ ≤ ρ → ‖deBrangesKernel E w z‖ ≤ M := by
  sorry
```

*Proof.* We may assume `ρ ≥ 0`.  On the compact `B = closedBall 0 ρ`, the continuous functions
`E, E', E^*, (E^*)'` are bounded by `M₀, M₁, M₀', M₁'` (`IsCompact.exists_bound_of_continuousOn`;
`E'` continuous: `hE.contDiff.continuous_deriv le_rfl` as in HB/H2).  For `w, z ∈ B`:
`K(w,z) = (i/2π)·dslope N_w (w̄) z` (`deBrangesKernel_eq_dslope`), `N_w' = E'·conj E(w) -
(E^*)'·conj E^*(w)` is bounded on `B` by `L = M₁M₀ + M₁'M₀'` (note `‖w‖ ≤ ρ`, and `fstar`
preserves the ball).  If `z ≠ w̄`: `‖dslope‖ = ‖N_w z - N_w w̄‖/‖z - w̄‖ ≤ L`
(`Convex.norm_image_sub_le_of_norm_deriv_le` on the convex `B ∋ z, w̄`).  If `z = w̄`:
`‖dslope‖ = ‖N_w'(w̄)‖ ≤ L` (`dslope_same`).  Take `M = L/(2π)`. ∎

*Implemented:* only `E` and `E'` are bounded on `B` (by `M₀`, `M₁`): `B` is closed under `conj` and
`(E^*)'(u) = conj E'(ū)` (`deriv_fstar`), so `L = 2M₁M₀` and `M = ‖i/(2π)‖·2M₁M₀`.

```lean
theorem integrand_eq {E : ℂ → ℂ} (w : ℂ) (f : ℂ → ℂ) {t : ℝ} (hEt : E t ≠ 0)
    (ht : (t : ℂ) ≠ w) :
    f t * conj (deBrangesKernel E w t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) =
      (-I / (2 * Real.pi)) *
        ((f t / E t * E w - conj (fstar f t / E t) * fstar E w) / ((t : ℂ) - w)) := by
  sorry
```

*Proof.* `t ≠ conj w` (else `t = conj t = w`), so by `deBrangesKernel_of_ne`
`conj K(w,t) = (-I/2)·conj N_w(t)/(π(t - w))` with
`conj N_w(t) = conj E(t)·E(w) - conj E^*(t)·E^*(w) = E^*(t)E(w) - E(t)E^*(w)` (`fstar_ofReal`).
`‖E t‖² = E(t)·E^*(t)` (as complex numbers), and `conj((f^*/E)(t)) = f(t)/E^*(t)`.  Then
`field_simp` (`E t ≠ 0`, `E^* t = conj E t ≠ 0`, `t - w ≠ 0`) and `ring`. ∎

```lean
theorem integrand_eq_real {E : ℂ → ℂ} (f : ℂ → ℂ) {x t : ℝ} (hEx : E x ≠ 0) (hEt : E t ≠ 0)
    (ht : t ≠ x) :
    f t * conj (deBrangesKernel E x t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) =
      (-I / (2 * Real.pi)) *
        (E x * ((f t / E t - f x / E x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x))
          - fstar E x *
            conj ((fstar f t / E t - fstar f x / E x * (I / ((t : ℂ) - x + I))) / ((t : ℂ) - x))
          + f x * (2 * I / ((((t - x) ^ 2 + 1 : ℝ)) : ℂ))) := by
  sorry
```

*Proof.* Start from `integrand_eq` with `w = ↑x` (`↑t ≠ ↑x`).  Put `A = f/E`, `g = f^*/E`,
`ψ(t) = I/(t - x + I)`; note `conj ψ(t) = -I/(t - x - I)` (`t, x` real), `E(x)A(x) = f(x)` and
`E^*(x)·conj g(x) = conj E(x)·f(x)/conj E(x) = f(x)`.  Then
`E(x)·(A(t) - A(x)ψ(t)) - E^*(x)·conj(g(t) - g(x)ψ(t)) = [E(x)A(t) - E^*(x)conj g(t)] -
f(x)(ψ(t) - conj ψ(t))`, and `(ψ(t) - conj ψ(t))/(t-x) = 2i/((t-x)²+1)` (with `s = t - x`:
`ψ = (1 + is)/(s²+1)`).  Dividing by `t - x` gives the claim (`field_simp`, `ring`; the `conj`
of the quotient by `map_div₀`, `map_sub`, `map_mul`, `Complex.conj_ofReal`, `Complex.conj_I`). ∎

## 3. `Kernel.lean` — `K_w ∈ H(E)` and the reproducing formula

```lean
theorem isH2Upper_of_decay {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im}) (c : ℂ)
    (A r M : ℝ) (hr : 0 < r)
    (hfar : ∀ z : ℂ, 0 < z.im → r ≤ ‖z - c‖ → ‖G z‖ ≤ A / ‖z - c‖)
    (hnear : ∀ z : ℂ, 0 < z.im → ‖z - c‖ < r → ‖G z‖ ≤ M) : IsH2Upper G := by
  sorry
```

*Proof.* For `y > 0`, `x ↦ G(x+iy)` is continuous (`continuous_line hG`), and pointwise, with
`z = x+iy`, `a = Re c`:
if `‖z - c‖ < r`, then `|x - a| < r` and `‖G z‖² ≤ M²`; otherwise
`‖G z‖² ≤ A²‖z-c‖⁻² ≤ 2A²((x-a)² + r²)⁻¹` (`inv_norm_sq_le_of_le`).  So
`‖G z‖ₑ² ≤ ofReal(M²·𝟙_{(a-r,a+r)}(x) + 2A²((x-a)²+r²)⁻¹)` and
`∫⁻ ≤ ofReal(2rM² + 2πA²/r) =: C` (`lintegral_add_left`, `setLIntegral_const`,
`ofReal_integral_eq_lintegral_ofReal`, `integral_inv_sq_add_sq`).  `C` does not depend on `y`;
take `C.toNNReal`. ∎

```lean
theorem kernel_div_E {E : ℂ → ℂ} (w z : ℂ) (hz : E z ≠ 0) (hne : z ≠ conj w) :
    deBrangesKernel E w z / E z =
      (I / (2 * Real.pi)) * (conj (E w) - (fstar E z / E z) * conj (fstar E w)) /
        (z - conj w) := by
  sorry
```

*Proof.* `deBrangesKernel_of_ne`, then `field_simp` (`E z ≠ 0`, `z - w̄ ≠ 0`, `π ≠ 0`), `ring`. ∎

```lean
theorem isH2Upper_kernel_div {E : ℂ → ℂ} (hE : IsHB E) {w : ℂ}
    (hw : 0 < w.im ∨ E (conj w) ≠ 0) : IsH2Upper (fun z ↦ deBrangesKernel E w z / E z) := by
  sorry
```

*Proof.* Put `c = conj w`, `A = (‖E w‖ + ‖E^* w‖)/(2π)`.  `G = K_w/E` is differentiable on `ℂ₊`
(`differentiable_deBrangesKernel hE.1`, `E ≠ 0` on `ℂ₊`).
* *Far bound* (any `z ∈ ℂ₊`, `z ≠ c`): by `kernel_div_E`, `‖G z‖ ≤ (‖E w‖ + ‖Θ z‖‖E^* w‖)/(2π‖z - c‖)
  ≤ A/‖z - c‖` since `‖Θ z‖ = ‖E(z̄)‖/‖E z‖ ≤ 1` (`norm_fstar`, `IsHB`).
* *Near bound*.  Case `0 < Im w`: `Im c < 0`, so `‖z - c‖ ≥ Im z - Im c > Im w` for `z ∈ ℂ₊`; take
  `r = Im w`: the near region is empty (`M = 0`).  Case `E c ≠ 0`: by continuity there is
  `r ∈ (0,1]` with `E ≠ 0` on `closedBall c r` (`ContinuousAt.eventually_ne`,
  `Metric.eventually_nhds_iff`); `K_w/E` is continuous on this compact ball, hence bounded by
  some `M` there.
Conclude with `isH2Upper_of_decay`. ∎

```lean
theorem memHE_deBrangesKernel_of_isHB {E : ℂ → ℂ} (hE : IsHB E) {w : ℂ}
    (hw : w.im ≠ 0 ∨ E w ≠ 0) : MemHE E (deBrangesKernel E w) := by
  sorry
```

*Proof.* Entire: `differentiable_deBrangesKernel hE.1`.  `K_w/E ∈ H²`: `isH2Upper_kernel_div` with
`0 < Im w ∨ E w̄ ≠ 0` (if `Im w > 0` left; if `Im w < 0`, `w̄ ∈ ℂ₊` so `E w̄ ≠ 0`; if `E w ≠ 0` and
`Im w = 0`, then `w̄ = w`).  `K_w^*/E = K_{w̄}/E` (`fstar_deBrangesKernel`) `∈ H²`:
`isH2Upper_kernel_div` at `w̄` with `0 < Im w̄ ∨ E w ≠ 0` (if `Im w < 0` left; if `Im w > 0`,
`E w ≠ 0` by `IsHB`; if `Im w = 0`, by hypothesis). ∎

```lean
theorem memHE_deBrangesKernel {E : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (w : ℂ) :
    MemHE E (deBrangesKernel E w) := by
  sorry
```

*Proof.* If `Im w = 0` then `w = ↑w.re` and `E w ≠ 0` by `h0`; otherwise `Im w ≠ 0`.
`memHE_deBrangesKernel_of_isHB`. ∎

```lean
theorem isH2Cont_of_memHE {E f : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) : IsH2Cont (fun z ↦ f z / E z) ∧ IsH2Cont (fun z ↦ fstar f z / E z) := by
  sorry
```

*Proof.* `hf.2.1`, `hf.2.2` give the `H²` parts; continuity at real `t`: `f`, `f^*`
(`hf.1.fstar`), `E` continuous and `E t ≠ 0` (`ContinuousAt.div`). ∎

```lean
theorem MemHE.heNormSq_lt_top {E f : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) : heNormSq E f < ⊤ := by
  sorry
```

*Proof.* `heNormSq E f = ∫⁻ ‖(f/E)(t)‖ₑ²` and `IsH2Cont.lintegral_real_lt_top` for `f/E`. ∎

```lean
theorem integrable_heInner {E f g : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) (hg : MemHE E g) :
    Integrable fun t : ℝ ↦ f t * conj (g t) / ((‖E t‖ ^ 2 : ℝ) : ℂ) := by
  sorry
```

*Proof.* Measurability: continuous integrand (`E t ≠ 0`).  Norm:
`‖f conj g/|E|²‖ = ‖f/E‖‖g/E‖ ≤ (‖f/E‖² + ‖g/E‖²)/2`, integrable by `memLp_real` of
`isH2Cont_of_memHE` and `memLp_two_iff_integrable_sq_norm`.  `Integrable.mono'`. ∎

```lean
theorem heInner_kernel_upper_of_isH2Cont {E f A B : ℂ → ℂ} (hE : IsHB E)
    (hE0 : ∀ᵐ t : ℝ, E t ≠ 0) (hA : IsH2Cont A) (hB : IsH2Cont B)
    (hAu : ∀ z : ℂ, 0 < z.im → A z = f z / E z)
    (hAr : ∀ᵐ t : ℝ, A t = f t / E t) (hBr : ∀ᵐ t : ℝ, B t = fstar f t / E t)
    {w : ℂ} (hw : 0 < w.im) : heInner E f (deBrangesKernel E w) = f w := by
  sorry
```

*Proof.* (This general form is for P4, where `E` may have real zeros.)  For a.e. `t` (`E t ≠ 0`,
`A t = (f/E)(t)`, `B t = (f^*/E)(t)`; `t ≠ w` always) the integrand of `heInner` equals
`(-i/2π)·[E(w)·A(t)/(t - w) - E^*(w)·conj(B(t))/(t - w)]` by `integrand_eq` (its hypothesis is
only `E t ≠ 0` at the point `t`) and the a.e. equalities `hAr`, `hBr`.  Both pieces are integrable:
`hA.integrable_div` (`Im w ≠ 0`) and `conj B(t)/(t - w) = conj(B(t)/(t - w̄))`, integrable by
`hB.integrable_div` and `ContinuousLinearMap.integrable_comp` with `Complex.conjCLE` (or
`Integrable.mono'` with `‖conj u‖ = ‖u‖`).  Values: `∫ A(t)/(t-w) = 2πi A(w) = 2πi f(w)/E(w)`
(`hA.cauchy_upper hw`, `hAu`), and `∫ conj B(t)/(t-w) = conj ∫ B(t)/(t - w̄) = conj 0 = 0`
(`integral_conj`, `hB.integral_div_lower`, `Im w̄ < 0`).  Total
`(-i/2π)·E(w)·2πi·f(w)/E(w) = f(w)` (`E w ≠ 0` by `IsHB`). ∎

```lean
theorem heInner_kernel_upper {E f : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) {w : ℂ} (hw : 0 < w.im) : heInner E f (deBrangesKernel E w) = f w := by
  sorry
```

*Proof.* `heInner_kernel_upper_of_isH2Cont` with `A = f/E`, `B = f^*/E`
(`isH2Cont_of_memHE`, equalities by `rfl`, `hE0` from `h0`). ∎

```lean
theorem heInner_kernel_lower {E f : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) {w : ℂ} (hw : w.im < 0) : heInner E f (deBrangesKernel E w) = f w := by
  sorry
```

*Proof.* As above with the roles exchanged: by `integrand_eq` (all real `t ≠ w`) and
integrability as above, `∫ (f/E)(t)/(t-w) = 0` (`integral_div_lower`, `Im w < 0`) and
`∫ conj((f^*/E)(t))/(t - w) = conj ∫ (f^*/E)(t)/(t - w̄) = conj(2πi (f^*/E)(w̄)) =
-2πi·f(w)/E^*(w)` (`cauchy_upper` at `w̄ ∈ ℂ₊`; `conj f^*(w̄) = f(w)`,
`conj E(w̄) = E^*(w)`).  Total `(-i/2π)·(-E^*(w))·(-2πi f(w)/E^*(w)) = f(w)`, using
`E^*(w) = conj E(w̄) ≠ 0` (`w̄ ∈ ℂ₊`). ∎

*Implemented:* `heInner_kernel_upper_of_isH2Cont` and `heInner_kernel_lower` share the new lemma
`heInner_kernel_eq_of_ae`: for nonreal `w` and `IsH2Cont` functions `A`, `B` equal a.e. on `ℝ` to `f/E`,
`f^*/E` (with `E ≠ 0` a.e. on `ℝ`),
`⟨f, K_w⟩ = (-i/2π)[E(w)∫A(t)/(t - w) dt - E^*(w)·conj ∫B(t)/(t - w̄) dt]`; it is reusable by P4.
The integrability of `conj` is the helper `integrable_conj` (through `Complex.conjCLE`).

```lean
theorem heInner_kernel_real {E f : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) (x : ℝ) : heInner E f (deBrangesKernel E x) = f x := by
  sorry
```

*Proof.* By `integrand_eq_real`, for every `t ≠ x` (a.e.) the integrand equals
`(-i/2π)[E(x)P(t) - E^*(x)conj Q(t) + f(x)·2i/((t-x)²+1)]` where
`P(t) = (A(t) - A(x)ψ(t))/(t-x)`, `Q(t) = (g(t) - g(x)ψ(t))/(t-x)`, `A = f/E`, `g = f^*/E`.
`A`, `g` are `IsH2Cont` (`isH2Cont_of_memHE`) and differentiable at `x` (`E x ≠ 0`).
`P`, `Q` integrable (`integrable_reg_real`), `conj Q` integrable, last term integrable.
`∫ P = 0`, `∫ Q = 0` (`cauchy_real`), `∫ conj Q = conj 0 = 0` (`integral_conj`),
`∫ 2i/((t-x)²+1) = 2πi` (`integral_two_I_div`).  Total `(-i/2π)·f(x)·2πi = f(x)`. ∎

```lean
theorem heInner_kernel {E f : ℂ → ℂ} (hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)
    (hf : MemHE E f) (w : ℂ) : heInner E f (deBrangesKernel E w) = f w := by
  sorry
```

*Proof.* Trichotomy on `Im w`: `heInner_kernel_upper`, `heInner_kernel_lower`, or `w = ↑w.re`
and `heInner_kernel_real`. ∎

---------------------------------------------------------------------------------------------------

## 4. `Space.lean` — `H(E)` as a Hilbert space of functions

No `InnerProductSpace` instance is built: everything is stated for functions `ℂ → ℂ` and the
integrals `heInner`, `heNormSq`.  Section variables in §4.2–4.4:
`(hE : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0)`, included only where marked `include hE h0 in`
(strictness is never needed in this file).

### 4.1 Linear structure

```lean
theorem MemHE.add {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    MemHE E (fun z ↦ f z + g z) := by
  sorry
```

*Proof.* `Differentiable.add`; `(f+g)/E = f/E + g/E` (`add_div`) and `IsH2Upper.add`;
`fstar (f + g) = f^* + g^*` (`fstar_add`), same. ∎

```lean
theorem MemHE.const_mul {f : ℂ → ℂ} (hf : MemHE E f) (c : ℂ) : MemHE E (fun z ↦ c * f z) := by
  sorry
```

*Proof.* `(c f)/E = c·(f/E)` (`mul_div_assoc`), `IsH2Upper.const_mul`;
`fstar (c f) = conj c · f^*` (`fstar_const_mul`), `IsH2Upper.const_mul (conj c)`. ∎

```lean
theorem MemHE.sub {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    MemHE E (fun z ↦ f z - g z) := by
  sorry

theorem memHE_zero : MemHE E (fun _ ↦ 0) := by
  sorry
```

*Proof.* `sub`: `add` and `const_mul (-1)` (or `IsH2Upper.sub`).  `zero`: `differentiable_const`;
`0/E = 0` has line integrals `0` (`lintegral_zero`); `fstar 0 = 0`. ∎

```lean
theorem MemHE.finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, MemHE E (f i)) : MemHE E (fun z ↦ ∑ i ∈ s, f i z) := by
  sorry
```

*Proof.* `Finset.induction_on` with `memHE_zero` and `MemHE.add` (`Finset.sum_insert`). ∎

```lean
theorem MemHE.of_const_mul {f : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) (h : MemHE E (fun z ↦ c * f z)) :
    MemHE E f := by
  sorry
```

*Proof.* `f = fun z ↦ c⁻¹ * (c * f z)` (`funext`, `inv_mul_cancel_left₀`); `MemHE.const_mul`. ∎

```lean
theorem memHE_fstar {f : ℂ → ℂ} (hf : MemHE E f) : MemHE E (fstar f) := by
  sorry
```

*Proof.* `hf.1.fstar`; the two `H²` conditions are swapped, using `fstar (fstar f) = f`
(`funext`, `simp [fstar]`). ∎

```lean
theorem heNormSq_fstar (f : ℂ → ℂ) : heNormSq E (fstar f) = heNormSq E f := by
  sorry
```

*Proof.* `lintegral_congr`: `‖fstar f t/E t‖ = ‖conj (f t)‖/‖E t‖ = ‖f t/E t‖`
(`fstar_ofReal`, `Complex.norm_conj`). ∎

### 4.2 The sesquilinear form

```lean
include hE in
theorem heInner_self {f : ℂ → ℂ} (hf : MemHE E f) :
    heInner E f f = (((heNormSq E f).toReal : ℝ) : ℂ) := by
  sorry
```

*Proof.* Pointwise `f t·conj (f t)/↑‖E t‖² = ↑(‖f t/E t‖²)` (`Complex.mul_conj`,
`Complex.normSq_eq_norm_sq`; both `0` if `E t = 0`).  `integral_ofReal`, then
`integral_eq_lintegral_of_nonneg_ae` (nonneg; `AEStronglyMeasurable` since `f/E` is measurable as
a quotient of continuous functions) and `enorm_sq_eq_ofReal`. ∎

*Implemented:* without `h0` (`include hE in`; call as `heInner_self hE hf`). It is unused: if
`‖f‖_E = ∞`, the Bochner integral of the non-integrable nonnegative integrand is `0 = ∞.toReal`, and the
measurability of `f/E` on `ℝ` needs only the continuity of `E` (helper `measurable_div_real`).

```lean
theorem heInner_conj_symm (f g : ℂ → ℂ) : conj (heInner E f g) = heInner E g f := by
  sorry
```

*Proof.* `integral_conj` (no integrability needed) and pointwise
`conj (f conj g/↑r) = g conj f/↑r` (`map_div₀`, `Complex.conj_ofReal`, `mul_comm`). ∎

```lean
include hE h0 in
theorem heInner_add_left {f g k : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) (hk : MemHE E k) :
    heInner E (fun z ↦ f z + g z) k = heInner E f k + heInner E g k := by
  sorry

include hE h0 in
theorem heInner_sub_left {f g k : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) (hk : MemHE E k) :
    heInner E (fun z ↦ f z - g z) k = heInner E f k - heInner E g k := by
  sorry
```

*Proof.* `integral_add`/`integral_sub` with `integrable_heInner hE.1 h0`; pointwise `ring`. ∎

```lean
theorem heInner_smul_left (f k : ℂ → ℂ) (c : ℂ) :
    heInner E (fun z ↦ c * f z) k = c * heInner E f k := by
  sorry

theorem heInner_smul_right (f k : ℂ → ℂ) (c : ℂ) :
    heInner E f (fun z ↦ c * k z) = conj c * heInner E f k := by
  sorry
```

*Proof.* `integral_const_mul` (valid without integrability) and pointwise `ring`
(`map_mul` for `conj (c * k t)`). ∎

```lean
include hE h0 in
theorem heInner_sum_left {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {k : ℂ → ℂ}
    (hf : ∀ i ∈ s, MemHE E (f i)) (hk : MemHE E k) :
    heInner E (fun z ↦ ∑ i ∈ s, f i z) k = ∑ i ∈ s, heInner E (f i) k := by
  sorry

include hE h0 in
theorem heInner_sum_right {ι : Type*} (s : Finset ι) {f : ℂ → ℂ} {k : ι → ℂ → ℂ}
    (hf : MemHE E f) (hk : ∀ i ∈ s, MemHE E (k i)) :
    heInner E f (fun z ↦ ∑ i ∈ s, k i z) = ∑ i ∈ s, heInner E f (k i) := by
  sorry
```

*Proof.* `Finset.induction_on`, `heInner_add_left`, `MemHE.finset_sum`; the right version by
`heInner_conj_symm` and `Complex.conj` of a finite sum (`map_sum`). ∎

```lean
include hE h0 in
theorem heNormSq_sub {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    (heNormSq E (fun z ↦ f z - g z)).toReal =
      (heNormSq E f).toReal + (heNormSq E g).toReal - 2 * (heInner E f g).re := by
  sorry
```

*Proof.* `heInner_self` for `f - g` (`MemHE.sub`), expand with `heInner_sub_left` and its right
analogue (from `heInner_conj_symm`), `heInner E g f = conj (heInner E f g)`, take real parts:
`‖f-g‖² = ‖f‖² - 2 Re⟨f,g⟩ + ‖g‖²` (`Complex.add_conj`, `Complex.ofReal_re`). ∎

```lean
include hE h0 in
theorem norm_heInner_sq_le {f g : ℂ → ℂ} (hf : MemHE E f) (hg : MemHE E g) :
    ‖heInner E f g‖ ^ 2 ≤ (heNormSq E f).toReal * (heNormSq E g).toReal := by
  sorry
```

*Proof.* `‖⟨f,g⟩‖ₑ ≤ ∫⁻ ‖f/E‖ₑ‖g/E‖ₑ` (`enorm_integral_le_lintegral_enorm`,
`heInner_eq_integral_div`), and `ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2`:
`≤ (∫⁻‖f/E‖ₑ²)^{1/2}(∫⁻‖g/E‖ₑ²)^{1/2}`.  Square and convert to `ℝ` (finite by
`MemHE.heNormSq_lt_top`).  (Alternative: the real Hölder inequality
`integral_mul_le_Lp_mul_Lq_of_nonneg` applied to `‖f/E‖`, `‖g/E‖`.) ∎

```lean
include hE h0 in
theorem tendsto_heInner_right {f g : ℂ → ℂ} {gs : ℕ → ℂ → ℂ} (hf : MemHE E f)
    (hg : MemHE E g) (hgs : ∀ n, MemHE E (gs n))
    (hlim : Tendsto (fun n ↦ heNormSq E (fun z ↦ gs n z - g z)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ heInner E f (gs n)) atTop (𝓝 (heInner E f g)) := by
  sorry
```

*Proof.* `‖⟨f, gₙ⟩ - ⟨f, g⟩‖² = ‖⟨f, gₙ - g⟩‖² ≤ ‖f‖²·‖gₙ - g‖²` (`heInner_sub_left` on the
conjugated side, `norm_heInner_sq_le`), and `‖gₙ - g‖² → 0` (`ENNReal.tendsto_toReal`).
`squeeze_zero`. ∎

### 4.3 Kernels and the evaluation bound

```lean
include hE h0 in
theorem heNormSq_kernel (w : ℂ) :
    (heNormSq E (deBrangesKernel E w)).toReal = (deBrangesKernel E w w).re := by
  sorry
```

*Proof.* `heInner_self` (with `memHE_deBrangesKernel hE h0 w`) and `heInner_kernel` with
`f = K_w`: `↑‖K_w‖² = ⟨K_w, K_w⟩ = K_w(w)`; take real parts. ∎

```lean
include hE h0 in
theorem heInner_kernel_kernel (w z : ℂ) :
    heInner E (deBrangesKernel E w) (deBrangesKernel E z) = deBrangesKernel E w z := by
  sorry
```

*Proof.* `heInner_kernel hE h0 (memHE_deBrangesKernel hE h0 w) z`. ∎

```lean
include hE h0 in
theorem norm_sq_le_kernel_mul {f : ℂ → ℂ} (hf : MemHE E f) (z : ℂ) :
    ‖f z‖ ^ 2 ≤ (deBrangesKernel E z z).re * (heNormSq E f).toReal := by
  sorry
```

*Proof.* `f z = ⟨f, K_z⟩` (`heInner_kernel`); `norm_heInner_sq_le` and `heNormSq_kernel`. ∎

```lean
include hE h0 in
theorem eq_zero_of_heNormSq_eq_zero {f : ℂ → ℂ} (hf : MemHE E f) (h : heNormSq E f = 0) :
    ∀ z, f z = 0 := by
  sorry
```

*Proof.* `norm_sq_le_kernel_mul` with `‖f‖² = 0`. ∎

### 4.4 Line integrals and completeness

```lean
include hE h0 in
theorem MemHE.lintegral_line_le {f : ℂ → ℂ} (hf : MemHE E f) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ heNormSq E f ∧
    ∫⁻ x : ℝ, ‖fstar f ((x : ℂ) + (y : ℂ) * I) / E ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤
      heNormSq E f := by
  sorry
```

*Proof.* `IsH2Cont.lintegral_line_le` for `f/E` and `f^*/E` (`isH2Cont_of_memHE`); the right sides
are `heNormSq E f` and `heNormSq E (fstar f) = heNormSq E f` (`heNormSq_fstar`). ∎

```lean
include hE h0 in
theorem memHE_of_cauchy (f : ℕ → ℂ → ℂ) (hf : ∀ n, MemHE E (f n))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      heNormSq E (fun z ↦ f m z - f n z) ≤ ENNReal.ofReal ε) :
    ∃ g : ℂ → ℂ, MemHE E g ∧ (∀ z : ℂ, Tendsto (fun n ↦ f n z) atTop (𝓝 (g z))) ∧
      Tendsto (fun n ↦ heNormSq E (fun z ↦ f n z - g z)) atTop (𝓝 0) := by
  sorry
```

*Proof.*
1. *Pointwise and locally uniform limit.*  For `z ∈ ℂ` and `m, n`,
   `‖f m z - f n z‖² ≤ K(z,z)·‖f m - f n‖²` (`norm_sq_le_kernel_mul` for `f m - f n ∈ H(E)`).
   With `M_ρ` from `exists_bound_deBrangesKernel hE.1 ρ` (so `K(z,z).re ≤ M_ρ` for `‖z‖ ≤ ρ`), the
   sequence is uniformly Cauchy on `closedBall 0 ρ`.  Let `g z = limUnder atTop (f · z)`
   (`cauchySeq_tendsto_of_complete`); `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto` gives
   uniform convergence on each ball, so `TendstoLocallyUniformlyOn` on `ball 0 ρ`, and
   `TendstoLocallyUniformlyOn.differentiableOn` (each `f n` entire) shows `g` is differentiable on
   every ball: `Differentiable ℂ g`.
2. *Norm convergence.*  For `n ≥ N(ε)`, Fatou (`lintegral_liminf_le`, pointwise
   `‖(f n t - f m t)/E t‖ₑ² → ‖(f n t - g t)/E t‖ₑ²` as `m → ∞`):
   `heNormSq E (f n - g) ≤ liminf_m heNormSq E (f n - f m) ≤ ofReal ε`.
3. *`g ∈ H(E)`.*  `B := sup_n ‖f n‖² < ∞` (for `n ≥ N(1)`:
   `‖f n‖² ≤ 2‖f N‖² + 2‖f n - f N‖²` by `enorm_add_sq_le` under the integral; finitely many
   others; all finite by `MemHE.heNormSq_lt_top`).  For `y > 0`, by Fatou with pointwise
   convergence on the line and `MemHE.lintegral_line_le`:
   `∫⁻ ‖(g/E)(x+iy)‖ₑ² ≤ liminf ∫⁻ ‖(f n/E)(x+iy)‖ₑ² ≤ B`.  Same for `g^*/E`, since
   `f n^*(z) = conj (f n (conj z)) → conj (g (conj z)) = g^*(z)` and the second conjunct of
   `MemHE.lintegral_line_le` bounds the lines of `f n^*/E` by `‖f n‖²`.  `g/E`, `g^*/E` are
   differentiable on `ℂ₊`.  So `MemHE E g` with constant `B.toNNReal`. ∎

*Implemented:* step 1 is the pair of helpers `uniformCauchySeqOn_of_cauchy` and `exists_limit_of_cauchy`;
the three Fatou steps use one helper, `lintegral_enorm_sq_le_of_tendsto` (Fatou for `‖·‖ₑ²` along
pointwise limits), which takes an *eventual* bound, so in step 3 the bound `B` is only needed for
`n ≥ N(1)`. `heInner_sub_right` is added to the file (R9 §8).

---------------------------------------------------------------------------------------------------

## 5. `Orthogonal.lean` — the system `{K_γ}`, Bessel, and `h = D/S`

```lean
structure DBData (E : ℂ → ℂ) (φ : ℝ → ℝ) : Prop where
  strict : IsStrictHB E
  noZero : ∀ x : ℝ, E x ≠ 0
  phase : IsPhaseFunction E φ

def cFun (E : ℂ → ℂ) (α : ℝ) : ℂ → ℂ :=
  fun z ↦ (Complex.exp (I * α) * E z + Complex.exp (-(I * α)) * fstar E z) / 2

def sFun (E : ℂ → ℂ) (α : ℝ) : ℂ → ℂ :=
  fun z ↦ (Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z) / (2 * I)

def wt (E : ℂ → ℂ) (x : ℝ) : ℝ := Real.pi / (phaseDeriv E x * ‖E x‖ ^ 2)

def cLev (E : ℂ → ℂ) (x : ℝ) : ℝ := 1 / (Real.pi * phaseDeriv E x)

def rTerm (E : ℂ → ℂ) (α : ℝ) (γ : ℝ) (z : ℂ) : ℂ :=
  ((cLev E γ : ℝ) : ℂ) * (1 + (γ : ℂ) * z) / (1 + (γ : ℂ) ^ 2) * dslope (sFun E α) (γ : ℂ) z

def rFun (E : ℂ → ℂ) (φ : ℝ → ℝ) (α : ℝ) (z : ℂ) : ℂ :=
  ∑' γ : phaseLevel φ α, rTerm E α γ z

def dFun (E : ℂ → ℂ) (φ : ℝ → ℝ) (α : ℝ) (z : ℂ) : ℂ :=
  cFun E α z + Real.pi * rFun E φ α z

def defectKer (E : ℂ → ℂ) (φ : ℝ → ℝ) (α : ℝ) (w z : ℂ) : ℂ :=
  deBrangesKernel E w z - ∑' γ : phaseLevel φ α,
    deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * ((wt E γ : ℝ) : ℂ)

def partialSum (E : ℂ → ℂ) (φ : ℝ → ℝ) (α : ℝ) (a : ℝ → ℂ) (F : Finset (phaseLevel φ α)) :
    ℂ → ℂ :=
  fun z ↦ ∑ γ ∈ F, a γ * ((wt E γ : ℝ) : ℂ) * deBrangesKernel E (γ : ℂ) z
```

Remarks on the definitions.  `rTerm` uses `dslope (sFun E α) γ` (entire) instead of `S(z)/(z-γ)`
so that every term is entire with no case distinction; `defectKer` and `rFun` are `tsum`s in `ℂ`
over the subtype `Γ = phaseLevel φ α` — every manipulation needs a summability proof
(`summable_rTerm`, `summable_defect`).  `partialSum` is the finite sum `Σ_{γ∈F} a(γ) wt(γ) K_γ`.

*Implemented:* the file imports `EAux/KernelSymm.lean` and uses `deBrangesKernel_conj_symm` where the
text below cites `conj_deBrangesKernel` (§2). Mathlib names in this version: `Summable.tsum_sub`,
`Summable.tsum_add`, `Summable.tsum_mul_left`, `Summable.tsum_le_tsum` (no root `tsum_sub` etc.);
`Complex.conj_tsum` and `Complex.ofReal_tsum` need no summability, `Complex.re_tsum` does.

### 5.1 Algebra of `C`, `S` and the kernel

```lean
theorem fstar_cFun (E : ℂ → ℂ) (α : ℝ) : fstar (cFun E α) = cFun E α := by
  sorry

theorem fstar_sFun (E : ℂ → ℂ) (α : ℝ) : fstar (sFun E α) = sFun E α := by
  sorry
```

*Proof.* `funext z`, unfold.  `conj (exp(Iα)) = exp(-Iα)` (`← Complex.exp_conj`,
`map_mul`, `Complex.conj_I`, `Complex.conj_ofReal`), `conj (fstar E (conj z)) = E z`,
`conj 2 = 2`, `conj (2I) = -2I`; `ring`. ∎

```lean
theorem differentiable_cFun (hE : Differentiable ℂ E) (α : ℝ) : Differentiable ℂ (cFun E α) := by
  sorry

theorem differentiable_sFun (hE : Differentiable ℂ E) (α : ℝ) : Differentiable ℂ (sFun E α) := by
  sorry
```

*Proof.* `hE`, `hE.fstar`, constants: `fun_prop`/`Differentiable.const_mul`, `.add`, `.sub`,
`.div_const`. ∎

```lean
theorem sAlpha_eq (E : ℂ → ℂ) (α : ℝ) :
    (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z) =
      fun z ↦ (2 * I) * sFun E α z := by
  sorry
```

*Proof.* `funext z; unfold sFun; field_simp` (`2I ≠ 0`). ∎

```lean
theorem E_eq_CS (E : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    E z = Complex.exp (-(I * α)) * (cFun E α z + I * sFun E α z) := by
  sorry
```

*Proof.* `C + iS = (U+V)/2 + (U-V)/2 = U = exp(Iα)E`; `exp(-Iα)exp(Iα) = 1`
(`← Complex.exp_add`, `Complex.exp_zero`). ∎

```lean
theorem kernel_mul_CS (E : ℂ → ℂ) (α : ℝ) (w z : ℂ) :
    deBrangesKernel E w z * (Real.pi * (z - conj w)) =
      cFun E α z * conj (sFun E α w) - sFun E α z * conj (cFun E α w) := by
  sorry
```

*Proof.* `deBrangesKernel_mul`: LHS `= (I/2)·kernelNum E w z`.  Substitute `E = e^{-iα}(C + iS)`
(`E_eq_CS`) and `E^* = e^{iα}(C - iS)` (apply `fstar` to `E_eq_CS`, use `fstar_cFun`,
`fstar_sFun`).  Since `e^{-iα}conj(e^{-iα}) = 1`,
`kernelNum = (C+iS)(z)(conj C - i conj S)(w) - (C-iS)(z)(conj C + i conj S)(w)
= -2i C(z)conj S(w) + 2i S(z)conj C(w)`, and `(I/2)·(that) = C(z)conj S(w) - S(z)conj C(w)`
(`ring` with `I² = -1`). ∎

### 5.2 The level set `Γ`

```lean
theorem sFun_eq_zero_iff (D : DBData E φ) (z : ℂ) :
    sFun E α z = 0 ↔ z ∈ Complex.ofReal '' phaseLevel φ α := by
  sorry
```

*Proof.* Let `θ = α - π/2`, `F = fun _ ↦ exp(Iθ)` (`= (isHB_one).rotate θ` up to `mul_one`), with
phase function `fun _ ↦ -θ` (`IsPhaseFunction` of the constant `1` with phase `0`, then
`IsPhaseFunction.rotate`), `F x ≠ 0`.  Then `E F + E^* F^* = exp(Iθ)E + exp(-Iθ)E^*` and
`exp(Iθ) = -I exp(Iα)`, `exp(-Iθ) = I exp(-Iα)` (`Complex.exp_add`,
`Complex.exp_pi_div_two_mul_I`-type identities or `exp(-iπ/2) = -I`), so
`E F + E^* F^* = -I(exp(Iα)E - exp(-Iα)E^*) = 2S`.  `zero_set_eq_phaseLevel D.strict hF D.noZero
(fun _ ↦ exp_ne_zero _) D.phase hφF z`: `2S z = 0 ↔ z ∈ ofReal '' phaseLevel (φ - θ) (π/2)`, and
`φ t - θ = π/2 + kπ ↔ φ t = α + kπ` (`phaseLevel` unfolds to an `∃ k`, `ring_nf`). ∎

```lean
theorem sFun_ne_zero (D : DBData E φ) {w : ℂ} (hw : w.im ≠ 0) : sFun E α w ≠ 0 := by
  sorry
```

*Proof.* If `S w = 0`, `w = ↑γ` by `sFun_eq_zero_iff`, so `Im w = 0`. ∎

```lean
theorem cFun_level (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    (cFun E α γ).im = 0 ∧ (cFun E α γ).re ^ 2 = ‖E γ‖ ^ 2 := by
  sorry
```

*Proof.* On `ℝ`, `V(x) = e^{-iα}conj E(x) = conj U(x)` (`fstar_ofReal`), so
`C(x) = (U + conj U)/2 = ↑(Re U(x))` and `S(x) = (U - conj U)/(2i) = ↑(Im U(x))`
(`Complex.add_conj`, `Complex.sub_conj`).  At `γ ∈ Γ`, `S γ = 0` (`sFun_eq_zero_iff`), so
`U(γ) = C(γ) + iS(γ) = C(γ)` is real and `C(γ).re² = ‖U γ‖² = ‖E γ‖²`
(`‖exp(Iα)‖ = 1`: `Complex.norm_exp_I_mul_ofReal`). ∎

```lean
theorem deriv_sFun_level (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    deriv (sFun E α) (γ : ℂ) = -(cFun E α γ) * (phaseDeriv E γ : ℂ) := by
  sorry
```

*Proof.* `deriv S x = (exp(Iα)E'(x) - exp(-Iα)(E^*)'(x))/(2I)` (`deriv_div_const`, `deriv_sub`,
`deriv_const_mul`; differentiability of `E`, `E^*`) and `(E^*)'(x) = conj E'(x)`
(`deriv_fstar_ofReal`), so `S'(x) = (U'(x) - conj U'(x))/(2i) = ↑(Im U'(x))` with
`U' = exp(Iα)E'`.  At `γ`: `U'(γ) = U(γ)·(E'/E)(γ) = C(γ)·(E'/E)(γ)` (`E γ ≠ 0`, `cFun_level`),
`C(γ) = ↑(C(γ).re)`, so `Im U'(γ) = C(γ).re·Im(E'/E)(γ) = -C(γ).re·phaseDeriv E γ`. ∎

```lean
theorem kernel_level_mul (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (z : ℂ) :
    deBrangesKernel E (γ : ℂ) z * (Real.pi * (z - γ)) = -(cFun E α γ) * sFun E α z := by
  sorry
```

*Proof.* `kernel_mul_CS` at `w = ↑γ`: `conj ↑γ = ↑γ`, `conj S(γ) = 0`, `conj C(γ) = C(γ)`
(`cFun_level`: imaginary part `0`, `Complex.conj_eq_iff_im`). ∎

```lean
theorem kernel_level_orth (D : DBData E φ) {γ γ' : ℝ} (hγ : γ ∈ phaseLevel φ α)
    (hγ' : γ' ∈ phaseLevel φ α) (hne : γ ≠ γ') : deBrangesKernel E (γ : ℂ) γ' = 0 := by
  sorry
```

*Proof.* `kernel_level_mul` at `z = ↑γ'`: `S(γ') = 0` gives `K(γ,γ')·π(γ' - γ) = 0` and
`π(γ' - γ) ≠ 0`. ∎

```lean
theorem kernel_level_eq_dslope (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (z : ℂ) :
    deBrangesKernel E (γ : ℂ) z = -(cFun E α γ / Real.pi) * dslope (sFun E α) (γ : ℂ) z := by
  sorry
```

*Proof.* `z ≠ γ`: `dslope S γ z = S z/(z - γ)` (`dslope_of_ne`, `slope_def_field`, `S γ = 0`) and
divide `kernel_level_mul` by `π(z - γ)`.  `z = γ`: `dslope_same`, `deriv_sFun_level`:
RHS `= -(C/π)(-C φ') = C²φ'/π = ‖E γ‖²φ'/π` (`C = ↑C.re`, `cFun_level`) `= K(γ,γ)`
(`deBrangesKernel_diag_real`). ∎

```lean
theorem wt_pos (D : DBData E φ) (x : ℝ) : 0 < wt E x := by
  sorry

theorem cLev_pos (D : DBData E φ) (x : ℝ) : 0 < cLev E x := by
  sorry
```

*Proof.* `IsStrictHB.phaseDeriv_pos D.strict (D.noZero x)`, `‖E x‖ > 0`, `Real.pi_pos`;
`div_pos`, `mul_pos`. ∎

```lean
theorem kernel_diag_mul_wt (D : DBData E φ) (x : ℝ) :
    deBrangesKernel E (x : ℂ) x * (wt E x : ℂ) = 1 := by
  sorry
```

*Proof.* `deBrangesKernel_diag_real`: `↑(φ'|E|²/π)·↑(π/(φ'|E|²)) = 1` (`field_simp` with the
positivity facts of `wt_pos`). ∎

```lean
theorem wt_mul_norm_kernel_level_sq (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (z : ℂ) :
    wt E γ * ‖deBrangesKernel E (γ : ℂ) z‖ ^ 2 =
      cLev E γ * ‖dslope (sFun E α) (γ : ℂ) z‖ ^ 2 := by
  sorry
```

*Proof.* `kernel_level_eq_dslope`: `‖K(γ,z)‖² = (‖C γ‖/π)²‖d_γ z‖²`, `‖C γ‖² = ‖E γ‖²`
(`cFun_level`), so `wt·‖K‖² = π/(φ'‖E‖²)·‖E‖²/π²·‖d‖² = ‖d‖²/(πφ') = c_γ‖d‖²`
(`field_simp`). ∎

```lean
theorem orthWeight_eq (E : ℂ → ℂ) (x : ℝ) : orthWeight E x = ENNReal.ofReal (wt E x) := by
  sorry
```

*Proof.* `rfl` (both unfold to `ENNReal.ofReal (π / (phaseDeriv E x * ‖E x‖ ^ 2))`). ∎

```lean
theorem phaseLevel_inter_Icc_finite (D : DBData E φ) (α a b : ℝ) :
    (phaseLevel φ α ∩ Icc a b).Finite := by
  sorry
```

*Proof.* `φ` is strictly monotone (`IsPhaseFunction.strictMono_of_isStrictHB D.strict D.noZero
D.phase`).  For `x ∈ Γ ∩ [a,b]`, `φ x = α + kπ ∈ [φ a, φ b]`, so `k` lies in the finite set
`Finset.Icc ⌈(φ a - α)/π⌉ ⌊(φ b - α)/π⌋` (`Int.ceil_le`, `Int.le_floor`).  Hence
`Γ ∩ [a,b] ⊆ φ ⁻¹' T` with `T = (fun k : ℤ ↦ α + kπ) '' (that finite set)` finite, and the
preimage of a finite set under the injective `φ` is finite (`Set.Finite.preimage`,
`StrictMono.injective.injOn`). ∎

### 5.3 Partial sums and Bessel's inequality

In this subsection `hE := D.strict.1`, `h0 := D.noZero`, and `K_γ ∈ H(E)` by
`memHE_deBrangesKernel`.  Distinct elements of the subtype `Γ` have distinct values
(`Subtype.ext`), so `kernel_level_orth` applies to them.

```lean
theorem memHE_partialSum (D : DBData E φ) (a : ℝ → ℂ) (F : Finset (phaseLevel φ α)) :
    MemHE E (partialSum E φ α a F) := by
  sorry
```

*Proof.* `MemHE.finset_sum`, each term `MemHE.const_mul (memHE_deBrangesKernel …) _`
(`partialSum` unfolds to `fun z ↦ Σ (a γ * wt γ) * K γ z`, `mul_assoc`). ∎

```lean
theorem heNormSq_partialSum (D : DBData E φ) (a : ℝ → ℂ) (F : Finset (phaseLevel φ α)) :
    (heNormSq E (partialSum E φ α a F)).toReal = ∑ γ ∈ F, wt E γ * ‖a γ‖ ^ 2 := by
  sorry
```

*Proof.* `heInner_self`: `↑‖s‖² = ⟨s, s⟩`.  Expand with `heInner_sum_left`, `heInner_sum_right`,
`heInner_smul_left/right`: `⟨s,s⟩ = Σ_{γ∈F}Σ_{γ'∈F} a_γ wt_γ conj(a_γ' wt_γ')⟨K_γ, K_γ'⟩`,
`⟨K_γ, K_γ'⟩ = K(γ,γ')` (`heInner_kernel_kernel`), `= 0` for `γ ≠ γ'`
(`Finset.sum_eq_single`).  Diagonal: `|a_γ|²wt_γ²K(γ,γ) = wt_γ|a_γ|²` (`kernel_diag_mul_wt`,
`Complex.mul_conj`).  Take real parts (`Complex.ofReal_sum`). ∎

*Implemented* more simply, without the double sum: the code proves `partialSum_level` and
`heInner_partialSum` first, and then `⟨s, s⟩ = Σ_F conj(a_γ)wt_γ s(γ)` (`heInner_partialSum` with
`f = s`) with `s(γ) = a_γ` (`partialSum_level`) gives `Σ_F wt_γ|a_γ|²`.

```lean
theorem heInner_partialSum (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f) (a : ℝ → ℂ)
    (F : Finset (phaseLevel φ α)) :
    heInner E f (partialSum E φ α a F) = ∑ γ ∈ F, conj (a γ) * (wt E γ : ℂ) * f γ := by
  sorry
```

*Proof.* `heInner_sum_right`, `heInner_smul_right`, `heInner_kernel`;
`conj (a γ * ↑wt) = conj (a γ) * ↑wt`. ∎

```lean
theorem partialSum_level (D : DBData E φ) (a : ℝ → ℂ) {F : Finset (phaseLevel φ α)}
    {γ : phaseLevel φ α} (hγ : γ ∈ F) : partialSum E φ α a F γ = a γ := by
  sorry
```

*Proof.* `Finset.sum_eq_single γ`: for `γ' ≠ γ`, `K(γ',γ) = 0` (`kernel_level_orth`); the diagonal
term is `a γ·wt γ·K(γ,γ) = a γ` (`kernel_diag_mul_wt`). ∎

```lean
theorem bessel_finite (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f)
    (F : Finset (phaseLevel φ α)) :
    ∑ γ ∈ F, wt E γ * ‖f γ‖ ^ 2 ≤ (heNormSq E f).toReal := by
  sorry
```

*Proof.* Let `a = fun t ↦ f t`, `s = partialSum E φ α a F`.  `0 ≤ ‖f - s‖².toReal`
`= ‖f‖² + ‖s‖² - 2Re⟨f,s⟩` (`heNormSq_sub`) with `‖s‖² = Σ_F wt|f(γ)|²`
(`heNormSq_partialSum`) and `⟨f, s⟩ = Σ_F conj(f γ)wt f(γ) = ↑Σ_F wt|f γ|²`
(`heInner_partialSum`, `Complex.mul_conj`).  So `0 ≤ ‖f‖² - Σ_F wt|f(γ)|²`. ∎

```lean
theorem bessel (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f) :
    Summable (fun γ : phaseLevel φ α ↦ wt E γ * ‖f γ‖ ^ 2) ∧
      ∑' γ : phaseLevel φ α, wt E γ * ‖f γ‖ ^ 2 ≤ (heNormSq E f).toReal := by
  sorry
```

*Proof.* Nonnegative terms (`wt_pos`) with bounded finite sums: `summable_of_sum_le` and
`Real.tsum_le_of_sum_le`. ∎

```lean
theorem summable_cLev_dslope_sq (D : DBData E φ) (z : ℂ) :
    Summable (fun γ : phaseLevel φ α ↦ cLev E γ * ‖dslope (sFun E α) (γ : ℂ) z‖ ^ 2) ∧
      ∑' γ : phaseLevel φ α, cLev E γ * ‖dslope (sFun E α) (γ : ℂ) z‖ ^ 2 ≤
        (deBrangesKernel E z z).re := by
  sorry
```

*Proof.* `bessel` for `f = K_z` (`memHE_deBrangesKernel`): `Σ wt|K(z,γ)|² ≤ ‖K_z‖² = K(z,z).re`
(`heNormSq_kernel`).  `‖K(z,γ)‖ = ‖K(γ,z)‖` (`conj_deBrangesKernel`, `Complex.norm_conj`) and
`wt·‖K(γ,z)‖² = c_γ‖d_γ z‖²` (`wt_mul_norm_kernel_level_sq`, using `γ.2`): rewrite the summand
(`funext`, `Summable.congr`, `tsum_congr`). ∎

```lean
theorem summable_cLev_div (D : DBData E φ) {w : ℂ} (hw : w.im ≠ 0) :
    Summable (fun γ : phaseLevel φ α ↦ cLev E γ / ‖w - (γ : ℂ)‖ ^ 2) := by
  sorry
```

*Proof.* For `w` nonreal, `w ≠ ↑γ`, `d_γ(w) = S(w)/(w - γ)` and `S w ≠ 0` (`sFun_ne_zero`), so
`c_γ/‖w - γ‖² = (‖S w‖²)⁻¹·c_γ‖d_γ w‖²`; `(summable_cLev_dslope_sq D w).1.mul_left`. ∎

```lean
theorem summable_cLev_div_one_add_sq (D : DBData E φ) :
    Summable (fun γ : phaseLevel φ α ↦ cLev E γ / (1 + (γ : ℝ) ^ 2)) := by
  sorry
```

*Proof.* `summable_cLev_div D (w := I)` (`Im I = 1 ≠ 0`) and `‖I - γ‖² = 1 + γ²`
(`norm_sq_line_sub`-type computation). ∎

### 5.4 The Mittag-Leffler series and `h = D/S`

```lean
theorem norm_rTerm_le (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) {ρ M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖sFun E α z‖ ≤ M) (hγρ : 2 * ρ + 1 ≤ |γ|) {z : ℂ} (hz : ‖z‖ ≤ ρ) :
    ‖rTerm E α γ z‖ ≤ 2 * M * (1 + ρ) * (cLev E γ / (1 + γ ^ 2)) := by
  sorry
```

*Proof.* `|γ| ≥ 2ρ+1 > ρ ≥ ‖z‖` so `z ≠ γ`, `d_γ z = S z/(z - γ)` and
`‖z - γ‖ ≥ |γ| - ρ ≥ |γ|/2`.  Also `‖1 + γz‖ ≤ 1 + |γ|ρ` and `|γ| ≥ 1`.  Hence
`‖rTerm γ z‖ ≤ c_γ(1 + |γ|ρ)/(1+γ²)·2M/|γ| = c_γ/(1+γ²)·2M(1/|γ| + ρ) ≤ 2M(1+ρ)c_γ/(1+γ²)`
(`cLev_pos`; `M ≥ 0` follows from `hM 0` if `ρ ≥ 0`, and the claim is vacuous if `ρ < 0`). ∎

```lean
theorem summable_rTerm (D : DBData E φ) (α : ℝ) (z : ℂ) :
    Summable fun γ : phaseLevel φ α ↦ rTerm E α γ z := by
  sorry
```

*Proof.* `ρ = ‖z‖`, `M` a bound of `‖S‖` on `closedBall 0 ρ`
(`IsCompact.exists_bound_of_continuousOn`).  Outside the finite set `Γ ∩ [-(2ρ+1), 2ρ+1]`
(`phaseLevel_inter_Icc_finite`), `‖rTerm γ z‖ ≤ 2M(1+ρ)·c_γ/(1+γ²)` (`norm_rTerm_le`), summable
by `summable_cLev_div_one_add_sq`.  `Summable.of_norm_bounded_eventually` (cofinite filter). ∎

```lean
theorem differentiable_rFun (D : DBData E φ) (α : ℝ) : Differentiable ℂ (rFun E φ α) := by
  sorry
```

*Proof.* Fix `ρ > 0`, `U = ball 0 ρ`, `M` as above, `T = {γ : |γ| < 2ρ+1}` finite.  Each
`rTerm γ` is entire (`(Complex.differentiableOn_dslope univ_mem).2 (differentiable_sFun …)`,
times a polynomial) hence bounded on `closedBall 0 ρ` by some `B_γ`.  Put
`u γ = if |γ| < 2ρ+1 then B_γ else 2M(1+ρ)c_γ/(1+γ²)`: summable (differs from a summable
function on a finite set: `Summable.congr_cofinite`/`summable_of_ne_finset_zero` plus `add`).
`differentiableOn_tsum_of_summable_norm hu (fun γ ↦ (entire).differentiableOn) isOpen_ball bounds`
gives `DifferentiableOn ℂ (rFun E φ α) (ball 0 ρ)`.  Every `z` lies in `ball 0 (‖z‖+1)` (open),
so `Differentiable`. ∎

```lean
theorem differentiable_dFun (D : DBData E φ) (α : ℝ) : Differentiable ℂ (dFun E φ α) := by
  sorry
```

*Proof.* `differentiable_cFun D.strict.1.1` and `(differentiable_rFun D α).const_mul _`. ∎

```lean
theorem fstar_dFun (E : ℂ → ℂ) (φ : ℝ → ℝ) (α : ℝ) : fstar (dFun E φ α) = dFun E φ α := by
  sorry
```

*Proof.* `funext z`.  `fstar dFun z = conj C(z̄) + π·conj R(z̄)` (`π` real).  `conj C(z̄) = C z`
(`fstar_cFun`).  `conj R(z̄) = Σ' conj (rTerm γ z̄)` (`Complex.conj_tsum`) and
`conj (rTerm γ z̄) = rTerm γ z`: `c_γ`, `γ` real, and `conj (d_γ z̄) = d_γ z` — for `z ≠ γ`,
`conj((S z̄ - S γ)/(z̄ - γ)) = (S z - S γ)/(z - γ)` (`S^* = S`, `S γ` real); for `z = γ`,
`conj S'(γ) = (S^*)'(γ) = S'(γ)` (`deriv_fstar_ofReal`, `fstar_sFun`). ∎

*Implemented:* without the hypothesis `D : DBData E φ` of the scaffold, which is unused (flagged by the
linter): the identity holds for every `E`, since `C^* = C`, each term satisfies `conj r_γ(z̄) = r_γ(z)`,
and `Complex.conj_tsum` needs no summability.

```lean
theorem dFun_level (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) :
    dFun E φ α γ = 0 := by
  sorry
```

*Proof.* `tsum_eq_single ⟨γ, hγ⟩`: for `γ' ≠ ⟨γ,hγ⟩`, `d_{γ'}(γ) = (S γ - S γ')/(γ - γ') = 0`
(`dslope_of_ne`, both zeros); the remaining term is
`c_γ(1+γ²)/(1+γ²)·S'(γ) = c_γ·(-C(γ)φ'(γ)) = -C(γ)/π` (`dslope_same`, `deriv_sFun_level`,
`field_simp`).  So `D(γ) = C(γ) + π(-C(γ)/π) = 0`. ∎

```lean
theorem exists_hFun (D : DBData E φ) (α : ℝ) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∀ z, dFun E φ α z = h z * sFun E α z) ∧
      ∀ z, h (conj z) = conj (h z) := by
  sorry
```

*Proof.* Define `h z = if S z = 0 then deriv D z / deriv S z else D z / S z`.
* `D = h S`: if `S z = 0` then `z ∈ Γ` (`sFun_eq_zero_iff`) and `D z = 0` (`dFun_level`); else
  `div_mul_cancel₀`.
* Differentiable at `z` with `S z ≠ 0`: `h =ᶠ[𝓝 z] D/S` (`S ≠ 0` near `z` by continuity),
  `DifferentiableAt.div`, `Filter.EventuallyEq.differentiableAt_iff`.
* Differentiable at `z = γ` with `S γ = 0`: `d_γ = dslope S γ` and `δ = dslope D γ` are entire,
  `d_γ γ = S'(γ) = -C(γ)φ'(γ) ≠ 0` (`deriv_sFun_level`, `cFun_level`, `phaseDeriv_pos`), so
  `d_γ ≠ 0` on a neighbourhood `N` of `γ`.  On `N`, `S z = (z - γ)d_γ(z)` vanishes only at `γ`
  (`sub_smul_dslope`), and `h = δ/d_γ` on `N` (for `z ≠ γ`: `D z/S z = (z-γ)δ(z)/((z-γ)d_γ(z))`;
  at `γ`: `deriv D γ/deriv S γ = δ γ/d_γ γ` by `dslope_same`).  `δ/d_γ` is differentiable at `γ`.
* Reality: `S(z̄) = conj S(z)`, `D(z̄) = conj D(z)` (`fstar_sFun`, `fstar_dFun`), the zero set of
  `S` is conjugation invariant, and `deriv D z̄ = conj (deriv D z)` (`deriv_fstar` with
  `fstar D = D`), likewise for `S`; both branches commute with `conj` (`map_div₀`). ∎

### 5.5 The defect kernel

```lean
theorem defect_term_eq (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (w z : ℂ) :
    deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * (wt E γ : ℂ) =
      (cLev E γ : ℂ) * conj (dslope (sFun E α) (γ : ℂ) w) * dslope (sFun E α) (γ : ℂ) z := by
  sorry
```

*Proof.* `K(γ,z) = -(C/π)d_γ(z)` (`kernel_level_eq_dslope`), `K(w,γ) = conj K(γ,w)
= -(C/π)conj d_γ(w)` (`conj_deBrangesKernel`, `C` real).  Product with `wt`:
`(C²/π²)·wt = ‖E γ‖²/π²·π/(φ'‖E γ‖²) = 1/(πφ') = c_γ` (`cFun_level`, `field_simp`). ∎

```lean
theorem summable_defect (D : DBData E φ) (w z : ℂ) :
    Summable (fun γ : phaseLevel φ α ↦
      deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * ((wt E γ : ℝ) : ℂ)) := by
  sorry
```

*Proof.* By `defect_term_eq`, `‖term‖ = c_γ‖d_γ w‖‖d_γ z‖ ≤ (c_γ‖d_γ w‖² + c_γ‖d_γ z‖²)/2`
(`two_mul_le_add_sq`), summable by `summable_cLev_dslope_sq` at `w` and at `z`;
`Summable.of_norm_bounded`. ∎

```lean
theorem term_identity (D : DBData E φ) {γ : ℝ} (hγ : γ ∈ phaseLevel φ α) (w z : ℂ) :
    (z - conj w) * (deBrangesKernel E w γ * deBrangesKernel E (γ : ℂ) z * (wt E γ : ℂ)) =
      sFun E α z * conj (rTerm E α γ w) - conj (sFun E α w) * rTerm E α γ z := by
  sorry
```

*Proof.* Rewrite the left side with `defect_term_eq`; `conj (rTerm γ w) =
c_γ(1 + γ w̄)/(1+γ²)·conj d_γ(w)`.  With `S z = (z - γ)d_γ(z)` and
`conj S w = (w̄ - γ)conj d_γ(w)` (`sub_smul_dslope`, `S γ = 0`), the right side is
`c_γ conj d_γ(w) d_γ(z)/(1+γ²)·[(z-γ)(1+γw̄) - (w̄-γ)(1+γz)]` and the bracket equals
`(z - w̄)(1 + γ²)` (`ring`).  `field_simp` (`1 + γ² ≠ 0`), `ring`. ∎

```lean
theorem defectKer_mul (D : DBData E φ) {h : ℂ → ℂ}
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) (w z : ℂ) :
    defectKer E φ α w z * (Real.pi * (z - conj w)) =
      sFun E α z * conj (sFun E α w) * (h z - conj (h w)) := by
  sorry
```

*Proof.* `Q·π(z - w̄) = K(w,z)π(z - w̄) - π·Σ'(z - w̄)·term_γ` (`tsum_mul_left`).
First part: `C(z)conj S(w) - S(z)conj C(w)` (`kernel_mul_CS`).  Second: by `term_identity`
(valid for every `γ ∈ Γ`, use `γ.2`) and `tsum_sub`, `tsum_mul_left`, `Complex.conj_tsum`
(summability: `summable_rTerm` at `z` and at `w`, `.conj`/`Summable.mapL`):
`Σ' (z - w̄)term = S(z)conj R(w) - conj S(w) R(z)`.  Hence
`Q·π(z-w̄) = conj S(w)(C(z) + πR(z)) - S(z)(conj C(w) + π conj R(w)) = conj S(w)D(z) - S(z)conj D(w)`
and with `D = hS`: `= S(z)conj S(w)(h(z) - conj h(w))` (`ring`). ∎

```lean
theorem defectKer_diag (w : ℂ) :
    (defectKer E φ α w w).re =
      (deBrangesKernel E w w).re - ∑' γ : phaseLevel φ α,
        wt E γ * ‖deBrangesKernel E w γ‖ ^ 2 := by
  sorry
```

*Proof.* `K(γ,w) = conj K(w,γ)`, so each term is `wt·K(w,γ)conj K(w,γ) = ↑(wt‖K(w,γ)‖²)`
(`Complex.mul_conj`); `Complex.ofReal_tsum`, `Complex.re_tsum` / `Complex.ofReal_re`
(summability by `summable_defect`). ∎

*Implemented:* without `D` (unused): `Complex.ofReal_tsum` casts the `tsum` of the real terms
`wt|K(w,γ)|²` without any summability, so `Complex.re_tsum` is not needed; `K(γ,w) = conj K(w,γ)` by
`deBrangesKernel_conj_symm`.

```lean
theorem defectKer_diag_nonneg (D : DBData E φ) (w : ℂ) : 0 ≤ (defectKer E φ α w w).re := by
  sorry
```

*Proof.* `defectKer_diag` and `bessel` for `K_w`: `Σ wt|K_w(γ)|² ≤ ‖K_w‖² = K(w,w).re`
(`heNormSq_kernel`). ∎

```lean
theorem im_hFun_nonneg (D : DBData E φ) {h : ℂ → ℂ}
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) {w : ℂ} (hw : 0 < w.im) : 0 ≤ (h w).im := by
  sorry
```

*Proof.* `defectKer_mul` at `z = w`: `Q(w,w)·π(w - w̄) = ‖S w‖²·(h w - conj h w)`, i.e.
`Q(w,w)·2πi Im w = ‖S w‖²·2i Im h(w)`.  `Q(w,w)` is real (`deBrangesKernel_diag` and
`defectKer_diag`'s computation), so `Im h(w) = π Im w·Q(w,w)/‖S w‖² ≥ 0`
(`defectKer_diag_nonneg`, `sFun_ne_zero`). ∎

*Implemented* (R9 F2): imaginary parts of `defectKer_mul D hh w w` give
`2π Im w·Re Q(w,w) = 2‖S w‖²·Im h(w)`, so only `Re Q(w,w) ≥ 0` (`defectKer_diag_nonneg`) is used, not
the reality of `Q(w,w)`; `nlinarith` concludes.

---------------------------------------------------------------------------------------------------

## 6. `EntireHerglotz.lean` — an entire Pick function is linear

This file imports only `Defs` (for Mathlib) and uses no project lemma.  Mathlib conventions: `poissonKernel c w z =
(‖z - c‖² - ‖w - c‖²)/‖(z - c) - (w - c)‖²` (`Mathlib/Analysis/Complex/Poisson.lean`), and
`InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul :
HarmonicOnNhd f (closedBall c R) → w ∈ ball c R → Real.circleAverage (poissonKernel c w • f) c R = f w`
(`Mathlib/Analysis/Complex/Harmonic/Poisson.lean`).

```lean
theorem entire_im_harmonicOnNhd {h : ℂ → ℂ} (hd : Differentiable ℂ h) (c : ℂ) (R : ℝ) :
    InnerProductSpace.HarmonicOnNhd (fun z ↦ (h z).im) (closedBall c R) := by
  sorry
```

*Proof.* `fun z _ ↦ (hd.analyticAt z).harmonicAt_im` (`Differentiable.analyticAt`,
`AnalyticAt.harmonicAt_im`). ∎

```lean
theorem two_mul_im_eq_circleAverage {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ z, h (conj z) = conj (h z)) {R : ℝ} {w : ℂ} (hw : ‖w‖ < R) :
    2 * (h w).im = Real.circleAverage
      (fun ζ ↦ (poissonKernel 0 w ζ - poissonKernel 0 (conj w) ζ) * (h ζ).im) 0 R := by
  sorry
```

*Proof.* `v = Im h` is harmonic near `closedBall 0 R` (previous lemma).  Poisson formula at `w`
and at `w̄` (`‖w̄‖ = ‖w‖ < R`): `⨍ P_w v = v(w)`, `⨍ P_{w̄} v = v(w̄) = -v(w)`
(`hreal`: `h(w̄) = conj h(w)`, `Complex.conj_im`).  Subtract (`Real.circleAverage_sub`;
circle integrability from continuity on the sphere, `ContinuousOn.circleIntegrable`, the kernels
being continuous on `|ζ| = R > |w|`): `⨍ (P_w - P_{w̄})v = 2v(w)`. ∎

```lean
theorem poissonKernel_sub_conj {R : ℝ} {w ζ : ℂ} (hζ : ‖ζ‖ = R) (hwR : ‖w‖ < R) :
    poissonKernel 0 w ζ - poissonKernel 0 (conj w) ζ =
      4 * (R ^ 2 - ‖w‖ ^ 2) * w.im * ζ.im / (‖ζ - w‖ ^ 2 * ‖ζ - conj w‖ ^ 2) := by
  sorry
```

*Proof.* Unfold `poissonKernel` (`c = 0`): `(R² - ‖w‖²)(‖ζ - w‖⁻² - ‖ζ - w̄‖⁻²)` (`‖w̄‖ = ‖w‖`,
`‖ζ‖ = R`), and `‖ζ - w̄‖² - ‖ζ - w‖² = 4 Im ζ Im w` (expand with `Complex.sq_norm`,
`Complex.normSq_apply`; `ring`).  `field_simp` (`ζ ≠ w`, `ζ ≠ w̄` since `‖ζ‖ = R > ‖w‖`). ∎

```lean
theorem im_mul_im_nonneg {h : ℂ → ℂ} (hreal : ∀ z, h (conj z) = conj (h z))
    (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im) (ζ : ℂ) : 0 ≤ ζ.im * (h ζ).im := by
  sorry
```

*Proof.* `Im ζ > 0`: `hpos`.  `Im ζ < 0`: `Im h(ζ) = Im conj h(ζ̄) = -Im h(ζ̄) ≤ 0`.
`Im ζ = 0`: `0`.  `mul_nonneg`/`mul_nonneg_of_nonpos_of_nonpos`. ∎

```lean
theorem kernel_ratio_le {R r : ℝ} {w w' ζ : ℂ} (hr : 0 < r) (hrR : r < R) (hw : ‖w‖ ≤ r)
    (hw' : ‖w'‖ ≤ r) (hζ : ‖ζ‖ = R) :
    (R ^ 2 - ‖w‖ ^ 2) / (‖ζ - w‖ ^ 2 * ‖ζ - conj w‖ ^ 2) ≤
      ((R + r) ^ 4 / ((R - r) ^ 4 * (1 - r ^ 2 / R ^ 2))) *
        ((R ^ 2 - ‖w'‖ ^ 2) / (‖ζ - w'‖ ^ 2 * ‖ζ - conj w'‖ ^ 2)) := by
  sorry
```

*Proof.* On `‖ζ‖ = R` with `‖w‖, ‖w'‖ ≤ r < R`: `R² - ‖w‖² ≤ R²`;
`‖ζ - w‖, ‖ζ - w̄‖ ≥ R - r`; `R² - ‖w'‖² ≥ R²(1 - r²/R²) > 0`; `‖ζ - w'‖, ‖ζ - w̄'‖ ≤ R + r`.
Hence `k_w(ζ) ≤ R²/(R - r)⁴` and `k_{w'}(ζ) ≥ R²(1 - r²/R²)/(R + r)⁴`, so
`k_w ≤ R²/(R-r)⁴ = κ·R²(1 - r²/R²)/(R+r)⁴ ≤ κ·k_{w'}` (`div_le_div`, `pow_le_pow_left`,
`norm_sub_norm_le`, `norm_sub_le`). ∎

```lean
theorem im_div_im_eq {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ z, h (conj z) = conj (h z)) (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im)
    {w w' : ℂ} (hw : w.im ≠ 0) (hw' : w'.im ≠ 0) :
    (h w).im / w.im = (h w').im / w'.im := by
  sorry
```

*Proof.* Let `m(ζ) = Im ζ·v(ζ) ≥ 0` (`im_mul_im_nonneg`), `k_w` as above.  By
`two_mul_im_eq_circleAverage` and `poissonKernel_sub_conj` (pointwise on the sphere,
`Real.circleAverage_congr_sphere`), for `R > ‖w‖`:
`v(w)/Im w = 2·⨍ k_w m` (`Real.circleAverage_smul`/const mul).  Fix `r = max ‖w‖ ‖w'‖ + 1`; for
`R > r`, `kernel_ratio_le` and `Real.circleAverage_mono` give
`v(w)/Im w ≤ κ(r,R)·v(w')/Im w'` (note `v(w')/Im w' ≥ 0`).  `κ(r,R) → 1` as `R → ∞`
(`Tendsto` of a rational function; `(R+r)/(R-r) → 1`, `r²/R² → 0`), so `le_of_tendsto` gives
`v(w)/Im w ≤ v(w')/Im w'`; by symmetry equality. ∎

```lean
theorem entire_im_eq_zero_const {g : ℂ → ℂ} (hd : Differentiable ℂ g) (him : ∀ z, (g z).im = 0) :
    ∀ z, g z = g 0 := by
  sorry
```

*Proof.* Open mapping: `g` is analytic on `univ` (`Differentiable.analyticAt`); by
`AnalyticOnNhd.is_constant_or_isOpen` (`univ` preconnected) either `g` is constant or
`g '' univ` is open; but `g '' univ ⊆ {Im = 0}`, which has empty interior.  (Alternative:
`exp(I g)` has norm `1`, Liouville `Differentiable.apply_eq_apply_of_bounded`, then
`deriv`.) ∎

```lean
theorem entire_pick_linear {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ z, h (conj z) = conj (h z)) (hpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im) :
    ∃ p q : ℝ, 0 ≤ p ∧ ∀ z, h z = p * z + q := by
  sorry
```

*Proof.* `p := Im h(i) ≥ 0`.  For nonreal `z`, `Im h(z) = p Im z` (`im_div_im_eq` with `w' = I`);
for real `z`, `Im h(z) = 0` (`hreal`: `h z = conj (h z)`).  So `g z = h z - p z` has `Im g = 0`
everywhere, hence `g z = g 0` (`entire_im_eq_zero_const`) and `q := (g 0).re`, `g 0 = ↑q`. ∎

---------------------------------------------------------------------------------------------------

## 7. `Complete.lean` — completeness of the system and Theorem E

### 7.1 Exhaustion and series limits

```lean
theorem exists_exhaustion (D : DBData E φ) (α : ℝ) :
    ∃ F : ℕ → Finset (phaseLevel φ α), Monotone F ∧ ∀ γ : phaseLevel φ α, ∃ n, γ ∈ F n := by
  sorry
```

*Proof.* `F n = Set.Finite.toFinset` of `{γ : Γ | (γ : ℝ) ∈ Icc (-n) n}`, finite as the preimage
of `Γ ∩ [-n,n]` (`phaseLevel_inter_Icc_finite`) under the injective `Subtype.val`.  Monotone since
the intervals grow; `γ ∈ F ⌈|γ|⌉₊` (`Nat.le_ceil`). ∎

```lean
theorem cauchy_partialSum (D : DBData E φ) {a : ℝ → ℂ}
    (ha : Summable fun γ : phaseLevel φ α ↦ wt E γ * ‖a γ‖ ^ 2)
    {F : ℕ → Finset (phaseLevel φ α)} (hF : Monotone F) (hex : ∀ γ, ∃ n, γ ∈ F n) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      heNormSq E (fun z ↦ partialSum E φ α a (F m) z - partialSum E φ α a (F n) z) ≤
        ENNReal.ofReal ε := by
  sorry
```

*Proof.* Let `σ(n) = Σ'_{γ ∉ F n} wt|a|²`.  By `ha.hasSum` composed with
`Filter.tendsto_atTop_finset_of_monotone hF hex`, `Σ_{F n} wt|a|² → Σ' wt|a|²`, and
`σ(n) = Σ' - Σ_{F n}` (`sum_add_tsum_compl`), so `σ(n) → 0`.  For `m ≥ n`:
`s_{F m} - s_{F n} = partialSum a (F m \ F n)` (`Finset.sum_sdiff`), whose squared norm is
`Σ_{F m \ F n} wt|a|² ≤ σ(n)` (`heNormSq_partialSum`; `sum_le_tsum` on the complement, nonneg).
For `m < n` the same with `‖-x‖ = ‖x‖` (`heNormSq` of a negation: `norm_neg` under
`lintegral_congr`).  Choose `N` with `σ(N) ≤ ε` (monotone decreasing in `n`). ∎

```lean
theorem exists_series_limit (D : DBData E φ) {a : ℝ → ℂ}
    (ha : Summable fun γ : phaseLevel φ α ↦ wt E γ * ‖a γ‖ ^ 2) :
    ∃ g : ℂ → ℂ, MemHE E g ∧
      (∀ z : ℂ, HasSum (fun γ : phaseLevel φ α ↦
        a γ * ((wt E γ : ℝ) : ℂ) * deBrangesKernel E (γ : ℂ) z) (g z)) ∧
      (∀ γ ∈ phaseLevel φ α, g γ = a γ) ∧
      (heNormSq E g).toReal = ∑' γ : phaseLevel φ α, wt E γ * ‖a γ‖ ^ 2 ∧
      ∀ f : ℂ → ℂ, MemHE E f →
        HasSum (fun γ : phaseLevel φ α ↦ conj (a γ) * (wt E γ : ℂ) * f γ) (heInner E f g) := by
  sorry
```

*Proof.* Exhaustion `F` (`exists_exhaustion`), `sₙ = partialSum a (F n)`.  `cauchy_partialSum` and
`memHE_of_cauchy` give `g ∈ H(E)`, `sₙ(z) → g(z)` for all `z`, `‖sₙ - g‖² → 0`.
* *HasSum at `z`*: `‖a_γ wt_γ K(γ,z)‖ ≤ (wt|a_γ|² + wt‖K(γ,z)‖²)/2` and
  `wt‖K(γ,z)‖² = c_γ‖d_γ z‖²` summable (`summable_cLev_dslope_sq`): the family is summable
  (`Summable.of_norm_bounded`); its sum is the limit along the exhaustion
  (`HasSum.comp (tendsto_atTop_finset_of_monotone …)`), i.e. `lim sₙ(z) = g z`
  (`tendsto_nhds_unique`).
* `g(γ) = a(γ)`: `sₙ(γ) = a(γ)` for `n` large (`partialSum_level`).
* `‖g‖² = Σ' wt|a|²`: `↑‖g‖² = ⟨g,g⟩ = lim ⟨g, sₙ⟩` (`tendsto_heInner_right`) and
  `⟨g, sₙ⟩ = Σ_{F n} conj(a_γ)wt_γ g(γ) = ↑Σ_{F n} wt|a_γ|²` (`heInner_partialSum`, `g(γ) = a_γ`),
  which tends to `↑Σ' wt|a|²`.
* `⟨f, g⟩`: `⟨f, sₙ⟩ = Σ_{F n} conj(a_γ)wt f(γ)` (`heInner_partialSum`) `→ ⟨f, g⟩`
  (`tendsto_heInner_right`); the family is absolutely summable (`(wt|a|² + wt|f|²)/2`, `bessel`),
  so its sum equals this limit: `HasSum`. ∎

### 7.2 The defect kernel in `H(E)`; `p = 0`

```lean
theorem memHE_defectKer (D : DBData E φ) (w : ℂ) :
    MemHE E (fun z ↦ defectKer E φ α w z) ∧
      (heNormSq E (fun z ↦ defectKer E φ α w z)).toReal = (defectKer E φ α w w).re := by
  sorry
```

*Proof.* `a = fun t ↦ K(w, t)`: `Σ wt|a|² < ∞` (`bessel` for `K_w`).  `exists_series_limit` gives
`g_w ∈ H(E)` with `g_w(z) = Σ' K(w,γ)wt(γ)K(γ,z)` (HasSum, `.tsum_eq`; reorder factors), so
`Q_w = K_w - g_w` pointwise (`funext`) and `MemHE.sub`.  Norm: `heNormSq_sub`:
`‖Q_w‖² = ‖K_w‖² + ‖g_w‖² - 2Re⟨K_w, g_w⟩` with `‖K_w‖² = K(w,w).re` (`heNormSq_kernel`),
`‖g_w‖² = Σ' wt|K(w,γ)|²`, and `⟨K_w, g_w⟩ = Σ' conj K(w,γ)·wt·K(w,γ) = ↑Σ' wt|K(w,γ)|²`
(HasSum part with `f = K_w`, `K_w(γ) = K(w,γ)`).  So `‖Q_w‖² = K(w,w).re - Σ' wt|K(w,γ)|² =
Q(w,w).re` (`defectKer_diag`). ∎

*Implemented:* the decomposition `Q_w = K_w - g_w` is the helper `exists_defect_decomp`, shared with
`heInner_defectKer_of_level_zero`; the summability of the cross terms is `summable_mul_wt_mul` (AM–GM).

```lean
theorem heInner_defectKer_of_level_zero (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f)
    (hz : ∀ γ ∈ phaseLevel φ α, f γ = 0) (w : ℂ) :
    heInner E f (fun z ↦ defectKer E φ α w z) = f w := by
  sorry
```

*Proof.* `⟨f, Q_w⟩ = ⟨f, K_w⟩ - ⟨f, g_w⟩` (conjugate of `heInner_sub_left`) `= f(w) - Σ'
conj K(w,γ)·wt·f(γ) = f(w) - 0` (`heInner_kernel`; HasSum of `exists_series_limit` with all terms
`0` by `hz`, `hasSum_zero`, uniqueness `HasSum.unique`). ∎

```lean
theorem hFun_linear (D : DBData E φ) {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) (hreal : ∀ z, h (conj z) = conj (h z)) :
    ∃ p q : ℝ, 0 ≤ p ∧ ∀ z, h z = p * z + q := by
  sorry
```

*Proof.* `entire_pick_linear hd hreal (fun z hz ↦ im_hFun_nonneg D hh hz)`. ∎

```lean
theorem defectKer_eq_of_linear (D : DBData E φ) {h : ℂ → ℂ}
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) {p q : ℝ} (hlin : ∀ z, h z = p * z + q)
    {w z : ℂ} (hz : z ≠ conj w) :
    defectKer E φ α w z = (p / Real.pi : ℝ) * sFun E α z * conj (sFun E α w) := by
  sorry
```

*Proof.* `defectKer_mul D hh w z`: `Q·π(z - w̄) = S(z)conj S(w)(pz + q - p w̄ - q) =
p S(z)conj S(w)(z - w̄)` (`hlin`, `conj (↑p * w + ↑q) = ↑p * conj w + ↑q`); cancel
`π(z - w̄) ≠ 0`. ∎

```lean
theorem memHE_sFun_of_pos (D : DBData E φ) {h : ℂ → ℂ}
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) {p q : ℝ} (hp : 0 < p)
    (hlin : ∀ z, h z = p * z + q) : MemHE E (sFun E α) := by
  sorry
```

*Proof.* `Q_i ∈ H(E)` (`memHE_defectKer D I`).  For `z ≠ -i = conj I`,
`Q(i,z) = κ·S(z)` with `κ = (p/π)conj S(i) ≠ 0` (`defectKer_eq_of_linear`, `sFun_ne_zero`,
`p > 0`).  Both `z ↦ Q(i,z)` (entire, as an element of `H(E)`) and `κ S` are continuous and agree on
the dense set `{-i}ᶜ` (`dense_compl_singleton`, `Continuous.ext_on`), so `Q_i = κ S` and
`S = κ⁻¹ Q_i ∈ H(E)` (`MemHE.const_mul`, `funext`). ∎

### 7.3 The key proposition and Theorem E

```lean
theorem eq_zero_of_level_zero (D : DBData E φ)
    (hα : ¬ MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z))
    {f : ℂ → ℂ} (hf : MemHE E f) (hz : ∀ γ ∈ phaseLevel φ α, f γ = 0) : ∀ z, f z = 0 := by
  sorry
```

*Proof.* `exists_hFun` gives `h`; `hFun_linear` gives `p ≥ 0`, `q`.  If `p > 0`,
`memHE_sFun_of_pos` gives `S ∈ H(E)`, hence `S_α = 2iS ∈ H(E)` (`sAlpha_eq`,
`MemHE.const_mul`), contradicting `hα`.  So `p = 0`.  For nonreal `w`:
`Q(w,w) = (0/π)·… = 0` (`defectKer_eq_of_linear` with `z = w ≠ w̄`), so `‖Q_w‖² = 0`
(`memHE_defectKer`) and `|f(w)|² = |⟨f, Q_w⟩|² ≤ ‖f‖²·‖Q_w‖² = 0`
(`heInner_defectKer_of_level_zero`, `norm_heInner_sq_le`).  For real `x`:
`f(x) = lim f(x + i/n) = 0` (continuity of `f`). ∎

```lean
theorem heNormSq_eq_tsum (D : DBData E φ)
    (hα : ¬ MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z))
    {f : ℂ → ℂ} (hf : MemHE E f) :
    Summable (fun γ : phaseLevel φ α ↦ wt E γ * ‖f γ‖ ^ 2) ∧
      (heNormSq E f).toReal = ∑' γ : phaseLevel φ α, wt E γ * ‖f γ‖ ^ 2 := by
  sorry
```

*Proof.* `bessel D hf` gives summability.  `exists_series_limit` with `a = fun t ↦ f t` gives
`g ∈ H(E)`, `g(γ) = f(γ)` on `Γ`, `‖g‖² = Σ' wt|f(γ)|²`.  `f - g ∈ H(E)` vanishes on `Γ`, so
`f = g` (`eq_zero_of_level_zero`, `funext`, `sub_eq_zero`), and `‖f‖² = ‖g‖²`. ∎

```lean
theorem theoremE_norm (D : DBData E φ)
    (hα : ¬ MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z))
    {f : ℂ → ℂ} (hf : MemHE E f) :
    heNormSq E f = ∑' γ : phaseLevel φ α, orthWeight E γ * ‖f γ‖ₑ ^ 2 := by
  sorry
```

*Proof.* `heNormSq E f = ofReal ((heNormSq E f).toReal)` (`ENNReal.ofReal_toReal`,
`MemHE.heNormSq_lt_top`) `= ofReal (Σ' wt|f(γ)|²)` (`heNormSq_eq_tsum`)
`= Σ' ofReal (wt|f(γ)|²)` (`ENNReal.ofReal_tsum_of_nonneg`)
`= Σ' orthWeight E γ * ‖f γ‖ₑ²` (`orthWeight_eq`, `ENNReal.ofReal_mul (wt_pos ..).le`,
`enorm_sq_eq_ofReal`). ∎

```lean
theorem theoremE_interp (D : DBData E φ) (a : ℝ → ℂ)
    (ha : ∑' γ : phaseLevel φ α, orthWeight E γ * ‖a γ‖ₑ ^ 2 < ∞) :
    ∃ f : ℂ → ℂ, MemHE E f ∧ ∀ γ ∈ phaseLevel φ α, f γ = a γ := by
  sorry
```

*Proof.* As in `theoremE_norm`, the `ℝ≥0∞` sum is `Σ' ofReal (wt|a γ|²)`; it is `≠ ∞`, so
`ENNReal.summable_toReal` and `ENNReal.toReal_ofReal` (nonneg) give
`Summable (wt|a|²)`.  `exists_series_limit` provides `f ∈ H(E)` with `f(γ) = a(γ)` on `Γ`. ∎

---------------------------------------------------------------------------------------------------

## 8. Assembly (`DeBrangesDE.lean`) — complete

```lean
theorem theoremD_holds : TheoremD := by

theorem theoremE_holds : TheoremE := by
```

(`TheoremD`'s integral is definitionally `heInner E f (deBrangesKernel E w)`; `hE.1 : IsHB E`.)

*Implemented* as planned: `theoremD_holds` is `memHE_deBrangesKernel` and `heInner_kernel`;
`theoremE_holds` builds `DBData` and applies `theoremE_norm` and `theoremE_interp`. At assembly (R9 F4)
`FourierFrames.lean` imports `Cited.DeBrangesDE`. The temporary stub `theoremD_holds` (`sorry`) in
`Cited/DeBrangesFC.lean` is still there; that file is now outside the default target (Lake target
`FourierFramesScaffold`), so the two declarations never meet, and P4 is to replace the stub by
`import FourierFrames.Cited.DeBrangesDE`.

---------------------------------------------------------------------------------------------------

## 9. Coordination with P4 (Theorem C)

P4's C.9/C.11 need exactly the `H²` Cauchy machinery of §1 and the kernel algebra of §2, for
`E ∈ \overline{HB}` that **may have real zeros**.  What is reusable as is:
* everything in `Cauchy.lean` (stated for an arbitrary `F ∈ IsH2Cont`);
* the kernel algebra of §2 (`deBrangesKernel_eq_dslope`, `differentiable_deBrangesKernel`,
  `deBrangesKernel_mul`, `conj_deBrangesKernel`, `fstar_deBrangesKernel`, `deBrangesKernel_diag`,
  `kernel_div_E`, `exists_bound_deBrangesKernel`) — only `Differentiable ℂ E` is assumed;
* `heInner`, `heInner_eq_integral_div` (P4 writes the pairing as `∫ (f/E) conj (g/E)`; these are
  equal for every `E`);
* `isH2Upper_kernel_div` and `memHE_deBrangesKernel_of_isHB` (`IsHB E`, `w` nonreal: no real-zero
  assumption) — this is P4's "membership `K(w,·) ∈ H(E)`" in C.9;
* `heInner_kernel_upper_of_isH2Cont` (reproducing formula at `w ∈ ℂ₊` with `IsH2Cont` replacements
  `A`, `B` of `f/E`, `f^*/E`, equal on `ℂ₊` and a.e. on `ℝ`): this is C.11; C.9 is its instance
  `f = K_v`.  When `E` has real zeros, P4 must supply the continuous extensions `A`, `B` (the Lean
  quotient `f/E` is `0` at a real zero of `E`, not its limit), e.g. via `dslope`-type removable
  singularity arguments, and show `IsH2Cont` for them.
* `theoremD_holds` itself (P4-F): import `FourierFrames.Cited.DeBrangesDE` and delete P4's
  placeholder in its "Upstream interface" section (still pending, see §8); there is no import cycle
  (P3 imports only `Defs`, `HB/*` and, through `HB.Comparable`, `PW/*`; R9 §5).
* *Implemented:* the decomposition `heInner_kernel_eq_of_ae` (§3) is the reusable core of C.11: it
  assumes only `E ≠ 0` a.e. on `ℝ` and `IsH2Cont` functions `A`, `B` equal a.e. to `f/E`, `f^*/E`. The
  two lemmas P4 still needs for `E` with real zeros are listed in R9 F5 (an order version of
  `not_isH2Upper_div_of_zero`, and `IsH2Cont` extensions of `f/E`, `f^*/E` across the real zeros).
  `conj_deBrangesKernel` and `fstar_deBrangesKernel` no longer take `hE`.
* Name clashes: none with `DeBrangesFC.lean` (`UHP`, `thetaFn`, `DBAxioms`, `herglotzG`, … are not
  defined here).

---------------------------------------------------------------------------------------------------

## Issues in the source

Recorded in `NOTEBOOK.md`: items 1, 2, 4 as N-43, N-44, N-45; item 3 is covered by N-02, N-28, N-37;
items 5 and 6 concern the proofs and the formal statement, and are in I-10 and N-02.

1. **Typo, p. 793 (tex l. 307–309).**  "`\|f\|_E^2= \int_{-\infty}^\infty \frac{|f(t)|^2}{|E(t)|^2}\, dx`":
   the integration variable is `t`, so `dx` should be `dt`.  Harmless.  Confidence: certain.
2. **Indexing of `Γ` in Theorem E, p. 794 (tex l. 359–361).**  "let `Γ={γ_k}` be the sequence of
   real numbers such that `φ(γ_k)=α+kπ`, `k∈ℤ`" presupposes that `φ` maps `ℝ` onto `ℝ`.  In
   general the range of a phase function is an open interval of any length (e.g. `E(z) = z + i`:
   `φ(x) = -arg(x+i) ∈ (-π, 0)`), and `Γ` can be finite, one-sided, or empty.  Fix (already in
   `Defs`): `Γ = {x : φ(x) ∈ α + πℤ}` (`phaseLevel`) and sums over the set `Γ`.  For the paper's
   application (`H(E) = PW`) `φ` is onto, so nothing is affected.  Confidence: high.
3. **Implicit hypotheses of Theorem E.**  "Let `H(E)` be a de Branges space and `φ` a phase
   function": the formula needs `φ'(γ) > 0` and `E(γ) ≠ 0`, i.e. `E` strict without real zeros
   (if `E^* = cE` then `H(E) = {0}`, `φ' ≡ 0`, and the weights are `π/0`).  `TheoremE` assumes
   `IsStrictHB E` and `∀ x, E x ≠ 0`; the paper only applies E when `H(E) = PW`, where both hold
   (`HEEqPW.isStrictHB`, `HEEqPW.ne_zero_ofReal`).  Confidence: high; no impact.
4. **Formula (1) at `z = ζ̄`.**  "The kernel has the following representation, which also defines
   it for real `ζ`": formula (1) is `0/0` at `z = ζ̄` for every `ζ` (real or not); the value there
   is the limit (`deBrangesKernel` uses the derivative form, proved equal to the `dslope` in
   `deBrangesKernel_eq_dslope`).  Harmless.  Confidence: certain.
5. **Simplification of the proof of Theorem E** (de Branges' Thm 22).  de Branges' proof uses
   his Theorems 20–21 and functions of bounded type (not reproduced here; the book is not in
   `literature/`, so this description is unchecked, R9 F6).  The argument formalized here is
   elementary: the reproducing kernel `Q` of the orthogonal complement
   of `{K_γ}` satisfies `Q(w,z)π(z - w̄) = S(z)conj S(w)(h(z) - conj h(w))` with `h = D/S` entire,
   real, `Im h ≥ 0` on `ℂ₊` (Mittag-Leffler series built from Bessel's inequality); hence
   `h = pz + q` and `Q = (p/π)S ⊗ conj S`, which is `0` iff `S_α ∉ H(E)`.  As a by-product one also
   gets the second alternative of de Branges' theorem (if `S_α ∈ H(E)`, the orthogonal complement
   is `ℂ·S_α`).  Checked by hand on `E = e^{-iπz}` (`α = 0, π/2`) and `E = z + i`.  Confidence:
   high.
6. **`TheoremD` is stated more narrowly than needed.**  The paper's statement for all
   `E ∈ \overline{HB}` is true. The Lean proof uses no strictness, but it covers real zeros of `E` only
   partly: `memHE_deBrangesKernel_of_isHB` gives `K_w ∈ H(E)` for nonreal `w`, and
   `heInner_kernel_upper_of_isH2Cont` gives the reproducing formula given `IsH2Cont` extensions of
   `f/E`, `f^*/E` (R9 F5). No change requested (the frozen `Prop` is what the paper uses).

## Requested changes to M00

None.  `TheoremD` and `TheoremE` are true as stated and are proved by the plan above.

## Risks (details)
* **R1 (Cauchy.lean plumbing).**  Tonelli on strips with a function that is only continuous on the
  closed half-plane (use the `piecewise` trick of `HB/H2.enorm_sq_le_of_lines`), conversions
  between interval integrals, Bochner integrals and lintegrals, a.e. equalities off one point.
  Moderate; the project already contains similar code (`HB/MeanValue`, `HB/H2`, `HB/Comparable`).
* **R2 (`tsum` over `Γ` in `ℂ`).**  Every rearrangement (`tsum_sub`, `tsum_mul_left`,
  `Complex.conj_tsum`, `re_tsum`) needs summability; the plan supplies `summable_rTerm`,
  `summable_defect`, `summable_cLev_dslope_sq`.  Moderate.
* **R3 (`exists_hFun`).**  Removable singularities by hand (`dslope` quotient); low.
* **R4 (Lemma L).**  Relies on Mathlib's disc Poisson formula for harmonic functions
  (`HarmonicOnNhd.circleAverage_poissonKernel_smul`, present in the pinned Mathlib) and
  `Real.circleAverage_mono`; low–moderate.
* **R5 (completeness).**  Uniform Cauchy on balls + Fatou on lines; moderate.
