# M02 — Hermite–Biehler class, phase functions, de Branges spaces, the "evident fact" of p. 799

**Lean files** (all in namespace `FF`):
`FourierFrames/HB/H2.lean` (Hardy-space toolkit), `FourierFrames/HB/Basic.lean` (`f^*`, `\overline{HB}`),
`FourierFrames/HB/Phase.lean` (phase functions), `FourierFrames/HB/DeBranges.lean` (`H(E)`),
`FourierFrames/HB/Comparable.lean` (main statement `heEqPW_of_comparable`); helper files
`HB/Hopf.lean` (`hopf_trig`, `hopf_boundary`: Hopf-type boundary lemma for `φ' > 0`) and
`HB/MeanValue.lean` (`circle_lintegral_ge`, `area_ge`, `lintegral_strip`). Imports: `Basic ← Defs`;
`Phase ← Basic, Hopf`; `H2 ← Defs, MeanValue`; `DeBranges ← Phase, H2, PW.Complete`;
`Comparable ← DeBranges, MeanValue`.

**Status (final).** All proved, no `sorry`. Lean blocks show the statements; where the implemented
route differs from the text it is marked *Implemented:* (source: `impl_notes/hb.md`). The module
docstrings of the code cite the sections of an earlier numbering: `HB/DeBranges.lean` says "§6–§8"
(it holds §7–§10), `HB/Comparable.lean` says "§9" (it is §11), `HB/Phase.lean` says "§4–§5" (it
also holds §6).

**Paper pages:** §2 (pp. 793–794: `\overline{HB}`, `H(E)`, phase, Theorems C–F), used in §3 (pp. 795–796) and §4 (p. 799).

**Depends on.** M00 (`Defs.lean`: `fstar`, `IsH2Upper`, `IsHB`, `IsStrictHB`, `MemHE`, `heNormSq`, `HEEqPW`,
`IsPhaseFunction`, `phaseDeriv`, `phaseLevel`, `orthWeight`, `TheoremE`, `PaleyWienerThm`). M01 (names as in the
README interface list; imported, see `IMPORTS.md`):
`exists_memPW_eval_ne_zero`, `MemPW.comp_sub_ofReal`, `pwNormSq_comp_sub_ofReal`, `MemPW.fstar`,
`pwNormSq_ne_top`, `pw_norm_sq_le`, `pw_line_integral_le`, `pw_eval_lower`.

**Used by.** M03 (`IsHB.mul`, `exists_isPhaseFunction`, `phaseDeriv_*`, `MemHE.mul_isHB`, `heNormSq_mul`,
`zero_set_eq_phaseLevel`, `HEEqPW.*`, the `H2` toolkit), M04, M05, M06, M07 (`IsHB.of_tendstoLocallyUniformly`,
`heEqPW_of_comparable`, phase lemmas).

## 0. Overview and differences from the README interface list

All README names are provided with the same names. Differences in form (all are strengthenings or
repairs; nothing is dropped):

| README | here |
|---|---|
| `IsHB.of_tendstoLocallyUniformly` | general filter `p` (`[p.NeBot]`), hypothesis `∃ z, E₀ z ≠ 0` (limit `≢ 0`). |
| `exists_isPhaseFunction` | `E` differentiable, no real zeros; conclusion `IsPhaseFunction E φ ∧ ∀ x, HasDerivAt φ (phaseDeriv E x) x`. Uniqueness: `IsPhaseFunction.exists_int_eq_add`; every phase function has derivative `phaseDeriv`: `IsPhaseFunction.hasDerivAt`. |
| `IsStrictHB.phaseDeriv_pos` | also the stronger `IsHB.phaseDeriv_pos_of_exists_lt` (strict at *one* point suffices) and `IsHB.isStrictHB_or_fstar_eq` (dichotomy), `IsPhaseFunction.strictMono_of_isStrictHB`. |
| `MemHE.mul_isHB` | no hypothesis `IsHB E` needed (only `IsHB F`). |
| `HEEqPW.isStrictHB`, `.ne_zero_ofReal` | extra hypothesis `IsHB E` (necessary: `H(E)` makes no sense otherwise, and the proofs use `E ≠ 0` on `ℂ₊`). No `hPW` needed. |
| `HEEqPW.phaseDeriv_mul_sq_ge/_le` | `∃ c > 0, ∀ x, c ≤ phaseDeriv E x * ‖E x‖^2` and `∃ C, ∀ x, … ≤ C`; hypotheses `hE : TheoremE`, `IsHB E`, `HEEqPW E`, and `hPW` for `_le` only (`_ge` does not use it, NOTEBOOK I-03). |
| `memHE_sAlpha_unique` | needs only `IsHB E` (strictness not needed); `sAlpha E α` is a new `def` (the function of Theorem E). |
| `zero_set_eq_phaseLevel` | `z ∈ Complex.ofReal '' phaseLevel (fun t ↦ φE t + φF t) (π/2)`. |
| — | New: `H2.lean` (Hardy toolkit: closure properties, area mean-value inequality, pointwise `H²` bound, Liouville for `L²` on lines, blow-up at a real zero). M03/M04 may use these freely. |
| — | Added at assembly: `IsStrictHB.mul_isHB`, `IsHB.rotate` (`HB/Basic.lean`), `IsPhaseFunction.rotate` (`HB/Phase.lean`), `HEEqPW.exists_phase_data` (the data of §10 for one phase function, `HB/DeBranges.lean`), `countable_real_zeros` (`HB/DeBranges.lean`). |

Where Mathlib lacks theory we prove it from scratch (as demanded): the three analytic facts about `H²` that are
used — (A) closure properties; (B) pointwise bounds `|g(z)|² ≲ ‖g‖²/Im z` (§1.3–1.4); (C) no nonzero entire function
is `L²` on all horizontal lines `y ≠ 0` uniformly, and no `f/E` with `f(x₀)≠0=E(x₀)` is in `H²` (§1.5–1.6) —
and **no boundary values / Fourier support of `H²` functions are ever used.** The only place where the real axis
meets `H²` is the Fatou step in §9.

Notation: `ℂ₊ = {Im z > 0}`; `L(g, y) = ∫⁻ x, ‖g(x + i y)‖ₑ²` (line integral).

---

## 1. `H2.lean` — Hardy space toolkit

### 1.1 Closure properties
```lean
theorem IsH2Upper.congr {g h : ℂ → ℂ} (hg : IsH2Upper g)
    (heq : ∀ z : ℂ, 0 < z.im → g z = h z) : IsH2Upper h := by
  sorry
```
Proof. `DifferentiableOn.congr` (the two functions agree on the open set `ℂ₊`); the line integrals are those of
`g` because `Im(x + i y) = y > 0` (rewrite pointwise with `heq`, `simp` the imaginary part).

```lean
/-- Elementary inequality `‖a + b‖ₑ² ≤ 2 ‖a‖ₑ² + 2 ‖b‖ₑ²`. -/
theorem enorm_add_sq_le (a b : ℂ) :
    ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  sorry
```
Proof. Real inequality `‖a+b‖² ≤ (‖a‖+‖b‖)² ≤ 2‖a‖²+2‖b‖²` (`norm_add_le`, `nlinarith [sq_nonneg (‖a‖-‖b‖)]`), then
`‖x‖ₑ = ENNReal.ofReal ‖x‖` (`ofReal_norm_eq_enorm`), `ENNReal.ofReal_pow`, `ofReal_add`, `ofReal_mul`, `ofReal_le_ofReal`.

```lean
theorem IsH2Upper.add {g h : ℂ → ℂ} (hg : IsH2Upper g) (hh : IsH2Upper h) :
    IsH2Upper (fun z ↦ g z + h z) := by
  sorry
```
```lean
theorem IsH2Upper.sub {g h : ℂ → ℂ} (hg : IsH2Upper g) (hh : IsH2Upper h) :
    IsH2Upper (fun z ↦ g z - h z) := by
  sorry
```
```lean
theorem IsH2Upper.const_mul {g : ℂ → ℂ} (hg : IsH2Upper g) (c : ℂ) :
    IsH2Upper (fun z ↦ c * g z) := by
  sorry
```
Proof. `DifferentiableOn.add/sub/const_mul`. For the bound `L(g+h,y) ≤ 2 L(g,y) + 2 L(h,y) ≤ 2C₁+2C₂`: pointwise
`enorm_add_sq_le`, `lintegral_mono`, then `lintegral_add_left` with `Measurable (fun x ↦ ‖g (x + y I)‖ₑ^2)`: the line
`x ↦ x + y I` lies in the open set `ℂ₊` where `g` is differentiable, hence continuous (`DifferentiableOn.continuousOn`,
`ContinuousOn.comp_continuous`), so `x ↦ g(x + yI)` is continuous, hence measurable. `ENNReal.coe` bookkeeping:
`C := 2 C₁ + 2 C₂ : ℝ≥0`. For `sub` use `sub = add` with `(-1)•` or the same pointwise inequality for `a - b`
(`‖a-b‖ ≤ ‖a‖+‖b‖`). For `const_mul`: `‖c g‖ₑ² = ‖c‖ₑ² ‖g‖ₑ²` (`enorm_mul`, `mul_pow`), `lintegral_const_mul'`
(`‖c‖ₑ² ≠ ∞`) and the bound `(‖c‖₊² * C : ℝ≥0)`.

```lean
/-- A bounded holomorphic multiplier (`|B| ≤ 1`) preserves `H²`. -/
theorem IsH2Upper.mul_bounded {g B : ℂ → ℂ} (hg : IsH2Upper g)
    (hB : DifferentiableOn ℂ B {z : ℂ | 0 < z.im}) (hB1 : ∀ z : ℂ, 0 < z.im → ‖B z‖ ≤ 1) :
    IsH2Upper (fun z ↦ B z * g z) := by
  sorry
```
Proof. Differentiability of the product. Pointwise `‖B g‖ₑ ≤ ‖g‖ₑ` when `‖B‖ ≤ 1` (`enorm_mul`, `enorm_le_one`-type
step: `ENNReal.ofReal_le_one` or `by simpa using ...` from `‖B z‖ ≤ 1`); then `lintegral_mono` and the same `C`.

```lean
/-- A constant function is in `H²(ℂ₊)` only if it is `0` (its line integrals are `∞`). -/
theorem IsH2Upper.const_eq_zero {c : ℂ} (h : IsH2Upper (fun _ ↦ c)) : c = 0 := by
  sorry
```
Proof. Suppose `c ≠ 0`. With the bound `C` at `y = 1`: `L(const, 1) = ‖c‖ₑ² * volume univ = ∞` (`lintegral_const`,
`Real.volume_univ`, `ENNReal.mul_top` since `‖c‖ₑ² ≠ 0`), contradicting `≤ C < ∞`.

### 1.2 Area mean-value inequality
```lean
/-- **Area mean-value inequality.**  If `G` is holomorphic on a neighbourhood of the closed disc
`B̄(c, r)`, `r > 0`, then `|G(c)|² ≤ (π r²)⁻¹ ∫_{B(c,r)} |G|² dA`. -/
theorem enorm_sq_le_setLIntegral_ball {G : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (closedBall c r)) :
    ‖G c‖ₑ ^ 2 ≤ (ENNReal.ofReal (Real.pi * r ^ 2))⁻¹ * ∫⁻ z in ball c r, ‖G z‖ₑ ^ 2 := by
  sorry
```
Proof (two steps; `r > 0`, `G` differentiable on the closed ball).

*(a) Area average of `G` itself.* For every `0 < ρ ≤ r`, `G` is `DiffContOnCl` on `ball c ρ`
(`DifferentiableOn.diffContOnCl`, closure `⊆ closedBall c r`), so by `DiffContOnCl.circleAverage`
(`Mathlib/Analysis/Complex/MeanValue.lean`)
`(2π)⁻¹ ∫₀^{2π} G(c + ρ e^{iθ}) dθ = G(c)`. Multiply by `ρ` and integrate over `ρ ∈ (0, r)`:
`∫₀^r ρ ∫₀^{2π} G(c + ρ e^{iθ}) dθ dρ = 2π G(c) r²/2 = π r² G(c)`.
By polar coordinates (`Complex.integral_comp_polarCoord_symm`, `Mathlib/Analysis/SpecialFunctions/PolarCoord.lean`; the
disc corresponds to `Ioo 0 r ×ˢ Ioo (-π) π`, a null set is discarded) the left side is `∫_{B(c,r)} G dA`. Hence
`G(c) = (π r²)⁻¹ ∫_{B(c,r)} G dA`. (Integrability: `G` continuous on the compact closed ball.)

*Implemented:* Cauchy–Schwarz on circles first (`circle_lintegral_ge`), then polar coordinates
(`MeanValue.area_ge`), instead of (a) then (b). The same inequality is proved independently as
`enorm_sq_le_lintegral_ball` in `PW/PlancherelPolya.lean` (duplication).

*(b) Cauchy–Schwarz.* `‖G(c)‖ ≤ (π r²)⁻¹ ∫_B ‖G‖ ≤ (π r²)⁻¹ (∫_B ‖G‖²)^{1/2} (π r²)^{1/2}`
(`norm_integral_le_integral_norm`, then Hölder/Cauchy–Schwarz for `1` and `‖G‖`: `integral_mul_le_Lp_mul_Lq_of_nonneg`
with `p = q = 2`, or the inequality `(∫ ‖G‖)² ≤ vol(B) ∫‖G‖²` via `MeasureTheory.sq_integral_le`/Jensen). Squaring:
`‖G(c)‖² ≤ (π r²)⁻¹ ∫_B ‖G‖²`. Convert to `ℝ≥0∞` with `ofReal_integral_eq_lintegral_ofReal` (integrable, nonnegative),
`Real.volume ball = π r²` (`Complex.volume_ball`/`EuclideanSpace.volume_ball`: area of a disc in `ℂ`;
`Complex.volume_ball : volume (ball a r) = .ofReal r ^ 2 * NNReal.pi`).

### 1.3 Pointwise bound from line integrals
```lean
/-- Pointwise bound from a bound on the horizontal line integrals in the strip
`|Im w - Im c| < r`: if `G` is holomorphic near `B̄(c, r)` and
`∫ |G(x + is)|² dx ≤ K` for almost every `s ∈ (Im c - r, Im c + r)`, then
`|G(c)|² ≤ (2 / (π r)) K`. -/
theorem enorm_sq_le_of_lines {G : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (closedBall c r)) {K : ℝ≥0∞}
    (hK : ∀ᵐ s : ℝ, s ∈ Ioo (c.im - r) (c.im + r) →
      ∫⁻ x : ℝ, ‖G ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2 ≤ K) :
    ‖G c‖ₑ ^ 2 ≤ ENNReal.ofReal (2 / (Real.pi * r)) * K := by
  sorry
```
Proof. `ball c r ⊆ {w | |Im w − Im c| < r}`. Transport `ℂ ≃ ℝ × ℝ` by the measure-preserving
`Complex.volume_preserving_equiv_real_prod` and apply Tonelli (`lintegral_prod`, using measurability of `‖G‖ₑ²`, `G`
being continuous on the closed ball — extend `G` by `0` off the ball via `Set.indicator` if needed):
`∫⁻_{ball} ‖G‖ₑ² ≤ ∫⁻ s in Ioo (Im c − r) (Im c + r), ∫⁻ x, ‖G(x+is)‖ₑ² ≤ ∫⁻ s in Ioo …, K = 2 r K`
(`lintegral_mono_ae` using `hK`; `setLIntegral_const`, `Real.volume_Ioo`). With §1.2:
`‖G c‖ₑ² ≤ (ofReal(π r²))⁻¹ · 2 r K = ofReal(2/(π r)) · K` (`ENNReal.ofReal_inv_of_pos`, `ENNReal.ofReal_mul`; `K` may be `∞`,
then there is nothing to prove, so take the case `K = ∞` first).

```lean
/-- **Pointwise bound in `H²`.**  If `g` is holomorphic on `Im z > 0` and
`∫ |g(x + iy)|² dx ≤ C` for all `y > 0`, then `|g(z)|² ≤ (4 / (π Im z)) C`. -/
theorem IsH2Upper.enorm_sq_le {g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, 0 < y → ∫⁻ x : ℝ, ‖g ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤ C)
    {z : ℂ} (hz : 0 < z.im) :
    ‖g z‖ₑ ^ 2 ≤ ENNReal.ofReal (4 / (Real.pi * z.im)) * C := by
  sorry
```
Proof. Put `y = Im z`, `r = y/2`. `closedBall z r ⊆ ℂ₊` (points have `Im ≥ y/2 > 0`), so `g` is differentiable there
(`DifferentiableOn.mono`). For `s ∈ Ioo (y/2) (3y/2)`, `s > 0` and `hC s` gives the line bound `C`. Apply §1.3:
`ofReal(2/(π y/2)) = ofReal(4/(π y))`.

### 1.4 Liouville for `L²` on lines
```lean
/-- **Liouville for `L²` on lines.**  An entire function whose line integrals
`∫ |G(x + is)|² dx` are bounded by a constant `K < ∞` for all (almost all) `s` is `0`. -/
theorem eq_zero_of_lines_le {G : ℂ → ℂ} (hG : Differentiable ℂ G) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hline : ∀ s : ℝ, s ≠ 0 → ∫⁻ x : ℝ, ‖G ((x : ℂ) + (s : ℂ) * I)‖ₑ ^ 2 ≤ K) :
    ∀ z, G z = 0 := by
  sorry
```
Proof. Fix `z`. For every `r > 0` apply §1.3 to `G` (entire, so differentiable on `closedBall z r`); the hypothesis `hK`
holds because `hline` covers every `s ≠ 0` and `{0}` is null (`Set.Finite.measure_zero`, `ae_iff`/`measure_singleton`
`∀ᵐ s, s ≠ 0`). Hence `‖G z‖ₑ² ≤ ofReal(2/(π r)) K → 0` as `r → ∞` (`K ≠ ⊤`;
`ENNReal.Tendsto.mul_const` or an `ε`-argument with `ENNReal.le_of_forall_pos_le_add`), so `‖G z‖ₑ² = 0`, `G z = 0`.

### 1.5 Blow-up at a real zero
```lean
/-- **Blow-up at a real zero.**  If `E` is entire without zeros in `Im z > 0` and has a zero at
the real point `x₀`, and `f` is entire with `f(x₀) ≠ 0`, then `f/E` is *not* in `H²(ℂ₊)`:
`∫ |f/E (x + iy)|² dx ≥ c / y` for small `y`. -/
theorem not_isH2Upper_div_of_zero {E f : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hf : Differentiable ℂ f) (hE0 : ∀ z : ℂ, 0 < z.im → E z ≠ 0) {x₀ : ℝ} (hx₀ : E x₀ = 0)
    (hfx : f x₀ ≠ 0) : ¬ IsH2Upper (fun z ↦ f z / E z) := by
  sorry
```
Proof. Suppose `f/E ∈ H²` with bound `C`. Let `a = ‖f x₀‖ > 0`.
1. *Lipschitz bound for `E`.* `E` is `C¹` (`hE.contDiff`), so `‖deriv E‖` is bounded by some `L₀` on the compact
   ball `closedBall (x₀:ℂ) 1` (`IsCompact.exists_bound_of_continuousOn`). Put `L = L₀ + 1 > 0`. Since `E x₀ = 0`,
   `Convex.norm_image_sub_le_of_norm_deriv_le` (`Mathlib/Analysis/Calculus/MeanValue.lean`) gives
   `‖E w‖ ≤ L ‖w − x₀‖` for `‖w − x₀‖ ≤ 1`.
2. *Lower bound for `f`.* Continuity of `f` at `x₀`: there is `δ₂ > 0` with `‖f w‖ ≥ a/2` for `‖w−x₀‖ < δ₂`.
3. Let `δ = min(1, δ₂)/4`. For `0 < y ≤ δ` and `|x − x₀| ≤ y`, `w = x + iy` satisfies
   `‖w − x₀‖² = (x−x₀)² + y² ≤ 2y²`, so `0 < ‖w−x₀‖ ≤ √2·y < 2y ≤ min(1,δ₂)/2`. Since `E w ≠ 0` (`w ∈ ℂ₊`),
   `‖f w / E w‖² ≥ (a/2)² / (L² · 2y²) = a²/(8 L² y²)`.
4. Integrate over `x ∈ [x₀ − y, x₀ + y]` (length `2y`): `L(f/E, y) ≥ 2y · a²/(8L²y²) = a²/(4 L² y)`
   (`lintegral_mono` to the indicator of `Icc`, `setLIntegral_const`). As `y ↓ 0` this exceeds any `C`:
   contradiction. (Take `y = min(δ, a²/(8 L² (C+1)))`.)

---

## 2. `Basic.lean` — algebra of `f^*`
Statements (all proved in the scaffold, with `simp [fstar]`/`funext`): `fstar_apply` (`rfl`, simp), `fstar_fstar`, `fstar_mul`, `fstar_add`, `fstar_sub`,
`fstar_const_mul`, `fstar_div`, `fstar_ofReal`, `norm_fstar` (`‖f^*(z)‖ = ‖f(z̄)‖`).

```lean
theorem Differentiable.fstar {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (FF.fstar f) := by
  sorry
```
Proof (checked, compiles). `Mathlib/Analysis/Calculus/Deriv/Star.lean`: `DifferentiableAt.conj_conj : DifferentiableAt 𝕜 f x →
DifferentiableAt 𝕜 (conj ∘ f ∘ conj) (conj x)`. Apply it to `f` at `conj z` and rewrite `conj (conj z) = z`
(`Complex.conj_conj`); `fstar f` is definitionally `conj ∘ f ∘ conj`.

```lean
/-- `(f^*)'(z) = conj (f'(z̄))`. -/
theorem deriv_fstar (f : ℂ → ℂ) (z : ℂ) :
    deriv (fstar f) z = conj (deriv f (conj z)) := by
  sorry
```
```lean
/-- For real `x`: `(f^*)'(x) = conj (f'(x))`. -/
theorem deriv_fstar_ofReal (f : ℂ → ℂ) (x : ℝ) :
    deriv (fstar f) (x : ℂ) = conj (deriv f (x : ℂ)) := by
  sorry
```
Proof (compiles). `deriv_conj_conj : deriv (conj ∘ f ∘ conj) = conj ∘ deriv f ∘ conj` (valid without differentiability).

## 3. `Basic.lean` — the class `\overline{HB}`

```lean
theorem isHB_one : IsHB (fun _ : ℂ ↦ (1 : ℂ)) := by
  sorry
```
```lean
theorem IsHB.mul {E F : ℂ → ℂ} (hE : IsHB E) (hF : IsHB F) : IsHB (fun z ↦ E z * F z) := by
  sorry
```
Proof (compiles). Differentiability, `mul_ne_zero`, and `‖E z̄ F z̄‖ = ‖E z̄‖‖F z̄‖ ≤ ‖E z‖‖F z‖` by `mul_le_mul`.

```lean
/-- The zeros of `E ∈ \overline{HB}` lie in `Im z ≤ 0`, and `|E^*(z)| ≤ |E(z)|` on `Im z > 0`. -/
theorem IsHB.norm_fstar_le {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : 0 < z.im) :
    ‖fstar E z‖ ≤ ‖E z‖ := by
  sorry
```
Proof. `norm_fstar` and the third component of `IsHB`.

### 3.1 Dichotomy: strict or `E^* = cE`
```lean
/-- **Dichotomy** for `E ∈ \overline{HB}`: either `|E(z̄)| < |E(z)|` on `Im z > 0` (`E` strict) or
`E^* = c E` with `|c| = 1`.  (Maximum modulus for `E^*/E`, then the identity theorem.) -/
theorem IsHB.isStrictHB_or_fstar_eq {E : ℂ → ℂ} (hE : IsHB E) :
    IsStrictHB E ∨ ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z : ℂ, fstar E z = c * E z := by
  sorry
```
```lean
/-- If `E ∈ \overline{HB}` is strict at one point of `Im z > 0`, it is strict everywhere. -/
theorem IsHB.isStrictHB_of_exists_lt {E : ℂ → ℂ} (hE : IsHB E)
    (h : ∃ z : ℂ, 0 < z.im ∧ ‖E (conj z)‖ < ‖E z‖) : IsStrictHB E := by
  sorry
```
Proof. Let `E ∈ \overline{HB}`. On `ℂ₊`, `E ≠ 0`, so `Θ = E^*/E` is holomorphic there (`E^*` entire by §2), with
`‖Θ(z)‖ = ‖E(z̄)‖/‖E(z)‖ ≤ 1`. *Case 1:* `‖E(z̄)‖ < ‖E(z)‖` for every `z ∈ ℂ₊`: `E` is strict (first alternative).
*Case 2:* there is `z₀ ∈ ℂ₊` with `‖E(z̄₀)‖ = ‖E(z₀)‖`, i.e. `‖Θ(z₀)‖ = 1 = max ‖Θ‖`. The set `ℂ₊` is open and
preconnected (convex: `convex_halfSpace_im_gt`, `.isPreconnected`); by the maximum modulus principle
`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm` (`Mathlib/Analysis/Complex/AbsMax.lean`: `DifferentiableOn ℂ f U`,
`IsPreconnected U`, `IsOpen U`, `IsMaxOn (‖f ·‖) U c` ⇒ `EqOn f (const (f c)) U`) `Θ ≡ c := Θ(z₀)` on `ℂ₊`, `‖c‖ = 1`.
So the entire function `E^* − cE` vanishes on the open nonempty set `ℂ₊`, hence everywhere
(`AnalyticOnNhd.eq_of_eventuallyEq` for entire functions, `Differentiable.analyticAt`; or `eqOn_of_preconnected_of_eventuallyEq`
with `U = univ`). `isStrictHB_of_exists_lt` is the contrapositive: if `E^* = cE`, `‖c‖ = 1`, then `‖E(z̄)‖ = ‖E^*(z)‖ = ‖E(z)‖`
for all `z`, so no point is strict.

### 3.2 Hurwitz-type closure
```lean
/-- **Hurwitz-type closure.**  A locally uniform limit of functions of `\overline{HB}` is in
`\overline{HB}` unless it vanishes identically. -/
theorem IsHB.of_tendstoLocallyUniformly {ι : Type*} {p : Filter ι} [p.NeBot]
    {E : ι → ℂ → ℂ} {E₀ : ℂ → ℂ} (hE : ∀ i, IsHB (E i))
    (hlim : TendstoLocallyUniformly E E₀ p) (hne : ∃ z, E₀ z ≠ 0) : IsHB E₀ := by
  sorry
```
Proof. Write `E₀` for the limit. Mathlib has no Hurwitz theorem; we use the *minimum modulus* argument below (no argument
principle needed).
1. *Entire.* `TendstoLocallyUniformlyOn.differentiableOn` (`Mathlib/Analysis/Complex/LocallyUniformLimit.lean`) with `U = univ`
   (`tendstoLocallyUniformlyOn_univ`), `hF` from `(hE i).1`, `isOpen_univ`.
2. *Inequality.* Locally uniform ⇒ pointwise: `E i z → E₀ z` for each `z`; `‖E i (z̄)‖ ≤ ‖E i z‖` for `Im z > 0` passes to
   the limit (`le_of_tendsto_of_tendsto'` with `tendsto_norm`; `p.NeBot`).
3. *No zeros in `ℂ₊`.* Suppose `E₀(z₀) = 0` with `Im z₀ > 0`.
   (a) `E₀` is analytic and `≢ 0`, so zeros are isolated: by `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`
   (`Analysis/Analytic/IsolatedZeros.lean`) either `E₀ = 0` near `z₀`, which by the identity theorem
   (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`, `U = univ`) contradicts `∃ z, E₀ z ≠ 0`, or
   `∀ᶠ z in 𝓝[≠] z₀, E₀ z ≠ 0`.
   (b) Choose `0 < r` with `closedBall z₀ r ⊆ ℂ₊` and `E₀ ≠ 0` on `sphere z₀ r` (from the punctured-neighbourhood
   statement, `Metric.eventually_nhdsWithin_iff`/`eventually_nhds_iff`). The sphere is compact and `‖E₀‖` is continuous, so
   `m := min_{sphere} ‖E₀‖ > 0` (`IsCompact.exists_isMinOn`).
   (c) Locally uniform convergence on the compact `closedBall z₀ r` (`tendstoLocallyUniformly_iff_forall_isCompact`) gives
   `i₀` (eventually in `p`) with `‖E i z − E₀ z‖ < m/2` on the closed ball; so `‖E i z‖ ≥ m/2` on the sphere.
   (d) For such `i`, `E i` has no zero in `closedBall z₀ r ⊆ ℂ₊` (`(hE i).2.1`), so `1/E i` is differentiable on a
   neighbourhood of the closed ball, i.e. `DiffContOnCl ℂ (1/E i) (ball z₀ r)`, with `‖1/E i‖ ≤ 2/m` on the frontier `sphere z₀ r`.
   By `Complex.norm_le_of_forall_mem_frontier_norm_le` (`AbsMax.lean`; `U = ball z₀ r` bounded,
   `frontier_ball`), `‖1/E i (z₀)‖ ≤ 2/m`, i.e. `‖E i z₀‖ ≥ m/2`.
   (e) But `E i z₀ → E₀ z₀ = 0`: contradiction for `i` eventually.
Remark. The hypothesis `E₀ ≢ 0` cannot be dropped (`E_n = e^{-n} (z+i)`). Closedness of `\overline{HB}` under this notion is
used in M07 (Corollary 2: `A − iB` as a limit of polynomials) and M06.

---

## 4. `Phase.lean` — existence, uniqueness, derivative of phase functions

```lean
theorem continuous_phaseDeriv {E : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0) :
    Continuous (phaseDeriv E) := by
  sorry
```
Proof. `deriv E` is continuous (`hE.contDiff.continuous_deriv le_rfl`, `Differentiable.contDiff` in `CauchyIntegral.lean`);
compose with `Complex.continuous_ofReal`; quotient `Continuous.div` with `h0`; `Complex.continuous_im.comp`, `Continuous.neg`.

```lean
/-- `phaseDeriv` is multiplicative-to-additive: `φ_{EF}' = φ_E' + φ_F'`. -/
theorem phaseDeriv_mul {E F : ℂ → ℂ} (hE : Differentiable ℂ E) (hF : Differentiable ℂ F)
    {x : ℝ} (hEx : E x ≠ 0) (hFx : F x ≠ 0) :
    phaseDeriv (fun z ↦ E z * F z) x = phaseDeriv E x + phaseDeriv F x := by
  sorry
```
Proof. `deriv_mul` at `(x:ℂ)`: `(EF)' = E'F + EF'`. With `E x, F x ≠ 0`: `(E'F+EF')/(EF) = E'/E + F'/F` (`field_simp`),
`Complex.add_im`, `neg_add`.

```lean
/-- **Existence of a phase function** with `φ' = phaseDeriv E`. -/
theorem exists_isPhaseFunction {E : ℂ → ℂ} (hE : Differentiable ℂ E) (h0 : ∀ x : ℝ, E x ≠ 0) :
    ∃ φ : ℝ → ℝ, IsPhaseFunction E φ ∧ ∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x := by
  sorry
```
Proof. Let `ρ = phaseDeriv E`, continuous by §4.1. Put
`Φ(x) = φ₀ + ∫₀^x ρ(t) dt`, `φ₀ = −arg(E 0)`.
(1) `HasDerivAt Φ (ρ x) x` for all `x` (`Continuous.integral_hasStrictDerivAt` or `intervalIntegral.integral_hasDerivAt_right`,
using continuity). In particular `Φ` is continuous.
(2) *Implemented* (`HB/Phase.lean`; `|E|` is never differentiated): with `R(x) = ∫₀ˣ Re(E'/E)`,
`M(x) = E(x) e^{iΦ(x) − R(x)}` has derivative `0`, because `E'/E + iρ − Re(E'/E) = 0`
(`HasDerivAt.comp_ofReal`, `HasDerivAt.cexp`). So `M` is constant, `M(0) = |E(0)|`, and
`E(x) = |E(0)| e^{R(x)} e^{−iΦ(x)}`; taking norms, `E(x) = ‖E(x)‖ e^{−iΦ(x)}`: `IsPhaseFunction E Φ`.

```lean
/-- **Uniqueness up to `2π ℤ`.** -/
theorem IsPhaseFunction.exists_int_eq_add {E : ℂ → ℂ} (h0 : ∀ x : ℝ, E x ≠ 0) {φ ψ : ℝ → ℝ}
    (hφ : IsPhaseFunction E φ) (hψ : IsPhaseFunction E ψ) :
    ∃ k : ℤ, ∀ x : ℝ, ψ x = φ x + 2 * Real.pi * k := by
  sorry
```
Proof. For each `x`, `‖E x‖ ≠ 0`, so `exp(−iφ x) = exp(−iψ x)`, i.e. (`Complex.exp_eq_exp_iff_exists_int`) there is
`k ∈ ℤ` with `−iφ(x) = −iψ(x) + 2π i k`, i.e. `ψ x − φ x = 2π k`. The continuous function `g = (ψ − φ)/(2π)` takes only
integer values; by the intermediate value theorem on `ℝ` (`intermediate_value_univ`) it is constant: if `g a ≠ g b`,
then `g` takes every value in between, including a non-integer. Put `k = g 0`.

```lean
/-- Every phase function of `E` (without real zeros) is differentiable with derivative
`phaseDeriv E`. -/
theorem IsPhaseFunction.hasDerivAt {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (h0 : ∀ x : ℝ, E x ≠ 0) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) (x : ℝ) :
    HasDerivAt φ (phaseDeriv E x) x := by
  sorry
```
Proof. `exists_isPhaseFunction` gives `Φ`; by uniqueness `φ = Φ + 2π k`, constants do not change derivatives.

```lean
/-- Phase functions add under products. -/
theorem IsPhaseFunction.mul {E F : ℂ → ℂ} {φ ψ : ℝ → ℝ} (hφ : IsPhaseFunction E φ)
    (hψ : IsPhaseFunction F ψ) :
    IsPhaseFunction (fun z ↦ E z * F z) (fun x ↦ φ x + ψ x) := by
  sorry
```
```lean
/-- `Re E(x) = |E(x)| cos φ(x)` on the real axis. -/
theorem IsPhaseFunction.re_eq {E : ℂ → ℂ} {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) (x : ℝ) :
    (E x).re = ‖E x‖ * Real.cos (φ x) := by
  sorry
```
Proof (`mul`). `E(x)F(x) = ‖E‖e^{−iφ}‖F‖e^{−iψ} = ‖EF‖ e^{−i(φ+ψ)}` (`norm_mul`, `Complex.exp_add`, `neg_add`);
continuity of the sum. (`re_eq`): `Re(‖E‖ e^{−iφ}) = ‖E‖ cos φ` (`Complex.re_ofReal_mul`, `Complex.exp_ofReal_mul_I_re`
after writing `−(I φ) = ((−φ : ℝ) : ℂ) I`, `Real.cos_neg`).

---

## 5. Sign of the phase derivative

### 5.1 `φ_F' ≥ 0` for `F ∈ \overline{HB}`
```lean
/-- **`φ_F' ≥ 0`** for `F ∈ \overline{HB}` (the non-strict class) at real points where `F ≠ 0`. -/
theorem IsHB.phaseDeriv_nonneg {F : ℂ → ℂ} (hF : IsHB F) {x : ℝ} (hx : F x ≠ 0) :
    0 ≤ phaseDeriv F x := by
  sorry
```
*Implemented:* both `φ' ≥ 0` and the strict case come from the dichotomy
`IsHB.phaseDeriv_pos_or_eventuallyEq` (`HB/Phase.lean`): either `E^* = cE` near `x`, so `φ'(x) = 0`, or
`φ'(x) > 0`. It is proved from the normal form of `E^*/E − c` at `x` and `hopf_boundary`
(`HB/Hopf.lean`). The `D(y)` argument below is a valid alternative for `≥ 0`, but it is not
formalized and cannot give strictness (`D(y) ≈ −y³` is possible).

Proof. Let `a = F(x) ≠ 0`, `b = F'(x)`. Let `D(y) = ‖F^*(x+iy)‖² − ‖F(x+iy)‖²`, `y ∈ ℝ`.
* `D(0) = 0` since `F^*(x) = ā` (`fstar_ofReal`), `‖ā‖ = ‖a‖`.
* `D(y) ≤ 0` for `y ≥ 0`: for `y > 0` this is `‖F^*(z)‖ = ‖F(z̄)‖ ≤ ‖F(z)‖` (`IsHB.norm_fstar_le`), `z = x+iy`.
* `D` is differentiable at `0`: `y ↦ F(x + iy)` has derivative `i b` at `0` (`HasDerivAt.comp_ofReal` of `F`, composed with
 `y ↦ x + y i`, or `HasDerivAt.scomp`), and `y ↦ F^*(x+iy)` has derivative `i (F^*)'(x) = i b̄` (`deriv_fstar_ofReal`).
 By `HasDerivAt.norm_sq` (`Mathlib/Analysis/InnerProductSpace/Calculus.lean`, inner product of `ℂ` as a real space `⟪u,v⟫ = Re(ū v)`):
 `D'(0) = 2 Re(conj(ā) · i b̄) − 2 Re(ā · i b) = 2 Re(i a b̄) − 2 Re(i ā b)`.
 Now `Re(i a b̄) = Im(ā b)` (it is `Re(conj(−i ā b)) = Re(−i ā b) = Im(ā b)`), and `Re(i ā b) = −Im(ā b)`, so
 **`D'(0) = 4 Im(ā b) = 4 ‖a‖² Im(b/a)`**.
* *One-sided maximum.* `D` has a local maximum at `0` on `Ici 0` (`IsLocalMaxOn`). By
 `IsLocalMaxOn.hasFDerivWithinAt_nonpos` (`Analysis/Calculus/LocalExtr/Basic.lean`) and
 `mem_posTangentConeAt_of_segment_subset` (the point `1 ∈ posTangentConeAt (Ici 0) 0`), `D'(0) ≤ 0`.
Hence `Im(b/a) ≤ 0`, i.e. `phaseDeriv F x = −Im(b/a) ≥ 0`. (Sanity: `F = z + i`, `phaseDeriv = 1/(1+x²)`.)

### 5.2 `φ_E' > 0` when `E^*/E` is non-constant
```lean
/-- **`φ_E' > 0`** if `E ∈ \overline{HB}` is strict at a single point of `Im z > 0`
(i.e. `E^*/E` is not constant). -/
theorem IsHB.phaseDeriv_pos_of_exists_lt {E : ℂ → ℂ} (hE : IsHB E) {x : ℝ} (hx : E x ≠ 0)
    (h : ∃ z : ℂ, 0 < z.im ∧ ‖E (conj z)‖ < ‖E z‖) : 0 < phaseDeriv E x := by
  sorry
```
```lean
theorem IsStrictHB.phaseDeriv_pos {E : ℂ → ℂ} (hE : IsStrictHB E) {x : ℝ} (hx : E x ≠ 0) :
    0 < phaseDeriv E x := by
  sorry
```
**This is the one place where the strict inequality in the *half-plane* has to be converted into a strict inequality for
the *derivative* on the boundary** (Hopf-type lemma). Proof, by contradiction via a local expansion of `Θ = E^*/E`.

Let `x₀ ∈ ℝ`, `E(x₀) ≠ 0`, and `‖E(z̄₁)‖ < ‖E(z₁)‖` for some `z₁ ∈ ℂ₊`. By §5.1, `phaseDeriv E x₀ ≥ 0`; suppose it is `0`.
1. *Setting.* `E ≠ 0` on some ball `U = ball x₀ ρ` (continuity). `Θ := E^*/E` is analytic on `U`, `‖Θ‖ ≤ 1` on `U ∩ ℂ₊`
 (`IsHB.norm_fstar_le`), `c := Θ(x₀) = conj(a)/a`, `‖c‖ = 1`.
2. *Θ' vs the phase.* `Θ' = ((E^*)'E − E^*E')/E²`. At `x₀`, with `a = E x₀`, `b = E' x₀`: `(E^*)'(x₀) = b̄`, `E^*(x₀) = ā`, so
 `Θ'(x₀) = (b̄ a − ā b)/a² = −2i Im(ā b)/a² = 2i · phaseDeriv E x₀ · ‖a‖²/a²`, hence **`‖Θ'(x₀)‖ = 2 |phaseDeriv E x₀|`**.
 Under our assumption `Θ'(x₀) = 0`.
3. *Θ is not constant near `x₀`.* If `Θ = c` on a neighbourhood of `x₀`, then `E^* − cE` is entire and vanishes on an open set,
 hence identically (identity theorem), so `‖E(z̄₁)‖ = ‖E^*(z₁)‖ = ‖E(z₁)‖`, contradicting the choice of `z₁`.
4. *Normal form.* By `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` (`IsolatedZeros.lean`) applied to `Θ − c` at
 `x₀`: there are `n ∈ ℕ` and `g` analytic at `x₀`, `g(x₀) ≠ 0`, with `Θ(z) − c = (z−x₀)^n g(z)` for `z` near `x₀`.
 `n ≥ 1` since `Θ(x₀) − c = 0`. If `n = 1` then `Θ'(x₀) = g(x₀) ≠ 0`, contradicting step 2. So **`n ≥ 2`**.
5. *Contradiction for `n ≥ 2`.* Put `h = g/c`, `h(x₀) = |h₀|e^{iβ} ≠ 0`. For `z = x₀ + t e^{iθ}`, `θ ∈ (0,π)`, `t > 0` small:
 `z ∈ ℂ₊ ∩ U`, `‖Θ(z)‖² ≤ 1` and `Θ(z) = c(1 + w)`, `w = t^n e^{inθ} h(z)`, so `0 ≥ ‖1+w‖² − 1 = 2 Re w + |w|²`, i.e.
 `Re(e^{inθ} h(z)) ≤ −t^n |h(z)|²/2 ≤ 0`. Let `t ↓ 0` (continuity of `h`): **`Re(e^{inθ} h(x₀)) = |h₀| cos(nθ + β) ≤ 0` for every `θ ∈ (0, π)`.**
 But as `θ` runs through `(0,π)`, `nθ + β` runs through an interval of length `nπ ≥ 2π`, which contains a full period of
 `cos`, so some `θ` has `cos(nθ+β) > 0`. (Precisely: `S = {θ : cos(nθ+β) > 0}` is open, nonempty and invariant under `θ ↦ θ + 2π/n`; `2π/n ≤ π`, so
 `S ∩ [0,π)` is a nonempty open subset of `[0,π)`, and removing the single point `0` leaves it nonempty.)
 Contradiction. Hence `phaseDeriv E x₀ > 0`.
(For `n = 1` the same inequality reads `Re(e^{iθ} h(x₀)) ≤ 0` on `(0,π)`, i.e. `h(x₀) = 2iφ'(x₀)` with `φ' ≥ 0`: this re-proves §5.1
and shows what is going on.) `IsStrictHB.phaseDeriv_pos` follows with `z₁ = i`, `‖E(−i)‖ < ‖E(i)‖`.

*Why not a shorter route?* Strictness of `‖E^*/E‖ < 1` gives only `D(y) < 0` for `y > 0`, which does not preclude `D'(0) = 0`
(e.g. `D(y) ≈ −y³`); some use of harmonicity/analyticity is needed. The argument above is the elementary form of Hopf's boundary
lemma for the half-disc; it needs only analytic normal forms and one trigonometric choice. The alternative of avoiding strict positivity
altogether is not possible: M03 needs that `φ_E + φ_F` is strictly increasing to define the level sets of Theorem E.

```lean
/-- A phase function of a strict `E` without real zeros is strictly increasing. -/
theorem IsPhaseFunction.strictMono_of_isStrictHB {E : ℂ → ℂ} (hE : IsStrictHB E)
    (h0 : ∀ x : ℝ, E x ≠ 0) {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) : StrictMono φ := by
  sorry
```
Proof. By `IsPhaseFunction.hasDerivAt` and `IsStrictHB.phaseDeriv_pos`, `deriv φ x = phaseDeriv E x > 0` for all `x`;
`strictMono_of_deriv_pos` (`Analysis/Calculus/Deriv/MeanValue.lean`).

---

## 6. The zero set of `EF + E^*F^*`
```lean
/-- **Zero set of `EF + E^*F^*`** (p. 796): for `E` strict and `F ∈ \overline{HB}`, both without
real zeros, the zeros of `EF + E^*F^*` are exactly the real points where the total phase
`φ_E + φ_F` is `≡ π/2 (mod π)`. -/
theorem zero_set_eq_phaseLevel {E F : ℂ → ℂ} (hE : IsStrictHB E) (hF : IsHB F)
    (hE0 : ∀ x : ℝ, E x ≠ 0) (hF0 : ∀ x : ℝ, F x ≠ 0) {φE φF : ℝ → ℝ}
    (hφE : IsPhaseFunction E φE) (hφF : IsPhaseFunction F φF) (z : ℂ) :
    E z * F z + fstar E z * fstar F z = 0 ↔
      z ∈ Complex.ofReal '' phaseLevel (fun t ↦ φE t + φF t) (Real.pi / 2) := by
  sorry
```
Proof. Put `P(z) = E(z)F(z) + E^*(z)F^*(z)`.
*(i) `Im z > 0`: `P(z) ≠ 0`.* `‖E^*(z)F^*(z)‖ = ‖E(z̄)‖‖F(z̄)‖ ≤ ‖E(z̄)‖‖F(z)‖ < ‖E(z)‖‖F(z)‖` (`hF.2.2`, then strictness of `E` and
`F(z) ≠ 0`, `hF.2.1`), so `‖E^*F^*(z)‖ < ‖EF(z)‖` and `P(z) ≠ 0` (`norm_add_eq`-type: if `P = 0` then
`EF = −E^*F^*` and the norms would agree).
*(ii) `Im z < 0`.* `w = z̄ ∈ ℂ₊`. `E^*(z) F^*(z) = conj(E(w)F(w))`, `E(z)F(z) = conj(E^*(w)F^*(w))` (`fstar_fstar`-type
identities `E(z) = conj(E^*(z̄))`). By (i), `‖E(w)F(w)‖ > ‖E^*(w)F^*(w)‖`, i.e. `‖E^*F^*(z)‖ > ‖EF(z)‖`: again `P(z) ≠ 0`.
*(iii) `z = x` real.* `P(x) = E(x)F(x) + conj(E(x)F(x))` (`fstar_ofReal`) `= 2 Re(EF(x)) = 2‖EF(x)‖ cos(φ_E(x) + φ_F(x))`
(`IsPhaseFunction.mul`, `.re_eq`). Since `E(x)F(x) ≠ 0`, `P(x) = 0 ⇔ cos(φ_E+φ_F)(x) = 0 ⇔ ∃ k ∈ ℤ, (φ_E+φ_F)(x) = (2k+1)π/2 = π/2 + kπ`
(`Real.cos_eq_zero_iff`), i.e. `x ∈ phaseLevel (φ_E+φ_F) (π/2)`.
Combining: `P(z) = 0 ⇔ z` real with `x ∈ phaseLevel …`, i.e. `z ∈ ofReal '' phaseLevel …` (for `Im z = 0` write `z = ↑z.re`).
Note that real zeros of `E`, `F` are excluded by hypotheses; the closed class is only used through `hF.2.2`.
(All zeros are simple: `φ_E' > 0`, `φ_F' ≥ 0` give `(φ_E+φ_F)' > 0`, so the `x` where `cos = 0` are simple zeros of `Re EF`.)

---

## 7. `DeBranges.lean` — multiplication by `F ∈ \overline{HB}`

```lean
/-- `F f ∈ H(E F)` for `f ∈ H(E)` and `F ∈ \overline{HB}`. -/
theorem MemHE.mul_isHB {E F f : ℂ → ℂ} (hF : IsHB F) (hf : MemHE E f) :
    MemHE (fun z ↦ E z * F z) (fun z ↦ F z * f z) := by
  sorry
```
Proof. Let `f ∈ H(E)`, `F ∈ \overline{HB}`; write `P = F f`, `Q = E F`.
1. `P` is entire (`Differentiable.mul`).
2. `P/Q ∈ H²`: on `ℂ₊`, `F(z) ≠ 0`, so `P(z)/Q(z) = F f/(E F) = f(z)/E(z)` (`mul_div_mul_left`, which holds even if `E z = 0`).
   Apply `IsH2Upper.congr` to `hf.2.1`.
3. `P^*/Q ∈ H²`: `P^* = F^* f^*` (`fstar_mul`). On `ℂ₊`, `P^*(z)/Q(z) = B(z) · (f^*(z)/E(z))`, `B = F^*/F`
   (`field_simp`, `F z ≠ 0`). `B` is differentiable on `ℂ₊` (`F^*` entire by `Differentiable.fstar`, `F ≠ 0` there) and
   `‖B‖ ≤ 1` (`IsHB.norm_fstar_le`, `div_le_one`). By `IsH2Upper.mul_bounded` applied to `hf.2.2` and `IsH2Upper.congr`, done.

```lean
/-- `‖F f‖_{EF} = ‖f‖_E`. -/
theorem heNormSq_mul {E F f : ℂ → ℂ} (hF : IsHB F) :
    heNormSq (fun z ↦ E z * F z) (fun z ↦ F z * f z) = heNormSq E f := by
  sorry
```
Proof. `heNormSq (EF) (Ff) = ∫⁻ ‖F(t) f(t)/(E(t)F(t))‖ₑ²`. For `t` with `F t ≠ 0` the integrand is `‖f t/E t‖ₑ²`
(`mul_div_mul_left`; true also if `E t = 0`). The set `Z = {t : ℝ | F t = 0}` is countable: `F` entire and `F(i) ≠ 0`, so
by `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected` (`univ`) its zero set is discrete and closed in `ℂ`, hence countable
(second countable ⇒ discrete subsets countable), and `Z` is its preimage under the injective `Complex.ofReal`
(`Set.Countable.preimage_of_injOn`). So `Z` is null (`Set.Countable.measure_zero`) and `lintegral_congr_ae` applies.
(No claim is made that `heNormSq` is finite.)

## 8. The functions `S_α` and the exceptional `α`

```lean
/-- `S_α = e^{iα} E - e^{-iα} E^*` (the function of Theorem E). -/
def sAlpha (E : ℂ → ℂ) (α : ℝ) : ℂ → ℂ :=
  fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z
```
```lean
/-- At most one `α` (mod `π`) has `S_α ∈ H(E)`. -/
theorem memHE_sAlpha_unique {E : ℂ → ℂ} (hE : IsHB E) {α β : ℝ}
    (hα : MemHE E (sAlpha E α)) (hβ : MemHE E (sAlpha E β)) :
    ∃ k : ℤ, β - α = k * Real.pi := by
  sorry
```
Proof. Let `Θ = E^*/E` on `ℂ₊` (`E ≠ 0` there). `S_α(z)/E(z) = e^{iα} − e^{−iα}Θ(z)` on `ℂ₊`. Hence on `ℂ₊`
`e^{iα} (S_α/E) − e^{iβ} (S_β/E) = (e^{2iα} − Θ) − (e^{2iβ} − Θ) = e^{2iα} − e^{2iβ}`
(a constant). The left side is in `H²` by `IsH2Upper.const_mul`, `IsH2Upper.sub` (from `hα.2.1`, `hβ.2.1`), so the constant function is
in `H²` (`IsH2Upper.congr`), hence zero (`IsH2Upper.const_eq_zero`): `e^{2iα} = e^{2iβ}`. By `Complex.exp_eq_exp_iff_exists_int`
`2iα = 2iβ + 2πi k'` for some integer `k'`, i.e. `β − α = −k'π`. (Only the first component `f/E ∈ H²` of `MemHE` is used, and no strictness.)
This is the proof that the exceptional `α` in Theorem E is unique mod `π`; the README's route ("`E ∈ H(E)` is impossible since `E/E = 1 ∉ H²`") is the special
case obtained by subtracting `S_α` from `S_β`.

## 9. `H(E) = PW` forces `E` to be strict without real zeros

```lean
/-- If `H(E) = PW` (as sets), `E ∈ \overline{HB}` has no real zeros. -/
theorem HEEqPW.ne_zero_ofReal {E : ℂ → ℂ} (hE : IsHB E) (h : HEEqPW E) (x : ℝ) : E x ≠ 0 := by
  sorry
```
Proof. Let `x₀` be real, `E x₀ = 0`. Take `g` with `MemPW g`, `g 0 = 1` (`exists_memPW_eval_ne_zero`), and
`f = g(· − x₀)`, `MemPW f` (`MemPW.comp_sub_ofReal`), `f x₀ = g 0 = 1 ≠ 0`. By `h.1`, `MemHE E f`; in particular `f/E ∈ H²`.
But `not_isH2Upper_div_of_zero` (§1.5; `hE.2.1` gives `E ≠ 0` on `ℂ₊`) says this is impossible. ∎
(*The paper says* "Since `H(E) = PW`, `E` does not vanish for `x ∈ ℝ`" on p. 796 without proof.)

```lean
/-- If `H(E) = PW`, then `E ∈ \overline{HB}` is strict: `H(E) = {0}` when `E^* = cE`. -/
theorem HEEqPW.isStrictHB {E : ℂ → ℂ} (hE : IsHB E) (h : HEEqPW E) : IsStrictHB E := by
  sorry
```
Proof. By `IsHB.isStrictHB_or_fstar_eq` it suffices to refute `E^* = cE`, `‖c‖ = 1`. Assume it. Then:
* `E` has no zeros on `ℂ`: none on `ℂ₊` (`IsHB`), none on `ℝ` (`HEEqPW.ne_zero_ofReal`), and for `Im z < 0`,
 `E(z) = c⁻¹ E^*(z) = c⁻¹ conj(E(z̄)) ≠ 0` since `z̄ ∈ ℂ₊`.
* Take `g₀ ∈ PW`, `g₀(0) = 1`. By `h.1`, `g₀ ∈ H(E)`: `g₀/E`, `g₀^*/E ∈ H²` with bounds `M₁, M₂ < ∞`. Put `G = g₀/E`: **entire**
 (`E` has no zeros).
* Lines `s > 0`: `L(G, s) ≤ M₁`. Lines `s < 0`, `z = x + is`: `‖E(z)‖ = ‖E^*(z)‖ = ‖E(z̄)‖` (as `‖c‖ = 1`) and `‖g₀(z)‖ = ‖g₀^*(z̄)‖`, so
 `‖G(z)‖ = ‖(g₀^*/E)(z̄)‖` with `z̄ = x + i|s|`; hence `L(G, s) ≤ M₂` (the reflection `x ↦ x` preserves the integral).
* `eq_zero_of_lines_le` (§1.4) with `K = max(M₁,M₂)` gives `G ≡ 0`, so `g₀ = G E ≡ 0`, contradicting `g₀(0) = 1`. ∎
(*The paper does not discuss this at all:* Theorem E, as quoted, needs `E` strict; `H(E) = PW ≠ {0}` is what rules out `E^* = cE`, where `H(E) = {0}`.)

## 10. `φ_E'|E|² ≃ 1` when `H(E) = PW`

Standing: `IsHB E`, `HEEqPW E` with constants `c₁‖f‖²_{PW} ≤ ‖f‖²_E ≤ C₁‖f‖²_{PW}`, `c₁ > 0` (`c₁, C₁ : ℝ≥0`), `hE : TheoremE`,
`hPW`. By §9, `E` is strict and has no real zeros; by §4 fix `φ` with `IsPhaseFunction E φ` (`exists_isPhaseFunction`; `HasDerivAt φ (phaseDeriv E x) x`),
strictly increasing (`strictMono_of_isStrictHB`). Write `w(x) = π/(φ'(x)‖E(x)‖²) = π/(phaseDeriv E x · ‖E x‖²) > 0` and
`κ(x) = phaseDeriv E x · ‖E x‖²` (continuous: `continuous_phaseDeriv`, `Continuous.norm`, positive by `IsStrictHB.phaseDeriv_pos`).

*Exceptional points.* Let `X = {x | MemHE E (sAlpha E (φ x))}`. If `x, x' ∈ X`, `memHE_sAlpha_unique` gives `φ x' − φ x ∈ πℤ`. So, if `X ≠ ∅` with
`x* ∈ X`, `X ⊆ φ⁻¹({φ x* + kπ | k ∈ ℤ})`: countable, because `φ` is injective (`Set.Countable.preimage_of_injOn`). A countable subset of `ℝ` has dense
complement (`Set.Countable.dense_compl`). So **`Xᶜ` is dense**.

*Bounds on `Xᶜ`.* Let `x₀ ∉ X` and `α = φ(x₀)`, `Γ = phaseLevel φ α ∋ x₀` (take `k = 0`). Theorem E (`hE E hstrict hnz φ hφ α hnotmem`) gives
(i) `heNormSq E f = ∑' γ : Γ, orthWeight E γ * ‖f γ‖ₑ²` for `f ∈ H(E)`,
(ii) for `a : ℝ → ℂ` with `∑' γ : Γ, orthWeight E γ * ‖a γ‖ₑ² < ∞` some `f ∈ H(E)` with `f γ = a γ` on `Γ`.
`orthWeight E x₀ = ofReal(w(x₀))`.
* **Lower bound** `κ(x₀) ≥ π c₀ / C₁`. `pw_eval_lower` (M01) gives a universal `c₀ > 0` and `f ∈ PW` with `c₀ ‖f‖²_{PW} ≤ |f(x₀)|²`, `0 ≠ ‖f‖²_{PW} ≠ ∞`
 (a translate of a fixed bump). `f ∈ H(E)` (`h.1`). By (i) keeping only the term `γ = x₀` (`ENNReal.le_tsum`):
 `ofReal(w(x₀)) · ‖f x₀‖ₑ² ≤ ‖f‖²_E ≤ C₁ ‖f‖²_{PW}`, so `ofReal(w(x₀)) c₀ ‖f‖²_{PW} ≤ C₁ ‖f‖²_{PW}`; cancel `‖f‖²_{PW} ∈ (0,∞)`
 (`ENNReal.mul_le_mul_right`): `w(x₀) c₀ ≤ C₁`, i.e. `κ(x₀) ≥ π c₀/C₁`. (If `C₁ = 0` the inequality `w c₀ ≤ 0` contradicts `w > 0`, so
 `C₁ > 0` automatically.) Take `c = π c₀/C₁` (depends on `C₁` and the absolute `c₀`).
* **Upper bound** `κ(x₀) ≤ π/c₁`. Datum `a = 1_{x₀}` (`a γ = if γ = x₀ then 1 else 0`): `∑' γ : Γ, orthWeight E γ ‖a γ‖ₑ² = ofReal(w(x₀)) < ∞`
 (`tsum_eq_single ⟨x₀, _⟩`). By (ii) there is `f ∈ H(E) = PW` with `f x₀ = 1`, `f γ = 0` for `γ ∈ Γ∖{x₀}`. By (i) again
 `‖f‖²_E = ofReal(w(x₀))`. Pointwise bound (M01, `hPW`): `1 = ‖f x₀‖² ≤ e^{0} (pwNormSq f).toReal`, and `pwNormSq f ≠ ∞` (`pwNormSq_ne_top`), so
 `1 ≤ ‖f‖²_{PW}` (in `ℝ≥0∞`). Then `c₁ ≤ c₁ ‖f‖²_{PW} ≤ ‖f‖²_E = ofReal(w(x₀))`, i.e. `w(x₀) ≥ c₁`, `κ(x₀) ≤ π/c₁`. (Depends only on `c₁`.)
*Extension to all `x`.* `{x | c ≤ κ x}` and `{x | κ x ≤ π/c₁}` are closed (continuity of `κ`) and contain the dense set `Xᶜ`, hence equal `ℝ`
(`Dense.closure_eq`, `closure_minimal`). This is the avoidance of the exceptional `α` by continuity (README §3.1).
**Scaffolds:** `HEEqPW.phaseDeriv_mul_sq_ge` states `∃ c > 0, ∀ x, c ≤ κ x`; `_le` states `∃ C, ∀ x, κ x ≤ C` (with `C = π/c₁`).
Only the upper bound uses `hPW` (the pointwise bound); `_ge` has no `hPW` argument (NOTEBOOK I-03).
(*Paper:* "`1 = sup_{‖f‖² ≤ 1}|f(x)|² ≃ … = K_E(x,x) = (1/π)φ_E'|E|²`" — the middle `sup |f(x)|` is missing its square (p. 796, NOTEBOOK N-05) and the identification `K_E(x,x)` uses Theorem D, which for strict `E` without real zeros is avoided here, see README §3.1.)

## 11. The "evident fact" of p. 799

**Standing.** `E ∈ \overline{HB}`, `c > 0`, `c e^{π y} ≤ ‖E z‖ ≤ C e^{π y}` for `Im z = y ≥ 0`. Then `0 < c ≤ ‖E(0)‖ ≤ C`, `E ≠ 0` on `{Im ≥ 0}` (in particular on `ℝ`),
and for real `t`: `c ≤ ‖E t‖ ≤ C`.

```lean
/-- `PW ⊆ H(E)` with `‖f‖²_E ≤ c⁻² ‖f‖²` and `‖f‖²_E ≥ C⁻² ‖f‖²`. -/
theorem memHE_of_memPW (hPW : PaleyWienerThm) {E : ℂ → ℂ} (hE : IsHB E) {c C : ℝ} (hc : 0 < c)
    (hcomp : ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im))
    {f : ℂ → ℂ} (hf : MemPW f) :
    MemHE E f ∧ heNormSq E f ≤ ENNReal.ofReal (c ^ 2)⁻¹ * pwNormSq f ∧
      ENNReal.ofReal (C ^ 2)⁻¹ * pwNormSq f ≤ heNormSq E f := by
  sorry
```
Proof. Let `f ∈ PW`, `N = pwNormSq f < ∞` (`pwNormSq_ne_top`).
* `f` entire. `f/E`, `f^*/E` are differentiable on `ℂ₊` (`E ≠ 0` there).
* Line integrals for `y > 0` (`pw_line_integral_le`, with `|y| = y`): `L(f/E, y) ≤ ∫⁻ ‖f(x+iy)‖ₑ²/(c² e^{2πy})
 = (c² e^{2πy})⁻¹ L(f,y) ≤ (c² e^{2πy})⁻¹ e^{2πy} N = c⁻² N` (`‖E(x+iy)‖ ≥ c e^{πy}`, `lintegral_mono`, `lintegral_const_mul`,
 `ENNReal.ofReal` arithmetic). Same for `f^*` (`MemPW.fstar`; `f^*∈PW`, `pwNormSq` of `f^*` is finite). So `IsH2Upper` holds with `C₀ = (c⁻² N).toNNReal`
 (resp. for `f^*`: `c⁻² · pwNormSq f^*`).
* Norm: on `ℝ`, `‖f t‖ₑ²/C² ≤ ‖f t/E t‖ₑ² ≤ ‖f t‖ₑ²/c²` (`c ≤ ‖E t‖ ≤ C`), integrate:
 `C⁻² N ≤ ‖f‖²_E ≤ c⁻² N`.
(*This is the paper's* "`f/E = (f e^{iπz})(e^{−iπz}/E)`" *with* `e^{-iπz}/E` *bounded on* `ℂ₊`; using `pw_line_integral_le` avoids `H²` of `f e^{iπ z}`.)

```lean
/-- `H(E) ⊆ PW` with `‖f‖²_{PW} ≤ C² ‖f‖²_E`. -/
theorem memPW_of_memHE {E : ℂ → ℂ} (hE : IsHB E) {c C : ℝ} (hc : 0 < c)
    (hcomp : ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im))
    {f : ℂ → ℂ} (hf : MemHE E f) :
    MemPW f ∧ pwNormSq f ≤ ENNReal.ofReal (C ^ 2) * heNormSq E f := by
  sorry
```
Proof. Let `f ∈ H(E)`, with `H²` bounds `M₁` for `G₁ = f/E` and `M₂` for `G₂ = f^*/E` (`M = max`, `ℝ≥0∞`, finite).
**Step 1 (real axis; Fatou).** For real `x`, `E x ≠ 0`, `f, E` continuous, so `G₁(x + i/n) → f(x)/E(x)` as `n → ∞`; thus
`‖f x/E x‖ₑ² = liminf_n ‖G₁(x + i/n)‖ₑ²`. Fatou (`lintegral_liminf_le`, measurability from continuity of `f/E` on the closed upper half-plane) gives
`heNormSq E f = ∫⁻ ‖f(x)/E(x)‖ₑ² ≤ liminf_n L(G₁, 1/n) ≤ M₁`. (This is the **only** place where the real axis is related to the `H²` line integrals;
no boundary-value theory is needed since `f` and `E` are entire.) As `‖E x‖ ≤ C`: `pwNormSq f = ∫⁻ ‖f x‖ₑ² ≤ C² ‖f‖²_E ≤ C² M₁ < ∞`, so
`MemLp (fun x : ℝ ↦ f x) 2` (`f` continuous, hence a.e.-strongly measurable; `memLp_two_iff_integrable_sq_norm`, `ofReal_integral_eq_lintegral_ofReal` or
`MeasureTheory.memLp_two_iff…`). Also `pwNormSq f ≤ ofReal(C²) heNormSq E f`.
**Step 2 (all lines in `|s| ≤ 2`).** Put `K₀ = C² e^{4π} M`. For `0 < s ≤ 2`: `‖E(x+is)‖ ≤ C e^{πs} ≤ C e^{2π}`, so
`L(f, s) ≤ C² e^{4π} L(G₁, s) ≤ K₀`. For `−2 ≤ s < 0`: `‖f(x+is)‖ = ‖f^*(x − is)‖` and
`‖E(x−is)‖ ≤ C e^{2π}` (`−s ∈ (0,2]`), so `L(f, s) = L(f^*, −s) ≤ C² e^{4π} L(G₂, −s) ≤ K₀` (translation invariance of the sum over `x`; the change `x ↦ x` is trivial
since `fstar` conjugates but does not move the real coordinate: `f^*(x − is) = conj f(x + is)`).
*Implemented:* only the lines `0 < |s| < 2` are used; `s = 0` is a null set (`HB/Comparable.lean`).
**Step 3 (bounded on `|Im z| ≤ 1`).** `enorm_sq_le_of_lines` (§1.3) with `r = 1` (the strip `(Im z − 1, Im z + 1) ⊆ (−2,2)`): `‖f z‖ₑ² ≤ ofReal(2/π) K₀ =: K₁`.
**Step 4 (`|Im z| ≥ 1`).** For `y = Im z ≥ 1`: `IsH2Upper.enorm_sq_le` gives `‖G₁ z‖² ≤ 4M/(π y) ≤ 4M/π` and
`‖f z‖ = ‖G₁ z‖‖E z‖ ≤ 2 √(M/π) C e^{π y}`. For `y ≤ −1`: `‖f z‖ = ‖f^*(z̄)‖ = ‖G₂(z̄)‖‖E(z̄)‖ ≤ 2√(M/π) C e^{π|y|}`.
**Step 5 (exponential type).** With `K = max(√K₁, 2C√(M/π))`: `‖f z‖ ≤ K e^{π |Im z|} ≤ K e^{(π+ε)‖z‖}` for every `ε > 0`
(`|Im z| ≤ ‖z‖`, `Complex.abs_im_le_norm`). That is `IsExpTypeLE π f`. Together with Step 1, `MemPW f`. ∎
Constants depend on `c, C` and on `M`, but the **norm inequality** `‖f‖²_{PW} ≤ C²‖f‖²_E` does not depend on `M`.

```lean
/-- **The "evident fact"** (p. 799): if `E ∈ \overline{HB}` and `|E(z)| ≃ e^{π Im z}` for
`Im z ≥ 0`, then `H(E) = PW`. -/
theorem heEqPW_of_comparable (hPW : PaleyWienerThm) {E : ℂ → ℂ} (hE : IsHB E)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) :
    HEEqPW E := by
  sorry
```
Proof. `E` entire (`hE.1`); obtain `c, C` from `hcomp`. The set equality `MemHE E f ↔ MemPW f` is `memHE_of_memPW` and `memPW_of_memHE`. Norm equivalence (`c', C' : ℝ≥0` in `HEEqPW`):
`C⁻² ‖f‖²_{PW} ≤ ‖f‖²_E ≤ c⁻² ‖f‖²_{PW}`, i.e. `c' = (C²)⁻¹.toNNReal`, `C' = (c²)⁻¹.toNNReal`, `0 < c'` since `C > 0`
(`C ≥ c > 0` from `z = 0`). (`‖f‖²_E ≥ C⁻²‖f‖²` uses only `‖E t‖ ≤ C`.) The statement coincides exactly with `comparator/statements.lean`
(namespace `FF`, hypothesis names `hPW hE hcomp`). The hypotheses `IsHB E` is used only through `Differentiable ℂ E`; the lower bound `c e^{πy} ≤ |E|` supplies `E ≠ 0` on `ℂ₊`.

---

## 12. Issues in the source (M02 and the parts of §3, §4 it supports)

1. **p. 796 (proof of Theorem 1, first line of the converse).** "*The function `E` has no zeros on the real axis since `PW = H(E)`.*"
 Unproved; true, and the proof is not obvious: it needs the blow-up estimate `∫|f/E(x+iy)|²dx ≳ 1/y` of §1.5. (Fix: `HEEqPW.ne_zero_ofReal`.) *Sure.*
2. **p. 794–796, strictness of `E`.** Theorem E (as quoted) is applied to `E` with `H(E) = PW` without remarking that `E` must lie in de Branges' strict
 class `HB` (`|E(z̄)| < |E(z)|`) — for `E^* = cE` the space `H(E)` is `{0}` and Theorem E is false (an interpolation problem cannot be solved). That
 `H(E) = PW ≠ {0}` implies strictness is proved in `HEEqPW.isStrictHB` (§9) via Liouville for `L²`-on-lines. Also `φ_E' > 0` (needed to
 enumerate `Γ` as `{γ_k}`, and for `K_E(x,x) = φ'|E|²/π`) is not discussed; it requires a Hopf-type argument (§5.2). *Sure.*
3. **p. 796, "`φ'_{EF} = φ'_E + φ'_F ≥ φ'_E`".** Uses `φ_F' ≥ 0` for `F ∈ \overline{HB}` (§5.1; elementary) and the existence of `φ_F` for `F`
 without real zeros (§4). The paper's earlier phrase "`φ_{EF} = φ_E + φ_F ≥ φ_E`" in the README seeds is about derivatives. Also `Λ_α` interlaces `Λ`
 (p. 796) requires `φ_E + φ_F` strictly increasing: `φ_E' > 0` (§5.2) and `φ_F' ≥ 0`; the claim "`Λ = Λ_{π/2}`" is `zero_set_eq_phaseLevel`
 (§6), which needs strictness of `E` to exclude non-real zeros. *Sure.*
4. **p. 796, `1 = sup_{‖f‖² ≤ 1} |f(x)|² ≃ sup |f(x)| = K_E(x,x) = (1/π) φ_E'(x)|E(x)|²`** (README §4a: missing square, harmless): also the first
 identity `sup_{‖f‖_PW ≤ 1}|f(x)|² = 1` is the sharp form of `pw_norm_sq_le`; our proof (§10) needs only `|f(x)|² ≤ ‖f‖²` and a fixed bump. Theorem D is not needed
 (README §3.1). *Sure.*
5. **p. 799 "evident fact".** True (§11) but not evident: (a) `⊇`: `f ∈ H(E)` gives only `sup_y ∫|f/E(x+iy)|²`; to get `f ∈ L²(ℝ)` one needs
 Fatou along `y ↓ 0` (§11, Step 1; `E` has no real zeros because of the lower bound); (b) exponential type `≤ π` needs both pointwise `H²`
 bounds (`|g(z)|² ≲ ‖g‖²/Im z`) *and* a separate argument in the strip `|Im z| ≤ 1`, where `f/E` gives no pointwise control (the area mean-value inequality
 on discs of radius `1` crossing the real axis, using the `L²` bounds on all lines in `[−2,2]`). *Sure* (this is a complete proof).
6. **p. 793, definition of `H(E)`.** For `E` with real zeros, `heNormSq` (`∫|f(t)/E(t)|²dt`) is the paper's norm only if `E ≢ 0` on `ℝ` a.e.; fine since real zeros of an entire `E ≢ 0` are
 discrete (§7). `‖Ff‖_{EF} = ‖f‖_E` for `F ∈ \overline{HB}` (p. 796) requires that `|F^*/F| ≤ 1` and the line-integral definition of `H²`, as in §7; the paper says "For every `f ∈ H(E)` the
 function `g = Ff` belongs to `H(EF)` with `‖f‖_{H(E)} = ‖Ff‖_{H(EF)}`" — correct, no gap. *Sure.*
7. **Theorem E (p. 794) "at most one `α` modulo `π`".** Fine and easy (§8: two lines subtract to a constant). *Sure.*

## 13. Requested changes to M00
None are necessary. Observations (no action required):
* `IsHB`, `IsStrictHB`, `MemHE`, `heNormSq`, `HEEqPW`, `IsPhaseFunction`, `phaseDeriv` are exactly what the proofs above need. In `HEEqPW` the constants
 `c C : ℝ≥0` are allowed to be anything with `0 < c`; `C = 0` forces `pwNormSq = 0` — harmless.
* `TheoremE` is used in the form `hE E hstrict hnz φ hφ α hnotmem` and only for `H(E) = PW` (infinite dimensional); no issue.
* `IsH2Upper` does not mention boundary values; this is consistent (and is why `memPW_of_memHE` needs the Fatou step).
* Suggestion (optional): a `@[simp]` lemma `FF.fstar_apply` is in `Basic.lean`; `fstar` being a `def` in `Defs.lean` is convenient and should stay.

## 14. Mathlib names checked (v4.35.0)
`DifferentiableAt.conj_conj`, `deriv_conj_conj` (`Analysis/Calculus/Deriv/Star.lean`); `HasDerivAt.norm_sq` (`InnerProductSpace/Calculus.lean`);
`IsLocalMaxOn.hasFDerivWithinAt_nonpos`, `mem_posTangentConeAt_of_segment_subset` (`LocalExtr/Basic.lean`) (these three are
not used by the implementation, see §4 and §5.1);
`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`, `Complex.norm_le_of_forall_mem_frontier_norm_le` (`AbsMax.lean`);
`TendstoLocallyUniformlyOn.differentiableOn` (`Complex/LocallyUniformLimit.lean`);
`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`,
`AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected` (`Analytic/IsolatedZeros.lean`);
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, `AnalyticOnNhd.eq_of_eventuallyEq` (`Analytic/Uniqueness.lean`);
`DiffContOnCl.circleAverage` (`Complex/MeanValue.lean`); `Complex.integral_comp_polarCoord_symm` (`SpecialFunctions/PolarCoord.lean`);
`Complex.volume_preserving_equiv_real_prod`, `lintegral_liminf_le`, `Complex.exp_eq_exp_iff_exists_int`, `Real.cos_eq_zero_iff`,
`Set.Countable.dense_compl`, `Set.Countable.preimage_of_injOn`, `strictMono_of_deriv_pos`, `is_const_of_deriv_eq_zero`,
`Convex.norm_image_sub_le_of_norm_deriv_le`, `HasDerivAt.comp_ofReal`, `Continuous.integral_hasStrictDerivAt`,
`Complex.norm_mul_exp_arg_mul_I`, `memLp_two_iff_integrable_sq_norm`, `Differentiable.contDiff`, `IsCompact.exists_bound_of_continuousOn`.
No Hurwitz theorem and no Hardy-space or disc-mean-value-inequality exists in Mathlib; both are replaced by the arguments in §3.2 and §1.2.
