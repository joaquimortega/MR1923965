import FourierFrames.HB.Phase
import OrtegaCerdaSeip.Lemma3.Main
import FourierFrames.Construction.Gaps

/-!
# M07 — The phase construction `E = A - iB` (p. 801)

See `blueprint/M07_Corollary2.md`, §2.

For a density `a ≤ m ≤ b` with `m → 1` at `±∞`, let `Γ = {γ_j}` be the barycentre sequence of
`[OS99, Lemma 3]` (`OCS.multGamma m`), `A = OCS.multF m 0` the associated real entire function with
simple zero set `Γ`, `B(z) = A(z - 1/2) P(z) / Q(z)` its companion (finitely many zeros moved so
that the zeros of `A` and `B` interlace) and `E = A - i B`.

* `exists_hb_of_density` (needs only the "shift" condition `U(z - 1/2) - U(z) = O(1)`): `E` is in
  `\overline{HB}`, has no real zeros, `|E| ≃ e^{U}` on `Im z ≥ 0` and `E + E^* = 2A` has zero set `Γ`.
* `exists_hb_of_density_phase` (needs `U - π Im z - κ Re z = O(1)` for some real `κ`): after the
  normalisation `E ↦ e^{-κ z} E`, `|E| ≃ e^{π Im z}`, and the phase of `E` satisfies
  `φ_E - π M → c₀` (`M = OCS.multPrim m`).  `κ ≠ 0` is the general case (M06).

**Deviation from `README.md` §4.**  The phase clause of the README's `exists_hb_of_density`
(for all `m → 1`) is not provable: it requires `U - π Im z - κ Re z` to be bounded (see the
blueprint, §0.2).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## A real exponential factor preserves `\overline{HB}` -/

/-- `z ↦ e^{β + c z}` (`c` real) is in `\overline{HB}`: `|e^{β + c z̄}| = |e^{β + c z}|`. -/
theorem isHB_cexp_real_linear (β : ℂ) (c : ℝ) :
    IsHB (fun z : ℂ ↦ Complex.exp (β + c * z)) := by
  refine ⟨by fun_prop, fun z _ ↦ Complex.exp_ne_zero _, fun z _ ↦ le_of_eq ?_⟩
  simp only [Complex.norm_exp, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  simp

/-! ## Gaps of `Γ` and the position of `γ_j` inside `I_j` -/

section Gaps

variable {m : ℝ → ℝ} {a b : ℝ}

/-- If `m → 1` then `|I_j| → 1`, `γ_j - x_j → 1/2` and hence `γ_{j+1} - γ_j → 1` as `|j| → ∞`. -/
theorem tendsto_multBary_sub_multPt (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    Tendsto (fun j : ℤ ↦ OCS.multBary m j - OCS.multPt m j) cofinite (𝓝 (1 / 2)) := Gaps.tendsto_multBary_sub_multPt hw hlim

theorem tendsto_multBary_succ_sub (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    Tendsto (fun j : ℤ ↦ OCS.multBary m (j + 1) - OCS.multBary m j) cofinite (𝓝 1) := Gaps.tendsto_multBary_succ_sub hw hlim

/-- `M(γ_j) = j + 1/2 + o(1)`. -/
theorem tendsto_multPrim_multBary (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    Tendsto (fun j : ℤ ↦ OCS.multPrim m (OCS.multBary m j) - (j + 1 / 2)) cofinite (𝓝 0) := Gaps.tendsto_multPrim_multBary hw hlim

/-- `M(x + τ) - M(x) → τ` uniformly in `|τ| ≤ T` as `|x| → ∞`. -/
theorem tendsto_multPrim_sub (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) (T : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ |x| → ∀ τ : ℝ, |τ| ≤ T →
      |OCS.multPrim m (x + τ) - OCS.multPrim m x - τ| ≤ ε := Gaps.tendsto_multPrim_sub hw hlim T

/-- There is `N` such that `γ_{j+1} - γ_j > 1/2` for `|j| ≥ N`, i.e. `γ_j + 1/2 ∈ (γ_j, γ_{j+1})`. -/
theorem exists_gap_index (hw : OCS.IsMultWeight m a b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) :
    ∃ N : ℕ, ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j := Gaps.exists_gap_index hw hlim

end Gaps

/-! ## Division by finitely many simple zeros -/

/-- `∏_{t ∈ l} (z - t)`. -/
def prodLin (l : List ℂ) (z : ℂ) : ℂ :=
  (l.map fun t ↦ z - t).prod

/-- `F(z) / ∏_{t ∈ l} (z - t)` for an entire `F` vanishing at the distinct points of `l`,
by iterating `dslope`. -/
def divZeros : List ℂ → (ℂ → ℂ) → ℂ → ℂ
  | [], F => F
  | a :: l, F => divZeros l (dslope F a)

/-- `divZeros l F` is entire. -/
theorem differentiable_divZeros (l : List ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (divZeros l F) := by
  sorry

/-- `(divZeros l F) z * ∏ (z - t) = F z` if `l` has no repetitions and `F` vanishes on `l`. -/
theorem divZeros_mul_prodLin {l : List ℂ} (hl : l.Nodup) {F : ℂ → ℂ} (hF : ∀ t ∈ l, F t = 0)
    (z : ℂ) : divZeros l F z * prodLin l z = F z := by
  sorry

/-- `divZeros` commutes with complex conjugation of real-symmetric data
(`F^* = F`, all `t ∈ l` real). -/
theorem divZeros_conj {l : List ℂ} (hl : ∀ t ∈ l, t.im = 0) {F : ℂ → ℂ}
    (hF : ∀ z, F (conj z) = conj (F z)) (z : ℂ) :
    divZeros l F (conj z) = conj (divZeros l F z) := by
  sorry

/-! ## The companion `B` -/

section Companion

variable (m : ℝ → ℝ)

/-- The generating function `A = OCS.multF m 0` of `Γ = {γ_j}`. -/
abbrev genA (z : ℂ) : ℂ := OCS.multF m 0 z

/-- The prescribed zeros `β_j` of `B`: `γ_j + 1/2` for `|j| ≥ N`, the midpoint of `(γ_j, γ_{j+1})`
for `|j| < N`. -/
def compBeta (N : ℕ) (j : ℤ) : ℝ :=
  if |j| < N then (OCS.multBary m j + OCS.multBary m (j + 1)) / 2 else OCS.multBary m j + 1 / 2

/-- The zeros `γ_j + 1/2`, `|j| < N`, of `A(z - 1/2)` that are removed. -/
def compRemoved (N : ℕ) : List ℂ :=
  ((Finset.Ioo (-(N : ℤ)) N).toList).map fun j ↦ ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)

/-- The companion `B(z) = A(z - 1/2) P(z) / Q(z)` with
`P(z) = ∏_{|j|<N} (z - β_j)` and `Q(z) = ∏_{|j|<N} (z - γ_j - 1/2)`. -/
def compB (N : ℕ) (z : ℂ) : ℂ :=
  divZeros (compRemoved m N) (fun w ↦ genA m (w - 1 / 2)) z *
    ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ))

/-- `E = A - i B`. -/
def compE (N : ℕ) (z : ℂ) : ℂ :=
  genA m z - Complex.I * compB m N z

/-- The drift-normalised `E_κ = e^{-κ z}(A - i e^{κ/2} B) = A_κ - i B_κ` with `A_κ = e^{-κ z} A`,
`B_κ = A_κ(· - 1/2) P/Q`.  (`e^{-κ z} E` alone is *not* right for the phase when `κ ≠ 0`: `A` and
`B = A(· - 1/2) P/Q` have amplitude ratio `e^{-κ/2}`, so the phase of `e^{-κ z}(A - iB)` does not
satisfy `φ - π M → c₀`.) -/
def compEκ (κ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-((κ : ℂ) * z)) * (genA m z - Complex.I * Real.exp (κ / 2) * compB m N z)

end Companion

section CompanionLemmas

variable {m : ℝ → ℝ} {a b : ℝ}

/-- Interlacing: `γ_j < β_j < γ_{j+1}` for all `j` (given the choice of `N`). -/
theorem compBeta_interlace (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) (j : ℤ) :
    OCS.multBary m j < compBeta m N j ∧ compBeta m N j < OCS.multBary m (j + 1) := by
  sorry

theorem differentiable_compB (hw : OCS.IsMultWeight m a b) (N : ℕ) :
    Differentiable ℂ (compB m N) := by
  sorry

theorem compB_conj (hw : OCS.IsMultWeight m a b) (N : ℕ) (z : ℂ) :
    compB m N (conj z) = conj (compB m N z) := by
  sorry

/-- The zero set of `B` is `{β_j}`, all simple. -/
theorem compB_eq_zero_iff (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) (z : ℂ) :
    compB m N z = 0 ↔ ∃ j : ℤ, z = (compBeta m N j : ℂ) := by
  sorry

/-- `B(z) = A(z - 1/2) P(z) / Q(z)` off the zeros of `Q`; in particular `B(z) / A(z - 1/2) → 1`
as `|z| → ∞` away from `ℝ`-neighbourhoods of `Γ + 1/2`. -/
theorem compB_mul_Q (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) (z : ℂ) :
    compB m N z * ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)) =
      genA m (z - 1 / 2) * ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ)) := by
  sorry

/-- `|A| ≃ e^U` for `|Im z| ≥ 1` (estimate (3)) and `|A| e^{-U} ≃ dist(z, Γ)` for `|Im z| ≤ 1`
(estimate (2)), repackaged: for all `z`,
`c₁ e^{U} min(1, dist(z,Γ)) ≤ |A| ≤ c₂ e^{U} min(1, dist(z,Γ))`. -/
theorem norm_genA_comparable (hw : OCS.IsMultWeight m a b) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℂ,
      c₁ * Real.exp (OCS.multU m 0 z) * min 1 (infDist z (OCS.multGammaC m)) ≤ ‖genA m z‖ ∧
      ‖genA m z‖ ≤ c₂ * Real.exp (OCS.multU m 0 z) * min 1 (infDist z (OCS.multGammaC m)) := by
  sorry

/-- **Polynomial Hermite–Biehler**: if `a_0 < b_0 < a_1 < b_1 < … < a_n < b_n` are real then
`∏ (z - b_k)/(z - a_k)` has positive imaginary part on `Im z > 0` (the arguments of the factors add
up to a number in `(0, π)`). -/
theorem im_prod_div_pos {n : ℕ} {a b : Fin (n + 1) → ℝ}
    (hab : ∀ k, a k < b k) (hba : ∀ k : Fin n, b k.castSucc < a k.succ) {z : ℂ} (hz : 0 < z.im) :
    0 < (∏ k, ((z - b k) / (z - a k))).im := by
  sorry

end CompanionLemmas

/-! ## `E ∈ \overline{HB}` and the main construction -/

section Main

variable {m : ℝ → ℝ} {a b : ℝ}

/-- The real polynomial `A_R(z) = ∏_{|j| ≤ R} (1 - z/γ_j)`. -/
def polyA (m : ℝ → ℝ) (R : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.Icc (-(R : ℤ)) R, (1 - z / (OCS.multBary m j : ℂ))

/-- The real polynomial `B_R(z) = A_R(z - 1/2) P(z) / Q(z)`, written without division:
`∏_{|j| < N} ((-1/γ_j)(z - β_j)) · ∏_{N ≤ |j| ≤ R} (1 - (z - 1/2)/γ_j)`. -/
def polyB (m : ℝ → ℝ) (N R : ℕ) (z : ℂ) : ℂ :=
  (∏ j ∈ Finset.Ioo (-(N : ℤ)) N, ((-1 / (OCS.multBary m j : ℂ)) * (z - (compBeta m N j : ℂ)))) *
    ∏ j ∈ Finset.Icc (-(R : ℤ)) R \ Finset.Ioo (-(N : ℤ)) N,
      (1 - (z - 1 / 2) / (OCS.multBary m j : ℂ))

/-- The exponent `c_R = ∑_{|j| ≤ R} 1/γ_j - κ`. -/
def polyExp (m : ℝ → ℝ) (R : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc (-(R : ℤ)) R, 1 / OCS.multBary m j) - OCS.multKappa m

/-- For `R ≥ N`: `polyB · Q = polyA(· - 1/2) · P`, i.e. `B_R = A_R(z - 1/2) P/Q`. -/
theorem polyB_mul_Q (hw : OCS.IsMultWeight m a b) {N R : ℕ} (hNR : N ≤ R) (z : ℂ) :
    polyB m N R z * ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)) =
      polyA m R (z - 1 / 2) * ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ)) := by
  sorry

/-- `A_R` and `B_R` have interlacing real zeros (`γ_j < β_j < γ_{j+1}`) and equal leading
coefficients, so for every `λ > 0`, `A_R - i λ B_R ∈ \overline{HB}` (`im_prod_div_pos`). -/
theorem isHB_polyA_sub_polyB (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) {R : ℕ}
    (hNR : N ≤ R) {lam : ℝ} (hlam : 0 < lam) :
    IsHB (fun z ↦ polyA m R z - Complex.I * lam * polyB m N R z) := by
  sorry

/-- `e^{β + c_R z} A_R(z) → A(z)` locally uniformly (symmetric partial products of the genus-one
product `OCS.multF`). -/
theorem tendsto_polyA (hw : OCS.IsMultWeight m a b) :
    TendstoLocallyUniformly
      (fun (R : ℕ) (z : ℂ) ↦ Complex.exp (OCS.multBeta m 0 + polyExp m R * z) * polyA m R z)
      (genA m) atTop := by
  sorry

/-- `e^{β + c_R z} e^{-c_R/2} B_R(z) → B(z)` locally uniformly. -/
theorem tendsto_polyB (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) :
    TendstoLocallyUniformly
      (fun (R : ℕ) (z : ℂ) ↦ Complex.exp (OCS.multBeta m 0 + polyExp m R * z) *
        Real.exp (-polyExp m R / 2) * polyB m N R z)
      (compB m N) atTop := by
  sorry

/-- `|B| ≃ e^{U(z - 1/2)} min(1, dist(z, {β_j}))` on `Im z ≥ 0`. -/
theorem norm_compB_comparable (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℂ, 0 ≤ z.im →
      c₁ * Real.exp (OCS.multU m 0 (z - 1 / 2)) *
          min 1 (infDist z (Set.range fun j : ℤ ↦ ((compBeta m N j : ℝ) : ℂ))) ≤
        ‖compB m N z‖ ∧
      ‖compB m N z‖ ≤ c₂ * Real.exp (OCS.multU m 0 (z - 1 / 2)) *
          min 1 (infDist z (Set.range fun j : ℤ ↦ ((compBeta m N j : ℝ) : ℂ))) := by
  sorry

/-- **`E = A - iB ∈ \overline{HB}`** (replaces Meĭman's theorem), via the real polynomials
`A_R = ∏_{|j| ≤ R} (1 - z/γ_j)` and the locally uniform limit
`e^{β + (S_R - κ) z} (A_R - i e^{-(S_R - κ)/2} B_R) → A - iB`. -/
theorem isHB_compE (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) :
    IsHB (compE m N) := by
  sorry

/-- `E_κ = e^{-κ z}(A - i e^{κ/2} B) ∈ \overline{HB}`: `A - i λ B ∈ \overline{HB}` for every `λ > 0`
(the proof of `isHB_compE` gives this, via `isHB_polyA_sub_polyB` for any positive multiplier),
and `e^{-κ z}` is a real entire factor (`isHB_cexp_real_linear`, `IsHB.mul`). -/
theorem isHB_compEκ (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) (κ : ℝ) :
    IsHB (compEκ m κ N) := by
  sorry

/-- `E_κ + E_κ^* = 2 e^{-κ z} A`. -/
theorem compEκ_add_fstar (hw : OCS.IsMultWeight m a b) (κ : ℝ) (N : ℕ) (z : ℂ) :
    compEκ m κ N z + fstar (compEκ m κ N) z = 2 * Complex.exp (-((κ : ℂ) * z)) * genA m z := by
  sorry

/-- `|E(z̄)|² - ...`: `E^* = A + i B`, hence `E + E^* = 2A`. -/
theorem fstar_compE (hw : OCS.IsMultWeight m a b) (N : ℕ) (z : ℂ) :
    fstar (compE m N) z = genA m z + Complex.I * compB m N z := by
  sorry

/-- `|A|² + |B|² ≤ |E|² ≤ 2 (|A|² + |B|²)` on `Im z ≥ 0` (from `|E^*| ≤ |E|`). -/
theorem norm_compE_sq_bounds {N : ℕ} (hE : IsHB (compE m N)) (hw : OCS.IsMultWeight m a b)
    {z : ℂ} (hz : 0 ≤ z.im) :
    ‖genA m z‖ ^ 2 + ‖compB m N z‖ ^ 2 ≤ ‖compE m N z‖ ^ 2 ∧
      ‖compE m N z‖ ^ 2 ≤ 2 * (‖genA m z‖ ^ 2 + ‖compB m N z‖ ^ 2) := by
  sorry

/-- **The phase construction of p. 801** (without phase asymptotics; replaces the first four
clauses of the README's `exists_hb_of_density`).  `hshift` is the condition
`U(z - 1/2) - U(z) = O(1)` on `Im z ≥ 0`, which is implied by `U - π Im z - κ Re z = O(1)` for some
real `κ` (with constant `2C + |κ|/2`). -/
theorem exists_hb_of_density (hm : Measurable m) (ha : 0 < a) (hlow : ∀ t, a ≤ m t)
    (hup : ∀ t, m t ≤ b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1))
    (hshift : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 (z - 1 / 2) - OCS.multU m 0 z| ≤ C) :
    ∃ E : ℂ → ℂ, IsHB E ∧ (∀ x : ℝ, E x ≠ 0) ∧
      (∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
        c * Real.exp (OCS.multU m 0 z) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (OCS.multU m 0 z)) ∧
      (∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ OCS.multGamma m, z = (γ : ℂ)) := by
  sorry

end Main

/-! ## Phase asymptotics -/

section Phase

variable {m : ℝ → ℝ} {a b : ℝ}

/-- `U` is even in `Im z`. -/
theorem multU_conj' (m : ℝ → ℝ) (z : ℂ) : OCS.multU m 0 (conj z) = OCS.multU m 0 z :=
  OCS.multU_conj m 0 z

/-- Under `hU` (with the linear drift `κ`), `|A(z)| ≃ e^{π |Im z| + κ Re z} min(1, dist(z, Γ))` on
all of `ℂ`.  (`A e^{-κ z}` is the normalised generating function.) -/
theorem norm_genA_comparable_of_hU (hw : OCS.IsMultWeight m a b) {κ : ℝ}
    (hU : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℂ,
      c₁ * Real.exp (Real.pi * |z.im| + κ * z.re) * min 1 (infDist z (OCS.multGammaC m)) ≤
        ‖genA m z‖ ∧
      ‖genA m z‖ ≤
        c₂ * Real.exp (Real.pi * |z.im| + κ * z.re) * min 1 (infDist z (OCS.multGammaC m)) := by
  sorry

/-- **Normal-family limit of the translates of `A`.**  If `|s_k| → ∞`, a subsequence of the
normalised translates `e^{-κ s_k} A(· + s_k)` converges locally uniformly to
`c e^{κ z} sin π(z - θ)` with `c ≠ 0` real (equivalently `A e^{-κ z}(· + s_k) → c sin π(· - θ)`;
the phase of `A` on `ℝ` is unaffected by the positive real factor `e^{κ x}`). -/
theorem genA_translate_limit (hw : OCS.IsMultWeight m a b)
    (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) {κ : ℝ}
    (hU : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C)
    {s : ℕ → ℝ} (hs : Tendsto (fun k ↦ |s k|) atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c θ : ℝ, c ≠ 0 ∧
      TendstoLocallyUniformly
        (fun k z ↦ genA m (z + s (φ k)) * Complex.exp (-((κ * s (φ k) : ℝ) : ℂ)))
        (fun z ↦ (c : ℂ) * Complex.exp ((κ : ℂ) * z) * Complex.sin (Real.pi * (z - θ))) atTop := by
  sorry

/-- **Local phase rigidity**: for a phase function `φ` of `E_κ = compEκ m κ N`,
`φ(s + τ) - φ(s) - π τ → 0` uniformly in `|τ| ≤ 2` as `|s| → ∞`. -/
theorem phase_rigidity (hw : OCS.IsMultWeight m a b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) {κ : ℝ}
    (hU : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j)
    {φ : ℝ → ℝ} (hφ : IsPhaseFunction (compEκ m κ N) φ) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ s : ℝ, X ≤ |s| → ∀ τ : ℝ, |τ| ≤ 2 →
      |φ (s + τ) - φ s - Real.pi * τ| ≤ ε := by
  sorry

/-- The phase function of `E` is strictly increasing and takes the values `π/2 + π ℤ` exactly on
`Γ`: `φ(γ_j) = π/2 + π (j + k₀)` for a fixed integer `k₀`. -/
theorem phase_levels (hw : OCS.IsMultWeight m a b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1)) {κ : ℝ}
    (hU : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j)
    {φ : ℝ → ℝ} (hφ : IsPhaseFunction (compEκ m κ N) φ) :
    StrictMono φ ∧ ∃ k₀ : ℤ, ∀ j : ℤ, φ (OCS.multBary m j) = Real.pi / 2 + Real.pi * (j + k₀) := by
  sorry

/-- **The phase construction with phase asymptotics** (generalised at assembly to a linear drift
`κ`).  If `U = π Im z + κ Re z + O(1)` on `Im z ≥ 0` (`κ ≠ 0` is the generic case, e.g. for the
example of p. 798), take `E = compEκ m κ N = e^{-κ z}(A - i e^{κ/2} B)` (the factor `e^{κ/2}`
compensates the amplitude ratio `e^{-κ/2}` of `A` and `B = A(· - 1/2) P/Q`; the plain twist
`e^{-κ z}(A - iB)` has the right modulus but not the right phase).  `E_κ + E_κ^* = 2 e^{-κ z} A` has
zero set `Γ`, `|E_κ| ≃ e^{π Im z}`, `E_κ ∈ \overline{HB}`, and the phase `φ` (with
`φ' = phaseDeriv E`, needed for the separation step of Corollary 2) satisfies `φ - π M → c₀`.  The
proof runs through the translates `e^{-κ s} A(· + s) → c e^{κ z} sin π(z - θ)`
(`genA_translate_limit`) and `E_κ(x + s) → i c e^{-iπ(x - θ)}`-type limits (`phase_rigidity`). -/
theorem exists_hb_of_density_phase (hm : Measurable m) (ha : 0 < a) (hlow : ∀ t, a ≤ m t)
    (hup : ∀ t, m t ≤ b) (hlim : Tendsto m (cocompact ℝ) (𝓝 1))
    (hU : ∃ κ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU m 0 z - Real.pi * z.im - κ * z.re| ≤ C) :
    ∃ E : ℂ → ℂ, IsHB E ∧ (∀ x : ℝ, E x ≠ 0) ∧
      (∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
        c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) ∧
      (∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ OCS.multGamma m, z = (γ : ℂ)) ∧
      ∃ φ : ℝ → ℝ, IsPhaseFunction E φ ∧ (∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x) ∧
        StrictMono φ ∧ ∃ c₀ : ℝ,
        Tendsto (fun x ↦ φ x - Real.pi * OCS.multPrim m x) (cocompact ℝ) (𝓝 c₀) := by
  sorry

end Phase

end FF
