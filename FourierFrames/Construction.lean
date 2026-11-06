import FourierFrames.HB.Phase
import OrtegaCerdaSeip.Lemma3.Main
import FourierFrames.Construction.Gaps
import FourierFrames.Construction.Comparable
import FourierFrames.Construction.PolyHB
import FourierFrames.Construction.Limits

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
  induction l generalizing F with
  | nil => exact hF
  | cons a l ih =>
    refine ih ?_
    intro z
    have h := (differentiableOn_dslope (s := (Set.univ : Set ℂ)) (c := a) (f := F)
      Filter.univ_mem).2 hF.differentiableOn
    exact (h z (Set.mem_univ z)).differentiableAt Filter.univ_mem

/-- `(divZeros l F) z * ∏ (z - t) = F z` if `l` has no repetitions and `F` vanishes on `l`. -/
theorem divZeros_mul_prodLin {l : List ℂ} (hl : l.Nodup) {F : ℂ → ℂ} (hF : ∀ t ∈ l, F t = 0)
    (z : ℂ) : divZeros l F z * prodLin l z = F z := by
  induction l generalizing F with
  | nil => simp [divZeros, prodLin]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have ha : F a = 0 := hF a (List.mem_cons_self ..)
    have h1 : ∀ t ∈ l, dslope F a t = 0 := by
      intro t ht
      have hta : t ≠ a := fun h ↦ hl.1 (h ▸ ht)
      rw [dslope_of_ne F hta, slope_def_field, hF t (List.mem_cons_of_mem _ ht), ha]
      simp
    have e := ih hl.2 h1
    have h2 := sub_smul_dslope F a z
    rw [ha, sub_zero, smul_eq_mul] at h2
    simp only [divZeros, prodLin, List.map_cons, List.prod_cons] at e ⊢
    rw [← h2, ← e]
    ring

/-- `divZeros` commutes with complex conjugation of real-symmetric data
(`F^* = F`, all `t ∈ l` real). -/
theorem divZeros_conj {l : List ℂ} (hl : ∀ t ∈ l, t.im = 0) {F : ℂ → ℂ}
    (hF : ∀ z, F (conj z) = conj (F z)) (z : ℂ) :
    divZeros l F (conj z) = conj (divZeros l F z) := by
  induction l generalizing F z with
  | nil => exact hF z
  | cons a l ih =>
    have ha : a.im = 0 := hl a (List.mem_cons_self ..)
    have hconja : conj a = a := Complex.conj_eq_iff_im.2 ha
    refine ih (fun t ht ↦ hl t (List.mem_cons_of_mem _ ht)) (fun w ↦ ?_) z
    by_cases hw : w = a
    · subst hw
      rw [hconja, dslope_same]
      have h1 : fstar F = F := by funext u; simp [fstar, hF u]
      have := deriv_fstar F w
      rw [h1, hconja] at this
      exact this
    · have hw' : conj w ≠ a := fun h ↦ hw (by rw [← hconja, ← h]; simp)
      rw [dslope_of_ne F hw', dslope_of_ne F hw, slope_def_field, slope_def_field,
        hF w]
      have haF : conj (F a) = F a := by
        have := hF a
        rw [hconja] at this
        exact this.symm
      simp only [map_div₀, map_sub, hconja, haF]

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

/-! ### Basic facts about `A` -/

theorem differentiable_genA (hw : OCS.IsMultWeight m a b) : Differentiable ℂ (genA m) :=
  OCS.differentiable_multF hw 0

theorem genA_conj (hw : OCS.IsMultWeight m a b) (z : ℂ) : genA m (conj z) = conj (genA m z) :=
  OCS.multF_conj hw 0 z

theorem genA_eq_zero_iff (hw : OCS.IsMultWeight m a b) (z : ℂ) :
    genA m z = 0 ↔ ∃ j : ℤ, z = (OCS.multBary m j : ℂ) := by
  rw [genA, OCS.multF_eq_zero_iff hw]
  constructor
  · rintro ⟨γ, ⟨j, rfl⟩, h⟩; exact ⟨j, h⟩
  · rintro ⟨j, h⟩; exact ⟨_, ⟨j, rfl⟩, h⟩

/-- The zeros of `A` are simple. -/
theorem genA_simple (hw : OCS.IsMultWeight m a b) {t : ℂ} (ht : genA m t = 0) :
    deriv (genA m) t ≠ 0 := by
  have hZ : t ∈ OCS.multGammaC m := by
    obtain ⟨j, rfl⟩ := (genA_eq_zero_iff hw t).1 ht
    exact ⟨_, ⟨j, rfl⟩, rfl⟩
  have hd := OCS.isGenusOneData_multGammaC hw
  have hP : OCS.canonicalProd (OCS.multGammaC m) (fun w ↦ w⁻¹) t = 0 :=
    (OCS.canonicalProd_eq_zero_iff hd).2 hZ
  have hP' := OCS.deriv_canonicalProd_ne_zero hd hZ
  have hdP : DifferentiableAt ℂ (OCS.canonicalProd (OCS.multGammaC m) (fun w ↦ w⁻¹)) t :=
    (OCS.differentiable_canonicalProd hd) t
  have hE : DifferentiableAt ℂ
      (fun z : ℂ ↦ Complex.exp (-(OCS.multKappa m : ℂ) * z + OCS.multBeta m 0)) t := by fun_prop
  have : genA m = fun z ↦ Complex.exp (-(OCS.multKappa m : ℂ) * z + OCS.multBeta m 0) *
      OCS.canonicalProd (OCS.multGammaC m) (fun w ↦ w⁻¹) z := rfl
  rw [this, deriv_fun_mul hE hdP, hP, mul_zero, zero_add]
  exact mul_ne_zero (Complex.exp_ne_zero _) hP'

theorem multBary_injective (hw : OCS.IsMultWeight m a b) : Function.Injective (OCS.multBary m) :=
  (OCS.strictMono_multBary hw).injective

/-! ### `Q` and the list `compRemoved` -/

/-- `∏_{|j|<N} (z - γ_j - 1/2)`. -/
def compQ (m : ℝ → ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ))

theorem prodLin_compRemoved (N : ℕ) (z : ℂ) : prodLin (compRemoved m N) z = compQ m N z := by
  unfold prodLin compRemoved compQ
  rw [List.map_map]
  exact Finset.prod_map_toList (Finset.Ioo (-(N : ℤ)) N) (fun j ↦ z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ))

theorem nodup_compRemoved (hw : OCS.IsMultWeight m a b) (N : ℕ) : (compRemoved m N).Nodup := by
  unfold compRemoved
  refine (Finset.nodup_toList _).map ?_
  intro i j h
  apply multBary_injective hw
  have := Complex.ofReal_injective h
  linarith

theorem compRemoved_im (N : ℕ) : ∀ t ∈ compRemoved m N, t.im = 0 := by
  intro t ht
  unfold compRemoved at ht
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 ht
  simp

theorem genA_shift_zero (hw : OCS.IsMultWeight m a b) (N : ℕ) :
    ∀ t ∈ compRemoved m N, genA m (t - 1 / 2) = 0 := by
  intro t ht
  unfold compRemoved at ht
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 ht
  rw [genA_eq_zero_iff hw]
  exact ⟨j, by push_cast; ring⟩

/-- `D · Q = A(· - 1/2)`. -/
theorem compD_mul_Q (hw : OCS.IsMultWeight m a b) (N : ℕ) (z : ℂ) :
    divZeros (compRemoved m N) (fun w ↦ genA m (w - 1 / 2)) z * compQ m N z =
      genA m (z - 1 / 2) := by
  rw [← prodLin_compRemoved]
  exact divZeros_mul_prodLin (nodup_compRemoved hw N) (genA_shift_zero hw N) z

theorem compB_conj_aux (hw : OCS.IsMultWeight m a b) (N : ℕ) (z : ℂ) :
    compB m N (conj z) = conj (compB m N z) := by
  unfold compB
  rw [map_mul, divZeros_conj (compRemoved_im N) (fun w ↦ ?_) z, map_prod]
  · congr 1
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    simp
  · rw [← genA_conj hw]
    have : conj w - 1 / 2 = conj (w - 1 / 2) := by
      rw [map_sub, map_div₀, map_one, map_ofNat]
    rw [this]

/-! ### Zeros of `divZeros` -/

/-- One step of `divZeros`: for `F` entire with simple zeros and `F a = 0`,
`dslope F a` has the same zeros except `a`, and these are again simple. -/
theorem dslope_step {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hs : ∀ t, F t = 0 → deriv F t ≠ 0)
    {a : ℂ} (ha : F a = 0) :
    (∀ z, dslope F a z = 0 ↔ F z = 0 ∧ z ≠ a) ∧
      ∀ t, dslope F a t = 0 → deriv (dslope F a) t ≠ 0 := by
  have hG : Differentiable ℂ (dslope F a) := by
    intro z
    have h := (differentiableOn_dslope (s := (Set.univ : Set ℂ)) (c := a) (f := F)
      Filter.univ_mem).2 hF.differentiableOn
    exact (h z (Set.mem_univ z)).differentiableAt Filter.univ_mem
  have hmul : ∀ z, (z - a) * dslope F a z = F z := fun z ↦ by
    have := sub_smul_dslope F a z
    rwa [ha, sub_zero, smul_eq_mul] at this
  have key : ∀ z, dslope F a z = 0 ↔ F z = 0 ∧ z ≠ a := by
    intro z
    by_cases hz : z = a
    · subst hz
      rw [dslope_same]
      simp only [ne_eq, not_true_eq_false, and_false, iff_false]
      exact hs z ha
    · simp only [hz, ne_eq, not_false_eq_true, and_true]
      rw [← hmul z]
      simp [sub_eq_zero, hz]
  refine ⟨key, fun t ht ↦ ?_⟩
  obtain ⟨hFt, hta⟩ := (key t).1 ht
  have hder : HasDerivAt F (dslope F a t + (t - a) * deriv (dslope F a) t) t := by
    have h1 : HasDerivAt (fun z ↦ (z - a) * dslope F a z)
        (1 * dslope F a t + (t - a) * deriv (dslope F a) t) t :=
      ((hasDerivAt_id t).sub_const a).mul (hG t).hasDerivAt
    have e : (fun z ↦ (z - a) * dslope F a z) = F := funext hmul
    rw [e, one_mul] at h1
    exact h1
  have := hs t hFt
  rw [hder.deriv, ht, zero_add] at this
  intro h0
  rw [h0, mul_zero] at this
  exact this rfl

theorem divZeros_zeros {l : List ℂ} (hl : l.Nodup) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hs : ∀ t, F t = 0 → deriv F t ≠ 0) (hF0 : ∀ t ∈ l, F t = 0) :
    (∀ z, divZeros l F z = 0 ↔ F z = 0 ∧ z ∉ l) ∧
      ∀ t, divZeros l F t = 0 → deriv (divZeros l F) t ≠ 0 := by
  induction l generalizing F with
  | nil => exact ⟨fun z ↦ by simp [divZeros], hs⟩
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have ha : F a = 0 := hF0 a (List.mem_cons_self ..)
    obtain ⟨hkey, hsG⟩ := dslope_step hF hs ha
    have hG : Differentiable ℂ (dslope F a) := by
      intro z
      have h := (differentiableOn_dslope (s := (Set.univ : Set ℂ)) (c := a) (f := F)
        Filter.univ_mem).2 hF.differentiableOn
      exact (h z (Set.mem_univ z)).differentiableAt Filter.univ_mem
    have hG0 : ∀ t ∈ l, dslope F a t = 0 := fun t ht ↦
      (hkey t).2 ⟨hF0 t (List.mem_cons_of_mem _ ht), fun h ↦ hl.1 (h ▸ ht)⟩
    obtain ⟨ih1, ih2⟩ := ih hl.2 hG hsG hG0
    refine ⟨fun z ↦ ?_, ih2⟩
    simp only [divZeros]
    rw [ih1 z, hkey z]
    simp only [List.mem_cons, not_or]
    tauto

theorem divZeros_eq_zero_iff {l : List ℂ} (hl : l.Nodup) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hs : ∀ t, F t = 0 → deriv F t ≠ 0) (hF0 : ∀ t ∈ l, F t = 0) (z : ℂ) :
    divZeros l F z = 0 ↔ F z = 0 ∧ z ∉ l :=
  (divZeros_zeros hl hF hs hF0).1 z

/-- Interlacing: `γ_j < β_j < γ_{j+1}` for all `j` (given the choice of `N`). -/
theorem compBeta_interlace (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) (j : ℤ) :
    OCS.multBary m j < compBeta m N j ∧ compBeta m N j < OCS.multBary m (j + 1) := by
  by_cases hj : |j| < N
  · have h := OCS.strictMono_multBary hw (lt_add_one j)
    simp only [compBeta, hj, ite_true]
    constructor <;> linarith
  · have h := hN j (not_lt.1 hj)
    simp only [compBeta, hj, ite_false]
    constructor <;> linarith

theorem differentiable_compB (hw : OCS.IsMultWeight m a b) (N : ℕ) :
    Differentiable ℂ (compB m N) := by
  unfold compB
  refine (differentiable_divZeros _ ?_).mul (by fun_prop)
  intro z
  exact ((differentiable_genA hw) (z - 1 / 2)).comp z (differentiableAt_id.sub_const _)

theorem compB_conj (hw : OCS.IsMultWeight m a b) (N : ℕ) (z : ℂ) :
    compB m N (conj z) = conj (compB m N z) := by
  exact compB_conj_aux hw N z

/-- The zero set of `B` is `{β_j}`, all simple. -/
theorem compB_eq_zero_iff (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) (z : ℂ) :
    compB m N z = 0 ↔ ∃ j : ℤ, z = (compBeta m N j : ℂ) := by
  have _ := hN
  have hFd : Differentiable ℂ (fun w ↦ genA m (w - 1 / 2)) := fun z ↦
    ((differentiable_genA hw) (z - 1 / 2)).comp z (differentiableAt_id.sub_const _)
  have hFs : ∀ t, genA m (t - 1 / 2) = 0 → deriv (fun w ↦ genA m (w - 1 / 2)) t ≠ 0 := by
    intro t ht
    have : deriv (fun w ↦ genA m (w - 1 / 2)) t = deriv (genA m) (t - 1 / 2) :=
      deriv_comp_sub_const (f := genA m) (a := 1 / 2) (x := t)
    rw [this]
    exact genA_simple hw ht
  have hD := divZeros_eq_zero_iff (nodup_compRemoved hw N) hFd hFs (genA_shift_zero hw N) z
  have hmemrem : z ∈ compRemoved m N ↔
      ∃ j ∈ Finset.Ioo (-(N : ℤ)) N, z = ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ) := by
    unfold compRemoved
    simp only [List.mem_map, Finset.mem_toList]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  have hFz : genA m (z - 1 / 2) = 0 ↔ ∃ k : ℤ, z = ((OCS.multBary m k + 1 / 2 : ℝ) : ℂ) := by
    rw [genA_eq_zero_iff hw]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, by push_cast; rw [← hk]; ring⟩
    · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; push_cast; ring⟩
  have hP : (∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ))) = 0 ↔
      ∃ j ∈ Finset.Ioo (-(N : ℤ)) N, z = (compBeta m N j : ℂ) := by
    rw [Finset.prod_eq_zero_iff]
    simp [sub_eq_zero]
  unfold compB
  rw [mul_eq_zero, hD, hP, hFz, hmemrem]
  constructor
  · rintro (⟨⟨k, hk⟩, hnot⟩ | ⟨j, hj, hz⟩)
    · refine ⟨k, ?_⟩
      have hk' : ¬ (|k| < N) := by
        intro hlt
        exact hnot ⟨k, Finset.mem_Ioo.2 (abs_lt.1 hlt), hk⟩
      simp only [compBeta, hk', ite_false]
      rw [hk]
    · exact ⟨j, hz⟩
  · rintro ⟨k, hk⟩
    by_cases hlt : |k| < N
    · right
      exact ⟨k, Finset.mem_Ioo.2 (abs_lt.1 hlt), hk⟩
    · left
      simp only [compBeta, hlt, ite_false] at hk
      refine ⟨⟨k, hk⟩, ?_⟩
      rintro ⟨j, hj, hjz⟩
      rw [hk] at hjz
      have := Complex.ofReal_injective hjz
      have hkj : k = j := multBary_injective hw (by linarith)
      subst hkj
      exact hlt (abs_lt.2 (Finset.mem_Ioo.1 hj))

theorem compBeta_of_not_lt {N : ℕ} {j : ℤ} (hj : j ∉ Finset.Ioo (-(N : ℤ)) N) :
    compBeta m N j = OCS.multBary m j + 1 / 2 := by
  have : ¬ (|j| < N) := by
    rw [abs_lt]; intro h; exact hj (Finset.mem_Ioo.2 h)
  simp [compBeta, this]

theorem compBeta_injective (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) :
    Function.Injective (compBeta m N) := by
  intro j k h
  by_contra hjk
  have hmono := (OCS.strictMono_multBary hw).monotone
  obtain ⟨hj1, hj2⟩ := compBeta_interlace hw hN j
  obtain ⟨hk1, hk2⟩ := compBeta_interlace hw hN k
  rcases lt_or_gt_of_ne hjk with hlt | hlt
  · have := hmono (show j + 1 ≤ k by omega); linarith
  · have := hmono (show k + 1 ≤ j by omega); linarith

/-- Simple zero of `P(z) = ∏_{j ∈ S} (z - β_j)` at `β_i`. -/
theorem deriv_compP_ne_zero (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) {i : ℤ}
    (hi : i ∈ Finset.Ioo (-(N : ℤ)) N) :
    deriv (fun z : ℂ ↦ ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ)))
      (compBeta m N i : ℂ) ≠ 0 := by
  have e : (fun z : ℂ ↦ ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ))) =
      fun z ↦ (z - (compBeta m N i : ℂ)) *
        ∏ j ∈ (Finset.Ioo (-(N : ℤ)) N).erase i, (z - (compBeta m N j : ℂ)) := by
    funext z
    rw [Finset.mul_prod_erase _ (fun j ↦ z - (compBeta m N j : ℂ)) hi]
  rw [e]
  have hG : Differentiable ℂ (fun z : ℂ ↦
      ∏ j ∈ (Finset.Ioo (-(N : ℤ)) N).erase i, (z - (compBeta m N j : ℂ))) := by fun_prop
  have h1 : HasDerivAt (fun z : ℂ ↦ (z - (compBeta m N i : ℂ)) *
      ∏ j ∈ (Finset.Ioo (-(N : ℤ)) N).erase i, (z - (compBeta m N j : ℂ)))
      (1 * ∏ j ∈ (Finset.Ioo (-(N : ℤ)) N).erase i, ((compBeta m N i : ℂ) - (compBeta m N j : ℂ)) +
        ((compBeta m N i : ℂ) - (compBeta m N i : ℂ)) * deriv (fun z : ℂ ↦
          ∏ j ∈ (Finset.Ioo (-(N : ℤ)) N).erase i, (z - (compBeta m N j : ℂ)))
          (compBeta m N i : ℂ)) (compBeta m N i : ℂ) :=
    ((hasDerivAt_id (compBeta m N i : ℂ)).sub_const (compBeta m N i : ℂ)).mul
      (hG (compBeta m N i : ℂ)).hasDerivAt
  rw [h1.deriv]
  simp only [sub_self, zero_mul, add_zero, one_mul]
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  rw [sub_ne_zero]
  intro h
  have := Complex.ofReal_injective h
  exact (Finset.ne_of_mem_erase hj) ((compBeta_injective hw hN this).symm)

/-- The zeros of `B` are simple. -/
theorem compB_simple (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) {t : ℂ}
    (ht : compB m N t = 0) : deriv (compB m N) t ≠ 0 := by
  have hFd : Differentiable ℂ (fun w ↦ genA m (w - 1 / 2)) := fun z ↦
    ((differentiable_genA hw) (z - 1 / 2)).comp z (differentiableAt_id.sub_const _)
  have hFs : ∀ t, genA m (t - 1 / 2) = 0 → deriv (fun w ↦ genA m (w - 1 / 2)) t ≠ 0 := by
    intro t ht
    have : deriv (fun w ↦ genA m (w - 1 / 2)) t = deriv (genA m) (t - 1 / 2) :=
      deriv_comp_sub_const (f := genA m) (a := 1 / 2) (x := t)
    rw [this]
    exact genA_simple hw ht
  obtain ⟨hD, hDs⟩ := divZeros_zeros (nodup_compRemoved hw N) hFd hFs (genA_shift_zero hw N)
  set D := divZeros (compRemoved m N) (fun w ↦ genA m (w - 1 / 2)) with hDdef
  set P : ℂ → ℂ := fun z ↦ ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ)) with hP
  have hDd : Differentiable ℂ D := differentiable_divZeros _ hFd
  have hPd : Differentiable ℂ P := by rw [hP]; fun_prop
  have hB : compB m N = fun z ↦ D z * P z := rfl
  have hPz : ∀ z, P z = 0 ↔ ∃ j ∈ Finset.Ioo (-(N : ℤ)) N, z = (compBeta m N j : ℂ) := by
    intro z
    rw [hP]
    simp only
    rw [Finset.prod_eq_zero_iff]
    simp [sub_eq_zero]
  have hmemrem : ∀ z, z ∈ compRemoved m N ↔
      ∃ j ∈ Finset.Ioo (-(N : ℤ)) N, z = ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ) := by
    intro z
    unfold compRemoved
    simp only [List.mem_map, Finset.mem_toList]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  have hder : deriv (compB m N) t = deriv D t * P t + D t * deriv P t := by
    rw [hB]; exact deriv_fun_mul (hDd t) (hPd t)
  rw [hB] at ht
  simp only at ht
  rw [hder]
  rcases mul_eq_zero.1 ht with h | h
  · -- D t = 0
    have hPt : P t ≠ 0 := by
      intro hP0
      obtain ⟨j, hj, rfl⟩ := (hPz t).1 hP0
      obtain ⟨hF, hnot⟩ := (hD _).1 h
      rw [genA_eq_zero_iff hw] at hF
      obtain ⟨k, hk⟩ := hF
      have hk' : (compBeta m N j : ℂ) = ((OCS.multBary m k + 1 / 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_add] ; push_cast at hk ⊢; rw [← hk]; ring
      have hkS : k ∉ Finset.Ioo (-(N : ℤ)) N := fun hkS ↦ hnot ((hmemrem _).2 ⟨k, hkS, hk'⟩)
      have : compBeta m N j = compBeta m N k := by
        rw [compBeta_of_not_lt hkS]; exact_mod_cast hk'
      exact hkS (compBeta_injective hw hN this ▸ hj)
    rw [h, zero_mul, add_zero]
    exact mul_ne_zero (hDs t h) hPt
  · -- P t = 0
    obtain ⟨j, hj, rfl⟩ := (hPz t).1 h
    have hDt : D (compBeta m N j : ℂ) ≠ 0 := by
      intro hD0
      obtain ⟨hF, hnot⟩ := (hD _).1 hD0
      exact hnot ((hmemrem _).2 (by
        rw [genA_eq_zero_iff hw] at hF
        obtain ⟨k, hk⟩ := hF
        have hk' : (compBeta m N j : ℂ) = ((OCS.multBary m k + 1 / 2 : ℝ) : ℂ) := by
          push_cast at hk ⊢; rw [← hk]; ring
        have hkS : k ∈ Finset.Ioo (-(N : ℤ)) N := by
          by_contra hkS
          have : compBeta m N j = compBeta m N k := by
            rw [compBeta_of_not_lt hkS]; exact_mod_cast hk'
          exact hkS (compBeta_injective hw hN this ▸ hj)
        exact ⟨k, hkS, hk'⟩))
    have hPs := deriv_compP_ne_zero hw hN hj
    rw [h, mul_zero, zero_add]
    exact mul_ne_zero hDt hPs

/-- `B(z) = A(z - 1/2) P(z) / Q(z)` off the zeros of `Q`; in particular `B(z) / A(z - 1/2) → 1`
as `|z| → ∞` away from `ℝ`-neighbourhoods of `Γ + 1/2`. -/
theorem compB_mul_Q (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) (z : ℂ) :
    compB m N z * ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)) =
      genA m (z - 1 / 2) * ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ)) := by
  have _ := hN
  have h := compD_mul_Q hw N z
  unfold compQ at h
  unfold compB
  rw [← h]
  ring

/-- `|A| ≃ e^U` for `|Im z| ≥ 1` (estimate (3)) and `|A| e^{-U} ≃ dist(z, Γ)` for `|Im z| ≤ 1`
(estimate (2)), repackaged: for all `z`,
`c₁ e^{U} min(1, dist(z,Γ)) ≤ |A| ≤ c₂ e^{U} min(1, dist(z,Γ))`. -/
theorem norm_genA_comparable (hw : OCS.IsMultWeight m a b) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℂ,
      c₁ * Real.exp (OCS.multU m 0 z) * min 1 (infDist z (OCS.multGammaC m)) ≤ ‖genA m z‖ ∧
      ‖genA m z‖ ≤ c₂ * Real.exp (OCS.multU m 0 z) * min 1 (infDist z (OCS.multGammaC m)) := by
  exact Comparable.norm_multF_comparable hw

/-- **Polynomial Hermite–Biehler**: if `a_0 < b_0 < a_1 < b_1 < … < a_n < b_n` are real then
`∏ (z - b_k)/(z - a_k)` has positive imaginary part on `Im z > 0` (the arguments of the factors add
up to a number in `(0, π)`). -/
theorem im_prod_div_pos {n : ℕ} {a b : Fin (n + 1) → ℝ}
    (hab : ∀ k, a k < b k) (hba : ∀ k : Fin n, b k.castSucc < a k.succ) {z : ℂ} (hz : 0 < z.im) :
    0 < (∏ k, ((z - b k) / (z - a k))).im := by
  exact im_prod_div_pos' hab hba hz

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

theorem multBary_ne_zero (hw : OCS.IsMultWeight m a b) (j : ℤ) : OCS.multBary m j ≠ 0 :=
  fun h ↦ OCS.zero_notMem_multGamma hw ⟨j, h⟩

theorem one_sub_div_eq (hw : OCS.IsMultWeight m a b) (j : ℤ) (w : ℂ) :
    1 - w / (OCS.multBary m j : ℂ) = (-1 / (OCS.multBary m j : ℂ)) * (w - OCS.multBary m j) := by
  have : (OCS.multBary m j : ℂ) ≠ 0 := by exact_mod_cast multBary_ne_zero hw j
  field_simp
  ring

theorem Ioo_subset_Icc {N R : ℕ} (hNR : N ≤ R) :
    Finset.Ioo (-(N : ℤ)) N ⊆ Finset.Icc (-(R : ℤ)) R := by
  intro j hj
  rw [Finset.mem_Ioo] at hj
  rw [Finset.mem_Icc]
  omega

theorem polyA_eq_prod (hw : OCS.IsMultWeight m a b) (R : ℕ) (z : ℂ) :
    polyA m R z = ∏ j ∈ Finset.Icc (-(R : ℤ)) R,
      ((-1 / (OCS.multBary m j : ℂ)) * (z - OCS.multBary m j)) := by
  unfold polyA
  exact Finset.prod_congr rfl fun j _ ↦ one_sub_div_eq hw j z

theorem polyB_eq_prod (hw : OCS.IsMultWeight m a b) {N R : ℕ} (hNR : N ≤ R) (z : ℂ) :
    polyB m N R z = ∏ j ∈ Finset.Icc (-(R : ℤ)) R,
      ((-1 / (OCS.multBary m j : ℂ)) * (z - (compBeta m N j : ℂ))) := by
  unfold polyB
  rw [← Finset.prod_sdiff (Ioo_subset_Icc hNR), mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_sdiff] at hj
  rw [compBeta_of_not_lt hj.2, one_sub_div_eq hw]
  push_cast
  ring

/-- For `R ≥ N`: `polyB · Q = polyA(· - 1/2) · P`, i.e. `B_R = A_R(z - 1/2) P/Q`. -/
theorem polyB_mul_Q (hw : OCS.IsMultWeight m a b) {N R : ℕ} (hNR : N ≤ R) (z : ℂ) :
    polyB m N R z * ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)) =
      polyA m R (z - 1 / 2) * ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ)) := by
  unfold polyB polyA
  have hsub := Ioo_subset_Icc hNR
  rw [← Finset.prod_sdiff hsub (f := fun j : ℤ ↦ (1 - (z - 1 / 2) / (OCS.multBary m j : ℂ)))]
  have e : ∀ j ∈ Finset.Ioo (-(N : ℤ)) N, (1 - (z - 1 / 2) / (OCS.multBary m j : ℂ)) =
      (-1 / (OCS.multBary m j : ℂ)) * (z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)) := by
    intro j _
    rw [one_sub_div_eq hw]
    push_cast
    ring_nf
  rw [Finset.prod_congr rfl e]
  set X := ∏ j ∈ Finset.Icc (-(R : ℤ)) R \ Finset.Ioo (-(N : ℤ)) N,
    (1 - (z - 1 / 2) / (OCS.multBary m j : ℂ))
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

theorem prod_Icc_eq_prod_fin (R : ℕ) (f : ℤ → ℂ) :
    ∏ j ∈ Finset.Icc (-(R : ℤ)) R, f j = ∏ k : Fin (2 * R + 1), f ((k : ℕ) - (R : ℤ)) := by
  symm
  refine Finset.prod_bij (fun k _ ↦ ((k : ℕ) : ℤ) - R) (fun k _ ↦ ?_) (fun k _ l _ h ↦ ?_)
    (fun j hj ↦ ?_) (fun _ _ ↦ rfl)
  · rw [Finset.mem_Icc]; have := k.isLt; omega
  · apply Fin.ext; omega
  · rw [Finset.mem_Icc] at hj
    exact ⟨⟨(j + R).toNat, by omega⟩, Finset.mem_univ _, by simp only; omega⟩

theorem polyA_conj (hw : OCS.IsMultWeight m a b) (R : ℕ) (z : ℂ) :
    polyA m R (conj z) = conj (polyA m R z) := by
  rw [polyA_eq_prod hw, polyA_eq_prod hw, map_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp [map_sub, map_div₀, Complex.conj_ofReal]

theorem polyB_conj (hw : OCS.IsMultWeight m a b) {N R : ℕ} (hNR : N ≤ R) (z : ℂ) :
    polyB m N R (conj z) = conj (polyB m N R z) := by
  rw [polyB_eq_prod hw hNR, polyB_eq_prod hw hNR, map_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp [map_sub, map_div₀, Complex.conj_ofReal]

/-- `A_R` and `B_R` have interlacing real zeros (`γ_j < β_j < γ_{j+1}`) and equal leading
coefficients, so for every `λ > 0`, `A_R - i λ B_R ∈ \overline{HB}` (`im_prod_div_pos`). -/
theorem isHB_polyA_sub_polyB (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) {R : ℕ}
    (hNR : N ≤ R) {lam : ℝ} (hlam : 0 < lam) :
    IsHB (fun z ↦ polyA m R z - Complex.I * lam * polyB m N R z) := by
  have hAd : Differentiable ℂ (polyA m R) := by
    intro z
    rw [show polyA m R = fun z ↦ ∏ j ∈ Finset.Icc (-(R : ℤ)) R,
      ((-1 / (OCS.multBary m j : ℂ)) * (z - OCS.multBary m j)) from
      funext (polyA_eq_prod hw R)]
    fun_prop
  have hBd : Differentiable ℂ (polyB m N R) := by
    intro z
    rw [show polyB m N R = fun z ↦ ∏ j ∈ Finset.Icc (-(R : ℤ)) R,
      ((-1 / (OCS.multBary m j : ℂ)) * (z - (compBeta m N j : ℂ))) from
      funext (polyB_eq_prod hw hNR)]
    fun_prop
  have hc : ∀ j : ℤ, (-1 / (OCS.multBary m j : ℂ)) ≠ 0 := fun j ↦ by
    have : (OCS.multBary m j : ℂ) ≠ 0 := by exact_mod_cast multBary_ne_zero hw j
    simp [this]
  have hA0 : ∀ z : ℂ, 0 < z.im → polyA m R z ≠ 0 := by
    intro z hz
    rw [polyA_eq_prod hw, Finset.prod_ne_zero_iff]
    intro j _
    refine mul_ne_zero (hc j) ?_
    intro h
    have := congrArg Complex.im h
    simp at this; linarith
  have him : ∀ z : ℂ, 0 < z.im → 0 < (polyB m N R z / polyA m R z).im := by
    intro z hz
    have hq : polyB m N R z / polyA m R z =
        ∏ j ∈ Finset.Icc (-(R : ℤ)) R, ((z - (compBeta m N j : ℂ)) / (z - OCS.multBary m j)) := by
      rw [polyB_eq_prod hw hNR, polyA_eq_prod hw, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [mul_div_mul_left _ _ (hc j)]
    rw [hq, prod_Icc_eq_prod_fin]
    refine im_prod_div_pos' (n := 2 * R) (a := fun k ↦ OCS.multBary m ((k : ℕ) - (R : ℤ)))
      (b := fun k ↦ compBeta m N ((k : ℕ) - (R : ℤ))) (fun k ↦ ?_) (fun k ↦ ?_) hz
    · exact (compBeta_interlace hw hN _).1
    · have := (compBeta_interlace hw hN (((k : ℕ) : ℤ) - R)).2
      simp only [Fin.val_succ, Fin.val_castSucc]
      convert this using 3
      push_cast; ring
  exact isHB_of_im_div_pos hAd hBd (polyA_conj hw R) (polyB_conj hw hNR) hA0 him hlam

theorem exp_mul_polyA (R : ℕ) (z : ℂ) :
    Complex.exp (OCS.multBeta m 0 + polyExp m R * z) * polyA m R z =
      Complex.exp (-(OCS.multKappa m : ℂ) * z + OCS.multBeta m 0) *
        ∏ j ∈ Finset.Icc (-(R : ℤ)) R,
          OCS.genusOneFactor (OCS.multBary m j : ℂ) ((OCS.multBary m j : ℂ)⁻¹) z := by
  unfold OCS.genusOneFactor polyA
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  have : (OCS.multBeta m 0 : ℂ) + polyExp m R * z =
      (-(OCS.multKappa m : ℂ) * z + OCS.multBeta m 0) +
        ∑ j ∈ Finset.Icc (-(R : ℤ)) R, z * (OCS.multBary m j : ℂ)⁻¹ := by
    unfold polyExp
    push_cast
    rw [← Finset.mul_sum]
    simp only [one_div]
    ring
  rw [this, Complex.exp_add]
  ring

/-- `e^{β + c_R z} A_R(z) → A(z)` locally uniformly (symmetric partial products of the genus-one
product `OCS.multF`). -/
theorem tendsto_polyA (hw : OCS.IsMultWeight m a b) :
    TendstoLocallyUniformly
      (fun (R : ℕ) (z : ℂ) ↦ Complex.exp (OCS.multBeta m 0 + polyExp m R * z) * polyA m R z)
      (genA m) atTop := by
  have h := Limits.tendstoLU_partial_prod hw
  have hc : Continuous (OCS.canonicalProd (OCS.multGammaC m) (fun w ↦ w⁻¹)) :=
    (OCS.differentiable_canonicalProd (OCS.isGenusOneData_multGammaC hw)).continuous
  have h2 := Limits.tendstoLU_const_mul (e := fun z ↦ Complex.exp (-(OCS.multKappa m : ℂ) * z +
    OCS.multBeta m 0)) (by fun_prop) h hc
  have e : (fun (R : ℕ) (z : ℂ) ↦
      Complex.exp (OCS.multBeta m 0 + polyExp m R * z) * polyA m R z) = fun (R : ℕ) (z : ℂ) ↦
      Complex.exp (-(OCS.multKappa m : ℂ) * z + OCS.multBeta m 0) *
        ∏ j ∈ Finset.Icc (-(R : ℤ)) R,
          OCS.genusOneFactor (OCS.multBary m j : ℂ) ((OCS.multBary m j : ℂ)⁻¹) z :=
    funext fun R ↦ funext fun z ↦ exp_mul_polyA R z
  rw [e]
  exact h2

theorem differentiable_polyB (m : ℝ → ℝ) (N R : ℕ) : Differentiable ℂ (polyB m N R) := by
  unfold polyB
  fun_prop

/-- `e^{β + c_R z} e^{-c_R/2} B_R(z) → B(z)` locally uniformly. -/
theorem tendsto_polyB (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) :
    TendstoLocallyUniformly
      (fun (R : ℕ) (z : ℂ) ↦ Complex.exp (OCS.multBeta m 0 + polyExp m R * z) *
        Real.exp (-polyExp m R / 2) * polyB m N R z)
      (compB m N) atTop := by
  have hA := tendsto_polyA hw
  have hTr := hA.comp (fun z : ℂ ↦ z - 1 / 2) (by fun_prop)
  set P : ℂ → ℂ := fun z ↦ ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ)) with hP
  have hPc : Continuous P := by rw [hP]; fun_prop
  have hlim : Continuous ((genA m) ∘ (fun z : ℂ ↦ z - 1 / 2)) :=
    (differentiable_genA hw).continuous.comp (by fun_prop)
  have h2 := Limits.tendstoLU_const_mul hPc hTr hlim
  refine Limits.tendstoLU_of_mul_prod (s := Finset.Ioo (-(N : ℤ)) N)
    (a := fun j ↦ ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)) (fun R ↦ ?_) (differentiable_compB hw N) ?_
  · have := differentiable_polyB m N R
    fun_prop
  · have hlimeq : (fun z : ℂ ↦ compB m N z * ∏ j ∈ Finset.Ioo (-(N : ℤ)) N,
        (z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ))) =
        fun z ↦ P z * ((genA m) ∘ (fun z : ℂ ↦ z - 1 / 2)) z := by
      funext z
      rw [compB_mul_Q hw hN z]
      simp only [Function.comp, hP]
      ring
    rw [hlimeq]
    refine Limits.tendstoLU_congr_eventually h2 ?_
    filter_upwards [eventually_ge_atTop N] with R hR
    funext z
    have hq := polyB_mul_Q hw hR z
    have hexp : Complex.exp (OCS.multBeta m 0 + polyExp m R * (z - 1 / 2)) =
        Complex.exp (OCS.multBeta m 0 + polyExp m R * z) *
          ((Real.exp (-polyExp m R / 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [Function.comp, hP]
    calc P z * (Complex.exp (OCS.multBeta m 0 + polyExp m R * (z - 1 / 2)) *
          polyA m R (z - 1 / 2))
        = Complex.exp (OCS.multBeta m 0 + polyExp m R * (z - 1 / 2)) *
          (polyA m R (z - 1 / 2) * P z) := by ring
      _ = _ := by
        rw [hexp]
        simp only [hP] at hq ⊢
        rw [← hq]
        ring

/-! ### Comparability of `B` -/

/-- `Γ + 1/2`. -/
def compZ₁ (m : ℝ → ℝ) : Set ℂ := (fun w : ℂ ↦ w + 1 / 2) '' OCS.multGammaC m

theorem compZ₁_eq (hw : OCS.IsMultWeight m a b) :
    compZ₁ m = {t | genA m (t - 1 / 2) = 0} := by
  ext t
  simp only [compZ₁, Set.mem_image, Set.mem_ofPred_eq, genA_eq_zero_iff hw, OCS.mem_multGammaC_iff]
  constructor
  · rintro ⟨w, ⟨γ, ⟨j, rfl⟩, rfl⟩, rfl⟩
    exact ⟨j, by ring⟩
  · rintro ⟨j, hj⟩
    exact ⟨(OCS.multBary m j : ℂ), ⟨_, ⟨j, rfl⟩, rfl⟩, by rw [← hj]; ring⟩

theorem infDist_compZ₁ (z : ℂ) :
    infDist z (compZ₁ m) = infDist (z - 1 / 2) (OCS.multGammaC m) := by
  have hiso : Isometry (fun w : ℂ ↦ w + 1 / 2) := (IsometryEquiv.addRight (1 / 2 : ℂ)).isometry
  have := Metric.infDist_image hiso (x := z - 1 / 2) (t := OCS.multGammaC m)
  rw [sub_add_cancel] at this
  exact this

theorem range_compBeta_eq (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) :
    (Set.range fun j : ℤ ↦ ((compBeta m N j : ℝ) : ℂ)) = {t | compB m N t = 0} := by
  ext t
  simp only [Set.mem_range, Set.mem_ofPred_eq, compB_eq_zero_iff hw hN t]
  constructor
  · rintro ⟨j, rfl⟩; exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩; exact ⟨j, rfl⟩

theorem exists_far (m : ℝ → ℝ) (N : ℕ) :
    ∃ ρ₀ : ℝ, ∀ z : ℂ, ρ₀ ≤ ‖z‖ →
      (∀ j ∈ Finset.Ioo (-(N : ℤ)) N, 1 ≤ ‖z - (compBeta m N j : ℂ)‖ ∧
        1 ≤ ‖z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)‖) ∧
      ‖(∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ))) /
          (∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ))) - 1‖
        ≤ 1 / 2 := by
  have h : Tendsto (fun z : ℂ ↦ ∏ j ∈ Finset.Ioo (-(N : ℤ)) N,
      ((z - (compBeta m N j : ℂ)) / (z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ))))
      (cocompact ℂ) (𝓝 1) := by
    have := tendsto_finsetProd (Finset.Ioo (-(N : ℤ)) N)
      (fun j _ ↦ Comparable.tendsto_sub_div_sub (compBeta m N j : ℂ)
        ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ))
    simpa using this
  have hev := (Metric.tendsto_nhds.1 h) (1 / 2) (by norm_num)
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 hev
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨max (r + 1) (1 + ∑ j ∈ Finset.Ioo (-(N : ℤ)) N,
    (‖(compBeta m N j : ℂ)‖ + ‖((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)‖)), fun z hz ↦ ⟨fun j hj ↦ ?_, ?_⟩⟩
  · have h1 : ‖(compBeta m N j : ℂ)‖ + ‖((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)‖ ≤
        ∑ j ∈ Finset.Ioo (-(N : ℤ)) N,
          (‖(compBeta m N j : ℂ)‖ + ‖((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)‖) :=
      Finset.single_le_sum (f := fun j ↦ ‖(compBeta m N j : ℂ)‖ +
        ‖((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)‖) (fun j _ ↦ by positivity) hj
    have h2 := le_max_right (r + 1) (1 + ∑ j ∈ Finset.Ioo (-(N : ℤ)) N,
      (‖(compBeta m N j : ℂ)‖ + ‖((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)‖))
    have h3 := norm_sub_norm_le z (compBeta m N j : ℂ)
    have h4 := norm_sub_norm_le z ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)
    have h5 := norm_nonneg (compBeta m N j : ℂ)
    have h6 := norm_nonneg ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)
    constructor <;> linarith
  · have hzK : z ∉ K := fun hzK ↦ by
      have := hr hzK
      rw [mem_closedBall, dist_zero_right] at this
      have := le_max_left (r + 1) (1 + ∑ j ∈ Finset.Ioo (-(N : ℤ)) N,
        (‖(compBeta m N j : ℂ)‖ + ‖((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)‖))
      linarith
    have := hKs hzK
    rw [Set.mem_ofPred_eq, dist_eq_norm, Finset.prod_div_distrib] at this
    exact this.le

/-- `e^{U(z - 1/2)}` is bounded above and below on compact sets. -/
theorem expU_bounds_on_compact (hw : OCS.IsMultWeight m a b) {K : Set ℂ} (hK : IsCompact K) :
    ∃ u₁ u₂ : ℝ, 0 < u₁ ∧ 0 < u₂ ∧ ∀ z ∈ K,
      u₁ ≤ Real.exp (OCS.multU m 0 (z - 1 / 2)) ∧ Real.exp (OCS.multU m 0 (z - 1 / 2)) ≤ u₂ := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hc⟩ := norm_genA_comparable hw
  have hFd : Differentiable ℂ (fun w ↦ genA m (w - 1 / 2)) := fun z ↦
    ((differentiable_genA hw) (z - 1 / 2)).comp z (differentiableAt_id.sub_const _)
  have hFs : ∀ t, genA m (t - 1 / 2) = 0 → deriv (fun w ↦ genA m (w - 1 / 2)) t ≠ 0 := by
    intro t ht
    have : deriv (fun w ↦ genA m (w - 1 / 2)) t = deriv (genA m) (t - 1 / 2) :=
      deriv_comp_sub_const (f := genA m) (a := 1 / 2) (x := t)
    rw [this]
    exact genA_simple hw ht
  have hne : ∃ t, genA m (t - 1 / 2) = 0 :=
    ⟨(OCS.multBary m 0 : ℂ) + 1 / 2, by
      rw [add_sub_cancel_right, genA_eq_zero_iff hw]; exact ⟨0, rfl⟩⟩
  obtain ⟨d₁, d₂, hd₁, hd₂, hd⟩ := Comparable.comparable_on_compact hFd hFs hne hK
  have hset : {t | genA m (t - 1 / 2) = 0} = compZ₁ m := (compZ₁_eq hw).symm
  have hcl : IsClosed (compZ₁ m) := by
    rw [← hset]; exact isClosed_eq hFd.continuous continuous_const
  -- the finite set `K ∩ Z₁`
  have hfin : (K ∩ compZ₁ m).Finite := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    have h1 := (OCS.isGenusOneData_multGammaC hw).finite_inter_ball (R + 1)
    refine ((h1.image (fun w : ℂ ↦ w + 1 / 2))).subset ?_
    rintro t ⟨htK, w, hwΓ, rfl⟩
    refine ⟨w, ⟨hwΓ, ?_⟩, rfl⟩
    have := hR htK
    rw [mem_closedBall, dist_zero_right] at this
    rw [mem_ball_zero_iff]
    have h2 : ‖w‖ ≤ ‖w + 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := by
      have := norm_sub_le (w + 1 / 2) (1 / 2 : ℂ)
      simpa using this
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    linarith
  obtain ⟨v₁, v₂, hv₁, hv₂, hv⟩ := Comparable.finite_bounds hfin
    (fun z ↦ Real.exp (OCS.multU m 0 (z - 1 / 2))) (fun z _ ↦ Real.exp_pos _)
  refine ⟨min v₁ (d₁ / c₂), max v₂ (d₂ / c₁), lt_min hv₁ (by positivity),
    lt_max_of_lt_left hv₂, fun z hz ↦ ?_⟩
  by_cases hzZ : z ∈ compZ₁ m
  · obtain ⟨h1, h2⟩ := hv z ⟨hz, hzZ⟩
    exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_left _ _)⟩
  · have hw1 : 0 < infDist z (compZ₁ m) := by
      have hne' : (compZ₁ m).Nonempty := by rw [← hset]; exact hne
      exact (hcl.notMem_iff_infDist_pos hne').1 hzZ
    have hm : 0 < min 1 (infDist z (compZ₁ m)) := lt_min one_pos hw1
    obtain ⟨hd1, hd2⟩ := hd z hz
    rw [hset] at hd1 hd2
    obtain ⟨hc1, hc2⟩ := hc (z - 1 / 2)
    rw [← infDist_compZ₁] at hc1 hc2
    have hE := Real.exp_pos (OCS.multU m 0 (z - 1 / 2))
    set E := Real.exp (OCS.multU m 0 (z - 1 / 2))
    set w₁ := min 1 (infDist z (compZ₁ m))
    set a₁ := ‖genA m (z - 1 / 2)‖
    constructor
    · refine (min_le_right _ _).trans ?_
      rw [div_le_iff₀ hc₂]
      nlinarith [mul_pos hE hm]
    · refine le_trans ?_ (le_max_right _ _)
      rw [le_div_iff₀ hc₁]
      nlinarith [mul_pos hE hm]

/-- `|B| ≃ e^{U(z - 1/2)} min(1, dist(z, {β_j}))` on `Im z ≥ 0`. -/
theorem norm_compB_comparable (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℂ, 0 ≤ z.im →
      c₁ * Real.exp (OCS.multU m 0 (z - 1 / 2)) *
          min 1 (infDist z (Set.range fun j : ℤ ↦ ((compBeta m N j : ℝ) : ℂ))) ≤
        ‖compB m N z‖ ∧
      ‖compB m N z‖ ≤ c₂ * Real.exp (OCS.multU m 0 (z - 1 / 2)) *
          min 1 (infDist z (Set.range fun j : ℤ ↦ ((compBeta m N j : ℝ) : ℂ))) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hc⟩ := norm_genA_comparable hw
  obtain ⟨ρ₀, hfar⟩ := exists_far m N
  have hK : IsCompact (closedBall (0 : ℂ) ρ₀) := isCompact_closedBall _ _
  obtain ⟨u₁, u₂, hu₁, hu₂, hu⟩ := expU_bounds_on_compact hw hK
  have hne : ∃ t, compB m N t = 0 := ⟨(compBeta m N 0 : ℂ), (compB_eq_zero_iff hw hN _).2 ⟨0, rfl⟩⟩
  obtain ⟨e₁, e₂, he₁, he₂, he⟩ := Comparable.comparable_on_compact (differentiable_compB hw N)
    (fun t ht ↦ compB_simple hw hN ht) hne hK
  rw [← range_compBeta_eq hw hN] at he
  refine ⟨min (c₁ / 2) (e₁ / u₂), max (3 * c₂ / 2) (e₂ / u₁), lt_min (by positivity) (by positivity),
    lt_max_of_lt_left (by positivity), fun z _ ↦ ?_⟩
  set wB := min 1 (infDist z (Set.range fun j : ℤ ↦ ((compBeta m N j : ℝ) : ℂ))) with hwB
  set E := Real.exp (OCS.multU m 0 (z - 1 / 2)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hwB0 : 0 ≤ wB := le_min zero_le_one infDist_nonneg
  by_cases hz : ρ₀ ≤ ‖z‖
  · -- far region
    obtain ⟨hSig, hR⟩ := hfar z hz
    have hQ : ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j hj h
      have := (hSig j hj).2
      rw [sub_eq_zero.1 h, sub_self, norm_zero] at this
      linarith
    have hBQ := compB_mul_Q hw hN z
    set P := ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - (compBeta m N j : ℂ))
    set Q := ∏ j ∈ Finset.Ioo (-(N : ℤ)) N, (z - ((OCS.multBary m j + 1 / 2 : ℝ) : ℂ))
    have hBeq : compB m N z = genA m (z - 1 / 2) * (P / Q) := by
      rw [mul_div_assoc', eq_div_iff hQ]
      exact hBQ
    have hn : ‖compB m N z‖ = ‖genA m (z - 1 / 2)‖ * ‖P / Q‖ := by rw [hBeq, norm_mul]
    have hR1 : 1 / 2 ≤ ‖P / Q‖ := by
      have := norm_sub_norm_le (1 : ℂ) (P / Q)
      rw [norm_sub_rev] at this
      simp only [norm_one] at this
      linarith
    have hR2 : ‖P / Q‖ ≤ 3 / 2 := by
      have := norm_le_norm_add_norm_sub' (P / Q) 1
      simp only [norm_one] at this
      linarith
    -- the minima agree
    have hΓBne : (Set.range fun j : ℤ ↦ ((compBeta m N j : ℝ) : ℂ)).Nonempty := ⟨_, ⟨0, rfl⟩⟩
    have hZne : (compZ₁ m).Nonempty := ⟨_, ⟨(OCS.multBary m 0 : ℂ), ⟨_, ⟨0, rfl⟩, rfl⟩, rfl⟩⟩
    have hmin : min 1 (infDist z (compZ₁ m)) = wB := by
      rw [hwB]
      refine Comparable.min_one_infDist_congr hZne hΓBne z ?_ ?_
      · rintro x ⟨w, ⟨γ, ⟨j, rfl⟩, rfl⟩, rfl⟩ hx
        by_cases hj : j ∈ Finset.Ioo (-(N : ℤ)) N
        · rw [dist_eq_norm]
          have := (hSig j hj).2
          push_cast at this ⊢
          exact this
        · exfalso
          apply hx
          refine ⟨j, ?_⟩
          show ((compBeta m N j : ℝ) : ℂ) = (OCS.multBary m j : ℂ) + 1 / 2
          rw [compBeta_of_not_lt hj]; push_cast; ring
      · rintro x ⟨j, rfl⟩ hx
        by_cases hj : j ∈ Finset.Ioo (-(N : ℤ)) N
        · rw [dist_eq_norm]; exact (hSig j hj).1
        · exfalso
          apply hx
          refine ⟨(OCS.multBary m j : ℂ), ⟨_, ⟨j, rfl⟩, rfl⟩, ?_⟩
          show (OCS.multBary m j : ℂ) + 1 / 2 = ((compBeta m N j : ℝ) : ℂ)
          rw [compBeta_of_not_lt hj]; push_cast; ring
    obtain ⟨hc1, hc2⟩ := hc (z - 1 / 2)
    rw [← infDist_compZ₁, hmin] at hc1 hc2
    constructor
    · calc min (c₁ / 2) (e₁ / u₂) * E * wB ≤ (c₁ / 2) * E * wB := by gcongr; exact min_le_left _ _
        _ = (1 / 2) * (c₁ * E * wB) := by ring
        _ ≤ (1 / 2) * ‖genA m (z - 1 / 2)‖ := by linarith
        _ ≤ ‖genA m (z - 1 / 2)‖ * ‖P / Q‖ := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left hR1 (norm_nonneg _)
        _ = _ := hn.symm
    · calc ‖compB m N z‖ = ‖genA m (z - 1 / 2)‖ * ‖P / Q‖ := hn
        _ ≤ ‖genA m (z - 1 / 2)‖ * (3 / 2) := mul_le_mul_of_nonneg_left hR2 (norm_nonneg _)
        _ ≤ (c₂ * E * wB) * (3 / 2) := by gcongr
        _ = (3 * c₂ / 2) * E * wB := by ring
        _ ≤ max (3 * c₂ / 2) (e₂ / u₁) * E * wB := by gcongr; exact le_max_left _ _
  · -- compact region
    push Not at hz
    have hzK : z ∈ closedBall (0 : ℂ) ρ₀ := by
      rw [mem_closedBall, dist_zero_right]; exact hz.le
    obtain ⟨hb1, hb2⟩ := he z hzK
    obtain ⟨hU1, hU2⟩ := hu z hzK
    rw [← hwB] at hb1 hb2
    constructor
    · calc min (c₁ / 2) (e₁ / u₂) * E * wB ≤ (e₁ / u₂) * E * wB := by
            gcongr; exact min_le_right _ _
        _ ≤ (e₁ / u₂) * u₂ * wB := by gcongr
        _ = e₁ * wB := by field_simp
        _ ≤ _ := hb1
    · calc ‖compB m N z‖ ≤ e₂ * wB := hb2
        _ = (e₂ / u₁) * u₁ * wB := by field_simp
        _ ≤ (e₂ / u₁) * E * wB := by gcongr
        _ ≤ max (3 * c₂ / 2) (e₂ / u₁) * E * wB := by gcongr; exact le_max_right _ _

/-- A real point where `A ≠ 0` and `B = 0`. -/
theorem exists_real_genA_ne_zero_compB_eq_zero (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) :
    ∃ x : ℝ, genA m (x : ℂ) ≠ 0 ∧ compB m N (x : ℂ) = 0 := by
  refine ⟨compBeta m N 0, ?_, (compB_eq_zero_iff hw hN _).2 ⟨0, rfl⟩⟩
  rw [Ne, genA_eq_zero_iff hw]
  rintro ⟨j, hj⟩
  have hj' : compBeta m N 0 = OCS.multBary m j := by exact_mod_cast hj
  obtain ⟨h1, h2⟩ := compBeta_interlace hw hN 0
  have hmono := (OCS.strictMono_multBary hw).monotone
  rcases le_or_gt j 0 with h | h
  · have := hmono h; linarith
  · have := hmono (show (1 : ℤ) ≤ j by omega); rw [zero_add] at h2; linarith

/-- `A - i λ B ∈ \overline{HB}` for every `λ > 0`. -/
theorem isHB_genA_sub_lam_compB (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) {lam : ℝ}
    (hlam : 0 < lam) :
    IsHB (fun z ↦ genA m z - Complex.I * lam * compB m N z) := by
  have hA := tendsto_polyA hw
  have hB := tendsto_polyB hw hN
  have hBc : Continuous (compB m N) := (differentiable_compB hw N).continuous
  have h1 := Limits.tendstoLU_const_mul (e := fun _ : ℂ ↦ Complex.I * lam) (by fun_prop) hB hBc
  have h2 := hA.sub h1
  have hseq : ∀ k : ℕ, IsHB (fun z ↦ Complex.exp (OCS.multBeta m 0 + polyExp m (k + N) * z) *
      (polyA m (k + N) z - Complex.I * ((lam * Real.exp (-polyExp m (k + N) / 2) : ℝ) : ℂ) *
        polyB m N (k + N) z)) := fun k ↦
    (isHB_cexp_real_linear (OCS.multBeta m 0 : ℂ) (polyExp m (k + N))).mul
      (isHB_polyA_sub_polyB hw hN (Nat.le_add_left N k) (mul_pos hlam (Real.exp_pos _)))
  have h3 := Limits.tendstoLU_comp_filter h2 (g := fun k : ℕ ↦ k + N)
    (tendsto_atTop_mono (fun k ↦ Nat.le_add_right k N) tendsto_id)
  obtain ⟨x, hx1, hx2⟩ := exists_real_genA_ne_zero_compB_eq_zero hw hN
  refine IsHB.of_tendstoLocallyUniformly hseq (Limits.tendstoLU_congr_eventually h3
    (Eventually.of_forall fun k ↦ ?_)) ⟨x, ?_⟩
  · funext z
    simp only [Pi.sub_apply]
    push_cast
    ring
  · simpa [hx2] using hx1

/-- **`E = A - iB ∈ \overline{HB}`** (replaces Meĭman's theorem), via the real polynomials
`A_R = ∏_{|j| ≤ R} (1 - z/γ_j)` and the locally uniform limit
`e^{β + (S_R - κ) z} (A_R - i e^{-(S_R - κ)/2} B_R) → A - iB`. -/
theorem isHB_compE (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) :
    IsHB (compE m N) := by
  have := isHB_genA_sub_lam_compB hw hN one_pos
  have e : compE m N = fun z ↦ genA m z - Complex.I * ((1 : ℝ) : ℂ) * compB m N z := by
    funext z; simp [compE]
  rw [e]; exact this

/-- `E_κ = e^{-κ z}(A - i e^{κ/2} B) ∈ \overline{HB}`: `A - i λ B ∈ \overline{HB}` for every `λ > 0`
(the proof of `isHB_compE` gives this, via `isHB_polyA_sub_polyB` for any positive multiplier),
and `e^{-κ z}` is a real entire factor (`isHB_cexp_real_linear`, `IsHB.mul`). -/
theorem isHB_compEκ (hw : OCS.IsMultWeight m a b) {N : ℕ}
    (hN : ∀ j : ℤ, N ≤ |j| → 1 / 2 < OCS.multBary m (j + 1) - OCS.multBary m j) (κ : ℝ) :
    IsHB (compEκ m κ N) := by
  have h := (isHB_cexp_real_linear 0 (-κ)).mul
    (isHB_genA_sub_lam_compB hw hN (Real.exp_pos (κ / 2)))
  convert h using 2 with z
  unfold compEκ
  congr 2
  push_cast
  ring

/-- `E_κ + E_κ^* = 2 e^{-κ z} A`. -/
theorem compEκ_add_fstar (hw : OCS.IsMultWeight m a b) (κ : ℝ) (N : ℕ) (z : ℂ) :
    compEκ m κ N z + fstar (compEκ m κ N) z = 2 * Complex.exp (-((κ : ℂ) * z)) * genA m z := by
  have hz : conj (Complex.exp (-((κ : ℂ) * conj z))) = Complex.exp (-((κ : ℂ) * z)) := by
    rw [← Complex.exp_conj]; simp [map_neg, map_mul, Complex.conj_ofReal]
  simp only [fstar, compEκ, map_mul, map_sub, Complex.conj_I, hz,
    Complex.conj_ofReal]
  rw [genA_conj hw, compB_conj hw, Complex.conj_conj, Complex.conj_conj]
  ring

/-- `|E(z̄)|² - ...`: `E^* = A + i B`, hence `E + E^* = 2A`. -/
theorem fstar_compE (hw : OCS.IsMultWeight m a b) (N : ℕ) (z : ℂ) :
    fstar (compE m N) z = genA m z + Complex.I * compB m N z := by
  simp only [fstar, compE, map_sub, map_mul, Complex.conj_I]
  rw [genA_conj hw, compB_conj hw]
  simp only [Complex.conj_conj, neg_mul, sub_neg_eq_add]

/-- `|A|² + |B|² ≤ |E|² ≤ 2 (|A|² + |B|²)` on `Im z ≥ 0` (from `|E^*| ≤ |E|`). -/
theorem norm_compE_sq_bounds {N : ℕ} (hE : IsHB (compE m N)) (hw : OCS.IsMultWeight m a b)
    {z : ℂ} (hz : 0 ≤ z.im) :
    ‖genA m z‖ ^ 2 + ‖compB m N z‖ ^ 2 ≤ ‖compE m N z‖ ^ 2 ∧
      ‖compE m N z‖ ^ 2 ≤ 2 * (‖genA m z‖ ^ 2 + ‖compB m N z‖ ^ 2) := by
  have hstar : ‖fstar (compE m N) z‖ ≤ ‖compE m N z‖ := by
    rcases hz.eq_or_lt with h | h
    · rw [norm_fstar]
      have : conj z = z := Complex.conj_eq_iff_im.2 h.symm
      rw [this]
    · exact hE.norm_fstar_le h
  have hpar := parallelogram_law_with_norm ℂ (genA m z) (Complex.I * compB m N z)
  have h1 : ‖Complex.I * compB m N z‖ = ‖compB m N z‖ := by simp
  have e1 : genA m z + Complex.I * compB m N z = fstar (compE m N) z := (fstar_compE hw N z).symm
  have e2 : genA m z - Complex.I * compB m N z = compE m N z := rfl
  rw [e1, e2, h1] at hpar
  have hs := sq_nonneg ‖fstar (compE m N) z‖
  have hs2 : ‖fstar (compE m N) z‖ ^ 2 ≤ ‖compE m N z‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hstar 2
  constructor <;> nlinarith

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
  obtain ⟨C, hC⟩ := hU
  have hCall : ∀ z : ℂ, |OCS.multU m 0 z - (Real.pi * |z.im| + κ * z.re)| ≤ C := by
    intro z
    rcases le_total 0 z.im with h | h
    · rw [abs_of_nonneg h]; have := hC z h; rwa [sub_sub] at this
    · have := hC (conj z) (by simpa using h)
      rw [multU_conj'] at this
      simp only [Complex.conj_im, Complex.conj_re, mul_neg, sub_neg_eq_add] at this
      rw [abs_of_nonpos h]
      convert this using 2
      ring
  obtain ⟨c₁, c₂, hc₁, hc₂, hc⟩ := norm_genA_comparable hw
  refine ⟨c₁ * Real.exp (-C), c₂ * Real.exp C, by positivity, by positivity, fun z ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hc z
  have hb := abs_le.1 (hCall z)
  have e1 : Real.exp (-C) * Real.exp (Real.pi * |z.im| + κ * z.re) ≤ Real.exp (OCS.multU m 0 z) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have e2 : Real.exp (OCS.multU m 0 z) ≤ Real.exp C * Real.exp (Real.pi * |z.im| + κ * z.re) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have hm : 0 ≤ min 1 (infDist z (OCS.multGammaC m)) := le_min zero_le_one infDist_nonneg
  constructor
  · refine le_trans ?_ h1
    have : c₁ * (Real.exp (-C) * Real.exp (Real.pi * |z.im| + κ * z.re)) ≤
        c₁ * Real.exp (OCS.multU m 0 z) := by gcongr
    nlinarith [mul_le_mul_of_nonneg_right this hm]
  · refine h2.trans ?_
    have : c₂ * Real.exp (OCS.multU m 0 z) ≤
        c₂ * (Real.exp C * Real.exp (Real.pi * |z.im| + κ * z.re)) := by gcongr
    nlinarith [mul_le_mul_of_nonneg_right this hm]

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
