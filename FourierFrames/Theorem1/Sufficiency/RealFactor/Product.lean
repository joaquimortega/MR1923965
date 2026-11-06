import FourierFrames.Theorem1.Sufficiency.RealFactor.Elem
import FourierFrames.Theorem1.Sufficiency.RealFactor.Zeros
import FourierFrames.Theorem1.Sufficiency.RealFactor.LUProd

/-!
# The real-zero product `S` of an entire function `F`

`S(z) = z^{m(0)} ∏_{a ∈ Z_r} E_{p_a}(z/a)^{m(a)}`, `Z_r` the nonzero real zeros of `F`,
`m(a)` the multiplicity and `p_a = m(a) + rank(a) + 1` with `rank : Z_r → ℕ` injective.
-/

open Complex Filter Topology Set Metric
open scoped ComplexConjugate

namespace FF
namespace Suff

noncomputable section

variable (F : ℂ → ℂ)

/-- The nonzero real zeros of `F`. -/
def Zr : Set ℝ := {x : ℝ | F (x : ℂ) = 0 ∧ x ≠ 0}

/-- The multiplicity of `a` as a zero of `F`. -/
def mult (a : ℝ) : ℕ := analyticOrderNatAt F (a : ℂ)

/-- An injection of `Z_r` into `ℕ` (it is countable). -/
def rankZ : Zr F → ℕ := by
  classical exact if h : (Zr F).Countable then Classical.choose (Set.countable_iff_exists_injective.mp h)
    else fun _ ↦ 0

/-- The genus used for the zero `a`. -/
def genus (a : Zr F) : ℕ := mult F a + rankZ F a + 1

/-- The factor of `S` for the zero `a`. -/
def facF (a : Zr F) (z : ℂ) : ℂ := elemFactor (genus F a) (z / ((a : ℝ) : ℂ)) ^ mult F a

/-- The product over the nonzero real zeros. -/
def S0 (z : ℂ) : ℂ := ∏' a : Zr F, facF F a z

/-- The real-zero factor `S`. -/
def Sfac (z : ℂ) : ℂ := z ^ analyticOrderNatAt F 0 * S0 F z

variable {F}

theorem countable_Zr (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) : (Zr F).Countable :=
  (countable_realZeros hF h).mono fun _ hx ↦ hx.1

theorem rankZ_injective (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) :
    Function.Injective (rankZ F) := by
  classical
  unfold rankZ
  simp only [countable_Zr hF h, ↓reduceDIte]
  exact Classical.choose_spec (Set.countable_iff_exists_injective.mp (countable_Zr hF h))

theorem ne_zero_of_mem_Zr (a : Zr F) : ((a : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast a.2.2

theorem differentiable_facF (a : Zr F) : Differentiable ℂ (facF F a) := by
  unfold facF
  exact ((differentiable_elemFactor _).comp (differentiable_id.div_const _)).pow _

theorem eventually_two_le_abs (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) (R : ℝ) :
    ∀ᶠ a : Zr F in cofinite, 2 * R ≤ |(a : ℝ)| := by
  rw [Filter.eventually_cofinite]
  refine ((finite_realZeros hF h (2 * R)).preimage (Subtype.val_injective.injOn)).subset ?_
  intro a ha
  simp only [Set.mem_ofPred_eq, not_le] at ha
  exact ⟨a.2.1, ha.le⟩

theorem norm_facF_sub_one_le {a : Zr F} {R : ℝ} {z : ℂ} (ha : 2 * R ≤ |(a : ℝ)|)
    (hz : ‖z‖ ≤ R) : ‖facF F a z - 1‖ ≤ (1 / 2 : ℝ) ^ rankZ F a := by
  set m := mult F a
  set r := rankZ F a
  have ha0 : 0 < |(a : ℝ)| := abs_pos.mpr a.2.2
  have hw : ‖z / ((a : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ ha0]
    linarith
  have hw' : ‖z / ((a : ℝ) : ℂ)‖ ^ (genus F a + 1) ≤ (1 / 2 : ℝ) ^ (m + r + 2) := by
    have : genus F a + 1 = m + r + 2 := by unfold genus; ring
    rw [this]
    exact pow_le_pow_left₀ (norm_nonneg _) hw _
  have hm : (m : ℝ) * (1 / 2) ^ m ≤ 1 := by
    have h1 : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
    calc (m : ℝ) * (1 / 2) ^ m ≤ 2 ^ m * (1 / 2) ^ m := by gcongr
      _ = 1 := by rw [← mul_pow]; norm_num
  have hkey : 4 * (m : ℝ) * (1 / 2 : ℝ) ^ (m + r + 2) ≤ (1 / 2 : ℝ) ^ r := by
    have : 4 * (m : ℝ) * (1 / 2 : ℝ) ^ (m + r + 2) = ((m : ℝ) * (1 / 2) ^ m) * (1 / 2) ^ r := by
      rw [pow_add, pow_add]; ring
    rw [this]
    calc ((m : ℝ) * (1 / 2) ^ m) * (1 / 2) ^ r ≤ 1 * (1 / 2) ^ r := by gcongr
      _ = _ := one_mul _
  have hr1 : (1 / 2 : ℝ) ^ r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h4 : 4 * (m : ℝ) * ‖z / ((a : ℝ) : ℂ)‖ ^ (genus F a + 1) ≤ (1 / 2 : ℝ) ^ r := by
    calc 4 * (m : ℝ) * ‖z / ((a : ℝ) : ℂ)‖ ^ (genus F a + 1)
        ≤ 4 * (m : ℝ) * (1 / 2 : ℝ) ^ (m + r + 2) := by gcongr
      _ ≤ _ := hkey
  have h2 : 2 * (m : ℝ) * ‖z / ((a : ℝ) : ℂ)‖ ^ (genus F a + 1) ≤ 1 := by
    have : 0 ≤ (m : ℝ) * ‖z / ((a : ℝ) : ℂ)‖ ^ (genus F a + 1) := by positivity
    linarith
  exact (norm_elemFactor_pow_sub_one_le (genus F a) m hw h2).trans h4

theorem luprod_facF (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) : LUProd (facF F) := by
  refine ⟨differentiable_facF, fun R ↦ ?_⟩
  refine ⟨fun a ↦ (1 / 2 : ℝ) ^ rankZ F a,
    summable_geometric_two.comp_injective (rankZ_injective hF h), ?_⟩
  filter_upwards [eventually_two_le_abs hF h R] with a ha z hz
  exact norm_facF_sub_one_le ha (by simpa using hz)

theorem differentiable_S0 (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) :
    Differentiable ℂ (S0 F) :=
  (luprod_facF hF h).differentiable

theorem differentiable_Sfac (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) :
    Differentiable ℂ (Sfac F) :=
  (differentiable_id.pow _).mul (differentiable_S0 hF h)

theorem conj_facF (a : Zr F) (z : ℂ) : conj (facF F a (conj z)) = facF F a z := by
  unfold facF
  rw [map_pow, conj_elemFactor, map_div₀, Complex.conj_conj, Complex.conj_ofReal]

theorem fstar_Sfac (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) (z : ℂ) :
    fstar (Sfac F) z = Sfac F z := by
  unfold fstar Sfac S0
  rw [map_mul, map_pow, Complex.conj_conj, (luprod_facF hF h).conj_tprod]
  simp only [conj_facF]

theorem one_le_orderNat_of_zero (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) {x : ℂ}
    (hx : F x = 0) : 1 ≤ analyticOrderNatAt F x := by
  by_contra hlt
  have h0 : analyticOrderNatAt F x = 0 := by omega
  have htop := analyticOrderAt_ne_top_of_exists hF h x
  have : analyticOrderAt F x = 0 := by
    rw [← Nat.cast_analyticOrderNatAt htop, h0]; rfl
  rw [analyticOrderAt_eq_zero] at this
  rcases this with h1 | h1
  · exact h1 (hF.analyticAt x)
  · exact h1 hx

theorem facF_eq_zero_iff (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) (a : Zr F) (z : ℂ) :
    facF F a z = 0 ↔ z = ((a : ℝ) : ℂ) := by
  have hm : mult F a ≠ 0 := by
    have := one_le_orderNat_of_zero hF h (x := ((a : ℝ) : ℂ)) a.2.1
    unfold mult; omega
  unfold facF
  rw [pow_eq_zero_iff hm, elemFactor_eq_zero_iff, div_eq_one_iff_eq (ne_zero_of_mem_Zr a)]

theorem Sfac_eq_zero (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) {z : ℂ} (hz : Sfac F z = 0) :
    ∃ x : ℝ, z = (x : ℂ) ∧ F (x : ℂ) = 0 := by
  unfold Sfac S0 at hz
  rcases mul_eq_zero.mp hz with h1 | h1
  · have hz0 : z = 0 := pow_eq_zero_iff'.mp h1 |>.1
    refine ⟨0, by simpa using hz0, ?_⟩
    by_contra hF0
    have : analyticOrderNatAt F 0 = 0 := by
      unfold analyticOrderNatAt
      rw [analyticOrderAt_eq_zero.mpr (Or.inr (by simpa using hF0))]
      rfl
    rw [this] at h1
    simp at h1
  · obtain ⟨a, ha⟩ := ((luprod_facF hF h).tprod_eq_zero_iff z).mp h1
    exact ⟨a, (facF_eq_zero_iff hF h a z).mp ha, a.2.1⟩

theorem Sfac_eq_zero_of_zero (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) {x : ℝ}
    (hx : F (x : ℂ) = 0) : Sfac F (x : ℂ) = 0 := by
  by_cases hx0 : x = 0
  · subst hx0
    have := one_le_orderNat_of_zero hF h (x := 0) (by simpa using hx)
    unfold Sfac
    rw [Complex.ofReal_zero, zero_pow (by omega), zero_mul]
  · unfold Sfac
    rw [S0, ((luprod_facF hF h).tprod_eq_zero_iff _).mpr ⟨⟨x, hx, hx0⟩,
      (facF_eq_zero_iff hF h ⟨x, hx, hx0⟩ _).mpr rfl⟩, mul_zero]

theorem facF_zero (a : Zr F) : facF F a 0 = 1 := by
  unfold facF elemFactor
  simp

theorem S0_zero (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) : S0 F 0 ≠ 0 := by
  unfold S0
  apply (luprod_facF hF h).tprod_ne_zero
  intro k
  rw [facF_zero]; exact one_ne_zero

theorem facF_ne_zero_of_ne (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) {a k : Zr F} (hk : k ≠ a) :
    facF F k ((a : ℝ) : ℂ) ≠ 0 := by
  rw [Ne, facF_eq_zero_iff hF h]
  intro h'
  exact hk (Subtype.ext (by exact_mod_cast h'.symm))

theorem Sfac_local (hF : Differentiable ℂ F) (h : ∃ z, F z ≠ 0) {a : ℝ} (ha : F (a : ℂ) = 0) :
    ∃ S₁ : ℂ → ℂ, AnalyticAt ℂ S₁ (a : ℂ) ∧ S₁ a ≠ 0 ∧
      ∀ z, Sfac F z = (z - a) ^ (mult F a) * S₁ z := by
  classical
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨S0 F, (differentiable_S0 hF h).analyticAt _, by simpa using S0_zero hF h, fun z ↦ ?_⟩
    simp [Sfac, mult]
  · set a' : Zr F := ⟨a, ha, ha0⟩ with ha'
    set T : ℂ → ℂ := fun z ↦ ∏' k : Zr F, (if k = a' then 1 else facF F k z) with hT
    have hLU : LUProd (fun (k : Zr F) (z : ℂ) ↦ if k = a' then 1 else facF F k z) := by
      refine (luprod_facF hF h).mono (fun k ↦ ?_) (fun k z ↦ ?_)
      · by_cases hk : k = a'
        · simp only [hk, ite_true]; exact differentiable_const _
        · simp only [hk, ite_false]; exact differentiable_facF k
      · by_cases hk : k = a' <;> simp [hk]
    have hsplit : ∀ z, S0 F z = facF F a' z * T z := by
      intro z
      have hmul : Multipliable (Function.update (fun k ↦ facF F k z) a' 1) := by
        have := hLU.multipliable z
        convert this using 1
        funext k
        by_cases hk : k = a' <;> simp [hk]
      exact Multipliable.tprod_eq_mul_tprod_ite' a' hmul
    have ha0' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
    set P : ℂ → ℂ := fun z ↦ ∑ k ∈ Finset.range (genus F a'), (z / a) ^ (k + 1) / (k + 1) with hP
    set S₁ : ℂ → ℂ := fun z ↦ ((-1 / (a : ℂ)) * Complex.exp (P z)) ^ mult F a *
      (z ^ analyticOrderNatAt F 0 * T z) with hS₁
    have hS₁d : Differentiable ℂ S₁ := by
      have hTd : Differentiable ℂ T := hLU.differentiable
      have hPd : Differentiable ℂ P := by
        simp only [hP]; fun_prop
      simp only [hS₁]
      exact ((differentiable_const _).mul hPd.cexp).pow _ |>.mul ((differentiable_id.pow _).mul hTd)
    refine ⟨S₁, hS₁d.analyticAt _, ?_, fun z ↦ ?_⟩
    · simp only [hS₁]
      refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by simpa using ha0') (Complex.exp_ne_zero _)))
        (mul_ne_zero (pow_ne_zero _ ha0') ?_)
      exact hLU.tprod_ne_zero _ (fun k ↦ by
        by_cases hk : k = a'
        · simp [hk]
        · simp only [hk, ite_false]; exact facF_ne_zero_of_ne hF h hk)
    · unfold Sfac
      rw [hsplit z]
      simp only [hS₁, facF, elemFactor]
      have : (1 : ℂ) - z / a = (z - a) * (-1 / a) := by field_simp; ring
      have e : (((a' : Zr F) : ℝ) : ℂ) = (a : ℂ) := rfl
      have e2 : mult F ((a' : Zr F) : ℝ) = mult F a := rfl
      rw [e, e2, this]
      have hPz : P z = ∑ k ∈ Finset.range (genus F a'), (z / (a : ℂ)) ^ (k + 1) / (k + 1) := rfl
      rw [hPz]
      generalize Complex.exp (∑ k ∈ Finset.range (genus F a'), (z / (a : ℂ)) ^ (k + 1) / (k + 1))
        = Ex
      generalize (-1 / (a : ℂ)) = c
      rw [mul_assoc (z - (a : ℂ)), mul_pow]
      ring

end

end Suff
end FF
