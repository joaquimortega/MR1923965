import OrtegaCerdaSeip.Products.Canonical
import OrtegaCerdaSeip.Lemma3.Potential

/-!
# M07 (Lemma 3) — the multiplier `F` and the proof of Lemma 3

See `blueprint/M07_Lemma3.md`, §1.9–§1.13.  Paper, pp. 405–407.

`F(z) = e^{−κz + C + ∑_j E_j(log|·|)} ∏_j (1 − z/γ_j) e^{z/γ_j}` (`multF`).  The exponential
factor realises the paper's choice `log|F| = U + ∑_j ∫_{I_j} log|1 − z/t| dμ(t)` (the linear
term `−κz`) *and* removes the constant `c₀ = ∫ H/t²` (README §4): with this normalisation
`log|F(z)| − U(z) = ∑_j E_j(log|· − z|)` for `z ∉ Γ` (`log_norm_multF_sub_multU`), which is
`−Re G(z)` off `ℝ` and `log dist(z, Γ) + O(1)` for `|Im z| ≤ 1`.

`L = −κz + β + ∑_j (Log(1 − z/γ_j) + z/γ_j)` (`multL`) is a holomorphic logarithm of `F` on
`ℂ ∖ ℝ`, and `V = Im(L + G)` (`multV`, `0` on `ℝ`) is the harmonic conjugate of `U` with
`V(z̄) = −V(z)`; then `L − U − iV = −G` and (3) follows from `|G| ≤ π/(2a|Im z|)`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-- The zero set `Γ` as a subset of `ℂ`. -/
def multGammaC (m : ℝ → ℝ) : Set ℂ :=
  (fun t : ℝ ↦ (t : ℂ)) '' multGamma m

/-- The additive constant `β = C + ∑_j E_j(log|·|)` (`= C − ∫ H/t²`). -/
def multBeta (m : ℝ → ℝ) (C : ℝ) : ℝ :=
  C + multLogConst m

/-- The multiplier `F(z) = e^{−κz + β} ∏_{γ ∈ Γ} (1 − z/γ) e^{z/γ}`. -/
def multF (m : ℝ → ℝ) (C : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(multKappa m : ℂ) * z + multBeta m C) *
    canonicalProd (multGammaC m) (fun w ↦ w⁻¹) z

/-- The logarithm `L(z) = −κz + β + ∑_{γ ∈ Γ} (Log(1 − z/γ) + z/γ)` of `F` on `ℂ ∖ ℝ`. -/
def multL (m : ℝ → ℝ) (C : ℝ) (z : ℂ) : ℂ :=
  -(multKappa m : ℂ) * z + multBeta m C + canonicalLog (multGammaC m) (fun w ↦ w⁻¹) z

/-- The harmonic conjugate `V = Im(L + G)` off `ℝ`, `V = 0` on `ℝ`. -/
def multV (m : ℝ → ℝ) (C : ℝ) (z : ℂ) : ℝ :=
  if z.im = 0 then 0 else (multL m C z + multG m z).im

/-! ## `F` is an entire function with zero set `Γ` -/

theorem multGammaC_eq_range (m : ℝ → ℝ) :
    multGammaC m = range fun j : ℤ ↦ ((multBary m j : ℝ) : ℂ) := by
  rw [multGammaC, multGamma, ← range_comp]
  rfl

theorem injective_multBaryC {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    Function.Injective fun j : ℤ ↦ ((multBary m j : ℝ) : ℂ) :=
  Complex.ofReal_injective.comp (strictMono_multBary hw).injective

/-- The enumeration `ℤ ≃ Γ`, `j ↦ γ_j`. -/
def multGammaEquiv {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) : ℤ ≃ multGammaC m :=
  (Equiv.ofInjective _ (injective_multBaryC hw)).trans
    (Set.equivOfEq (multGammaC_eq_range m).symm)

@[simp]
theorem multGammaEquiv_apply {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) :
    (multGammaEquiv hw j : ℂ) = multBary m j := rfl

theorem mem_multGammaC_iff {m : ℝ → ℝ} {z : ℂ} :
    z ∈ multGammaC m ↔ ∃ γ ∈ multGamma m, z = γ := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩; exact ⟨γ, hγ, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩; exact ⟨γ, hγ, rfl⟩

theorem im_eq_zero_of_mem_multGammaC {m : ℝ → ℝ} {z : ℂ} (hz : z ∈ multGammaC m) : z.im = 0 := by
  obtain ⟨γ, _, rfl⟩ := hz; simp

theorem notMem_multGammaC_of_im_ne_zero {m : ℝ → ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    z ∉ multGammaC m := fun h ↦ hz (im_eq_zero_of_mem_multGammaC h)

theorem conj_mem_multGammaC {m : ℝ → ℝ} : ∀ a ∈ multGammaC m, conj a ∈ multGammaC m := by
  rintro _ ⟨γ, hγ, rfl⟩; exact ⟨γ, hγ, by simp⟩

theorem isGenusOneData_multGammaC {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    IsGenusOneData (multGammaC m) (fun w ↦ w⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨γ, hγ, h⟩
    exact zero_notMem_multGamma hw (by rw [Complex.ofReal_eq_zero.mp h] at hγ; exact hγ)
  · rw [← (multGammaEquiv hw).summable_iff]
    have := summable_multBary_inv_sq hw
    refine this.congr fun j ↦ ?_
    simp [Function.comp_apply, Complex.norm_real]
  · simp

theorem differentiable_multF {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (C : ℝ) :
    Differentiable ℂ (multF m C) := by
  unfold multF
  exact ((differentiable_id.const_mul _).add_const _).cexp.mul
    (differentiable_canonicalProd (isGenusOneData_multGammaC hw))

theorem multF_eq_zero_iff {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (C : ℝ) (z : ℂ) :
    multF m C z = 0 ↔ ∃ γ ∈ multGamma m, z = γ := by
  unfold multF
  rw [mul_eq_zero, canonicalProd_eq_zero_iff (isGenusOneData_multGammaC hw), mem_multGammaC_iff]
  simp [Complex.exp_ne_zero]

theorem multF_conj {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (C : ℝ) (z : ℂ) :
    multF m C (conj z) = conj (multF m C z) := by
  unfold multF
  rw [canonicalProd_conj (isGenusOneData_multGammaC hw) conj_mem_multGammaC
    (fun a _ ↦ by rw [map_inv₀]), map_mul, ← Complex.exp_conj]
  congr 2
  simp [map_add, map_mul, map_neg, Complex.conj_ofReal]

/-! ## The main identity -/

theorem hasSum_multErr_logDist_all {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (C : ℝ)
    {z : ℂ} (hz : z ∉ multGammaC m) :
    HasSum (fun j : ℤ ↦ multErr m (fun t ↦ Real.log ‖(t : ℂ) - z‖) j)
      (Real.log ‖multF m C z‖ - multU m C z) := by
  have hG := isGenusOneData_multGammaC hw
  have hP0 : canonicalProd (multGammaC m) (fun w ↦ w⁻¹) z ≠ 0 :=
    fun h ↦ hz ((canonicalProd_eq_zero_iff hG).mp h)
  -- `log|P|` as a sum over `ℤ`
  have hP := hasSum_log_norm_canonicalProd hG hz
  rw [← (multGammaEquiv hw).hasSum_iff] at hP
  have hP' : HasSum (fun j : ℤ ↦ Real.log ‖1 - z / (multBary m j : ℂ)‖ + z.re / multBary m j)
      (Real.log ‖canonicalProd (multGammaC m) (fun w ↦ w⁻¹) z‖) := by
    refine hP.congr_fun fun j ↦ ?_
    simp only [Function.comp_apply, multGammaEquiv_apply]
    rw [← div_eq_mul_inv, Complex.div_ofReal_re]
  have hU := hasSum_multU hw C z
  have hL : HasSum (fun j ↦ multErr m (fun t ↦ Real.log |t|) j) (multLogConst m) :=
    (summable_multErr_log hw).of_abs.hasSum
  have hc : HasSum (fun j ↦ multLinCoeff m j * z.re) (multKappa m * z.re) :=
    ((summable_multLinCoeff hw).of_abs.hasSum).mul_right z.re
  have hsum := ((hP'.sub hU).add hL).sub hc
  have hF : Real.log ‖multF m C z‖ =
      -multKappa m * z.re + (C + multLogConst m) +
        Real.log ‖canonicalProd (multGammaC m) (fun w ↦ w⁻¹) z‖ := by
    rw [multF, log_norm_exp_mul _ _ _ _ hP0, multBeta]
    simp
  rw [hF]
  convert hsum using 1
  · funext j
    have hzj : z ≠ multBary m j := fun h ↦ hz ⟨multBary m j, ⟨j, rfl⟩, h.symm⟩
    rw [multErr_decomp hw j z hzj]
    ring
  · ring

/-- **Main identity.**  For `z ∉ Γ`: `log|F(z)| − U(z) = ∑_j E_j(log|· − z|)`. -/
theorem log_norm_multF_sub_multU {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (C : ℝ)
    {z : ℂ} (hz : z ∉ multGammaC m) :
    Real.log ‖multF m C z‖ - multU m C z =
      ∑' j : ℤ, multErr m (fun t ↦ Real.log ‖(t : ℂ) - z‖) j :=
  (hasSum_multErr_logDist_all hw C hz).tsum_eq.symm

/-- Off `ℝ`: `log|F(z)| − U(z) = −Re G(z)`. -/
theorem log_norm_multF_sub_multU_eq_multG {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b)
    (C : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Real.log ‖multF m C z‖ - multU m C z = -(multG m z).re := by
  rw [log_norm_multF_sub_multU hw C (notMem_multGammaC_of_im_ne_zero hz)]
  exact (hasSum_multErr_logDist hw hz).tsum_eq

/-! ## Estimate (2) -/

/-! ## Estimate (2): the three nearest intervals -/

/-- The three intervals `I_{k−1}, I_k, I_{k+1}` around `x ∈ I_k` lie within `3/a` of `x`. -/
theorem abs_sub_le_of_near {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (x : ℝ) {j : ℤ}
    (hj : j ∈ Finset.Icc (multIdx m x - 1) (multIdx m x + 1)) {t : ℝ}
    (ht : t ∈ Icc (multPt m j) (multPt m (j + 1))) : |t - x| ≤ 3 / a := by
  set k := multIdx m x with hk_def
  have hk : multPt m k ≤ x ∧ x < multPt m (k + 1) := multIdx_mem hw x
  rw [Finset.mem_Icc] at hj
  have hmono := (strictMono_multPt hw).monotone
  have h1 : multPt m (k - 1) ≤ multPt m j := hmono hj.1
  have h2 : multPt m (j + 1) ≤ multPt m (k + 1 + 1) := hmono (by omega)
  have l1 := (multPt_succ_sub_bounds hw (k - 1)).2
  have l2 := (multPt_succ_sub_bounds hw k).2
  have l3 := (multPt_succ_sub_bounds hw (k + 1)).2
  rw [show k - 1 + 1 = k by ring] at l1
  have e : 3 / a = 1 / a + 1 / a + 1 / a := by ring
  rw [abs_le]; constructor <;> linarith [ht.1, ht.2]

theorem norm_ofReal_sub_le_of_near {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {z : ℂ}
    (hz : |z.im| ≤ 1) {j : ℤ} (hj : j ∈ Finset.Icc (multIdx m z.re - 1) (multIdx m z.re + 1))
    {t : ℝ} (ht : t ∈ Icc (multPt m j) (multPt m (j + 1))) : ‖(t : ℂ) - z‖ ≤ 3 / a + 1 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, zero_sub, abs_neg]
  linarith [abs_sub_le_of_near hw z.re hj ht]

/-- The near integrals: `|∫_{I_j} log|t − z| m(t) dt| ≤ K₁(a, b)`. -/
theorem abs_integral_logDist_le_of_near {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b)
    {z : ℂ} (hz : |z.im| ≤ 1) {j : ℤ}
    (hj : j ∈ Finset.Icc (multIdx m z.re - 1) (multIdx m z.re + 1)) :
    |∫ t in multPt m j..multPt m (j + 1), Real.log ‖(t : ℂ) - z‖ * m t| ≤
      Real.log (3 / a + 1) + b * ∫ s in (-(3 / a))..(3 / a), |Real.log ‖(s : ℂ) - 0‖| := by
  set x := z.re with hx_def
  set x₀ := multPt m j with hx₀
  set x₁ := multPt m (j + 1) with hx₁
  have hx : x₀ ≤ x₁ := (multPt_lt_succ hw j).le
  have ha := hw.pos
  have hb := hw.b_pos
  have h3a : 0 < 3 / a := by positivity
  have hD : 1 ≤ 3 / a + 1 := by linarith
  have hlogD : 0 ≤ Real.log (3 / a + 1) := Real.log_nonneg hD
  have hint : IntervalIntegrable (fun t : ℝ ↦ Real.log ‖(t : ℂ) - z‖ * m t) volume x₀ x₁ :=
    hw.intervalIntegrable_mul (intervalIntegrable_log_norm_sub z x₀ x₁)
  have hup : ∫ t in x₀..x₁, Real.log ‖(t : ℂ) - z‖ * m t ≤ Real.log (3 / a + 1) := by
    have : ∫ t in x₀..x₁, Real.log ‖(t : ℂ) - z‖ * m t ≤
        ∫ t in x₀..x₁, Real.log (3 / a + 1) * m t :=
      intervalIntegral.integral_mono_on hx hint ((hw.intervalIntegrable _ _).const_mul _)
        fun t ht ↦ by
          refine mul_le_mul_of_nonneg_right ?_ (hw.nonneg t)
          have hn := norm_ofReal_sub_le_of_near hw hz hj ht
          rcases eq_or_lt_of_le (norm_nonneg ((t : ℂ) - z)) with h | h
          · rw [← h, Real.log_zero]; exact hlogD
          · exact Real.log_le_log h hn
    rwa [intervalIntegral.integral_const_mul, integral_multPt hw, mul_one] at this
  set Λ := ∫ s in (-(3 / a))..(3 / a), |Real.log ‖(s : ℂ) - 0‖| with hΛ_def
  have hΛ : 0 ≤ Λ := intervalIntegral.integral_nonneg (by linarith) fun _ _ ↦ abs_nonneg _
  have hlow : -(b * Λ) ≤ ∫ t in x₀..x₁, Real.log ‖(t : ℂ) - z‖ * m t := by
    have hL : IntervalIntegrable (fun t : ℝ ↦ |Real.log ‖(t : ℂ) - (x : ℂ)‖|) volume
        (x - 3 / a) (x + 3 / a) := (intervalIntegrable_log_norm_sub (x : ℂ) _ _).abs
    have h1 : ∫ t in x₀..x₁, -b * |Real.log ‖(t : ℂ) - (x : ℂ)‖| ≤
        ∫ t in x₀..x₁, Real.log ‖(t : ℂ) - z‖ * m t := by
      refine intervalIntegral.integral_mono_ae hx
        ((intervalIntegrable_log_norm_sub (x : ℂ) _ _).abs.const_mul _) hint ?_
      filter_upwards [ae_ne_real x] with t htx
      have hpos : 0 < ‖(t : ℂ) - (x : ℂ)‖ := by
        rw [norm_pos_iff, sub_ne_zero]; exact_mod_cast htx
      have hle : ‖(t : ℂ) - (x : ℂ)‖ ≤ ‖(t : ℂ) - z‖ := by
        have := Complex.abs_re_le_norm ((t : ℂ) - z)
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        simpa using this
      have hlog : Real.log ‖(t : ℂ) - (x : ℂ)‖ ≤ Real.log ‖(t : ℂ) - z‖ :=
        Real.log_le_log hpos hle
      have hm0 := hw.nonneg t
      have hmb := hw.ge t
      have h2 : -|Real.log ‖(t : ℂ) - (x : ℂ)‖| ≤ Real.log ‖(t : ℂ) - z‖ :=
        (neg_abs_le _).trans hlog
      have h3 := abs_nonneg (Real.log ‖(t : ℂ) - (x : ℂ)‖)
      show -b * |Real.log ‖(t : ℂ) - (x : ℂ)‖| ≤ Real.log ‖(t : ℂ) - z‖ * m t
      nlinarith
    have hx0 : x - 3 / a ≤ x₀ := by
      have := abs_sub_le_of_near hw x hj ⟨le_rfl, hx⟩
      rw [abs_le] at this; linarith
    have hx1 : x₁ ≤ x + 3 / a := by
      have := abs_sub_le_of_near hw x hj ⟨hx, le_rfl⟩
      rw [abs_le] at this; linarith
    have h2 : ∫ t in x₀..x₁, |Real.log ‖(t : ℂ) - (x : ℂ)‖| ≤
        ∫ t in (x - 3 / a)..(x + 3 / a), |Real.log ‖(t : ℂ) - (x : ℂ)‖| :=
      intervalIntegral.integral_mono_interval hx0 hx hx1 (ae_of_all _ fun t ↦ abs_nonneg _) hL
    have h3 : ∫ t in (x - 3 / a)..(x + 3 / a), |Real.log ‖(t : ℂ) - (x : ℂ)‖| = Λ := by
      have := intervalIntegral.integral_comp_sub_right
        (fun s : ℝ ↦ |Real.log ‖(s : ℂ) - 0‖|) x (a := x - 3 / a) (b := x + 3 / a)
      rw [show x - 3 / a - x = -(3 / a) by ring, show x + 3 / a - x = 3 / a by ring] at this
      rw [hΛ_def, ← this]
      refine intervalIntegral.integral_congr fun t _ ↦ ?_
      simp only [sub_zero, Complex.ofReal_sub]
    rw [intervalIntegral.integral_const_mul] at h1
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- The near point values: if `γ_{j'}` is at least as close to `z` as `γ_j`, `j ≠ j'`, then
`|log|γ_j − z|| ≤ K₂(a, b)`. -/
theorem abs_log_norm_sub_le_of_near {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {z : ℂ}
    (hz : |z.im| ≤ 1) {j j' : ℤ}
    (hj : j ∈ Finset.Icc (multIdx m z.re - 1) (multIdx m z.re + 1)) (hne : j ≠ j')
    (hmin : ‖z - multBary m j'‖ ≤ ‖z - multBary m j‖) :
    |Real.log ‖((multBary m j : ℝ) : ℂ) - z‖| ≤
      |Real.log (a / (2 * b ^ 2))| + |Real.log (3 / a + 1)| := by
  have ha := hw.pos
  have hb := hw.b_pos
  have hc : 0 < a / (2 * b ^ 2) := by positivity
  have hsep : a / b ^ 2 ≤ |multBary m j - multBary m j'| := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_sub_comm, abs_of_pos (by linarith [multBary_sub_ge hw h, div_pos ha (pow_pos hb 2)])]
      exact multBary_sub_ge hw h
    · rw [abs_of_pos (by linarith [multBary_sub_ge hw h, div_pos ha (pow_pos hb 2)])]
      exact multBary_sub_ge hw h
  have htri : |multBary m j - multBary m j'| ≤ ‖z - multBary m j‖ + ‖z - multBary m j'‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub ((multBary m j : ℂ)) z (multBary m j')
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev] at this
    exact this
  have hlow : a / (2 * b ^ 2) ≤ ‖((multBary m j : ℝ) : ℂ) - z‖ := by
    rw [norm_sub_rev]
    have : a / (2 * b ^ 2) = (a / b ^ 2) / 2 := by ring
    rw [this]; linarith
  have hmem : multBary m j ∈ Icc (multPt m j) (multPt m (j + 1)) := by
    have := multBary_mem hw j
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hup := norm_ofReal_sub_le_of_near hw hz hj hmem
  have hpos : 0 < ‖((multBary m j : ℝ) : ℂ) - z‖ := hc.trans_le hlow
  have l1 : Real.log (a / (2 * b ^ 2)) ≤ Real.log ‖((multBary m j : ℝ) : ℂ) - z‖ :=
    Real.log_le_log hc hlow
  have l2 : Real.log ‖((multBary m j : ℝ) : ℂ) - z‖ ≤ Real.log (3 / a + 1) :=
    Real.log_le_log hpos hup
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log (a / (2 * b ^ 2))), abs_nonneg (Real.log (3 / a + 1))]
  · linarith [le_abs_self (Real.log (3 / a + 1)), abs_nonneg (Real.log (a / (2 * b ^ 2)))]

/-- The distance to `Γ` is attained among `γ_{k−1}, γ_k, γ_{k+1}`, `k = j(Re z)`. -/
theorem exists_infDist_multGammaC_eq {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (z : ℂ) :
    ∃ i ∈ Finset.Icc (multIdx m z.re - 1) (multIdx m z.re + 1),
      (∀ j ∈ Finset.Icc (multIdx m z.re - 1) (multIdx m z.re + 1),
        ‖z - multBary m i‖ ≤ ‖z - multBary m j‖) ∧
      infDist z (multGammaC m) = ‖z - multBary m i‖ := by
  set k := multIdx m z.re with hk_def
  set N := Finset.Icc (k - 1) (k + 1) with hN
  obtain ⟨i, hi, hmin⟩ := N.exists_min_image (fun j ↦ ‖z - multBary m j‖)
    ⟨k, by simp [hN]⟩
  have hmem : ((multBary m i : ℝ) : ℂ) ∈ multGammaC m := ⟨multBary m i, ⟨i, rfl⟩, rfl⟩
  refine ⟨i, hi, hmin, le_antisymm ?_ ?_⟩
  · exact (infDist_le_dist_of_mem hmem).trans_eq (dist_eq_norm _ _)
  · rw [le_infDist ⟨_, hmem⟩]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    rw [dist_eq_norm]
    by_cases hj : j ∈ N
    · exact hmin j hj
    · have h2 : 2 ≤ |j - k| := by
        simp only [hN, Finset.mem_Icc, not_and_or, not_le] at hj
        rcases hj with h | h
        · rw [abs_of_neg (by omega)]; omega
        · rw [abs_of_pos (by omega)]; omega
      rcases norm_sub_multBary_far hw z h2 with ⟨h, _⟩ | ⟨h, _⟩
      · exact (hmin _ (by simp only [hN, Finset.mem_Icc, hk_def]; omega)).trans h
      · exact (hmin _ (by simp only [hN, Finset.mem_Icc, hk_def]; omega)).trans h

theorem integral_indicator_inv_sq_translate (δ x : ℝ) :
    ∫ t, {s : ℝ | δ ≤ |s - x|}.indicator (fun s ↦ ((s - x) ^ 2)⁻¹) t =
      ∫ t, {s : ℝ | δ ≤ |s - 0|}.indicator (fun s ↦ ((s - 0) ^ 2)⁻¹) t := by
  rw [← integral_sub_right_eq_self
    (fun t ↦ {s : ℝ | δ ≤ |s - 0|}.indicator (fun s ↦ ((s - 0) ^ 2)⁻¹) t) x]
  congr 1
  funext t
  simp only [indicator, Set.mem_ofPred_eq, sub_zero]

/-- Near the real axis: `|∑_j E_j(log|· − z|) − log dist(z, Γ)| ≤ K` (`K = K(a, b)`). -/
theorem exists_abs_sum_multErr_sub_log_infDist_le {m : ℝ → ℝ} {a b : ℝ}
    (hw : IsMultWeight m a b) :
    ∃ K : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → z ∉ multGammaC m →
      |(∑' j : ℤ, multErr m (fun t ↦ Real.log ‖(t : ℂ) - z‖) j) -
          Real.log (infDist z (multGammaC m))| ≤ K := by
  have ha := hw.pos
  have hb := hw.b_pos
  set K₁ := Real.log (3 / a + 1) + b * ∫ s in (-(3 / a))..(3 / a), |Real.log ‖(s : ℂ) - 0‖|
  set K₂ := |Real.log (a / (2 * b ^ 2))| + |Real.log (3 / a + 1)|
  set K₃ := 1 / (2 * a) *
    ∫ t, {s : ℝ | 1 / b ≤ |s - 0|}.indicator (fun s ↦ ((s - 0) ^ 2)⁻¹) t
  refine ⟨K₃ + 3 * K₁ + 3 * K₂, fun z hz1 _ ↦ ?_⟩
  set k := multIdx m z.re with hk_def
  set N := Finset.Icc (k - 1) (k + 1) with hN
  set E : ℤ → ℝ := fun j ↦ multErr m (fun t ↦ Real.log ‖(t : ℂ) - z‖) j with hE_def
  have hE : Summable E := (summable_multErr_logDist hw z).of_abs
  obtain ⟨i, hi, hmin, hd⟩ := exists_infDist_multGammaC_eq hw z
  -- the far part
  set F : ℝ → ℝ := fun t ↦ {s : ℝ | 1 / b ≤ |s - z.re|}.indicator (fun s ↦ ((s - z.re) ^ 2)⁻¹) t
  have hF : Integrable F := integrable_indicator_inv_sq (one_div_pos.mpr hb) z.re
  have hF0 : ∀ t, 0 ≤ F t := fun t ↦ by
    simp only [F, indicator]; split_ifs <;> positivity
  set far : ℤ → ℝ := fun j ↦ if j ∈ N then 0 else E j with hfar
  set near : ℤ → ℝ := fun j ↦ if j ∈ N then E j else 0 with hnear
  have hsplit : E = fun j ↦ near j + far j := by
    funext j; simp only [hnear, hfar]; split_ifs <;> simp
  have hnear_s : Summable near := summable_of_ne_finset_zero (s := N) fun j hj ↦ by
    simp [hnear, hj]
  have hnear_sum : ∑' j, near j = ∑ j ∈ N, E j := by
    rw [tsum_eq_sum (s := N) fun j hj ↦ by simp [hnear, hj]]
    exact Finset.sum_congr rfl fun j hj ↦ by simp [hnear, hj]
  have hbound : ∀ j, |far j| ≤ 1 / (2 * a) * ∫ t in multPt m j..multPt m (j + 1), F t := by
    intro j
    by_cases hj : j ∈ N
    · simp only [hfar, hj, ↓reduceIte, abs_zero]
      exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg
        (multPt_lt_succ hw j).le fun t _ ↦ hF0 t)
    · simp only [hfar, hj, ↓reduceIte]
      have h2 : 2 ≤ |j - k| := by
        simp only [hN, Finset.mem_Icc, not_and_or, not_le] at hj
        rcases hj with h | h
        · rw [abs_of_neg (by omega)]; omega
        · rw [abs_of_pos (by omega)]; omega
      exact abs_multErr_logDist_le hw z h2
  have hsumF := (hasSum_integral_multPt hw hF).mul_left (1 / (2 * a))
  have hfar_abs : Summable fun j ↦ |far j| :=
    Summable.of_nonneg_of_le (fun j ↦ abs_nonneg _) hbound hsumF.summable
  have hfar_s : Summable far := hfar_abs.of_abs
  have hfar_le : |∑' j, far j| ≤ K₃ := by
    calc |∑' j, far j| ≤ ∑' j, |far j| := by
          simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := far) hfar_abs
      _ ≤ ∑' j, 1 / (2 * a) * ∫ t in multPt m j..multPt m (j + 1), F t :=
          hfar_abs.tsum_le_tsum hbound hsumF.summable
      _ = K₃ := by
          rw [hsumF.tsum_eq, integral_indicator_inv_sq_translate]
  -- the near part
  have hcard : (N.erase i).card ≤ 3 := by
    refine (Finset.card_erase_le).trans ?_
    rw [hN, Int.card_Icc, show k + 1 + 1 - (k - 1) = 3 by ring]
    rfl
  have hcardN : N.card ≤ 3 := by
    rw [hN, Int.card_Icc, show k + 1 + 1 - (k - 1) = 3 by ring]
    rfl
  have hpts : |∑ j ∈ N.erase i, Real.log ‖((multBary m j : ℝ) : ℂ) - z‖| ≤ 3 * K₂ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ K₂ fun j hj ↦ ?_).trans ?_
    · exact abs_log_norm_sub_le_of_near hw hz1 (Finset.mem_of_mem_erase hj)
        (Finset.ne_of_mem_erase hj) (hmin j (Finset.mem_of_mem_erase hj))
    · rw [nsmul_eq_mul]
      have : 0 ≤ K₂ := by positivity
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) this
  have hints : |∑ j ∈ N, ∫ t in multPt m j..multPt m (j + 1), Real.log ‖(t : ℂ) - z‖ * m t|
      ≤ 3 * K₁ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ K₁ fun j hj ↦
      abs_integral_logDist_le_of_near hw hz1 hj).trans ?_
    rw [nsmul_eq_mul]
    have h3a : 0 < 3 / a := by positivity
    have : 0 ≤ K₁ := by
      have h1 : 0 ≤ Real.log (3 / a + 1) := Real.log_nonneg (by linarith)
      have h2 : 0 ≤ ∫ s in (-(3 / a))..(3 / a), |Real.log ‖(s : ℂ) - 0‖| :=
        intervalIntegral.integral_nonneg (by linarith) fun _ _ ↦ abs_nonneg _
      positivity
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardN) this
  have hnear_eq : ∑ j ∈ N, E j - Real.log (infDist z (multGammaC m)) =
      (∑ j ∈ N.erase i, Real.log ‖((multBary m j : ℝ) : ℂ) - z‖) -
        ∑ j ∈ N, ∫ t in multPt m j..multPt m (j + 1), Real.log ‖(t : ℂ) - z‖ * m t := by
    simp only [hE_def, multErr, Finset.sum_sub_distrib]
    rw [← Finset.add_sum_erase N _ hi, hd, norm_sub_rev]
    ring
  have htsum : ∑' j, E j = ∑ j ∈ N, E j + ∑' j, far j := by
    have : ∑' j, E j = ∑' j, (near j + far j) := by rw [hsplit]
    rw [this, hnear_s.tsum_add hfar_s, hnear_sum]
  rw [show (∑' j : ℤ, multErr m (fun t ↦ Real.log ‖(t : ℂ) - z‖) j) = ∑' j, E j from rfl, htsum]
  have : (∑ j ∈ N, E j + ∑' j, far j) - Real.log (infDist z (multGammaC m)) =
      ((∑ j ∈ N.erase i, Real.log ‖((multBary m j : ℝ) : ℂ) - z‖) -
        ∑ j ∈ N, ∫ t in multPt m j..multPt m (j + 1), Real.log ‖(t : ℂ) - z‖ * m t) +
        ∑' j, far j := by
    rw [← hnear_eq]; ring
  rw [this]
  calc _ ≤ |(∑ j ∈ N.erase i, Real.log ‖((multBary m j : ℝ) : ℂ) - z‖) -
        ∑ j ∈ N, ∫ t in multPt m j..multPt m (j + 1), Real.log ‖(t : ℂ) - z‖ * m t| +
        |∑' j, far j| := abs_add_le _ _
    _ ≤ (3 * K₂ + 3 * K₁) + K₃ := by
        gcongr
        exact (abs_sub _ _).trans (add_le_add hpts hints)
    _ = K₃ + 3 * K₁ + 3 * K₂ := by ring

/-- **Estimate (2)**: `|F(z)| e^{−U(z)} ≃ dist(z, Γ)` for `|Im z| ≤ 1`. -/
theorem multF_estimate_two {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (C : ℝ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℂ, |z.im| ≤ 1 →
      c₁ * infDist z (multGammaC m) ≤ ‖multF m C z‖ * Real.exp (-multU m C z) ∧
      ‖multF m C z‖ * Real.exp (-multU m C z) ≤ c₂ * infDist z (multGammaC m) := by
  obtain ⟨K, hK⟩ := exists_abs_sum_multErr_sub_log_infDist_le hw
  refine ⟨Real.exp (-K), Real.exp K, Real.exp_pos _, Real.exp_pos _, fun z hz ↦ ?_⟩
  by_cases hzΓ : z ∈ multGammaC m
  · have hF : multF m C z = 0 := (multF_eq_zero_iff hw C z).2 (mem_multGammaC_iff.1 hzΓ)
    have hd : infDist z (multGammaC m) = 0 := infDist_zero_of_mem hzΓ
    simp [hF, hd]
  · have hF0 : multF m C z ≠ 0 := fun h ↦
      hzΓ (mem_multGammaC_iff.2 ((multF_eq_zero_iff hw C z).1 h))
    have hS := hK z hz hzΓ
    rw [← log_norm_multF_sub_multU hw C hzΓ] at hS
    obtain ⟨i, _, _, hd⟩ := exists_infDist_multGammaC_eq hw z
    have hdpos : 0 < infDist z (multGammaC m) := by
      rw [hd, norm_pos_iff, sub_ne_zero]
      intro h; exact hzΓ ⟨multBary m i, ⟨i, rfl⟩, h.symm⟩
    have hexp : ‖multF m C z‖ * Real.exp (-multU m C z) =
        Real.exp (Real.log ‖multF m C z‖ - multU m C z) := by
      rw [Real.exp_sub, Real.exp_log (norm_pos_iff.mpr hF0), Real.exp_neg, div_eq_mul_inv]
    rw [hexp]
    rw [abs_le] at hS
    constructor
    · calc Real.exp (-K) * infDist z (multGammaC m) =
            Real.exp (Real.log (infDist z (multGammaC m)) - K) := by
            rw [Real.exp_sub, Real.exp_log hdpos, Real.exp_neg]; ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    · calc Real.exp (Real.log ‖multF m C z‖ - multU m C z) ≤
            Real.exp (Real.log (infDist z (multGammaC m)) + K) := Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp K * infDist z (multGammaC m) := by
            rw [Real.exp_add, Real.exp_log hdpos]; ring

/-! ## The logarithm `L`, the conjugate `V`, estimate (3) -/

theorem differentiableOn_multL {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (C : ℝ) :
    DifferentiableOn ℂ (multL m C) {z | z.im ≠ 0} := by
  unfold multL
  have hΩ : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  refine (((differentiable_id.const_mul _).add_const _).differentiableOn).add
    (differentiableOn_canonicalLog (isGenusOneData_multGammaC hw) hΩ fun z hz a ha ↦ ?_)
  exact one_sub_div_mem_slitPlane (im_eq_zero_of_mem_multGammaC ha) hz

theorem exp_multL {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (C : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) : Complex.exp (multL m C z) = multF m C z := by
  unfold multL multF
  rw [Complex.exp_add, exp_canonicalLog (isGenusOneData_multGammaC hw)
    fun a ha ↦ one_sub_div_mem_slitPlane (im_eq_zero_of_mem_multGammaC ha) hz]

theorem multL_conj (m : ℝ → ℝ) (C : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) : multL m C (conj z) = conj (multL m C z) := by
  unfold multL
  rw [canonicalLog_conj conj_mem_multGammaC
    (fun a _ ↦ by rw [map_inv₀])
    fun a ha ↦ one_sub_div_mem_slitPlane (im_eq_zero_of_mem_multGammaC ha) hz]
  simp [map_add, map_mul, map_neg, Complex.conj_ofReal]

/-- `U + iV = L + G` off `ℝ`. -/
theorem multU_add_I_mul_multV {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (C : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) :
    (multU m C z : ℂ) + Complex.I * multV m C z = multL m C z + multG m z := by
  have hre : (multL m C z + multG m z).re = multU m C z := by
    have h1 : (multL m C z).re = Real.log ‖multF m C z‖ := by
      rw [← exp_multL hw C hz, Complex.norm_exp, Real.log_exp]
    have h2 := log_norm_multF_sub_multU_eq_multG hw C hz
    rw [add_re, h1]
    linarith
  have hV : multV m C z = (multL m C z + multG m z).im := by
    rw [multV, ite_eq_right hz]
  apply Complex.ext
  · simp [hre]
  · simp [hV]

theorem multV_conj (m : ℝ → ℝ) (C : ℝ) (z : ℂ) :
    multV m C (conj z) = -multV m C z := by
  by_cases hz : z.im = 0
  · have hz' : ((starRingEnd ℂ) z).im = 0 := by rw [Complex.conj_im, hz, neg_zero]
    rw [multV, multV, ite_eq_left hz, ite_eq_left hz', neg_zero]
  · have hz' : ((starRingEnd ℂ) z).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.mpr hz
    rw [multV, multV, ite_eq_right hz, ite_eq_right hz', multL_conj m C hz, multG_conj, ← map_add,
      Complex.conj_im]

theorem differentiableOn_multU_add_I_mul_multV {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b)
    (C : ℝ) :
    DifferentiableOn ℂ (fun z ↦ (multU m C z : ℂ) + Complex.I * multV m C z) {z | z.im ≠ 0} :=
  ((differentiableOn_multL hw C).add (differentiableOn_multG hw)).congr
    fun _ hz ↦ multU_add_I_mul_multV hw C hz

/-- **Estimate (3)**, with the sharper constant `π/(2a)`: `L − U − iV = −G`. -/
theorem multF_estimate_three {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (C : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) :
    ‖multL m C z - multU m C z - Complex.I * multV m C z‖ ≤ Real.pi / (2 * a) / |z.im| := by
  have h : multL m C z - multU m C z - Complex.I * multV m C z = -multG m z := by
    have := multU_add_I_mul_multV hw C hz
    linear_combination -this
  rw [h, norm_neg]
  exact norm_multG_le hw hz

/-! ## Lemma 3 -/

/-- **Lemma 3** (the multiplier lemma, p. 405).  `m ≃ 1` is written `a ≤ m ≤ b` with `a > 0`;
`π ‖1/m‖_∞` is replaced by the (larger or equal) `π / a`. -/
theorem lemma3 {m : ℝ → ℝ} (hm : Measurable m) {a b : ℝ} (ha : 0 < a) (hlow : ∀ t, a ≤ m t)
    (hup : ∀ t, m t ≤ b) (C : ℝ) :
    ∃ (F : ℂ → ℂ) (Γ : Set ℝ), Differentiable ℂ F ∧ (∀ z, F z = 0 ↔ ∃ γ ∈ Γ, z = γ) ∧
      IsSeparated ((fun t : ℝ ↦ (t : ℂ)) '' Γ) ∧ (0 : ℝ) ∉ Γ ∧
      (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℂ, |z.im| ≤ 1 →
        c₁ * Metric.infDist z ((fun t : ℝ ↦ (t : ℂ)) '' Γ) ≤ ‖F z‖ * Real.exp (-multU m C z) ∧
        ‖F z‖ * Real.exp (-multU m C z) ≤ c₂ * Metric.infDist z ((fun t : ℝ ↦ (t : ℂ)) '' Γ)) ∧
      ∃ (V : ℂ → ℝ) (L : ℂ → ℂ),
        DifferentiableOn ℂ (fun z ↦ (multU m C z : ℂ) + Complex.I * V z) {z | z.im ≠ 0} ∧
        (∀ z, V ((starRingEnd ℂ) z) = -V z) ∧
        DifferentiableOn ℂ L {z | z.im ≠ 0} ∧ (∀ z, z.im ≠ 0 → Complex.exp (L z) = F z) ∧
        ∀ z, z.im ≠ 0 → ‖L z - multU m C z - Complex.I * V z‖ ≤ Real.pi / a / |z.im| := by
  have hw : IsMultWeight m a b := ⟨hm, ha, hlow, hup⟩
  refine ⟨multF m C, multGamma m, differentiable_multF hw C, multF_eq_zero_iff hw C,
    isSeparated_multGamma hw, zero_notMem_multGamma hw, multF_estimate_two hw C, multV m C,
    multL m C, differentiableOn_multU_add_I_mul_multV hw C, multV_conj m C,
    differentiableOn_multL hw C, fun z hz ↦ exp_multL hw C hz, fun z hz ↦ ?_⟩
  refine (multF_estimate_three hw C hz).trans ?_
  have hy : 0 < |z.im| := abs_pos.mpr hz
  have : Real.pi / (2 * a) ≤ Real.pi / a := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le ha (by linarith)
  exact div_le_div_of_nonneg_right this hy.le

end OCS
