import FourierFrames.Cited.Pavlov.CellBounds
import FourierFrames.PW.PlancherelPolya

/-!
# Finite weighted tests for the Pavlov argument

Elementary finite-matrix necessities and imaginary-line sampling estimates.
The planned A2 transfer is described in `blueprint/P5_A2.md`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal

noncomputable section
namespace FF.Pavlov

/-- Plancherel–Pólya on a fixed horizontal line, with a uniform constant. -/
theorem shifted_plancherelPolya {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    ∃ C : ℝ≥0, ∀ Λ : Set ℝ, IsSepBy δ Λ → ∀ f : ℂ → ℂ, MemPW f →
      sampleSum Λ (fun z ↦ f (z + (y : ℂ) * I)) ≤ C * pwNormSq f := by
  obtain ⟨C, hC⟩ := plancherelPolya paleyWiener_holds hδ
  refine ⟨C * (ENNReal.ofReal (Real.exp (2 * Real.pi * |y|))).toNNReal, ?_⟩
  intro Λ hΛ f hf
  have hpp := hC Λ hΛ _ (pw_translate_I paleyWiener_holds hf y)
  have hn := pw_line_integral_le paleyWiener_holds hf y
  change pwNormSq (fun z ↦ f (z + (y : ℂ) * I)) ≤ _ at hn
  calc
    _ ≤ (C : ℝ≥0∞) * pwNormSq (fun z ↦ f (z + (y : ℂ) * I)) := hpp
    _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * pwNormSq f) :=
      mul_le_mul' le_rfl hn
    _ = _ := by rw [ENNReal.coe_mul, ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]; ring

/-- A finite portion of the shifted sample sequence obeys the same bound. -/
theorem shifted_finite_sampling {Γ : Set ℝ} (hΓ : IsSeparated Γ) (y : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : Finset Γ) (f : ℂ → ℂ), MemPW f →
      (∑ j ∈ t, ‖f ((j : ℂ) + (y : ℂ) * I)‖^2) ≤ C * (pwNormSq f).toReal := by
  obtain ⟨δ, hδ, hsep⟩ := hΓ
  obtain ⟨C, hC⟩ := shifted_plancherelPolya hδ y
  refine ⟨(C : ℝ) + 1, by positivity, ?_⟩
  intro t f hf
  have hsum : (∑ j ∈ t, ‖f ((j : ℂ) + (y : ℂ) * I)‖ₑ^2) ≤
      sampleSum Γ (fun z ↦ f (z + (y : ℂ) * I)) :=
    ENNReal.sum_le_tsum t
  have h := hsum.trans (hC Γ hsep f hf)
  have hfin : (C : ℝ≥0∞) * pwNormSq f ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (pwNormSq_ne_top hf)
  have hr := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_sum (fun _ _ ↦ by simp), ENNReal.toReal_mul] at hr
  simp only [ENNReal.toReal_pow, toReal_enorm, ENNReal.coe_toReal] at hr
  exact hr.trans (by gcongr; norm_num)

/-- Off the real nodes, synthesis is a finite Cauchy sum times the generator. -/
theorem GeneratingData.cardinal_synthesis_cauchy {Γ : Set ℝ} (d : GeneratingData Γ)
    (s : Finset Γ) (b : Γ → ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    (∑ k ∈ s, (b k * deriv d.G (k : ℂ)) * cardinal d.G (k : ℝ) z) =
      d.G z * ∑ k ∈ s, b k / (z - (k : ℂ)) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hne : z - (k : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.im (sub_eq_zero.mp h)
    simp only [Complex.ofReal_im] at hh
    exact hz hh
  have hid := d.cardinal_mul_sub k.2 z
  field_simp
  linear_combination (b k) * hid

/-- Uniform shifted sampling and cardinal synthesis control the weighted Cauchy matrix. -/
theorem GeneratingData.weighted_cauchy_bound {Γ : Set ℝ} (d : GeneratingData Γ)
    (hΓ : IsSeparated Γ) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hshift : ∀ j : Γ, c * ‖deriv d.G (j : ℂ)‖ ≤
      ‖d.G ((j : ℂ) + (ε : ℂ) * I)‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s t : Finset Γ) (b : Γ → ℂ),
      (∑ j ∈ t, ‖deriv d.G (j : ℂ)‖^2 *
        ‖∑ k ∈ s, b k / ((j : ℂ) + (ε : ℂ) * I - (k : ℂ))‖^2) ≤
      C * ∑ k ∈ s, ‖deriv d.G (k : ℂ)‖^2 * ‖b k‖^2 := by
  obtain ⟨S, hS, hsyn⟩ := d.cardinal_synthesis_bound
  obtain ⟨P, hP, hsample⟩ := shifted_finite_sampling hΓ ε
  refine ⟨P * S / c^2, by positivity, ?_⟩
  intro s t b
  let a : Γ → ℂ := fun k ↦ b k * deriv d.G (k : ℂ)
  let f : ℂ → ℂ := fun z ↦ ∑ k ∈ s, a k * cardinal d.G (k : ℝ) z
  have hf : MemPW f := d.cardinal_synthesis_mem s a
  have hn := (hsample t f hf).trans (mul_le_mul_of_nonneg_left (hsyn s a) hP.le)
  have ha : (∑ k ∈ s, ‖a k‖^2) =
      ∑ k ∈ s, ‖deriv d.G (k : ℂ)‖^2 * ‖b k‖^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [a]
    rw [norm_mul, mul_pow, mul_comm]
  rw [ha] at hn
  have hp (j : Γ) :
      c^2 * (‖deriv d.G (j : ℂ)‖^2 *
        ‖∑ k ∈ s, b k / ((j : ℂ) + (ε : ℂ) * I - (k : ℂ))‖^2) ≤
      ‖f ((j : ℂ) + (ε : ℂ) * I)‖^2 := by
    have hz : (((j : ℂ) + (ε : ℂ) * I) : ℂ).im ≠ 0 := by simpa using hε.ne'
    have hid := d.cardinal_synthesis_cauchy s b hz
    change f ((j : ℂ) + (ε : ℂ) * I) = _ at hid
    rw [hid, norm_mul, mul_pow]
    have hh := pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg _)) (hshift j) 2
    have hm := mul_le_mul_of_nonneg_right hh
      (sq_nonneg ‖∑ k ∈ s, b k / ((j : ℂ) + (ε : ℂ) * I - (k : ℂ))‖)
    nlinarith [hm]
  have hl := Finset.sum_le_sum (fun j (_ : j ∈ t) ↦ hp j)
  rw [← Finset.mul_sum] at hl
  have ht := hl.trans hn
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  calc
    _ ≤ P * (S * ∑ k ∈ s, ‖deriv d.G (k : ℂ)‖^2 * ‖b k‖^2) := by nlinarith [ht]
    _ = _ := by ring

variable {ι : Type*}

/-- The total weight on a finite set. -/
def weightSum (s : Finset ι) (v : ι → ℝ) : ℝ := ∑ k ∈ s, v k

/-- The total reciprocal weight on a finite set. -/
def invWeightSum (s : Finset ι) (v : ι → ℝ) : ℝ := ∑ k ∈ s, (v k)⁻¹

/-- Cauchy–Schwarz supplies the lower A2 bound on every finite set. -/
theorem card_sq_le_weightSum_mul_invWeightSum (s : Finset ι) (v : ι → ℝ)
    (hv : ∀ k ∈ s, 0 < v k) :
    (s.card : ℝ)^2 ≤ weightSum s v * invWeightSum s v := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun k hk ↦ (hv k hk).le) (fun k hk ↦ (inv_pos.mpr (hv k hk)).le)
    (r := fun _ ↦ (1 : ℝ)) (fun k hk ↦ by simp [(hv k hk).ne'])
  simpa [weightSum, invWeightSum] using h

/-- Two cross tests and the companion block's lower bound give diagonal A2. -/
theorem diagonal_of_cross_tests {WI VI WJ VJ K n : ℝ}
    (hWI : 0 ≤ WI) (hVI : 0 ≤ VI) (hWJ : 0 ≤ WJ) (hVJ : 0 ≤ VJ)
    (hn : 0 < n) (hlower : n^2 ≤ WJ * VJ)
    (hcross₁ : WJ * VI ≤ K) (hcross₂ : WI * VJ ≤ K) :
    WI * VI ≤ K^2 / n^2 := by
  have hK : 0 ≤ K := (mul_nonneg hWJ hVI).trans hcross₁
  have hmul := mul_le_mul hcross₁ hcross₂ (mul_nonneg hWI hVJ) hK
  have hl := mul_le_mul_of_nonneg_left hlower (mul_nonneg hWI hVI)
  apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
  nlinarith [hmul, hl]

/-- A matrix whose entries are bounded below has a positive block test. -/
theorem cross_test_of_positive_matrix [DecidableEq ι] (s t : Finset ι) (v : ι → ℝ)
    (T : ι → ι → ℝ) {κ C : ℝ} (hs : s.Nonempty)
    (hv : ∀ k ∈ s ∪ t, 0 < v k) (hκ : 0 < κ)
    (hT : ∀ j ∈ t, ∀ k ∈ s, κ ≤ T j k)
    (hbound : (∑ j ∈ t, v j * (∑ k ∈ s, T j k / v k)^2) ≤
      C * invWeightSum s v) :
    weightSum t v * invWeightSum s v ≤ C / κ^2 := by
  classical
  have hvs : ∀ k ∈ s, 0 < v k := fun k hk ↦ hv k (Finset.mem_union_left t hk)
  have hvt : ∀ k ∈ t, 0 < v k := fun k hk ↦ hv k (Finset.mem_union_right s hk)
  have hV : 0 < invWeightSum s v := by
    exact Finset.sum_pos (fun k hk ↦ inv_pos.mpr (hvs k hk)) hs
  have hW : 0 ≤ weightSum t v := Finset.sum_nonneg (fun j hj ↦ (hvt j hj).le)
  have hterm (j : ι) (hj : j ∈ t) :
      κ * invWeightSum s v ≤ ∑ k ∈ s, T j k / v k := by
    rw [invWeightSum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k hk ↦ by
      simpa only [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right (hT j hj k hk) (inv_pos.mpr (hvs k hk)).le)
  have hsq (j : ι) (hj : j ∈ t) :
      (κ * invWeightSum s v)^2 ≤ (∑ k ∈ s, T j k / v k)^2 := by
    exact pow_le_pow_left₀ (mul_pos hκ hV).le (hterm j hj) 2
  have hsum : weightSum t v * (κ * invWeightSum s v)^2 ≤
      ∑ j ∈ t, v j * (∑ k ∈ s, T j k / v k)^2 := by
    rw [weightSum, Finset.sum_mul]
    exact Finset.sum_le_sum (fun j hj ↦
      mul_le_mul_of_nonneg_left (hsq j hj) (hvt j hj).le)
  have hc : (weightSum t v * κ^2 * invWeightSum s v) * invWeightSum s v ≤
      C * invWeightSum s v := by nlinarith [hsum.trans hbound]
  have hc' := (mul_le_mul_iff_left₀ hV).mp hc
  apply (le_div_iff₀ (sq_pos_of_pos hκ)).mpr
  nlinarith [hc']

/-- The real-part block test applies directly to a complex matrix norm bound. -/
theorem cross_test_of_complex_matrix [DecidableEq ι] (s t : Finset ι) (v : ι → ℝ)
    (T : ι → ι → ℂ) {κ C : ℝ} (hs : s.Nonempty)
    (hv : ∀ k ∈ s ∪ t, 0 < v k) (hκ : 0 < κ)
    (hT : ∀ j ∈ t, ∀ k ∈ s, κ ≤ (T j k).re)
    (hbound : (∑ j ∈ t, v j * ‖∑ k ∈ s, ((v k)⁻¹ : ℂ) * T j k‖^2) ≤
      C * invWeightSum s v) :
    weightSum t v * invWeightSum s v ≤ C / κ^2 := by
  apply cross_test_of_positive_matrix s t v (fun j k ↦ (T j k).re) hs hv hκ hT
  apply le_trans (Finset.sum_le_sum ?_) hbound
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hv j (Finset.mem_union_right s hj)).le
  have he : (∑ k ∈ s, (T j k).re / v k) =
      (∑ k ∈ s, ((v k)⁻¹ : ℂ) * T j k).re := by
    simp only [← Complex.ofReal_inv, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he]
  exact (sq_abs _).symm.trans_le
    (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2)

/-- A Cauchy kernel has a uniform positive real part between ordered blocks. -/
theorem cauchy_re_lower {r ε L U : ℝ} (hL : 0 < L) (hr : L ≤ r)
    (hU : r ≤ U) :
    L / (U^2 + ε^2) ≤ (((r : ℂ) + (ε : ℂ) * I)⁻¹).re := by
  have hr0 : 0 < r := hL.trans_le hr
  have hU0 : 0 < U := hr0.trans_le hU
  have hden : 0 < r^2 + ε^2 := by positivity
  have hdenU : 0 < U^2 + ε^2 := by positivity
  have he : (((r : ℂ) + (ε : ℂ) * I)⁻¹).re = r / (r^2 + ε^2) := by
    simp [Complex.inv_re, Complex.normSq_apply, pow_two]
  rw [he, div_le_div_iff₀ hdenU hden]
  have hs : r^2 ≤ U^2 := pow_le_pow_left₀ hr0.le hU 2
  nlinarith

/-- Telescoping the gap bounds controls any two ordered grid nodes. -/
theorem Grid.point_sub_bounds {Γ : Set ℝ} (g : Grid Γ) {k j : ℤ} (hkj : k ≤ j) :
    g.lower * ((j-k : ℤ) : ℝ) ≤ g.point j - g.point k ∧
      g.point j - g.point k ≤ g.upper * ((j-k : ℤ) : ℝ) := by
  have hl := g.monotone_sub_lower hkj
  have hm : Monotone (fun k : ℤ ↦ g.upper * (k : ℝ) - g.point k) := by
    apply monotone_int_of_le_succ
    intro i
    have h := g.gap_upper i
    push_cast
    linarith
  have hu := hm hkj
  push_cast
  constructor <;> linarith

/-- The real Cauchy kernel between separated N-blocks is bounded below by c/N. -/
theorem Grid.block_cauchy_re_lower {Γ : Set ℝ} (g : Grid Γ)
    {a N j k : ℤ} {ε : ℝ} (hN : 0 < N) (hε : 0 ≤ ε) (hεu : ε ≤ g.upper)
    (hk : k ∈ Finset.Ico a (a+N))
    (hj : j ∈ Finset.Ico (a+2*N) (a+3*N)) :
    (g.lower / (10 * g.upper^2)) / (N : ℝ) ≤
      (((g.point j : ℂ) + (ε : ℂ)*I - (g.point k : ℂ))⁻¹).re := by
  have hk' := Finset.mem_Ico.mp hk
  have hj' := Finset.mem_Ico.mp hj
  have hkj : k ≤ j := by omega
  obtain ⟨hl, hu⟩ := g.point_sub_bounds hkj
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hidxL : (N : ℝ) ≤ ((j-k : ℤ) : ℝ) := by exact_mod_cast (show N ≤ j-k by omega)
  have hidxU : ((j-k : ℤ) : ℝ) ≤ 3*(N : ℝ) := by exact_mod_cast (show j-k ≤ 3*N by omega)
  have hL : g.lower * (N : ℝ) ≤ g.point j-g.point k :=
    (mul_le_mul_of_nonneg_left hidxL g.lower_pos.le).trans hl
  have hU : g.point j-g.point k ≤ 3*g.upper*(N : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hidxU g.upper_pos.le]
  have he := cauchy_re_lower (ε := ε) (mul_pos g.lower_pos (by linarith : 0 < (N : ℝ))) hL hU
  have hident : (g.point j : ℂ) + (ε : ℂ)*I - (g.point k : ℂ) =
      ((g.point j-g.point k : ℝ) : ℂ) + (ε : ℂ)*I := by push_cast; ring
  rw [hident]
  apply le_trans _ he
  have hu0 := g.upper_pos
  have hn0 : 0 < (N : ℝ) := by linarith
  have hd : 0 < (3*g.upper*(N : ℝ))^2+ε^2 := by positivity
  have hg : 0 < 10*g.upper^2 := by positivity
  rw [div_div, div_le_div_iff₀ (mul_pos hg (by linarith)) hd]
  have heps : ε^2 ≤ g.upper^2 := pow_le_pow_left₀ hε hεu 2
  have hn2 : 1 ≤ (N : ℝ)^2 := by nlinarith
  have hx : g.upper^2 ≤ g.upper^2 * (N : ℝ)^2 := by
    simpa using mul_le_mul_of_nonneg_left hn2 (sq_nonneg g.upper)
  nlinarith [mul_nonneg g.lower_pos.le (sub_nonneg.mpr (heps.trans hx))]

/-- Testing a weighted operator on reciprocal weights gives a cross-weight estimate. -/
theorem cross_test_of_weighted_operator [DecidableEq ι] (s t : Finset ι)
    (v : ι → ℝ) (T : ι → ι → ℂ) {κ C : ℝ} (hs : s.Nonempty)
    (hv : ∀ k ∈ s ∪ t, 0 < v k) (hκ : 0 < κ)
    (hT : ∀ j ∈ t, ∀ k ∈ s, κ ≤ (T j k).re)
    (hbound : ∀ b : ι → ℂ,
      (∑ j ∈ t, v j * ‖∑ k ∈ s, b k * T j k‖^2) ≤
        C * ∑ k ∈ s, v k * ‖b k‖^2) :
    weightSum t v * invWeightSum s v ≤ C / κ^2 := by
  apply cross_test_of_complex_matrix s t v T hs hv hκ hT
  have h := hbound (fun k ↦ ((v k)⁻¹ : ℂ))
  have he : (∑ k ∈ s, v k * ‖((v k)⁻¹ : ℂ)‖^2) = invWeightSum s v := by
    apply Finset.sum_congr rfl
    intro k hk
    have hp := hv k (Finset.mem_union_left t hk)
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    field_simp
  rwa [he] at h

/-- Positive real parts of the shifted Cauchy kernel give cross derivative-weight bounds. -/
theorem GeneratingData.cauchy_cross_bound {Γ : Set ℝ} (d : GeneratingData Γ)
    (hΓ : IsSeparated Γ) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hshift : ∀ j : Γ, c * ‖deriv d.G (j : ℂ)‖ ≤
      ‖d.G ((j : ℂ) + (ε : ℂ) * I)‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s t : Finset Γ) (κ : ℝ), s.Nonempty → 0 < κ →
      (∀ j ∈ t, ∀ k ∈ s, κ ≤
        (((j : ℂ) + (ε : ℂ) * I - (k : ℂ))⁻¹).re) →
      weightSum t (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) *
        invWeightSum s (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) ≤ C / κ^2 := by
  classical
  obtain ⟨C, hC, hbound⟩ := d.weighted_cauchy_bound hΓ hε hc hshift
  refine ⟨C, hC, ?_⟩
  intro s t κ hs hκ hT
  refine cross_test_of_weighted_operator s t
    (fun k ↦ ‖deriv d.G (k : ℂ)‖^2)
    (fun j k ↦ ((j : ℂ) + (ε : ℂ) * I - (k : ℂ))⁻¹) hs
    (fun k _ ↦ sq_pos_of_pos (norm_pos_iff.mpr (d.simple k.2))) hκ hT ?_
  intro b
  simpa only [div_eq_mul_inv] using hbound s t b

/-- Negative real parts give the reverse cross test by negating the matrix. -/
theorem GeneratingData.cauchy_cross_bound_negative {Γ : Set ℝ} (d : GeneratingData Γ)
    (hΓ : IsSeparated Γ) {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hshift : ∀ j : Γ, c * ‖deriv d.G (j : ℂ)‖ ≤
      ‖d.G ((j : ℂ) + (ε : ℂ) * I)‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s t : Finset Γ) (κ : ℝ), s.Nonempty → 0 < κ →
      (∀ j ∈ t, ∀ k ∈ s, κ ≤
        -(((j : ℂ) + (ε : ℂ) * I - (k : ℂ))⁻¹).re) →
      weightSum t (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) *
        invWeightSum s (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) ≤ C / κ^2 := by
  classical
  obtain ⟨C, hC, hbound⟩ := d.weighted_cauchy_bound hΓ hε hc hshift
  refine ⟨C, hC, ?_⟩
  intro s t κ hs hκ hT
  refine cross_test_of_weighted_operator s t
    (fun k ↦ ‖deriv d.G (k : ℂ)‖^2)
    (fun j k ↦ -((j : ℂ) + (ε : ℂ) * I - (k : ℂ))⁻¹) hs
    (fun k _ ↦ sq_pos_of_pos (norm_pos_iff.mpr (d.simple k.2))) hκ (by simpa only [Complex.neg_re] using hT) ?_
  intro b
  simpa only [mul_neg, Finset.sum_neg_distrib, norm_neg, div_eq_mul_inv] using hbound s t b

/-- A grid node viewed as an element of its underlying sequence. -/
def Grid.nodeEmbedding {Γ : Set ℝ} (g : Grid Γ) : ℤ ↪ Γ where
  toFun k := ⟨g.point k, g.point_mem k⟩
  inj' := by intro a b h; exact g.strictMono.injective (congrArg Subtype.val h)

/-- The finite node block indexed by `[a,a+N)`. -/
def Grid.block {Γ : Set ℝ} (g : Grid Γ) (a : ℤ) (N : ℕ) : Finset Γ :=
  (Finset.Ico a (a + N)).map g.nodeEmbedding

theorem Grid.block_card {Γ : Set ℝ} (g : Grid Γ) (a : ℤ) (N : ℕ) :
    (g.block a N).card = N := by
  simp [Grid.block, Int.card_Ico]

theorem Grid.block_nonempty {Γ : Set ℝ} (g : Grid Γ) (a : ℤ) {N : ℕ}
    (hN : 0 < N) : (g.block a N).Nonempty := by
  rw [← Finset.card_pos, g.block_card]
  exact hN

/-- Reflection across the vertical axis changes only the sign of the real kernel. -/
theorem cauchy_re_reflect (x y ε : ℝ) :
    -(((x : ℂ) + (ε : ℂ)*I - (y : ℂ))⁻¹).re =
      (((y : ℂ) + (ε : ℂ)*I - (x : ℂ))⁻¹).re := by
  simp only [Complex.inv_re, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, Complex.normSq_apply, Complex.sub_im,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  have he : (x-y)*(x-y)+ε*ε = (y-x)*(y-x)+ε*ε := by ring
  rw [he, ← neg_div]
  congr 1
  ring

/-- Uniform A2 bounds on every consecutive finite grid block. -/
theorem GeneratingData.discrete_A2 {Γ : Set ℝ} (d : GeneratingData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) {ε c : ℝ}
    (hε : 0 < ε) (hεu : ε ≤ g.upper) (hc : 0 < c)
    (hshift : ∀ j : Γ, c * ‖deriv d.G (j : ℂ)‖ ≤
      ‖d.G ((j : ℂ) + (ε : ℂ) * I)‖) :
    ∃ A : ℝ, 0 < A ∧ ∀ (a : ℤ) (N : ℕ), 0 < N →
      weightSum (g.block a N) (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) *
        invWeightSum (g.block a N) (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) ≤ A * (N : ℝ)^2 := by
  classical
  obtain ⟨C₁, hC₁, hcross₁⟩ := d.cauchy_cross_bound hΓ hε hc hshift
  obtain ⟨C₂, hC₂, hcross₂⟩ := d.cauchy_cross_bound_negative hΓ hε hc hshift
  let D := max C₁ C₂
  let b := g.lower / (10 * g.upper^2)
  have hD : 0 < D := hC₁.trans_le (le_max_left _ _)
  have hu := g.upper_pos
  have hb : 0 < b := div_pos g.lower_pos (by positivity)
  refine ⟨(D/b^2)^2, by positivity, ?_⟩
  intro a N hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnI : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  let s := g.block a N
  let t := g.block (a+2*N) N
  let v : Γ → ℝ := fun k ↦ ‖deriv d.G (k : ℂ)‖^2
  have hv (k : Γ) : 0 < v k := sq_pos_of_pos (norm_pos_iff.mpr (d.simple k.2))
  have hf : ∀ j ∈ t, ∀ k ∈ s, b/(N : ℝ) ≤
      (((j : ℂ) + (ε : ℂ)*I - (k : ℂ))⁻¹).re := by
    intro j hj k hk
    obtain ⟨j₀, hj₀, rfl⟩ := Finset.mem_map.mp hj
    obtain ⟨k₀, hk₀, rfl⟩ := Finset.mem_map.mp hk
    have hj₀' : j₀ ∈ Finset.Ico (a+2*(N : ℤ)) (a+3*(N : ℤ)) := by
      have hab : a+2*(N : ℤ)+(N : ℤ) = a+3*(N : ℤ) := by ring
      simpa only [hab] using hj₀
    exact g.block_cauchy_re_lower hnI hε.le hεu hk₀ hj₀'
  have hr : ∀ j ∈ s, ∀ k ∈ t, b/(N : ℝ) ≤
      -(((j : ℂ) + (ε : ℂ)*I - (k : ℂ))⁻¹).re := by
    intro j hj k hk
    rw [cauchy_re_reflect]
    exact hf k hk j hj
  have hF := hcross₁ s t (b/(N : ℝ)) (g.block_nonempty a hN) (div_pos hb hn) hf
  have hR := hcross₂ t s (b/(N : ℝ)) (g.block_nonempty _ hN) (div_pos hb hn) hr
  have hcommon (C : ℝ) (hC : C ≤ D) : C / (b/(N : ℝ))^2 ≤ D/b^2*(N : ℝ)^2 := by
    calc
      _ ≤ D / (b/(N : ℝ))^2 := div_le_div_of_nonneg_right hC (sq_nonneg _)
      _ = _ := by field_simp
  have hF' := hF.trans (hcommon C₁ (le_max_left _ _))
  have hR' := hR.trans (hcommon C₂ (le_max_right _ _))
  have hl : (N : ℝ)^2 ≤ weightSum t v * invWeightSum t v := by
    simpa [t, g.block_card] using card_sq_le_weightSum_mul_invWeightSum t v (fun k _ ↦ hv k)
  have hd := diagonal_of_cross_tests
    (Finset.sum_nonneg (fun k (_ : k ∈ s) ↦ (hv k).le))
    (Finset.sum_nonneg (fun k (_ : k ∈ s) ↦ (inv_pos.mpr (hv k)).le))
    (Finset.sum_nonneg (fun k (_ : k ∈ t) ↦ (hv k).le))
    (Finset.sum_nonneg (fun k (_ : k ∈ t) ↦ (inv_pos.mpr (hv k)).le))
    hn hl hF' hR'
  change weightSum s v * invWeightSum s v ≤ _
  apply hd.trans
  have hn0 : (N : ℝ) ≠ 0 := hn.ne'
  apply le_of_eq
  field_simp [hn0]

/-- The derivative weights of a complete interpolation generator satisfy discrete A2. -/
theorem CardinalData.discrete_A2 {Γ : Set ℝ} (d : CardinalData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (a : ℤ) (N : ℕ), 0 < N →
      weightSum (g.block a N) (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) *
        invWeightSum (g.block a N) (fun k ↦ ‖deriv d.G (k : ℂ)‖^2) ≤ A * (N : ℝ)^2 := by
  obtain ⟨ε, c, C, hε, hεl, hc, hC, hbd⟩ := generating_cell_bounds g d
  apply d.toGeneratingData.discrete_A2 g hΓ hε (by linarith [g.lower_le_upper]) hc
  intro j
  obtain ⟨k, hk⟩ := g.range_eq.symm.subset j.2
  have h := (hbd k (g.point k) (g.point_mem_cell k)).1.1
  simpa only [hk] using h

end FF.Pavlov
