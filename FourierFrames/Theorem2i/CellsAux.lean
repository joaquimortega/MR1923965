import FourierFrames.Theorem2i.Basic

/-!
# M08 helper (cells): integrability of the `U_ψ` integrand
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

/-- The integrand of `UPsi`. -/
def upsiInt (ψ : ℝ → ℝ) (z : ℂ) (s : ℝ) : ℝ :=
  (Real.log ‖1 - z / s‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 s) * (z / s).re) * deriv ψ s

theorem RegData.continuous_deriv (h : RegData ψ t C M) : Continuous (deriv ψ) :=
  (contDiff_one_iff_deriv.1 h.adm.1).2

theorem RegData.deriv_eq_zero_of_nonpos (h : RegData ψ t C M) {s : ℝ} (hs : s ≤ 0) :
    deriv ψ s = 0 := by
  have hcl : IsClosed {s : ℝ | deriv ψ s = 0} := isClosed_eq h.continuous_deriv continuous_const
  have hsub : Iio (0 : ℝ) ⊆ {s : ℝ | deriv ψ s = 0} := by
    intro s hs
    have : ψ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hs] with x hx using h.zero x (le_of_lt hx)
    simpa using this.deriv_eq
  have := hcl.closure_subset_iff.2 hsub
  rw [closure_Iio] at this
  exact this hs

theorem RegData.exists_bound_deriv (h : RegData ψ t C M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s, |deriv ψ s| ≤ B := by
  have hT := h.adm.2.2.2
  have hev : ∀ᶠ s in cocompact ℝ, |deriv ψ s| < 1 := by
    have := hT.abs
    rw [abs_zero] at this
    exact this.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 hev
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn h.continuous_deriv.continuousOn
  refine ⟨max B 1, le_max_of_le_right zero_le_one, fun s => ?_⟩
  by_cases hs : s ∈ K
  · exact (by simpa using hB s hs : |deriv ψ s| ≤ B).trans (le_max_left _ _)
  · exact ((hKs (by simpa using hs)).le).trans (le_max_right _ _)

theorem logsub_intervalIntegrable (z : ℂ) (R : ℝ) :
    IntervalIntegrable (fun s : ℝ => Real.log ‖(s : ℂ) - z‖) volume 0 R := by
  by_cases hz : z.im = 0
  · have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
    have e : (fun s : ℝ => Real.log ‖(s : ℂ) - z‖) = fun s : ℝ => Real.log (s - z.re) := by
      funext s
      conv_lhs => rw [hz']
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
    rw [e]
    have := (intervalIntegral.intervalIntegrable_log' (a := 0 - z.re) (b := R - z.re)).comp_sub_right
      z.re
    simpa using this
  · apply Continuous.intervalIntegrable
    apply Continuous.log (by fun_prop)
    intro s h0
    have := (norm_eq_zero.1 h0)
    have := congrArg Complex.im this
    simp at this
    exact hz this

theorem log_one_sub_div_integrableOn (z : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun s : ℝ => Real.log ‖1 - z / (s : ℂ)‖) (Ioc 0 R) := by
  have h1 : IntegrableOn (fun s : ℝ => Real.log ‖(s : ℂ) - z‖ - Real.log s) (Ioc 0 R) := by
    have a := (logsub_intervalIntegrable z R)
    have b := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := R))
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).1 a).sub
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).1 b)
  refine h1.congr_fun_ae ?_
  have hae : ∀ᵐ s : ℝ, s ≠ z.re := by
    rw [ae_iff]; simp
  have hae' := ae_restrict_of_ae (s := Ioc 0 R) hae
  filter_upwards [hae', ae_restrict_mem measurableSet_Ioc] with s hs hs0
  have hs0' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.1.ne'
  have hsz : (s : ℂ) - z ≠ 0 := by
    intro h0
    apply hs
    have := congrArg Complex.re h0
    simp at this
    linarith
  have : 1 - z / (s : ℂ) = ((s : ℂ) - z) / s := by field_simp
  rw [this, norm_div, Real.log_div (norm_ne_zero_iff.2 hsz) (norm_ne_zero_iff.2 hs0'),
    Complex.norm_real, Real.norm_eq_abs, Real.log_abs]

theorem measurable_upsiInt (h : RegData ψ t C M) (z : ℂ) : Measurable (upsiInt ψ z) := by
  have := h.continuous_deriv.measurable
  have hm : MeasurableSet (Icc (-1 : ℝ) 1) := measurableSet_Icc
  unfold upsiInt
  fun_prop

/-- The "linear" part: bounded on `Ioc 0 R`. -/
theorem RegData.integrableOn_linPart (h : RegData ψ t C M) (z : ℂ) {R : ℝ} :
    IntegrableOn (fun s : ℝ => (1 - (Icc (-1 : ℝ) 1).indicator 1 s) * (z / s).re * deriv ψ s)
      (Ioc 0 R) := by
  obtain ⟨B, hB0, hB⟩ := h.exists_bound_deriv
  refine Measure.integrableOn_of_bounded (M := ‖z‖ * B) (by simp) ?_ ?_
  · have := h.continuous_deriv.measurable
    have hm : MeasurableSet (Icc (-1 : ℝ) 1) := measurableSet_Icc
    exact (by fun_prop : Measurable fun s : ℝ =>
      (1 - (Icc (-1 : ℝ) 1).indicator 1 s) * (z / s).re * deriv ψ s).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    by_cases h1 : s ≤ 1
    · have : s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], h1⟩
      simp [this]
      positivity
    · have : s ∉ Icc (-1 : ℝ) 1 := fun h' => h1 h'.2
      have hs1 : 1 < s := lt_of_not_ge h1
      simp only [this, not_false_eq_true, indicator_of_notMem, sub_zero, one_mul,
        Real.norm_eq_abs]
      rw [abs_mul]
      refine mul_le_mul ?_ (hB s) (abs_nonneg _) (norm_nonneg _)
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg z]

theorem RegData.integrableOn_upsiInt_Ioc (h : RegData ψ t C M) (z : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (upsiInt ψ z) (Ioc 0 R) := by
  obtain ⟨B, hB0, hB⟩ := h.exists_bound_deriv
  have hD : IntegrableOn (deriv ψ) (Ioc 0 R) :=
    (h.continuous_deriv.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h1 : IntegrableOn (fun s : ℝ => Real.log ‖1 - z / (s : ℂ)‖ * deriv ψ s) (Ioc 0 R) :=
    (log_one_sub_div_integrableOn z hR).mul_bdd h.continuous_deriv.aestronglyMeasurable
      (c := B) (Filter.Eventually.of_forall fun s => by simpa using hB s)
  have h2 := (h.integrableOn_linPart z (R := R))
  refine (h1.add h2).congr_fun (fun s _ => ?_) measurableSet_Ioc
  simp only [upsiInt, Pi.add_apply]; ring

/-- Tail estimate. -/
theorem RegData.integrableOn_upsiInt_Ioi (h : RegData ψ t C M) (z : ℂ) :
    IntegrableOn (upsiInt ψ z) (Ioi (max 1 (2 * ‖z‖))) := by
  obtain ⟨B, hB0, hB⟩ := h.exists_bound_deriv
  set S := max 1 (2 * ‖z‖) with hS
  have hS1 : 1 ≤ S := le_max_left _ _
  have hS2 : 2 * ‖z‖ ≤ S := le_max_right _ _
  have hint : IntegrableOn (fun s : ℝ => (‖z‖ ^ 2 * B) * s ^ (-2 : ℝ)) (Ioi S) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith)).const_mul _
  refine Integrable.mono' hint (measurable_upsiInt h z).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs' : S < s := hs
  have hs0 : 0 < s := by linarith
  have hnot : s ∉ Icc (-1 : ℝ) 1 := fun h' => by linarith [h'.2]
  have hw : ‖z / (s : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0, div_le_iff₀ hs0]
    linarith
  have key := OCS.norm_log_one_sub_add_le hw
  have hre : |Real.log ‖1 - z / (s : ℂ)‖ + (z / (s : ℂ)).re| ≤ ‖z / (s : ℂ)‖ ^ 2 := by
    have : Real.log ‖1 - z / (s : ℂ)‖ + (z / (s : ℂ)).re =
        (Complex.log (1 - z / (s : ℂ)) + z / (s : ℂ)).re := by
      simp [Complex.log_re]
    rw [this]
    exact (Complex.abs_re_le_norm _).trans key
  simp only [upsiInt, hnot, not_false_eq_true, indicator_of_notMem, sub_zero,
    one_mul, Real.norm_eq_abs]
  rw [abs_mul]
  have hn : ‖z / (s : ℂ)‖ ^ 2 = ‖z‖ ^ 2 * s ^ (-2 : ℝ) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0, div_pow,
      Real.rpow_neg hs0.le, Real.rpow_two]
    ring
  calc _ ≤ (‖z / (s : ℂ)‖ ^ 2) * B := mul_le_mul hre (hB s) (abs_nonneg _) (sq_nonneg _)
    _ = _ := by rw [hn]; ring

theorem RegData.integrable_upsiInt (h : RegData ψ t C M) (z : ℂ) :
    Integrable (upsiInt ψ z) := by
  set S := max 1 (2 * ‖z‖) with hS
  have hS0 : 0 ≤ S := le_trans zero_le_one (le_max_left _ _)
  have h1 := h.integrableOn_upsiInt_Ioc z hS0
  have h2 := h.integrableOn_upsiInt_Ioi z
  have h3 : IntegrableOn (upsiInt ψ z) (Iic 0) := by
    refine (integrableOn_zero (μ := volume) (s := Iic (0:ℝ))).congr_fun (fun s hs => ?_)
      measurableSet_Iic
    simp [upsiInt, h.deriv_eq_zero_of_nonpos hs]
  rw [← integrableOn_univ]
  have : (univ : Set ℝ) = Iic 0 ∪ Ioc 0 S ∪ Ioi S := by
    ext x
    simp only [mem_univ, mem_union, mem_Iic, mem_Ioc, mem_Ioi, true_iff]
    by_cases a : x ≤ 0
    · exact Or.inl (Or.inl a)
    · by_cases b : x ≤ S
      · exact Or.inl (Or.inr ⟨lt_of_not_ge a, b⟩)
      · exact Or.inr (lt_of_not_ge b)
  rw [this]
  exact (h3.union h1).union h2

end FF
