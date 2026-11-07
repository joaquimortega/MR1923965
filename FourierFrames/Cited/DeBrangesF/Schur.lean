import FourierFrames.Cited.DeBrangesF.Isometry
import FourierFrames.Cited.DeBrangesF.Cauchy

/-!
# The contractive parameter from kernel identities

The elementary proof of Theorem F uses Cauchy--Schwarz for a probability measure
and two polarized kernel identities. No inner-function factorization is required.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace FF

/-- The squared Cauchy--Schwarz inequality for complex-valued functions. -/
theorem norm_integral_mul_conj_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ t, f t * conj (g t) ∂μ‖ ^ 2 ≤
      (∫ t, ‖f t‖ ^ 2 ∂μ) * ∫ t, ‖g t‖ ^ 2 ∂μ := by
  have hinner {u v : α → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
      ⟪hu.toLp u, hv.toLp v⟫_ℂ = ∫ t, conj (u t) * v t ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with t ht ht'
    simp [ht, ht', RCLike.inner_apply, mul_comm]
  have hnorm {u : α → ℂ} (hu : MemLp u 2 μ) :
      ‖hu.toLp u‖ ^ 2 = ∫ t, ‖u t‖ ^ 2 ∂μ := by
    have h := hinner hu hu
    rw [inner_self_eq_norm_sq_to_K] at h
    simp_rw [mul_comm (conj _) _, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
    rw [integral_complex_ofReal] at h
    have hh := congrArg Complex.re h
    norm_cast at hh
  have h := norm_inner_le_norm (𝕜 := ℂ) (hg.toLp g) (hf.toLp f)
  have hsq := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2 h
  rw [hinner hg hf, mul_pow, hnorm hg, hnorm hf] at hsq
  simpa only [mul_comm] using hsq

/-- The scalar consequence of the kernel Cauchy--Schwarz inequality. -/
theorem schur_bound_of_scalar_inequality {F p : ℂ} {d : ℝ} (hd : 0 < d) (hp : ‖p‖ < 1)
    (h : ‖((1 - ‖p‖ ^ 2 : ℝ) : ℂ) * conj F / (d : ℂ)‖ ^ 2 ≤
      ((2 * F.re - 1) / d) * ((1 - ‖p‖ ^ 2) / d)) :
    ‖F - 1‖ ≤ ‖p * F‖ := by
  have hp' : 0 < 1 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  simp only [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hd, abs_of_pos hp'] at h
  have h' : (1 - ‖p‖ ^ 2) * ‖F‖ ^ 2 ≤ 2 * F.re - 1 := by
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
    have hh := (div_le_div_iff_of_pos_right hd2).mp
      (show (1 - ‖p‖ ^ 2) ^ 2 * ‖F‖ ^ 2 / d ^ 2 ≤
          (2 * F.re - 1) * (1 - ‖p‖ ^ 2) / d ^ 2 by
        simpa only [div_pow, mul_pow, ← mul_div_mul_comm, ← sq] using h)
    nlinarith
  have hn : ‖F - 1‖ ^ 2 = ‖F‖ ^ 2 - 2 * F.re + 1 := by
    simpa [RCLike.inner_apply] using (norm_sub_sq (𝕜 := ℂ) F 1)
  rw [norm_mul]
  nlinarith [norm_nonneg (F - 1), norm_nonneg F, norm_nonneg p,
    mul_nonneg (norm_nonneg p) (norm_nonneg F)]

/-- The normalized model kernel on the boundary circle. -/
def diskModelKernel (u v : ℝ → ℂ) (w p : ℂ) (t : ℝ) : ℂ :=
  (1 - v t * conj p) / (1 - u t * conj w)

theorem diskModelKernel_eq (u v : ℝ → ℂ) (w p : ℂ) (t : ℝ) :
    diskModelKernel u v w p t = (1 - conj p * v t) * conj (diskCauchyKernel u w t) := by
  simp [diskModelKernel, diskCauchyKernel, div_eq_mul_inv, mul_comm]

theorem diskCauchyKernel_circle_identity {u : ℝ → ℂ} (hun : ∀ t, ‖u t‖ = 1)
    {w : ℂ} (hw : ‖w‖ < 1) (t : ℝ) :
    ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) *
        (conj (diskCauchyKernel u w t) * diskCauchyKernel u w t) =
      diskCauchyKernel u w t + conj (diskCauchyKernel u w t) - 1 := by
  have h := diskCauchyKernel_re_identity hun hw t
  have hc := congrArg (fun r : ℝ ↦ (r : ℂ)) h
  rw [Complex.ofReal_mul] at hc
  rw [mul_comm (conj _) _, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← hc]
  apply Complex.ext
  · simp; ring
  · simp

theorem diskModelKernel_memLp {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {u v : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    (hv : Measurable v) (hvn : ∀ t, ‖v t‖ = 1) {w : ℂ} (hw : ‖w‖ < 1) (p : ℂ) :
    MemLp (diskModelKernel u v w p) 2 ρ := by
  have hm : Measurable (diskModelKernel u v w p) := by
    unfold diskModelKernel
    fun_prop
  refine MemLp.of_bound hm.aestronglyMeasurable ((1 + ‖p‖) * (1 - ‖w‖)⁻¹)
    (Eventually.of_forall fun t ↦ ?_)
  rw [diskModelKernel_eq, norm_mul, Complex.norm_conj]
  apply mul_le_mul _ (diskCauchyKernel_norm_le hun hw t) (norm_nonneg _)
    (by positivity)
  calc ‖1 - conj p * v t‖ ≤ ‖(1 : ℂ)‖ + ‖conj p * v t‖ := norm_sub_le _ _
    _ = 1 + ‖p‖ := by simp [hvn t]

/-- The two polarized kernel identities determine the mixed Cauchy integral. -/
theorem diskModelKernel_integral_mul {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {u v : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    (hv : Measurable v) (hvn : ∀ t, ‖v t‖ = 1) {w p : ℂ} (hw : ‖w‖ < 1)
    (h₁ : diskCauchyTransform ρ u (fun _ ↦ 1) w - 1 =
      p * diskCauchyTransform ρ u (fun t ↦ conj (v t)) w)
    (h₂ : diskCauchyTransform ρ u v w - ∫ t, v t ∂ρ =
      p * diskCauchyTransform ρ u (fun _ ↦ 1) w) :
    ∫ t, diskModelKernel u v w p t * diskCauchyKernel u w t ∂ρ =
      ((1 - ‖p‖ ^ 2 : ℝ) : ℂ) * diskCauchyTransform ρ u (fun _ ↦ 1) w /
        ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
  let C := diskCauchyKernel u w
  have hC : Integrable C ρ := diskCauchyKernel_integrable hu hun hw
  have hvC : Integrable (fun t ↦ v t * C t) ρ :=
    diskCauchyTransform_integrable hu hun hv (M := 1) (fun t ↦ (hvn t).le) hw
  have hvbC : Integrable (fun t ↦ conj (v t) * C t) ρ :=
    diskCauchyTransform_integrable hu hun (Complex.continuous_conj.measurable.comp hv) (M := 1) (fun t ↦ by simp [hvn t]) hw
  have hvint : Integrable v ρ :=
    (integrable_const (1 : ℝ)).mono' hv.aestronglyMeasurable
      (Eventually.of_forall fun t ↦ (hvn t).le)
  have hCc : Integrable (fun t ↦ conj (C t)) ρ :=
    RCLike.conjCLE.toContinuousLinearMap.integrable_comp hC
  have hvbCc : Integrable (fun t ↦ conj (conj (v t) * C t)) ρ :=
    RCLike.conjCLE.toContinuousLinearMap.integrable_comp hvbC
  have hpt (t : ℝ) :
      ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) *
          (diskModelKernel u v w p t * C t) =
        (C t + conj (C t) - 1) -
          conj p * (v t * C t + conj (conj (v t) * C t) - v t) := by
    rw [diskModelKernel_eq]
    have h := diskCauchyKernel_circle_identity hun hw t
    change ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) * (conj (C t) * C t) =
      C t + conj (C t) - 1 at h
    simp only [map_mul, Complex.conj_conj]
    linear_combination (1 - conj p * v t) * h
  have hi := integral_congr_ae (μ := ρ) (Eventually.of_forall hpt)
  simp only [integral_const_mul] at hi
  have hsplit := integral_sub ((hC.add hCc).sub (integrable_const 1))
      (((hvC.add hvbCc).sub hvint).const_mul (conj p))
  simp only [Pi.add_apply, Pi.sub_apply] at hsplit
  have hs₁ := integral_sub (hC.add hCc) (integrable_const (1 : ℂ))
  have ha₁ := integral_add hC hCc
  have hs₂ := integral_sub (hvC.add hvbCc) hvint
  have ha₂ := integral_add hvC hvbCc
  simp only [Pi.add_apply] at hs₁ ha₁ hs₂ ha₂
  rw [hsplit, hs₁, ha₁, integral_const_mul, hs₂, ha₂,
    integral_conj, integral_conj, integral_const] at hi
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hi
  have hc₁ := congrArg conj h₁
  simp only [map_sub, map_one, map_mul] at hc₁
  have hn : conj p * p = ((‖p‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hd : ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    exact Complex.ofReal_ne_zero.mpr this.ne'
  apply (eq_div_iff hd).2
  dsimp [diskCauchyTransform] at h₁ h₂ hc₁ ⊢
  simp only [one_mul] at h₁ h₂ hc₁ ⊢
  dsimp [C] at hi
  push_cast at hi hn ⊢
  linear_combination hi + hc₁ - conj p * h₂ - (∫ t, C t ∂ρ) * hn

/-- Cauchy--Schwarz converts the two kernel identities into a Schur bound. -/
theorem schur_bound_of_kernel_identities {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {u v : ℝ → ℂ} (hu : Measurable u) (hun : ∀ t, ‖u t‖ = 1)
    (hv : Measurable v) (hvn : ∀ t, ‖v t‖ = 1) {w p : ℂ} (hw : ‖w‖ < 1) (hp : ‖p‖ < 1)
    (h₁ : diskCauchyTransform ρ u (fun _ ↦ 1) w - 1 =
      p * diskCauchyTransform ρ u (fun t ↦ conj (v t)) w)
    (h₂ : diskCauchyTransform ρ u v w - ∫ t, v t ∂ρ =
      p * diskCauchyTransform ρ u (fun _ ↦ 1) w)
    (hn : ∫ t, ‖(1 - v t * conj p) / (1 - u t * conj w)‖ ^ 2 ∂ρ =
      (1 - ‖p‖ ^ 2) / (1 - ‖w‖ ^ 2)) :
    ‖diskCauchyTransform ρ u (fun _ ↦ 1) w - 1‖ ≤
      ‖p * diskCauchyTransform ρ u (fun _ ↦ 1) w‖ := by
  have hC : MemLp (diskCauchyKernel u w) 2 ρ :=
    (memLp_two_iff_integrable_sq_norm (diskCauchyKernel_measurable hu w).aestronglyMeasurable).2
      (diskCauchyKernel_sq_integrable hu hun hw)
  have hR := diskModelKernel_memLp (ρ := ρ) hu hun hv hvn hw p
  have hcs := norm_integral_mul_conj_sq_le hR hC.star
  simp only [Pi.star_apply, starRingEnd_apply, star_star] at hcs
  rw [diskModelKernel_integral_mul hu hun hv hvn hw h₁ h₂] at hcs
  simp only [norm_star] at hcs
  rw [diskCauchyKernel_sq_integral hu hun hw] at hcs
  change _ ≤ (∫ t, ‖(1 - v t * conj p) / (1 - u t * conj w)‖ ^ 2 ∂ρ) * _ at hcs
  rw [hn, mul_comm] at hcs
  apply schur_bound_of_scalar_inequality (d := 1 - ‖w‖ ^ 2)
    (by nlinarith [norm_nonneg w]) hp
  simpa only [norm_div, norm_mul, Complex.norm_conj, mul_comm] using hcs

end FF
