import FourierFrames.Cited.Pavlov.SchwarzBoundary
import FourierFrames.Cited.Pavlov.LogClipping
import FourierFrames.Cited.Pavlov.LogPoissonBoundary
import FourierFrames.Cited.Pavlov.HarmonicReflection
import FourierFrames.HB.DeBranges
import FourierFrames.Cited.DeBrangesFC
import TauCeti.Analysis.InnerProductSpace.Laplacian.Comparison

/-!
# Logarithmic Poisson domination for the Pavlov generating function

The compact comparison argument works with a squared holomorphic modulus,
so finite-order boundary zeros cause no discontinuity in the comparison.
-/

open MeasureTheory Complex Set Filter Topology InnerProductSpace Laplacian Metric

noncomputable section
namespace FF.Pavlov

/-- Squared moduli of holomorphic functions have nonnegative Laplacian. -/
lemma laplacian_norm_sq_nonneg {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    0 ≤ Δ (fun w ↦ ‖f w‖ ^ 2) z := by
  have hh := hf.harmonicAt
  rw [hh.1.laplacian_norm_sq Complex.orthonormalBasisOneI,
    hh.2.self_of_nhds]
  simp only [Pi.zero_apply, inner_zero_right, mul_zero, add_zero]
  positivity

/-- A compact maximum principle for functions locally given by squared
holomorphic moduli. Continuity is needed only for the real-valued modulus. -/
lemma le_of_locally_holomorphic_norm_sq {K : Set ℂ} (hK : IsCompact K)
    {T : ℂ → ℝ} {C : ℝ} (hT : ContinuousOn T K)
    (hloc : ∀ z ∈ interior K, ∃ f : ℂ → ℂ, AnalyticAt ℂ f z ∧
      T =ᶠ[𝓝 z] (fun w ↦ ‖f w‖ ^ 2))
    (hbd : ∀ z ∈ frontier K, T z ≤ C) : ∀ z ∈ K, T z ≤ C := by
  apply TauCeti.le_of_laplacian_nonneg_le_frontier hK hT
  · intro z hz
    obtain ⟨f, hf, heq⟩ := hloc z hz
    exact (hf.harmonicAt.1.norm_sq ℝ).congr_of_eventuallyEq heq
  · intro z hz
    obtain ⟨f, hf, heq⟩ := hloc z hz
    rw [(laplacian_congr_nhds heq).self_of_nhds]
    exact laplacian_norm_sq_nonneg hf
  · exact fun z hz ↦ hbd z hz

/-- Compact upper-half-disk comparison with a continuous Poisson extension.
The complex Schwarz integral need only be holomorphic in the open half-plane. -/
lemma compact_poisson_modulus_comparison
    {A S : ℂ → ℂ} {p : ℂ → ℝ} {R C : ℝ}
    (hA : Differentiable ℂ A)
    (hS : AnalyticOnNhd ℂ S UHP)
    (hp : ContinuousOn p {z : ℂ | 0 ≤ z.im})
    (hpre : ∀ z ∈ UHP, p z = (S z).re)
    (hbd : ∀ z ∈ frontier (Metric.closedBall (0 : ℂ) R ∩ {z : ℂ | 0 ≤ z.im}),
      ‖A z‖ ^ 2 * Real.exp (2 * p z) ≤ C) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R ∩ {z : ℂ | 0 ≤ z.im},
      ‖A z‖ ^ 2 * Real.exp (2 * p z) ≤ C := by
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const continuous_im
  apply le_of_locally_holomorphic_norm_sq
    ((isCompact_closedBall (0 : ℂ) R).inter_right hclosed)
    ((hA.continuous.norm.pow 2).continuousOn.mul
      ((hp.const_mul 2).rexp) |>.mono inter_subset_right)
  · intro z hz
    have hzu : z ∈ UHP := by
      have hz' := interior_mono inter_subset_right hz
      simpa only [interior_setOfPred_le_im, UHP] using hz'
    refine ⟨fun w ↦ A w * Complex.exp (S w),
      (hA.analyticAt z).mul (hS z hzu).cexp, ?_⟩
    filter_upwards [isOpen_lt continuous_const continuous_im |>.mem_nhds hzu] with w hw
    change ‖A w‖ ^ 2 * Real.exp (2 * p w) = _
    rw [hpre w hw, norm_mul, mul_pow, Complex.norm_exp]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  · exact hbd

/-- The frontier of a closed upper half-disk consists of its semicircle and diameter. -/
lemma mem_frontier_upper_halfdisk {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ frontier (Metric.closedBall (0 : ℂ) R ∩ {w : ℂ | 0 ≤ w.im})) :
    (‖z‖ = R ∧ 0 ≤ z.im) ∨ (‖z‖ ≤ R ∧ z.im = 0) := by
  have hclosed : IsClosed {w : ℂ | 0 ≤ w.im} := isClosed_le continuous_const continuous_im
  have hzK := ((isClosed_closedBall.inter hclosed).closure_eq ▸ frontier_subset_closure) hz
  have hzn : ‖z‖ ≤ R := by simpa using hzK.1
  rcases frontier_inter_subset (Metric.closedBall (0 : ℂ) R) {w : ℂ | 0 ≤ w.im} hz with h | h
  · exact Or.inl ⟨by simpa [frontier_closedBall _ hR.ne'] using h.1, hzK.2⟩
  · exact Or.inr ⟨hzn, by simpa using h.2⟩

/-- A diameter modulus bound and a small semicircle Poisson bound give the
same bound in the half-disk, up to its explicit exponential error. -/
lemma poisson_modulus_le_on_halfdisk
    {A S : ℂ → ℂ} {p : ℂ → ℝ} {R M e : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hA : Differentiable ℂ A) (hS : AnalyticOnNhd ℂ S UHP)
    (hp : ContinuousOn p {z : ℂ | 0 ≤ z.im})
    (hpre : ∀ z ∈ UHP, p z = (S z).re)
    (hAn : ∀ z : ℂ, 0 ≤ z.im → ‖A z‖ ≤ M)
    (hdiam : ∀ x : ℝ, ‖A x‖ ^ 2 * Real.exp (2*p x) ≤ M^2)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → 0 ≤ z.im → p z ≤ e) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R ∩ {w : ℂ | 0 ≤ w.im},
      ‖A z‖ ^ 2 * Real.exp (2*p z) ≤ M^2*Real.exp (2*e) := by
  apply compact_poisson_modulus_comparison hA hS hp hpre
  intro z hz
  rcases mem_frontier_upper_halfdisk hR hz with ⟨hzn, hzi⟩ | ⟨_, hzi⟩
  · exact mul_le_mul (sq_le_sq₀ (norm_nonneg _) hM |>.mpr (hAn z hzi))
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hcircle z hzn hzi) (by norm_num)))
      (Real.exp_pos _).le (sq_nonneg _)
  · have hzr : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hzi]
    rw [hzr]
    exact (hdiam z.re).trans (le_mul_of_one_le_right (sq_nonneg M)
      (Real.one_le_exp (mul_nonneg (by norm_num) he)))

/-- A continuous upper-half-plane bound persists on its finite boundary. -/
lemma norm_le_on_closed_upper {A : ℂ → ℂ} (hA : Continuous A) {M : ℝ}
    (hbd : ∀ z ∈ UHP, ‖A z‖ ≤ M) :
    ∀ z : ℂ, 0 ≤ z.im → ‖A z‖ ≤ M := by
  intro z hz
  have hc : IsClosed {w : ℂ | ‖A w‖ ≤ M} := isClosed_le hA.norm continuous_const
  apply closure_minimal (fun w hw ↦ hbd w hw) hc
  simpa [UHP, closure_setOfPred_lt_im] using hz

/-- Uniform decay of the half-plane Poisson kernel on a large semicircle,
for boundary data supported in a fixed compact interval. -/
lemma poisson_kernel_le_on_semicircle {R B : ℝ} (hR : 0 < R) (hBR : B ≤ R/2)
    {z : ℂ} (hzn : ‖z‖ = R) {t : ℝ} (ht : |t| ≤ B) :
    z.im / (Real.pi*((t-z.re)^2+z.im^2)) ≤ 4/(Real.pi*R) := by
  have hnorm : R/2 ≤ ‖(t : ℂ)-z‖ := by
    have hb := norm_sub_norm_le z (t : ℂ)
    rw [hzn, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev] at hb
    linarith
  have hden : (R/2)^2 ≤ (t-z.re)^2+z.im^2 := by
    have hb := (sq_le_sq₀ (by positivity : 0 ≤ R/2) (norm_nonneg ((t : ℂ)-z))).mpr hnorm
    rw [Complex.sq_norm, Complex.normSq_apply] at hb
    simpa [pow_two] using hb
  have him : z.im ≤ R := (le_abs_self _).trans ((abs_im_le_norm z).trans_eq hzn)
  calc
    _ ≤ R/(Real.pi*((R/2)^2)) := div_le_div₀ hR.le him
      (by positivity) (mul_le_mul_of_nonneg_left hden Real.pi_pos.le)
    _ = _ := by field_simp; ring

/-- A compactly supported nonnegative datum has uniformly small Poisson
extension on a large upper semicircle. -/
lemma schwarzIntegral_re_le_on_semicircle {g : ℝ → ℝ}
    (hg : LogIntegrable g) (hgi : Integrable g) (hgn : ∀ t, 0 ≤ g t)
    {R B : ℝ} (hR : 0 < R) (hBR : B ≤ R/2)
    (hgs : ∀ t : ℝ, B < |t| → g t = 0)
    {z : ℂ} (hzn : ‖z‖ = R) (hz : 0 < z.im) :
    (schwarzIntegral g z).re ≤ (4/(Real.pi*R)) * ∫ t : ℝ, g t := by
  let P : ℝ → ℝ := fun t ↦ z.im/(Real.pi*((t-z.re)^2+z.im^2))
  have hP : ∀ t, 0 ≤ P t := fun t ↦ by dsimp [P]; positivity
  have hb : ∀ t, P t*g t ≤ (4/(Real.pi*R))*g t := by
    intro t
    by_cases ht : |t| ≤ B
    · exact mul_le_mul_of_nonneg_right
        (poisson_kernel_le_on_semicircle hR hBR hzn ht) (hgn t)
    · rw [hgs t (lt_of_not_ge ht), mul_zero, mul_zero]
  have hm : AEStronglyMeasurable (fun t ↦ P t*g t) volume :=
    (show Measurable P by dsimp [P]; fun_prop).aestronglyMeasurable.mul
      hgi.aestronglyMeasurable
  have hi : Integrable (fun t ↦ P t*g t) :=
    (hgi.const_mul (4/(Real.pi*R))).mono' hm
      (Eventually.of_forall fun t ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hP t) (hgn t))]
        exact hb t)
  rw [schwarzIntegral_re hg hz, ← integral_const_mul]
  exact integral_mono_ae hi (hgi.const_mul _) (Eventually.of_forall hb)

/-- Domination for one continuous compact logarithmic cutoff. This is the
compact-comparison step; later monotone limits remove the cutoff. -/
lemma schwarzIntegral_re_le_log_deficit_of_compact
    {A : ℂ → ℂ} (hA : Differentiable ℂ A) {M : ℝ} (hM : 0 < M)
    (hAb : ∀ z ∈ UHP, ‖A z‖ ≤ M)
    {g : ℝ → ℝ} (hg : LogIntegrable g) (hgi : Integrable g)
    (hgc : Continuous g) (hgn : ∀ t, 0 ≤ g t)
    {B : ℝ} (hgs : ∀ t : ℝ, B < |t| → g t = 0)
    (hdiam : ∀ t : ℝ, ‖A t‖^2 * Real.exp (2*g t) ≤ M^2)
    {z : ℂ} (hz : z ∈ UHP) (hAz : A z ≠ 0) :
    (schwarzIntegral g z).re ≤ Real.log M - Real.log ‖A z‖ := by
  let p := poissonExtension g
  let e : ℝ → ℝ := fun R ↦ (4/(Real.pi*R)) * ∫ t : ℝ, g t
  have hgp : 0 ≤ ∫ t : ℝ, g t := integral_nonneg hgn
  have hclose := norm_le_on_closed_upper hA.continuous hAb
  have hpre : ∀ w ∈ UHP, p w = (schwarzIntegral g w).re := by
    intro w hw
    change 0 < w.im at hw
    simp only [p, poissonExtension, ite_eq_left hw]
  have hb : ∀ᶠ R : ℝ in atTop,
      ‖A z‖^2 * Real.exp (2*p z) ≤ M^2 * Real.exp (2*e R) := by
    filter_upwards [eventually_gt_atTop (max (max (2*B) (‖z‖+1)) 1)] with R hRbig
    have hR : 0 < R := by have := lt_of_le_of_lt (le_max_right (max (2*B) (‖z‖+1)) 1) hRbig; linarith
    have hBR : B ≤ R/2 := by
      have := lt_of_le_of_lt ((le_max_left (2*B) (‖z‖+1)).trans
        (le_max_left (max (2*B) (‖z‖+1)) 1)) hRbig
      linarith
    have hzn : ‖z‖ ≤ R := by
      have := lt_of_le_of_lt ((le_max_right (2*B) (‖z‖+1)).trans
        (le_max_left (max (2*B) (‖z‖+1)) 1)) hRbig
      linarith
    apply poisson_modulus_le_on_halfdisk hR hM.le (by dsimp [e]; positivity) hA
      ((differentiableOn_schwarzIntegral hg).analyticOnNhd (isOpen_lt continuous_const continuous_im))
      (continuousOn_poissonExtension hg hgc) hpre hclose
      (by intro t; simpa [p, poissonExtension] using hdiam t) ?_ z ⟨by simpa using hzn, (show 0 ≤ z.im from hz.le)⟩
    intro w hwn hwi
    change p w ≤ e R
    by_cases hw : 0 < w.im
    · rw [hpre w hw]
      exact schwarzIntegral_re_le_on_semicircle hg hgi hgn hR hBR hgs hwn hw
    · have hw0 : w.im = 0 := le_antisymm (le_of_not_gt hw) hwi
      have hwr : |w.re| = R := by
        have he : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hw0]
        have heNorm : ‖w‖ = |w.re| := by
          simpa only [Complex.norm_real, Real.norm_eq_abs] using congrArg norm he
        exact heNorm.symm.trans hwn
      have hRB : B < R := by linarith
      have hgzero : g w.re = 0 := hgs w.re (by rw [hwr]; exact hRB)
      simp only [p, poissonExtension, ite_eq_right hw, hgzero]
      dsimp [e]
      positivity
  have he0 : Tendsto e atTop (𝓝 0) := by
    have ht : Tendsto (fun R : ℝ ↦ ((4/Real.pi) * ∫ t : ℝ, g t)/R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    convert ht using 1
    ext R
    dsimp [e]
    ring
  have hlim : Tendsto (fun R ↦ M^2 * Real.exp (2*e R)) atTop (𝓝 (M^2)) := by
    have hx : Tendsto (fun R : ℝ ↦ 2*e R) atTop (𝓝 0) := by simpa using he0.const_mul (2 : ℝ)
    have hy : Tendsto (fun R : ℝ ↦ Real.exp (2*e R)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp hx
    simpa using hy.const_mul (M^2)
  have hfinal := ge_of_tendsto hlim hb
  have hn : 0 < ‖A z‖ := norm_pos_iff.mpr hAz
  have hlog := Real.log_le_log (by positivity : 0 < ‖A z‖^2*Real.exp (2*p z)) hfinal
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp,
    Real.log_pow] at hlog
  rw [hpre z hz] at hlog
  norm_num at hlog
  linarith

/-- A bounded entire function without upper-half-plane zeros lies below the
Poisson extension of its boundary logarithm. -/
theorem log_norm_le_poisson_boundary
    {A : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hnz : ∀ z ∈ UHP, A z ≠ 0)
    (hbd : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ UHP, ‖A z‖ ≤ M)
    (hv : LogIntegrable (fun t : ℝ ↦ Real.log ‖A t‖)) :
    ∀ z ∈ UHP, Real.log ‖A z‖ ≤
      (schwarzIntegral (fun t : ℝ ↦ Real.log ‖A t‖) z).re := by
  obtain ⟨M, hM, hAb⟩ := hbd
  have hclose := norm_le_on_closed_upper hA.continuous hAb
  have hab : ∀ t : ℝ, ‖A t‖ ≤ M := fun t ↦ hclose t (by simp)
  have hc : Continuous (fun t : ℝ ↦ A t) := hA.continuous.comp continuous_ofReal
  let v : ℝ → ℝ := fun t ↦ Real.log ‖A t‖
  let b : ℝ → ℝ := fun t ↦ Real.log M-v t
  have hb : LogIntegrable b := LogIntegrable.sub (logIntegrable_const (Real.log M)) hv
  have haez : ∀ᵐ t : ℝ, A t ≠ 0 := by
    rw [ae_iff]
    simp only [not_not]
    exact (countable_real_zeros hA ⟨I, hnz I (by simp [UHP])⟩).measure_zero volume
  intro z hz
  have hzim : 0 < z.im := hz
  let P : ℝ → ℝ := fun t ↦ z.im/(Real.pi*((t-z.re)^2+z.im^2))
  have hP : ∀ t, 0 ≤ P t := fun t ↦ by dsimp [P]; positivity
  have hbi : Integrable (fun t ↦ P t*b t) := poissonKernel_mul_integrable hb hz
  have hl : Tendsto (fun n : ℕ ↦ (schwarzIntegral (logClip M A n) z).re) atTop
      (𝓝 (∫ t : ℝ, P t*b t)) := by
    simp_rw [schwarzIntegral_re (logIntegrable_logClip hM hc _) hz]
    apply tendsto_integral_of_dominated_convergence (fun t ↦ P t*b t)
    · intro n
      exact (show Measurable P by dsimp [P]; fun_prop).aestronglyMeasurable.mul
        (continuous_logClip hM hc n).aestronglyMeasurable
    · exact hbi
    · intro n
      filter_upwards [haez] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hP t) (logClip_nonneg hM hab n t))]
      exact mul_le_mul_of_nonneg_left (logClip_le_deficit hM hab n ht) (hP t)
    · filter_upwards [haez] with t ht
      exact (tendsto_logClip ht).const_mul (P t)
  have hclip : ∀ n : ℕ, (schwarzIntegral (logClip M A n) z).re ≤
      Real.log M-Real.log ‖A z‖ := by
    intro n
    apply schwarzIntegral_re_le_log_deficit_of_compact hA hM hAb
      (logIntegrable_logClip hM hc n) (integrable_logClip hM hc n)
      (continuous_logClip hM hc n) (logClip_nonneg hM hab n)
      (B := (n : ℝ)+1)
      (fun t ht ↦ logClip_eq_zero_of_abs_ge ht.le)
      (logClip_boundary_bound hM hab n) hz (hnz z hz)
  have hbnd := le_of_tendsto hl (Eventually.of_forall hclip)
  have hei : (∫ t : ℝ, P t*b t) = Real.log M-(schwarzIntegral v z).re := by
    rw [show (fun t ↦ P t*b t) = (fun t ↦ P t*Real.log M-P t*v t) by
      funext t; dsimp [b]; ring]
    rw [integral_sub (poissonKernel_mul_integrable (logIntegrable_const (Real.log M)) hz)
      (poissonKernel_mul_integrable hv hz)]
    rw [← schwarzIntegral_re (logIntegrable_const (Real.log M)) hz,
      schwarzIntegral_re_const (Real.log M) hzim, ← schwarzIntegral_re hv hz]
  rw [hei] at hbnd
  linarith

/-- The only defect in logarithmic Poisson dispersion is a nonnegative
multiple of height. Boundary singularities contribute no additional term. -/
theorem poisson_log_defect_eq_mul_im
    {A : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hnz : ∀ z ∈ UHP, A z ≠ 0)
    (hbd : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ UHP, ‖A z‖ ≤ M)
    (hv : LogIntegrable (fun t : ℝ ↦ Real.log ‖A t‖)) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ z ∈ UHP,
      (schwarzIntegral (fun t : ℝ ↦ Real.log ‖A t‖) z).re -
        Real.log ‖A z‖ = a*z.im := by
  have ho : IsOpen UHP := isOpen_lt continuous_const continuous_im
  have hr : HarmonicOnNhd (poissonLogDefect A) UHP := by
    intro z hz
    have hs := ((differentiableOn_schwarzIntegral hv).analyticOnNhd ho z hz).harmonicAt_re
    have hl := (hA.analyticAt z).harmonicAt_log_norm (hnz z hz)
    have heq : poissonLogDefect A =ᶠ[𝓝 z] (fun w ↦
        (schwarzIntegral (fun t : ℝ ↦ Real.log ‖A t‖) w).re-Real.log ‖A w‖) := by
      filter_upwards [ho.mem_nhds hz] with w hw
      exact ite_eq_left (show 0 < w.im from hw)
    exact (harmonicAt_congr_nhds heq).mpr (hs.sub hl)
  have hpos : ∀ z ∈ UHP, 0 ≤ poissonLogDefect A z := by
    intro z hz
    simp only [poissonLogDefect, ite_eq_left (show 0 < z.im from hz)]
    exact sub_nonneg.mpr (log_norm_le_poisson_boundary hA hnz hbd hv z hz)
  obtain ⟨a, ha, heq⟩ := nonneg_harmonic_zero_boundary_eq_mul_im hr
    (poisson_log_defect_continuous_zero_boundary hA hnz hv)
    (by intro t; simp [poissonLogDefect]) hpos
  refine ⟨a, ha, fun z hz ↦ ?_⟩
  simpa only [poissonLogDefect, ite_eq_left (show 0 < z.im from hz)] using heq z hz

end FF.Pavlov
