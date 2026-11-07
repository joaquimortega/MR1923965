import FourierFrames.Cited.Pavlov.BoundaryWeight
import FourierFrames.Cited.Pavlov.BMOLogIntegrable
import FourierFrames.Cited.Pavlov.LogPoissonKernel

/-!
# Logarithmic data of a normalized cardinal function

The real PW cardinal, multiplied by exp(iπz), gives bounded zero-free
upper-half-plane data for the specialized dispersion argument.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section
namespace FF.Pavlov
variable {Γ : Set ℝ}

/-- The bounded analytic upper-half-plane normalization of a cardinal. -/
def cardinalUpper (d : CardinalData Γ) (γ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (I*(Real.pi : ℂ)*z) * cardinal d.G γ z

/-- Its real boundary logarithmic modulus. -/
def cardinalLog (d : CardinalData Γ) (γ : ℝ) (t : ℝ) : ℝ :=
  Real.log ‖cardinal d.G γ (t : ℂ)‖

theorem GeneratingData.deriv_real (d : GeneratingData Γ) (γ : ℝ) :
    conj (deriv d.G (γ : ℂ)) = deriv d.G (γ : ℂ) := by
  have h := deriv_fstar_ofReal d.G γ
  rw [d.real] at h
  exact h.symm

/-- The normalized cardinal function is real entire. -/
theorem GeneratingData.cardinal_real (d : GeneratingData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    fstar (cardinal d.G γ) = cardinal d.G γ := by
  funext z
  have hD := d.deriv_real γ
  have hG : conj (d.G (conj z)) = d.G z := congrFun d.real z
  have hds : conj (dslope d.G (γ : ℂ) (conj z)) = dslope d.G (γ : ℂ) z := by
    by_cases hz : z = (γ : ℂ)
    · subst z
      simp only [Complex.conj_ofReal, dslope_same, hD]
    · have hzc : conj z ≠ (γ : ℂ) := by
        intro h
        apply hz
        have hh := congrArg conj h
        simpa only [Complex.conj_conj, Complex.conj_ofReal] using hh
      rw [dslope_of_ne _ hzc, dslope_of_ne _ hz, slope_def_field, slope_def_field,
        d.zero hγ, sub_zero, map_div₀, map_sub, Complex.conj_conj, Complex.conj_ofReal,
        hG]
      simp only [sub_zero]
  change conj (dslope d.G (γ : ℂ) (conj z) / deriv d.G (γ : ℂ)) = _
  rw [map_div₀, hds, hD]
  rfl

theorem cardinalUpper_entire (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    Differentiable ℂ (cardinalUpper d γ) := by
  exact ((differentiable_id.const_mul (I*(Real.pi : ℂ))).cexp).mul
    (d.toGeneratingData.cardinal_mem hγ).1

theorem cardinalUpper_ne_zero (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    ∀ z ∈ UHP, cardinalUpper d γ z ≠ 0 := by
  intro z hz
  apply mul_ne_zero (Complex.exp_ne_zero _)
  intro h
  obtain ⟨t, -, -, rfl⟩ := (d.toGeneratingData.cardinal_zero_iff hγ z).mp h
  simp [UHP] at hz

/-- The exponential normalization is bounded throughout the upper half-plane. -/
theorem cardinalUpper_bounded (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ UHP, ‖cardinalUpper d γ z‖ ≤ M := by
  refine ⟨Real.sqrt d.normBound+1, by positivity, ?_⟩
  intro z hz
  have hq := pw_norm_sq_le paleyWiener_holds (d.toGeneratingData.cardinal_mem hγ) z
  rw [abs_of_pos hz] at hq
  have hN := d.cardinal_norm γ hγ
  have hb : ‖cardinal d.G γ z‖^2 ≤ Real.exp (2*Real.pi*z.im)*d.normBound :=
    hq.trans (mul_le_mul_of_nonneg_left hN (Real.exp_pos _).le)
  have he : ‖Complex.exp (I*(Real.pi : ℂ)*z)‖ = Real.exp (-Real.pi*z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hexp : Real.exp (-Real.pi*z.im)^2 * Real.exp (2*Real.pi*z.im) = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hsq : ‖cardinalUpper d γ z‖^2 ≤ d.normBound := by
    rw [cardinalUpper, norm_mul, mul_pow, he]
    calc
      _ ≤ Real.exp (-Real.pi*z.im)^2 * (Real.exp (2*Real.pi*z.im)*d.normBound) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = d.normBound := by rw [← mul_assoc, hexp, one_mul]
  have hs := Real.sq_sqrt d.normBound_pos.le
  have hs0 := Real.sqrt_nonneg d.normBound
  nlinarith [norm_nonneg (cardinalUpper d γ z)]

theorem cardinal_ne_zero_upper (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ)
    {z : ℂ} (hz : z ∈ UHP) : cardinal d.G γ z ≠ 0 := by
  intro h
  obtain ⟨t, -, -, rfl⟩ := (d.toGeneratingData.cardinal_zero_iff hγ z).mp h
  simp [UHP] at hz

theorem log_generating_eq_cardinal_upper (d : CardinalData Γ) {γ : ℝ}
    (hγ : γ ∈ Γ) {z : ℂ} (hz : z ∈ UHP) :
    Real.log ‖d.G z‖ = Real.log ‖cardinal d.G γ z‖ + Real.log ‖z-(γ : ℂ)‖ +
      Real.log ‖deriv d.G (γ : ℂ)‖ := by
  have hD := norm_ne_zero_iff.mpr (d.toGeneratingData.simple hγ)
  have hq := norm_ne_zero_iff.mpr (cardinal_ne_zero_upper d hγ hz)
  have hd : ‖z-(γ : ℂ)‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro h
    have he := congrArg Complex.im (sub_eq_zero.mp h)
    simp only [Complex.ofReal_im] at he
    exact (ne_of_gt hz) he
  rw [d.toGeneratingData.norm_generating_eq hγ,
    Real.log_mul (mul_ne_zero hD hd) hq, Real.log_mul hD hd]
  ring

theorem log_cardinalUpper_eq (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ)
    {z : ℂ} (hz : z ∈ UHP) :
    Real.log ‖cardinalUpper d γ z‖ = -Real.pi*z.im + Real.log ‖cardinal d.G γ z‖ := by
  have hq := norm_ne_zero_iff.mpr (cardinal_ne_zero_upper d hγ hz)
  rw [cardinalUpper, norm_mul, Real.log_mul
    (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)) hq, Complex.norm_exp, Real.log_exp]
  simp

/-- The exponential normalization has unit modulus on the real axis. -/
theorem cardinalUpper_boundary_norm (d : CardinalData Γ) (γ t : ℝ) :
    ‖cardinalUpper d γ (t : ℂ)‖ = ‖cardinal d.G γ (t : ℂ)‖ := by
  rw [cardinalUpper, norm_mul]
  have he : ‖Complex.exp (I*(Real.pi : ℂ)*(t : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [he, one_mul]

/-- The quotient logarithm identity at every real point outside the zero set. -/
theorem cardinalLog_eq_of_not_mem (d : CardinalData Γ) {γ : ℝ} (hγ : γ ∈ Γ)
    {t : ℝ} (ht : t ∉ Γ) :
    cardinalLog d γ t = Real.log ‖d.G (t : ℂ)‖ -
      Real.log |t-γ| - Real.log ‖deriv d.G (γ : ℂ)‖ := by
  have hD : ‖deriv d.G (γ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (d.toGeneratingData.simple hγ)
  have hdist : |t-γ| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr (fun h ↦ ht (h.symm ▸ hγ)))
  have hq : cardinal d.G γ (t : ℂ) ≠ 0 := by
    intro h
    obtain ⟨x, hx, -, he⟩ := (d.toGeneratingData.cardinal_zero_iff hγ _).mp h
    have hxt : t = x := Complex.ofReal_inj.mp he
    exact ht (hxt.symm ▸ hx)
  have hqn : ‖cardinal d.G γ (t : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  rw [d.toGeneratingData.norm_generating_eq hγ]
  have he : ‖(t : ℂ)-(γ : ℂ)‖ = |t-γ| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [he, Real.log_mul (mul_ne_zero hD hdist) hqn, Real.log_mul hD hdist]
  dsimp only [cardinalLog]
  ring

/-- The quotient logarithm identity is asserted almost everywhere across the null zero set. -/
theorem cardinalLog_eq_ae (d : CardinalData Γ) (g : Grid Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    cardinalLog d γ =ᵐ[volume] (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖ -
      Real.log |t-γ| - Real.log ‖deriv d.G (γ : ℂ)‖) := by
  filter_upwards [g.ae_not_mem] with t ht
  exact cardinalLog_eq_of_not_mem d hγ ht

theorem log_generating_eq_cardinalLog_of_not_mem (d : CardinalData Γ) {γ : ℝ}
    (hγ : γ ∈ Γ) {t : ℝ} (ht : t ∉ Γ) :
    Real.log ‖d.G (t : ℂ)‖ = cardinalLog d γ t + Real.log |t-γ| +
      Real.log ‖deriv d.G (γ : ℂ)‖ := by
  have h := cardinalLog_eq_of_not_mem d hγ ht
  linarith

theorem log_generating_eq_cardinalLog_ae (d : CardinalData Γ) (g : Grid Γ)
    {γ : ℝ} (hγ : γ ∈ Γ) :
    (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖) =ᵐ[volume]
      (fun t ↦ cardinalLog d γ t + Real.log |t-γ| + Real.log ‖deriv d.G (γ : ℂ)‖) := by
  filter_upwards [g.ae_not_mem] with t ht
  exact log_generating_eq_cardinalLog_of_not_mem d hγ ht

theorem cardinalLog_logIntegrable (d : CardinalData Γ) (g : Grid Γ) (hΓ : IsSeparated Γ)
    {γ : ℝ} (hγ : γ ∈ Γ) : LogIntegrable (cardinalLog d γ) := by
  have hu := memBMO_logIntegrable (d.boundary_log_bmo g hΓ)
  have hv := (hu.sub (logIntegrable_log_abs_sub γ)).sub_const
    (Real.log ‖deriv d.G (γ : ℂ)‖)
  exact hv.congr (cardinalLog_eq_ae d g hγ).symm

/-- Exponentiating the boundary logarithm recovers the squared modulus almost everywhere. -/
theorem exp_two_cardinalLog_eq_ae (d : CardinalData Γ) (g : Grid Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    (fun t : ℝ ↦ Real.exp (2*cardinalLog d γ t)) =ᵐ[volume]
      (fun t : ℝ ↦ ‖cardinal d.G γ (t : ℂ)‖^2) := by
  filter_upwards [g.ae_not_mem] with t ht
  have hq : cardinal d.G γ (t : ℂ) ≠ 0 := by
    intro h
    obtain ⟨x, hx, -, he⟩ := (d.toGeneratingData.cardinal_zero_iff hγ _).mp h
    exact ht ((Complex.ofReal_inj.mp he).symm ▸ hx)
  have hn := norm_pos_iff.mpr hq
  dsimp only [cardinalLog]
  rw [show 2*Real.log ‖cardinal d.G γ (t : ℂ)‖ =
    Real.log ‖cardinal d.G γ (t : ℂ)‖+Real.log ‖cardinal d.G γ (t : ℂ)‖ by ring,
    Real.exp_add, Real.exp_log hn]
  ring

theorem integrable_exp_two_cardinalLog (d : CardinalData Γ) (g : Grid Γ)
    {γ : ℝ} (hγ : γ ∈ Γ) : Integrable (fun t : ℝ ↦ Real.exp (2*cardinalLog d γ t)) := by
  have hq := (d.toGeneratingData.cardinal_mem hγ).2.2
  have hi := (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mp hq
  exact hi.congr (exp_two_cardinalLog_eq_ae d g hγ).symm

theorem CardinalData.log_generating_logIntegrable (d : CardinalData Γ) (g : Grid Γ)
    (hΓ : IsSeparated Γ) : LogIntegrable (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖) :=
  memBMO_logIntegrable (d.boundary_log_bmo g hΓ)

theorem cardinalUpper_logIntegrable (d : CardinalData Γ) (g : Grid Γ)
    (hΓ : IsSeparated Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    LogIntegrable (fun t : ℝ ↦ Real.log ‖cardinalUpper d γ (t : ℂ)‖) := by
  have hv := cardinalLog_logIntegrable d g hΓ hγ
  change LogIntegrable (fun t : ℝ ↦ Real.log ‖cardinal d.G γ (t : ℂ)‖) at hv
  simpa only [cardinalUpper_boundary_norm] using hv

/-- All cardinal boundary data needed by the specialized dispersion argument. -/
structure CardinalLogInput (d : CardinalData Γ) (γ : ℝ) : Prop where
  memPW : MemPW (cardinal d.G γ)
  real : fstar (cardinal d.G γ) = cardinal d.G γ
  at_node : cardinal d.G γ (γ : ℂ) = 1
  zeros : ∀ z : ℂ, cardinal d.G γ z = 0 ↔ ∃ t ∈ Γ, t ≠ γ ∧ z = (t : ℂ)
  upper_entire : Differentiable ℂ (cardinalUpper d γ)
  upper_ne_zero : ∀ z ∈ UHP, cardinalUpper d γ z ≠ 0
  upper_bounded : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ UHP, ‖cardinalUpper d γ z‖ ≤ M
  boundary_norm : ∀ t : ℝ, ‖cardinalUpper d γ (t : ℂ)‖ = ‖cardinal d.G γ (t : ℂ)‖
  log_G_integrable : LogIntegrable (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖)
  log_q_integrable : LogIntegrable (cardinalLog d γ)
  log_upper_integrable : LogIntegrable (fun t : ℝ ↦ Real.log ‖cardinalUpper d γ (t : ℂ)‖)
  exp_sq_integrable : Integrable (fun t : ℝ ↦ Real.exp (2*cardinalLog d γ t))
  log_identity : (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖) =ᵐ[volume]
    (fun t ↦ cardinalLog d γ t + Real.log |t-γ| + Real.log ‖deriv d.G (γ : ℂ)‖)

theorem CardinalData.cardinal_log_input (d : CardinalData Γ) (g : Grid Γ)
    (hΓ : IsSeparated Γ) {γ : ℝ} (hγ : γ ∈ Γ) : CardinalLogInput d γ where
  memPW := d.toGeneratingData.cardinal_mem hγ
  real := d.toGeneratingData.cardinal_real hγ
  at_node := by simpa only [ite_true] using d.toGeneratingData.cardinal_values hγ hγ
  zeros := d.toGeneratingData.cardinal_zero_iff hγ
  upper_entire := cardinalUpper_entire d hγ
  upper_ne_zero := cardinalUpper_ne_zero d hγ
  upper_bounded := cardinalUpper_bounded d hγ
  boundary_norm := cardinalUpper_boundary_norm d γ
  log_G_integrable := d.log_generating_logIntegrable g hΓ
  log_q_integrable := cardinalLog_logIntegrable d g hΓ hγ
  log_upper_integrable := cardinalUpper_logIntegrable d g hΓ hγ
  exp_sq_integrable := integrable_exp_two_cardinalLog d g hγ
  log_identity := log_generating_eq_cardinalLog_ae d g hγ

end FF.Pavlov
