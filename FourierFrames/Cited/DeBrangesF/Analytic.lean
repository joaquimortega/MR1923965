import FourierFrames.Cited.DeBrangesF.Basic
import FourierFrames.Cited.DeBrangesF.Algebra

/-!
# Extending the Schur bound across isolated zeros

The kernel argument first bounds the quotient away from zeros of an entire
numerator. Continuity and the identity theorem extend that inequality to every
point of the upper half-plane.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- A continuous inequality on the upper half-plane extends across the zeros
of a nonzero entire function. -/
theorem le_on_upper_of_le_off_entire_zeros {N : ℂ → ℂ} (hN : Differentiable ℂ N)
    (hne : ∃ z : ℂ, N z ≠ 0) {u v : ℂ → ℝ}
    (hu : ContinuousOn u UHP) (hv : ContinuousOn v UHP)
    (h : ∀ z ∈ UHP, N z ≠ 0 → u z ≤ v z) : ∀ z ∈ UHP, u z ≤ v z := by
  intro z hz
  have ho : IsOpen UHP := isOpen_lt continuous_const Complex.continuous_im
  have hu' := (hu z hz).continuousAt (ho.mem_nhds hz)
  have hv' := (hv z hz).continuousAt (ho.mem_nhds hz)
  have hn : ∀ᶠ w in 𝓝[≠] z, N w ≠ 0 := by
    rcases (hN.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with he | he
    · have heq := eq_of_eventuallyEq_entire hN (differentiable_const (0 : ℂ)) he
      obtain ⟨w, hw⟩ := hne
      exact (hw (congrFun heq w)).elim
    · exact he
  have hm : ∀ᶠ w in 𝓝[≠] z, w ∈ UHP :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (ho.mem_nhds hz)
  have hb : ∀ᶠ w in 𝓝[≠] z, u w ≤ v w := by
    filter_upwards [hn, hm] with w hn hw
    exact h w hw hn
  exact le_of_tendsto_of_tendsto
    (hu'.tendsto.mono_left nhdsWithin_le_nhds)
    (hv'.tendsto.mono_left nhdsWithin_le_nhds) hb

/-- Cancel an analytic factor in a norm inequality, including at its zeros. -/
theorem norm_le_on_upper_of_mul_norm_le {N : ℂ → ℂ} (hN : Differentiable ℂ N)
    (hne : ∃ z : ℂ, N z ≠ 0) {φ f g : ℂ → ℂ}
    (hf : ContinuousOn f UHP) (hg : ContinuousOn g UHP)
    (hφ : ∀ z ∈ UHP, N z ≠ 0 → φ z ≠ 0)
    (h : ∀ z ∈ UHP, ‖φ z * f z‖ ≤ ‖φ z * g z‖) :
    ∀ z ∈ UHP, ‖f z‖ ≤ ‖g z‖ := by
  apply le_on_upper_of_le_off_entire_zeros hN hne hf.norm hg.norm
  intro z hz hn
  have hb := h z hz
  rw [norm_mul, norm_mul] at hb
  exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr (hφ z hz hn))).1 hb

/-- The Schur parameter obtained by undoing the normalization at `i`. -/
def schurParameter (a : ℂ) (F H : ℂ → ℂ) (z : ℂ) : ℂ :=
  (conj a * F z + H z) / (F z + a * H z)

/-- The inverse disk automorphism gives a holomorphic contractive parameter. -/
theorem schurParameter_spec {a : ℂ} (ha : ‖a‖ < 1) {F H : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F UHP) (hH : DifferentiableOn ℂ H UHP)
    (hF0 : ∀ z ∈ UHP, F z ≠ 0) (hbound : ∀ z ∈ UHP, ‖H z‖ ≤ ‖F z‖) :
    DifferentiableOn ℂ (schurParameter a F H) UHP ∧
      ∀ z ∈ UHP, ‖schurParameter a F H z‖ ≤ 1 := by
  constructor
  · exact ((hF.const_mul _).add hH).div (hF.add (hH.const_mul _))
      (fun z hz ↦ schurBack_linear_den_ne_zero ha (hF0 z hz) (hbound z hz))
  · intro z hz
    exact norm_schurBack_linear_le ha (hF0 z hz) (hbound z hz)

end FF
