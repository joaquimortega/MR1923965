import FourierFrames.Cited.Pavlov.CardinalLog
import FourierFrames.Cited.Pavlov.LogPoisson
import FourierFrames.Cited.Pavlov.OuterComparison
import FourierFrames.Cited.Pavlov.NoExponentialDefect

/-!
# Logarithmic dispersion of the generating function

The positive harmonic defect of a normalized cardinal is linear in height.
Its outer comparison lies in H², so interpolation uniqueness rules out a
positive exponential factor. Adding back the removed real zero gives the
exact logarithmic dispersion of the generating function.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF.Pavlov

variable {Γ : Set ℝ}

theorem CardinalData.log_norm_eq_poisson (d : CardinalData Γ) (g : Grid Γ)
    (hΓ : IsSeparated Γ) (hcis : IsCompleteInterpolating Γ) :
    ∀ z ∈ UHP, Real.log ‖d.G z‖ = Real.pi * z.im +
      (schwarzIntegral (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖) z).re := by
  let γ := g.point 0
  have hγ : γ ∈ Γ := g.point_mem 0
  have hd := d.cardinal_log_input g hΓ hγ
  have hb : (fun t : ℝ ↦ Real.log ‖cardinalUpper d γ (t : ℂ)‖) = cardinalLog d γ := by
    funext t
    rw [hd.boundary_norm]
    rfl
  obtain ⟨a, ha, hdef⟩ := poisson_log_defect_eq_mul_im hd.upper_entire
    hd.upper_ne_zero hd.upper_bounded hd.log_upper_integrable
  rw [hb] at hdef
  have hO := isH2Upper_exp_schwarzIntegral hd.log_q_integrable hd.exp_sq_integrable
  obtain ⟨b, hfactor⟩ := factor_of_log_defect hd.log_q_integrable
    hd.upper_entire.differentiableOn hd.upper_ne_zero a hdef
  have haz : a = 0 := no_exponential_defect hcis hd.memPW.1 hd.real hO
    (by rw [hd.at_node]; exact one_ne_zero)
    (fun x hx hne ↦ (hd.zeros x).2 ⟨x, hx, hne, rfl⟩) ha hfactor
  intro z hz
  have hdefz := hdef z hz
  rw [haz, zero_mul] at hdefz
  have hs : (schwarzIntegral (cardinalLog d γ) z).re =
      (schwarzIntegral (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖) z).re -
        Real.log ‖z - (γ : ℂ)‖ - Real.log ‖deriv d.G (γ : ℂ)‖ := by
    rw [schwarzIntegral_congr_ae (cardinalLog_eq_ae d g hγ) z,
      schwarzIntegral_sub (hd.log_G_integrable.sub (logIntegrable_log_abs_sub γ))
        (logIntegrable_const (Real.log ‖deriv d.G (γ : ℂ)‖)) hz,
      schwarzIntegral_sub hd.log_G_integrable (logIntegrable_log_abs_sub γ) hz,
      schwarzIntegral_const _ hz, Complex.sub_re, Complex.sub_re, Complex.ofReal_re,
      schwarzIntegral_re_log_abs_sub γ hz]
  have hA := log_cardinalUpper_eq d hγ hz
  have hG := log_generating_eq_cardinal_upper d hγ hz
  linarith

/-- Every holomorphic logarithm has the same normalized Schwarz representation,
up to one imaginary constant. -/
theorem CardinalData.upper_log_dispersion (d : CardinalData Γ) (g : Grid Γ)
    (hΓ : IsSeparated Γ) (hcis : IsCompleteInterpolating Γ)
    {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L UHP)
    (hexp : ∀ z ∈ UHP, Complex.exp (L z) = d.G z) :
    ∃ c : ℝ, ∀ z ∈ UHP,
      L z = schwarzIntegral (fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖) z -
        I * Real.pi * z + (c : ℂ) * I := by
  let u := fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖
  have hu : LogIntegrable u := d.log_generating_logIntegrable g hΓ
  let K := fun z : ℂ ↦ L z - schwarzIntegral u z + I * Real.pi * z
  have hK : DifferentiableOn ℂ K UHP :=
    (hL.sub (differentiableOn_schwarzIntegral hu)).add
      (differentiable_id.const_mul (I * Real.pi)).differentiableOn
  have hRe : ∀ z ∈ UHP, (K z).re = 0 := by
    intro z hz
    have hlog : Real.log ‖d.G z‖ = (L z).re := by
      rw [← hexp z hz, Complex.norm_exp, Real.log_exp]
    have hd := d.log_norm_eq_poisson g hΓ hcis z hz
    dsimp only [K, u]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    linarith
  have ho : IsOpen UHP := isOpen_lt continuous_const Complex.continuous_im
  have hconn : IsConnected UHP := (convex_halfSpace_im_gt 0).isConnected ⟨I, by simp⟩
  obtain ⟨c, hc⟩ := (hK.analyticOnNhd ho).eq_re_add_const_mul_I_of_re_eq_const hRe ho hconn
  refine ⟨c, fun z hz ↦ ?_⟩
  have h := hc z hz
  dsimp only [K] at h
  simp only [Complex.ofReal_zero, zero_add] at h
  linear_combination h

end FF.Pavlov
