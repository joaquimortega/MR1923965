import FourierFrames.Cited.Pavlov.GeneratingDispersion
import FourierFrames.Cited.Pavlov.BoundaryPhase
import FourierFrames.Cited.Pavlov.CountingBMO

/-!
# Pavlov's BMO necessity theorem

Cardinal-function estimates give an A₂ weight and BMO of the real logarithmic
modulus of the generating function. Its exact Schwarz representation identifies
the conjugate-Poisson boundary limit with the counting discrepancy. Uniform BMO
estimates and Fatou then prove the unchanged statement `PavlovBMO`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF
namespace Pavlov

theorem CardinalData.counting_discrepancy_bmo {Γ : Set ℝ} (d : CardinalData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) (hcis : IsCompleteInterpolating Γ) :
    MemBMO (fun x ↦ countFn Γ x - x) := by
  obtain ⟨L, hL, hexp⟩ := d.toGeneratingData.exists_upper_log
  obtain ⟨c₀, hphase⟩ := d.toGeneratingData.boundary_phase hΓ g hL hexp
  obtain ⟨c₁, hdisp⟩ := d.upper_log_dispersion g hΓ hcis hL hexp
  let u := fun t : ℝ ↦ Real.log ‖d.G (t : ℂ)‖
  have hu : MemBMO u := d.boundary_log_bmo g hΓ
  have hlog : LogIntegrable u := memBMO_logIntegrable hu
  have hcp (x y : ℝ) (hy : 0 < y) :
      conjugatePoisson u y x = (L ((x : ℂ) + (y : ℂ) * I)).im + Real.pi * x - c₁ := by
    have hz : (x : ℂ) + (y : ℂ) * I ∈ UHP := by simpa [UHP] using hy
    have h := congrArg Complex.im (hdisp _ hz)
    have he : (I * (Real.pi : ℂ) * ((x : ℂ) + (y : ℂ) * I)).im = Real.pi * x := by
      simp
    simp only [Complex.add_im, Complex.sub_im, he, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero] at h
    have hs := schwarzIntegral_im hlog (x := x) hy
    change (schwarzIntegral u ((x : ℂ) + (y : ℂ) * I)).im = _ at hs
    change (L ((x : ℂ) + (y : ℂ) * I)).im =
      (schwarzIntegral u ((x : ℂ) + (y : ℂ) * I)).im - Real.pi * x + c₁ at h
    linarith
  let y : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1)⁻¹
  have hy : ∀ n, 0 < y n := fun n ↦ by dsimp [y]; positivity
  have hyt : Tendsto y atTop (𝓝[>] 0) := by
    have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop := by
      apply Filter.tendsto_atTop.mpr
      intro b
      obtain ⟨N, hN⟩ := exists_nat_gt b
      filter_upwards [eventually_ge_atTop N] with n hn
      have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact tendsto_inv_atTop_nhdsGT_zero.comp ht
  apply memBMO_countFn_sub_id_of_conjugatePoisson_limit hΓ hu (c₀ - c₁) hy
  filter_upwards [g.ae_not_mem] with x hx
  have ht := (((hphase x hx).add_const (Real.pi * x)).sub_const c₁).comp hyt
  have he : (fun n ↦ conjugatePoisson u (y n) x) =
      fun n ↦ (L ((x : ℂ) + (y n : ℂ) * I)).im + Real.pi * x - c₁ := by
    funext n
    exact hcp x (y n) (hy n)
  rw [he]
  have hvalue : -Real.pi * countFn Γ x + c₀ + Real.pi * x - c₁ =
      -Real.pi * (countFn Γ x - x) + (c₀ - c₁) := by ring
  simpa only [Function.comp_def, hvalue] using ht

end Pavlov

/-- **Pavlov's theorem**, in the BMO necessity form used in the paper. -/
theorem pavlovBMO_holds : PavlovBMO := by
  intro Γ hΓ hcis
  obtain ⟨d⟩ := Pavlov.exists_cardinalData hΓ hcis
  obtain ⟨g⟩ := Pavlov.exists_grid hΓ hcis
  exact d.counting_discrepancy_bmo g hΓ hcis

end FF
