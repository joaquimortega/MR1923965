import FourierFrames.Landau
import FourierFrames.Cited.Pavlov.PoissonBMO

/-!
# Passing a conjugate Poisson limit to the counting discrepancy

A separated counting function is monotone and hence locally integrable.
The uniform conjugate Poisson BMO estimate and its a.e. limit theorem then
recover BMO for the discrepancy after removing an affine normalization.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace FF.Pavlov

/-- A separated counting function is monotone. -/
theorem countFn_monotone {Γ : Set ℝ} (hΓ : IsSeparated Γ) : Monotone (countFn Γ) := by
  intro a b hab
  have he := FF.countFn_sub (fun a b ↦ hΓ.finite_inter_Ioc a b) hab
  have hn : (0:ℝ) ≤ ((Γ ∩ Ioc a b).ncard : ℝ) := Nat.cast_nonneg _
  linarith

/-- Separated counting functions are locally integrable. -/
theorem locallyIntegrable_countFn {Γ : Set ℝ} (hΓ : IsSeparated Γ) :
    LocallyIntegrable (countFn Γ) :=
  (countFn_monotone hΓ).locallyIntegrable

/-- The counting discrepancy is locally integrable independently of Pavlov's theorem. -/
theorem locallyIntegrable_countFn_sub_id {Γ : Set ℝ} (hΓ : IsSeparated Γ) :
    LocallyIntegrable (fun x ↦ countFn Γ x-x) :=
  (locallyIntegrable_countFn hΓ).sub continuous_id.locallyIntegrable

/-- A conjugate Poisson boundary limit supplies BMO for the counting discrepancy. -/
theorem memBMO_countFn_sub_id_of_conjugatePoisson_limit {Γ : Set ℝ}
    (hΓ : IsSeparated Γ) {u : ℝ → ℝ} (hu : MemBMO u) (c : ℝ)
    {y : ℕ → ℝ} (hy : ∀ n, 0 < y n)
    (hlim : ∀ᵐ x : ℝ, Tendsto (fun n ↦ conjugatePoisson u (y n) x) atTop
      (𝓝 (-Real.pi*(countFn Γ x-x)+c))) :
    MemBMO (fun x ↦ countFn Γ x-x) := by
  have hd := locallyIntegrable_countFn_sub_id hΓ
  have hg : LocallyIntegrable (fun x ↦ -Real.pi*(countFn Γ x-x)+c) :=
    (hd.smul (-Real.pi)).add continuous_const.locallyIntegrable
  have hb := memBMO_of_conjugatePoisson_ae_limit hu hg hy hlim
  have hs := memBMO_const_mul (memBMO_sub hb (memBMO_const c)) (-Real.pi)⁻¹
  have he : (fun x ↦ (-Real.pi)⁻¹ * ((-Real.pi*(countFn Γ x-x)+c)-c)) =
      (fun x ↦ countFn Γ x-x) := by
    ext x
    rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr Real.pi_ne_zero), one_mul]
  rw [he] at hs
  exact hs

end FF.Pavlov
