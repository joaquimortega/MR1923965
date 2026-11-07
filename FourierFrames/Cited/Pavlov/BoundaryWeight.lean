import FourierFrames.Cited.Pavlov.WeightTransfer
import FourierFrames.Cited.Pavlov.LogDistance

/-! # BMO of the real boundary modulus from shifted A2 -/

open MeasureTheory Metric Set Complex

noncomputable section
namespace FF.Pavlov

/-- A complete interpolation generator has BMO boundary logarithmic modulus. -/
theorem CardinalData.boundary_log_bmo {Γ : Set ℝ} (d : CardinalData Γ)
    (g : Grid Γ) (hΓ : IsSeparated Γ) :
    MemBMO (fun x : ℝ ↦ Real.log ‖d.G (x : ℂ)‖) := by
  obtain ⟨ε, c, C, hε, hεl, hc, hC, hbd⟩ := generating_cell_bounds g d
  obtain ⟨K, hK, hw, hwi, hpos, hmean⟩ := d.shifted_A2_of_bounds g hΓ ε c C hc hC
    (fun k x hx ↦ (hbd k x hx).1)
  have hlog := memBMO_log_of_A2 hw hwi (Filter.Eventually.of_forall hpos) hmean
  have hhalf := memBMO_const_mul hlog (1/2)
  have hshift : MemBMO (fun x : ℝ ↦ Real.log ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖) := by
    convert hhalf using 1
    funext x
    rw [Real.log_pow]
    ring
  apply memBMO_boundary_log_of_cell_comparison g d.G ε |Real.log C-Real.log c|
    (locallyIntegrable_boundary_log_of_entire d.entire) hshift
  intro k x hx hne
  obtain ⟨⟨hsL, hsU⟩, ⟨hrL, hrU⟩⟩ := hbd k x hx
  have hd : 0 < ‖deriv d.G (g.point k : ℂ)‖ :=
    norm_pos_iff.mpr (d.toGeneratingData.simple (g.point_mem k))
  have ht : 0 < |x-g.point k| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hr : 0 < ‖d.G (x : ℂ)‖ := (mul_pos (mul_pos hc hd) ht).trans_le hrL
  have hs : 0 < ‖d.G ((x : ℂ)+(ε : ℂ)*I)‖ := (mul_pos hc hd).trans_le hsL
  have hsL' := Real.log_le_log (mul_pos hc hd) hsL
  have hsU' := Real.log_le_log hs hsU
  have hrL' := Real.log_le_log (mul_pos (mul_pos hc hd) ht) hrL
  have hrU' := Real.log_le_log hr hrU
  rw [Real.log_mul hc.ne' hd.ne'] at hsL'
  rw [Real.log_mul hC.ne' hd.ne'] at hsU'
  rw [Real.log_mul (mul_pos hc hd).ne' ht.ne', Real.log_mul hc.ne' hd.ne'] at hrL'
  rw [Real.log_mul (mul_pos hC hd).ne' ht.ne', Real.log_mul hC.ne' hd.ne'] at hrU'
  have ha := le_abs_self (Real.log C-Real.log c)
  apply abs_le.mpr
  constructor <;> linarith

end FF.Pavlov
