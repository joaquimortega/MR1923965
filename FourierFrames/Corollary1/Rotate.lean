import FourierFrames.HB.DeBranges

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF

theorem isH2Upper_unit_mul {c : ℂ} (hc : ‖c‖ = 1) {g : ℂ → ℂ} (hg : IsH2Upper g) :
    IsH2Upper (fun z ↦ c * g z) := by
  refine ⟨(differentiableOn_const c).mul hg.1, ?_⟩
  obtain ⟨C, hC⟩ := hg.2
  refine ⟨C, fun y hy ↦ ?_⟩
  refine le_trans (le_of_eq ?_) (hC y hy)
  congr 1; ext x
  rw [enorm_mul, ← ofReal_norm, hc]; simp

theorem memHE_unit_mul {c : ℂ} (hc : ‖c‖ = 1) {E f : ℂ → ℂ} (hf : MemHE E f) :
    MemHE (fun z ↦ c * E z) f := by
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc]; simp
  obtain ⟨hd, h1, h2⟩ := hf
  refine ⟨hd, ?_, ?_⟩
  · have := isH2Upper_unit_mul hci h1
    convert this using 2 with z
    field_simp
  · have := isH2Upper_unit_mul hci h2
    convert this using 2 with z
    field_simp

theorem memHE_unit_mul_iff {c : ℂ} (hc : ‖c‖ = 1) {E f : ℂ → ℂ} :
    MemHE (fun z ↦ c * E z) f ↔ MemHE E f := by
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc]; simp
  refine ⟨fun h ↦ ?_, memHE_unit_mul hc⟩
  have := memHE_unit_mul hci h
  convert this using 2 with z
  field_simp

theorem heNormSq_unit_mul {c : ℂ} (hc : ‖c‖ = 1) (E f : ℂ → ℂ) :
    heNormSq (fun z ↦ c * E z) f = heNormSq E f := by
  unfold heNormSq
  congr 1; ext t
  have e : f t / (c * E t) = f t / E t / c := by rw [mul_comm, ← div_div]
  rw [e, ← ofReal_norm (f t / E t / c), ← ofReal_norm (f t / E t), norm_div, hc, div_one]

theorem HEEqPW.rotate_aux {E : ℂ → ℂ} (h : HEEqPW E) (θ : ℝ) :
    HEEqPW (fun z ↦ Complex.exp (I * θ) * E z) := by
  have hc : ‖Complex.exp (I * θ)‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ
  refine ⟨fun f ↦ (memHE_unit_mul_iff hc).trans (h.1 f), ?_⟩
  obtain ⟨c, C, hc0, h2⟩ := h.2
  exact ⟨c, C, hc0, fun f hf ↦ by rw [heNormSq_unit_mul hc]; exact h2 f hf⟩

end FF
