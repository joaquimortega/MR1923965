import FourierFrames.Theorem2i.Product
import FourierFrames.Theorem2i.CellsAux

/-!
# M08 helper: U_psi as a sum over cells

See `blueprint/M08_Theorem2i.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

/-! ## §4. `U_ψ` as a sum over cells -/

theorem RegData.integrable_UPsi (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    Integrable fun s : ℝ =>
      (Real.log ‖1 - z / s‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 s) * (z / s).re) * deriv ψ s :=
  (fun _ => h.integrable_upsiInt z) hz

theorem RegData.cell_succ (n : ℕ) : cell t (n + 1) = Ioc (t n) (t (n + 1)) := by
  simp [cell]

theorem RegData.iUnion_cell (h : RegData ψ t C M) : (⋃ n : ℕ, cell t (n + 1)) = Ioi 0 := by
  have ht := h.tendsto_t
  ext x
  simp only [mem_iUnion, mem_Ioi, RegData.cell_succ, mem_Ioc]
  constructor
  · rintro ⟨n, h1, _⟩
    have : t 0 ≤ t n := h.mono.monotone (Nat.zero_le n)
    linarith [h.t0]
  · intro hx
    have hex : ∃ m, x ≤ t m := (ht.eventually (eventually_ge_atTop x)).exists
    classical
    let m := Nat.find hex
    have hm : x ≤ t m := Nat.find_spec hex
    have hm0 : m ≠ 0 := by
      intro h0
      have : x ≤ t 0 := by simpa [m, h0] using hm
      linarith [h.t0]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    refine ⟨k, ?_, by rw [hk] at hm; exact hm⟩
    have := Nat.find_min hex (m := k) (by omega)
    exact lt_of_not_ge this

theorem RegData.pairwise_cell (h : RegData ψ t C M) :
    Pairwise (Function.onFun Disjoint fun n : ℕ => cell t (n + 1)) := by
  intro a b hab
  wlog hlt : a < b generalizing a b
  · exact (this hab.symm (lt_of_le_of_ne (not_lt.1 hlt) hab.symm)).symm
  simp only [Function.onFun, RegData.cell_succ]
  rw [Set.disjoint_left]
  intro x hx hx'
  have : t (a + 1) ≤ t b := h.mono.monotone (by omega)
  linarith [hx.2, hx'.1]

theorem RegData.hasSum_UPsi (h : RegData ψ t C M) (z : ℂ) :
    HasSum (fun n : ℕ => ∫ s in cell t (n + 1),
        (Real.log ‖1 - z / s‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 s) * (z / s).re) * deriv ψ s)
      (UPsi ψ z) := by
  have hint := h.integrable_upsiInt z
  have h1 := hasSum_integral_iUnion (μ := volume) (f := upsiInt ψ z)
    (s := fun n : ℕ => cell t (n + 1)) (fun n => measurableSet_Ioc) h.pairwise_cell
    hint.integrableOn
  rw [h.iUnion_cell] at h1
  have h2 : ∫ s in Ioi (0 : ℝ), upsiInt ψ z s = UPsi ψ z := by
    unfold UPsi
    show _ = ∫ s, upsiInt ψ z s
    rw [← integral_add_compl measurableSet_Ioi hint]
    have : ∫ s in (Ioi (0 : ℝ))ᶜ, upsiInt ψ z s = 0 := by
      rw [compl_Ioi]
      refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
      simp [upsiInt, h.deriv_eq_zero_of_nonpos hs]
    rw [this, add_zero]
  rw [h2] at h1
  exact h1

theorem RegData.cellTerm_eq (h : RegData ψ t C M) {z : ℂ} (n : ℕ) :
    cellTerm ψ t C (n + 1) z =
      (∫ s in cell t (n + 1), upsiInt ψ z s) -
        (Real.log ‖1 - z / zPt ψ t C (n + 1)‖ + z.re * convFac ψ t (n + 1)) := by
  have hsub : cell t (n + 1) ⊆ Ioc 0 (t (n + 1)) := by
    rw [RegData.cell_succ]
    have : t 0 ≤ t n := h.mono.monotone (Nat.zero_le n)
    intro x hx
    exact ⟨by linarith [h.t0, hx.1], hx.2⟩
  have hR : 0 ≤ t (n + 1) := by
    have : t 0 ≤ t (n + 1) := h.mono.monotone (Nat.zero_le _)
    linarith [h.t0]
  have hD : IntegrableOn (deriv ψ) (cell t (n + 1)) :=
    (h.continuous_deriv.continuousOn.integrableOn_Icc (a := 0) (b := t (n + 1))).mono_set
      (hsub.trans Ioc_subset_Icc_self)
  have hL : IntegrableOn (fun s : ℝ => Real.log ‖1 - z / (s : ℂ)‖ * deriv ψ s)
      (cell t (n + 1)) := by
    obtain ⟨B, hB0, hB⟩ := h.exists_bound_deriv
    exact (((log_one_sub_div_integrableOn z hR).mono_set hsub).mul_bdd
      h.continuous_deriv.aestronglyMeasurable (c := B)
      (Filter.Eventually.of_forall fun s => by simpa using hB s))
  have hP := (h.integrableOn_linPart z (R := t (n + 1))).mono_set hsub
  have e1 : ∫ s in cell t (n + 1), upsiInt ψ z s =
      (∫ s in cell t (n + 1), Real.log ‖1 - z / (s : ℂ)‖ * deriv ψ s) +
      ∫ s in cell t (n + 1),
        (1 - (Icc (-1 : ℝ) 1).indicator 1 s) * (z / s).re * deriv ψ s := by
    rw [← integral_add hL hP]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [upsiInt]; ring
  have e2 : ∫ s in cell t (n + 1),
        (1 - (Icc (-1 : ℝ) 1).indicator 1 s) * (z / s).re * deriv ψ s =
      z.re * convFac ψ t (n + 1) := by
    unfold convFac
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [Complex.div_ofReal_re]
    ring
  have e3 : cellTerm ψ t C (n + 1) z =
      (∫ s in cell t (n + 1), Real.log ‖1 - z / (s : ℂ)‖ * deriv ψ s) -
        Real.log ‖1 - z / zPt ψ t C (n + 1)‖ := by
    unfold cellTerm
    have : ∀ s : ℝ, (Real.log ‖1 - z / (s : ℂ)‖ - Real.log ‖1 - z / zPt ψ t C (n + 1)‖) *
        deriv ψ s = Real.log ‖1 - z / (s : ℂ)‖ * deriv ψ s -
        Real.log ‖1 - z / zPt ψ t C (n + 1)‖ * deriv ψ s := fun s => by ring
    simp_rw [this]
    rw [integral_sub hL (hD.const_mul _), integral_const_mul, h.integral_cell (Nat.succ_pos n)]
    ring
  rw [e1, e2, e3]
  ring

/-- `U_ψ - log|f| = ∑ j_n`. -/
theorem RegData.hasSum_cellTerm (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    HasSum (fun n : ℕ => cellTerm ψ t C (n + 1) z)
      (UPsi ψ z - Real.log ‖fProd ψ t C z‖) := by
  have := (h.hasSum_UPsi z).sub (h.hasSum_log_fProd hz)
  convert this using 1
  funext n
  exact h.cellTerm_eq n

end FF
