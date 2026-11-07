import FourierFrames.Frames
import FourierFrames.HB.Comparable
import FourierFrames.Theorem1.Main
import FourierFrames.Corollary1
import FourierFrames.Landau
import FourierFrames.LogExample
import FourierFrames.Corollary2
import FourierFrames.Theorem2i
import FourierFrames.Cited.PaleyWiener
import FourierFrames.Cited.DSPerturbation
import FourierFrames.Cited.JohnNirenberg
import FourierFrames.Cited.DeBrangesDE
import FourierFrames.Cited.DeBrangesFC

/-!
# The main results with the proved cited results discharged

Phase 2 proves the Paley–Wiener theorem (`paleyWiener_holds`), de Branges' Theorems C, D and E
(`theoremC_holds`, `theoremD_holds`, `theoremE_holds`), the John–Nirenberg inequality
(`johnNirenberg_holds`) and Duffin–Schaeffer's Lemma III (`dsPerturbation_holds`).  This file
applies them to the main theorems.  The results that need only these hypotheses become
unconditional (`*_unconditional`); those that also need de Branges' Theorem F or Pavlov's
Theorem A keep exactly those hypotheses (`*_of_theoremF`, `*_of_theoremF_pavlov`).  The
intermediate forms `*_of_theoremCF`, `*_of_theoremC`, `*_of_theoremCF_pavlov` are kept.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF

/-- **Lemma III of Duffin–Schaeffer**, unconditionally. -/
theorem dsPerturbation_holds : DSPerturbation :=
  dsPerturbation_of_paleyWiener paleyWiener_holds

/-- **Fourier frames ⟺ sampling** (p. 790), unconditionally. -/
theorem isFourierFrame_iff_isSampling_unconditional (Λ : Set ℝ) :
    IsFourierFrame Λ ↔ IsSampling Λ :=
  isFourierFrame_iff_isSampling paleyWiener_holds Λ

/-- **The "evident fact"** (p. 799), unconditionally. -/
theorem heEqPW_of_comparable_unconditional {E : ℂ → ℂ} (hE : IsHB E)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) :
    HEEqPW E :=
  heEqPW_of_comparable paleyWiener_holds hE hcomp

/-- **Theorem 1, sufficiency**, unconditionally. -/
theorem theorem1_sufficiency_unconditional {Λ : Set ℝ} (hΛ : IsSeparated Λ) {E F : ℂ → ℂ}
    (hEHB : IsHB E) (hFHB : IsHB F) (hEPW : HEEqPW E)
    (hzero : ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ)) :
    IsSampling Λ :=
  theorem1_sufficiency paleyWiener_holds theoremE_holds hΛ hEHB hFHB hEPW hzero

/-- **Theorem 1, necessity**, from de Branges' Theorems C and F alone. -/
theorem theorem1_necessity_of_theoremCF (hC : TheoremC) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) :=
  theorem1_necessity paleyWiener_holds hC hF hΛ hs

/-- **Theorem 1**, from de Branges' Theorems C and F alone. -/
theorem theorem1_of_theoremCF (hC : TheoremC) (hF : TheoremF) {Λ : Set ℝ} (hΛ : IsSeparated Λ) :
    IsSampling Λ ↔ ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) :=
  theorem1 paleyWiener_holds hC theoremE_holds hF hΛ

/-- **Remark p. 797**, from de Branges' Theorem C alone. -/
theorem completeInterpolating_zero_set_of_theoremC (hC : TheoremC)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hcis : IsCompleteInterpolating Λ) :
    ∃ E : ℂ → ℂ, IsHB E ∧ HEEqPW E ∧ ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) :=
  completeInterpolating_zero_set paleyWiener_holds hC theoremD_holds hΛ hcis

/-- **Corollary 1**, from de Branges' Theorems C and F alone. -/
theorem corollary1_of_theoremCF (hC : TheoremC) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ IsCompleteInterpolating (Set.range γ) ∧
      ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1) :=
  corollary1 paleyWiener_holds hC theoremE_holds hF hΛ hs

/-- **Landau's inequality** (the Claim of §4), from de Branges' Theorems C and F and Pavlov's
Theorem A alone. -/
theorem landau_inequality_of_theoremCF_pavlov (hC : TheoremC) (hF : TheoremF) (hA : PavlovBMO)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ A B : ℝ, ∀ a b : ℝ, a < b →
      ENNReal.ofReal (b - a - A * Real.posLog (b - a) - B) ≤ ((Λ ∩ Ioc a b).encard : ℝ≥0∞) :=
  landau_inequality paleyWiener_holds hC theoremE_holds hF hA johnNirenberg_holds hΛ hs

/-- **The example of p. 798** is a complete interpolating sequence, unconditionally. -/
theorem logExample_isCompleteInterpolating_unconditional :
    IsCompleteInterpolating logExample :=
  logExample_isCompleteInterpolating paleyWiener_holds theoremE_holds

/-- **Landau's inequality is best possible**, unconditionally. -/
theorem landau_sharp_unconditional :
    IsSeparated logExample ∧ IsSampling logExample ∧
      ∀ A : ℝ, A < 1 → ¬ ∃ B : ℝ, ∀ a b : ℝ, a < b →
        ENNReal.ofReal (b - a - A * Real.posLog (b - a) - B) ≤
          ((logExample ∩ Ioc a b).encard : ℝ≥0∞) :=
  landau_sharp paleyWiener_holds theoremE_holds

/-- **Corollary 2**, unconditionally. -/
theorem corollary2_unconditional {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {f : ℂ → ℂ} (hf : IsHB f)
    (hφ : Tendsto (phaseDeriv f) (cocompact ℝ) (𝓝 0))
    (happ : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.exp (UPsi ψ z - C) ≤ ‖f z‖ ∧ ‖f z‖ ≤ Real.exp (UPsi ψ z + C)) :
    IsSampling (LambdaPsi ψ) :=
  corollary2 paleyWiener_holds theoremE_holds dsPerturbation_holds hψ hf hφ happ

/-- **Theorem 2 (i)** (with `ψ'` eventually nonincreasing), unconditionally. -/
theorem theorem2_i_unconditional {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ)
    (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0) (hreg : IsLogRegularPartition ψ)
    (hmono : ∃ X : ℝ, AntitoneOn (deriv ψ) (Set.Ici X)) :
    IsSampling (LambdaPsi ψ) :=
  theorem2_i paleyWiener_holds theoremE_holds dsPerturbation_holds hψ h0 hreg hmono

/-- **Theorem 2 (i)** (with the cell density bound), unconditionally. -/
theorem theorem2_i_of_densityBound_unconditional {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ)
    (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0) (hreg : IsLogRegularPartitionWithDensity ψ) :
    IsSampling (LambdaPsi ψ) :=
  theorem2_i_of_densityBound paleyWiener_holds theoremE_holds dsPerturbation_holds hψ h0 hreg

/-- **Theorem 1, necessity**, from de Branges' Theorem F alone. -/
theorem theorem1_necessity_of_theoremF (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) :=
  theorem1_necessity_of_theoremCF theoremC_holds hF hΛ hs

/-- **Theorem 1**, from de Branges' Theorem F alone. -/
theorem theorem1_of_theoremF (hF : TheoremF) {Λ : Set ℝ} (hΛ : IsSeparated Λ) :
    IsSampling Λ ↔ ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) :=
  theorem1_of_theoremCF theoremC_holds hF hΛ

/-- **Remark p. 797**, unconditionally. -/
theorem completeInterpolating_zero_set_unconditional
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hcis : IsCompleteInterpolating Λ) :
    ∃ E : ℂ → ℂ, IsHB E ∧ HEEqPW E ∧ ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) :=
  completeInterpolating_zero_set_of_theoremC theoremC_holds hΛ hcis

/-- **Corollary 1**, from de Branges' Theorem F alone. -/
theorem corollary1_of_theoremF (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ IsCompleteInterpolating (Set.range γ) ∧
      ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1) :=
  corollary1_of_theoremCF theoremC_holds hF hΛ hs

/-- **Landau's inequality**, from de Branges' Theorem F and Pavlov's Theorem A alone. -/
theorem landau_inequality_of_theoremF_pavlov (hF : TheoremF) (hA : PavlovBMO)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ A B : ℝ, ∀ a b : ℝ, a < b →
      ENNReal.ofReal (b - a - A * Real.posLog (b - a) - B) ≤ ((Λ ∩ Ioc a b).encard : ℝ≥0∞) :=
  landau_inequality_of_theoremCF_pavlov theoremC_holds hF hA hΛ hs

end FF
