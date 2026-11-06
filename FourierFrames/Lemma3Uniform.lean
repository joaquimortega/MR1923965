import OrtegaCerdaSeip.Lemma3.Main

/-!
# Uniform form of estimate (2) of [OS99, Lemma 3]

The vendored `OCS.multF_estimate_two` states `∃ c₁ c₂` *after* fixing the weight `m`.  Its proof
(`OCS.exists_abs_sum_multErr_sub_log_infDist_le`) produces `c₁ = e^{-K}`, `c₂ = e^{K}` with `K`
an explicit expression in `a, b` only (the constants `K₁, K₂, K₃` of that proof), so the constants
can be chosen uniformly over all weights `m` with `a ≤ m ≤ b`.  This uniform form is what M09
(`Theorem2ii.lean`) needs.  The file is not part of the vendored library, which must not be edited;
its proof is "re-run the proof of `OCS.multF_estimate_two` with `K` taken from the explicit
formula" and is left as `sorry` in the scaffold.
-/

open Metric Set Complex Filter Topology

noncomputable section

namespace FF

/-- **Lemma 3, estimate (2), with constants depending only on `(a, b)`.** -/
theorem lemma3_estimate_uniform {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (m : ℝ → ℝ), OCS.IsMultWeight m a b → ∀ C : ℝ, ∀ z : ℂ,
      |z.im| ≤ 1 →
        c₁ * infDist z (OCS.multGammaC m) ≤ ‖OCS.multF m C z‖ * Real.exp (-OCS.multU m C z) ∧
        ‖OCS.multF m C z‖ * Real.exp (-OCS.multU m C z) ≤ c₂ * infDist z (OCS.multGammaC m) := by
  sorry

end FF
