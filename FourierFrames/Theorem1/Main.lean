import FourierFrames.Theorem1.Necessity
import FourierFrames.Theorem1.Sufficiency

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF

/-!
# M04 — `theorem1`

See `blueprint/M04_Sufficiency.md`.
-/

/-- **Theorem 1** (p. 795): a separated sequence `Λ` is sampling for `PW` if and only if there are
`E, F ∈ \overline{HB}` with `H(E) = PW` such that `Λ` is the zero set of `EF + E^*F^*`. -/
theorem theorem1 (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) :
    IsSampling Λ ↔ ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  constructor
  · intro hs
    exact theorem1_necessity hPW hC hF hΛ hs
  · rintro ⟨E, F, hEHB, hFHB, hEPW, hzero⟩
    exact theorem1_sufficiency hPW hE hΛ hEHB hFHB hEPW hzero

end FF
