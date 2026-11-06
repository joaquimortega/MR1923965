import FourierFrames.PW.Bounds
import OrtegaCerdaSeip.Bernstein.NormalFamily

/-!
# M01 — Completeness and normal-family compactness of `PW`

See `blueprint/M01_PW.md`, §4.  Both results use only the pointwise bound `pw_norm_sq_le`
(hence `hPW`) and Fatou's lemma.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- **Completeness.** An `L²(ℝ)`-Cauchy sequence in `PW` converges in `L²` and locally uniformly
to some `g ∈ PW`. -/
theorem pw_complete (hPW : PaleyWienerThm) {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemPW (f n))
    (hc : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      pwNormSq (fun z ↦ f m z - f n z) < ε) :
    ∃ g : ℂ → ℂ, MemPW g ∧ TendstoLocallyUniformly f g atTop ∧
      Tendsto (fun n ↦ pwNormSq (fun z ↦ f n z - g z)) atTop (nhds 0) := by
  sorry

/-- **Normal families.** A norm-bounded sequence in `PW` has a subsequence converging locally
uniformly to some `g ∈ PW`, and `‖g‖² ≤ liminf ‖f_n‖²` (even `≤ lim ‖f_{φ n}‖²` along the
subsequence, which may be chosen to realise the `liminf`). -/
theorem pw_normal_family (hPW : PaleyWienerThm) {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemPW (f n))
    {M : ℝ} (hM : ∀ n, pwNormSq (f n) ≤ ENNReal.ofReal M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, MemPW g ∧
      TendstoLocallyUniformly (fun n ↦ f (φ n)) g atTop ∧
      pwNormSq g ≤ liminf (fun n ↦ pwNormSq (f n)) atTop := by
  sorry

end FF
