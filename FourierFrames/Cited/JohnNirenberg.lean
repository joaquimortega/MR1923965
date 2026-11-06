import FourierFrames.Defs

/-!
# P2b — The John–Nirenberg inequality (`JohnNirenberg`)

See `blueprint/P2_DS_JN.md`, Part B.  Route: dyadic Calderón–Zygmund (stopping-time) decomposition at
level `2M` on `[a,b]`, Lebesgue differentiation from Mathlib
(`IsUnifLocDoublingMeasure.ae_tendsto_average`), and iteration; constants `C = 2`, `c = log 2 / 4`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace FF

/-! ## Dyadic subintervals -/

/-- The `k`-th dyadic subinterval (half-open) of generation `n` of `[a, b]`. -/
def dyadic (a b : ℝ) (n k : ℕ) : Set ℝ :=
  Ico (a + k * (b - a) / 2 ^ n) (a + (k + 1) * (b - a) / 2 ^ n)

/-- The generation-`n` dyadic interval of `[a,b)` containing `x`, as an index `k < 2^n`. -/
def dyadicIdx (a b : ℝ) (n : ℕ) (x : ℝ) : ℕ :=
  ⌊(x - a) / (b - a) * 2 ^ n⌋₊

theorem mem_dyadic_dyadicIdx {a b : ℝ} (hab : a < b) (n : ℕ) {x : ℝ} (hx : x ∈ Ico a b) :
    x ∈ dyadic a b n (dyadicIdx a b n x) := by
  sorry

theorem dyadic_parent {a b : ℝ} (n k : ℕ) : dyadic a b (n + 1) k ⊆ dyadic a b n (k / 2) := by
  sorry

theorem volume_dyadic {a b : ℝ} (hab : a < b) (n k : ℕ) :
    volume (dyadic a b n k) = ENNReal.ofReal ((b - a) / 2 ^ n) := by
  sorry

/-! ## One Calderón–Zygmund step -/

/-- **CZ step.**  If every mean oscillation of `h` is `≤ M`, then `[a,b]` contains countably many
subintervals `(a'ᵢ, b'ᵢ]` which are pairwise disjoint, of total length `≤ (b-a)/2`, with means
within `4M` of `h_{[a,b]}`, and off whose union `|h - h_{[a,b]}| ≤ 2M` a.e. -/
theorem cz_step {h : ℝ → ℝ} (hh : LocallyIntegrable h) {M : ℝ} (hM : 0 < M)
    (hosc : ∀ a b : ℝ, a < b → meanOsc h a b ≤ M) {a b : ℝ} (hab : a < b) :
    ∃ (ι : Type) (_ : Countable ι) (a' b' : ι → ℝ), (∀ i, a ≤ a' i ∧ a' i < b' i ∧ b' i ≤ b) ∧
      (Pairwise fun i j ↦ Disjoint (Ioc (a' i) (b' i)) (Ioc (a' j) (b' j))) ∧
      (∑' i, ENNReal.ofReal (b' i - a' i)) ≤ ENNReal.ofReal ((b - a) / 2) ∧
      (∀ i, |intervalMean h (a' i) (b' i) - intervalMean h a b| ≤ 4 * M) ∧
      ∀ᵐ t, t ∈ Ioc a b → t ∉ (⋃ i, Ioc (a' i) (b' i)) → |h t - intervalMean h a b| ≤ 2 * M := by
  sorry

/-! ## Iteration and conclusion -/

/-- `|{t ∈ (a,b] : |h - h_{[a,b]}| > 4Mk}| ≤ 2^{-k} (b - a)`. -/
theorem jn_iter {h : ℝ → ℝ} (hh : LocallyIntegrable h) {M : ℝ} (hM : 0 < M)
    (hosc : ∀ a b : ℝ, a < b → meanOsc h a b ≤ M) (k : ℕ) :
    ∀ a b : ℝ, a < b →
      volume {t ∈ Ioc a b | 4 * M * k < |h t - intervalMean h a b|} ≤
        ENNReal.ofReal ((1 / 2) ^ k * (b - a)) := by
  sorry

/-- **John–Nirenberg**, with `C = 2`, `c = log 2 / 4`. -/
theorem johnNirenberg_holds : JohnNirenberg := by
  sorry

end FF
