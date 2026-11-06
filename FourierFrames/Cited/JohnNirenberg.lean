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

theorem dyadic_eq (a b : ℝ) (n k : ℕ) :
    dyadic a b n k = Ico (a + k * ((b - a) / 2 ^ n)) (a + (k + 1) * ((b - a) / 2 ^ n)) := by
  simp only [dyadic, mul_div_assoc]

theorem mem_dyadic_dyadicIdx {a b : ℝ} (hab : a < b) (n : ℕ) {x : ℝ} (hx : x ∈ Ico a b) :
    x ∈ dyadic a b n (dyadicIdx a b n x) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  set y : ℝ := (x - a) / (b - a) * 2 ^ n with hy
  have hy0 : 0 ≤ y := by
    have : 0 ≤ x - a := sub_nonneg.2 hx.1
    positivity
  have hxy : x = a + y * ((b - a) / 2 ^ n) := by
    rw [hy]; field_simp; ring
  have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have h3 : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
  have hid : dyadicIdx a b n x = ⌊y⌋₊ := rfl
  rw [hid, dyadic_eq]
  have hw : 0 < (b - a) / 2 ^ n := by positivity
  refine ⟨?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right h1 hw.le
    linarith
  · have := mul_lt_mul_of_pos_right h3 hw
    linarith

theorem dyadicIdx_eq_of_mem {a b : ℝ} (hab : a < b) {n k : ℕ} {x : ℝ} (hx : x ∈ dyadic a b n k) :
    dyadicIdx a b n x = k := by
  have hba : 0 < b - a := sub_pos.2 hab
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadic_eq] at hx
  have hw : 0 < (b - a) / 2 ^ n := by positivity
  have hxy : (x - a) / (b - a) * 2 ^ n = (x - a) / ((b - a) / 2 ^ n) := by
    field_simp
  have h1 : (k : ℝ) ≤ (x - a) / ((b - a) / 2 ^ n) := by
    rw [le_div_iff₀ hw]; linarith [hx.1]
  have h3 : (x - a) / ((b - a) / 2 ^ n) < k + 1 := by
    rw [div_lt_iff₀ hw]; linarith [hx.2]
  unfold dyadicIdx
  rw [hxy, Nat.floor_eq_iff (div_nonneg (by linarith [hx.1, (by positivity : (0:ℝ) ≤ k * ((b-a)/2^n))]) hw.le)]
  exact ⟨h1, h3⟩

theorem dyadic_parent {a b : ℝ} (n k : ℕ) : dyadic a b (n + 1) k ⊆ dyadic a b n (k / 2) := by
  intro x hx
  rw [dyadic_eq] at hx ⊢
  set w : ℝ := (b - a) / 2 ^ n with hw
  have hw1 : (b - a) / 2 ^ (n + 1) = w / 2 := by rw [hw, pow_succ]; field_simp
  rw [hw1] at hx
  have hwpos : 0 < w := by
    have := lt_of_le_of_lt hx.1 hx.2
    nlinarith
  have h1 : ((k / 2 : ℕ) : ℝ) * 2 ≤ k := by exact_mod_cast (by omega : k / 2 * 2 ≤ k)
  have h2 : (k : ℝ) + 1 ≤ ((k / 2 : ℕ) : ℝ) * 2 + 2 := by
    exact_mod_cast (by omega : k + 1 ≤ k / 2 * 2 + 2)
  refine ⟨?_, ?_⟩
  · have := hx.1
    nlinarith
  · have := hx.2
    nlinarith

theorem dyadic_anc {a b : ℝ} (n m k : ℕ) : dyadic a b (n + m) k ⊆ dyadic a b n (k / 2 ^ m) := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    refine (dyadic_parent (n + m) k).trans ((ih (k / 2)).trans ?_)
    rw [Nat.div_div_eq_div_mul, ← pow_succ']

theorem volume_dyadic {a b : ℝ} (_hab : a < b) (n k : ℕ) :
    volume (dyadic a b n k) = ENNReal.ofReal ((b - a) / 2 ^ n) := by
  rw [dyadic_eq, Real.volume_Ico]
  congr 1
  ring

theorem measurableSet_dyadic (a b : ℝ) (n k : ℕ) : MeasurableSet (dyadic a b n k) :=
  measurableSet_Ico

theorem dyadic_subset {a b : ℝ} (hab : a < b) (n : ℕ) {k : ℕ} (hk : k < 2 ^ n) :
    dyadic a b n k ⊆ Ico a b := by
  intro x hx
  rw [dyadic_eq] at hx
  have hba : 0 < b - a := sub_pos.2 hab
  have hw : 0 < (b - a) / 2 ^ n := by positivity
  have hk' : (k : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hk
  refine ⟨?_, ?_⟩
  · have : 0 ≤ (k : ℝ) * ((b - a) / 2 ^ n) := by positivity
    linarith [hx.1]
  · have h1 : ((k : ℝ) + 1) * ((b - a) / 2 ^ n) ≤ 2 ^ n * ((b - a) / 2 ^ n) :=
      mul_le_mul_of_nonneg_right hk' hw.le
    have h2 : (2 : ℝ) ^ n * ((b - a) / 2 ^ n) = b - a := by field_simp
    linarith [hx.2]

/-- Nested-or-disjoint: a common point of two dyadic cells forces the coarser one to be the
ancestor of the finer. -/
theorem dyadic_nested {a b : ℝ} (hab : a < b) {n m k k' : ℕ} {x : ℝ}
    (hx : x ∈ dyadic a b n k) (hx' : x ∈ dyadic a b (n + m) k') : k = k' / 2 ^ m := by
  have := dyadic_anc n m k' hx'
  exact (dyadicIdx_eq_of_mem hab hx).symm.trans (dyadicIdx_eq_of_mem hab this)

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
