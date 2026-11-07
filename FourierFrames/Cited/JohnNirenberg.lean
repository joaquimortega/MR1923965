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

theorem volume_dyadic (a b : ℝ) (n k : ℕ) :
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

/-! ## Stopping-time machinery -/

/-- The oscillation function `t ↦ |h t - h_I|`. -/
def osc (h : ℝ → ℝ) (a b : ℝ) (t : ℝ) : ℝ := |h t - intervalMean h a b|

theorem osc_nonneg (h : ℝ → ℝ) (a b t : ℝ) : 0 ≤ osc h a b t := abs_nonneg _

theorem locInt_osc {h : ℝ → ℝ} (hh : LocallyIntegrable h) (a b : ℝ) :
    LocallyIntegrable (osc h a b) := by
  refine locallyIntegrable_iff.2 fun K hK ↦ ?_
  have := ((hh.integrableOn_isCompact hK).sub
    (integrableOn_const hK.measure_lt_top.ne (C := intervalMean h a b))).norm
  have e : osc h a b = fun t ↦ ‖(h - fun _ : ℝ ↦ intervalMean h a b) t‖ := by
    funext t; simp [osc, Real.norm_eq_abs]
  rw [e]; exact this

theorem integrableOn_Icc_of_locInt {h : ℝ → ℝ} (hh : LocallyIntegrable h) (a b : ℝ) :
    IntegrableOn h (Icc a b) := hh.integrableOn_isCompact isCompact_Icc

theorem integral_osc_le {h : ℝ → ℝ} {M : ℝ}
    (hosc : ∀ a b : ℝ, a < b → meanOsc h a b ≤ M) {a b : ℝ} (hab : a < b) :
    ∫ t in Ioc a b, osc h a b t ≤ M * (b - a) := by
  have h1 := hosc a b hab
  unfold meanOsc at h1
  rw [intervalIntegral.integral_of_le hab.le] at h1
  have hba : 0 < b - a := sub_pos.2 hab
  have := (inv_mul_le_iff₀ hba).1 h1
  simpa [osc, mul_comm] using this

theorem abs_intervalMean_sub_le {h : ℝ → ℝ} (hh : LocallyIntegrable h) {a b : ℝ} (hab : a < b)
    (m : ℝ) :
    |intervalMean h a b - m| ≤ (b - a)⁻¹ * ∫ t in Ioc a b, |h t - m| := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hint : IntegrableOn h (Ioc a b) := (integrableOn_Icc_of_locInt hh a b).mono_set Ioc_subset_Icc_self
  have e : intervalMean h a b - m = (b - a)⁻¹ * ∫ t in Ioc a b, (h t - m) := by
    unfold intervalMean
    rw [intervalIntegral.integral_of_le hab.le, integral_sub hint (integrableOn_const (by simp)),
      setIntegral_const]
    simp [Real.volume_real_Ioc, hab.le]
    field_simp
  rw [e, abs_mul, abs_of_pos (inv_pos.2 hba)]
  gcongr
  have := norm_integral_le_integral_norm (μ := volume.restrict (Ioc a b)) (fun t ↦ h t - m)
  simpa [Real.norm_eq_abs] using this


/-- `∫` of `|h - h_I|` over the dyadic cell. -/
def czG (h : ℝ → ℝ) (a b : ℝ) (n k : ℕ) : ℝ := ∫ t in dyadic a b n k, osc h a b t

/-- Left endpoint of a dyadic cell. -/
def cl (a b : ℝ) (n k : ℕ) : ℝ := a + k * (b - a) / 2 ^ n

/-- Right endpoint of a dyadic cell. -/
def cr (a b : ℝ) (n k : ℕ) : ℝ := a + (k + 1) * (b - a) / 2 ^ n

theorem dyadic_def (a b : ℝ) (n k : ℕ) : dyadic a b n k = Ico (cl a b n k) (cr a b n k) := rfl

theorem cr_sub_cl (a b : ℝ) (n k : ℕ) : cr a b n k - cl a b n k = (b - a) / 2 ^ n := by
  unfold cr cl; ring

def czStop (h : ℝ → ℝ) (a b M : ℝ) (n k : ℕ) : Prop :=
  1 ≤ n ∧ 2 * M * ((b - a) / 2 ^ n) < czG h a b n k

def czSel (h : ℝ → ℝ) (a b M : ℝ) (n k : ℕ) : Prop :=
  k < 2 ^ n ∧ czStop h a b M n k ∧ ∀ j, 1 ≤ j → j < n → ¬ czStop h a b M j (k / 2 ^ (n - j))

theorem czSel_disjoint_aux {h : ℝ → ℝ} {a b M : ℝ} (hab : a < b) {n n' k k' : ℕ} (hle : n ≤ n')
    (hs : czSel h a b M n k) (hs' : czSel h a b M n' k') (hne : (n, k) ≠ (n', k')) :
    Disjoint (dyadic a b n k) (dyadic a b n' k') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hk := dyadic_nested hab hx hx'
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp at hk
    exact hne (by simp [hk])
  · apply hs'.2.2 n hs.2.1.1 (by omega)
    have : n + m - n = m := by omega
    rw [this, ← hk]
    exact hs.2.1

theorem czSel_disjoint {h : ℝ → ℝ} {a b M : ℝ} (hab : a < b) {n n' k k' : ℕ}
    (hs : czSel h a b M n k) (hs' : czSel h a b M n' k') (hne : (n, k) ≠ (n', k')) :
    Disjoint (dyadic a b n k) (dyadic a b n' k') := by
  rcases le_total n n' with hle | hle
  · exact czSel_disjoint_aux hab hle hs hs' hne
  · exact (czSel_disjoint_aux hab hle hs' hs (Ne.symm hne)).symm

theorem integrableOn_osc_dyadic {h : ℝ → ℝ} (hh : LocallyIntegrable h) (a b : ℝ) (n k : ℕ) :
    IntegrableOn (osc h a b) (dyadic a b n k) :=
  ((locInt_osc hh a b).integrableOn_isCompact isCompact_Icc).mono_set Ico_subset_Icc_self

theorem czG_mono_parent {h : ℝ → ℝ} (hh : LocallyIntegrable h) (a b : ℝ) (n k : ℕ) :
    czG h a b (n + 1) k ≤ czG h a b n (k / 2) :=
  setIntegral_mono_set (integrableOn_osc_dyadic hh a b n (k / 2))
    (Eventually.of_forall fun t ↦ osc_nonneg h a b t) (Eventually.of_forall (dyadic_parent n k))

theorem czSel_mean {h : ℝ → ℝ} (hh : LocallyIntegrable h) {M : ℝ} (hM : 0 < M)
    (hosc : ∀ a b : ℝ, a < b → meanOsc h a b ≤ M) {a b : ℝ} (hab : a < b) {n k : ℕ}
    (hs : czSel h a b M n k) :
    |intervalMean h (cl a b n k) (cr a b n k) - intervalMean h a b| ≤ 4 * M := by
  obtain ⟨hk, ⟨hn1, hstop⟩, hanc⟩ := hs
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hba : 0 < b - a := sub_pos.2 hab
  have hpar : czG h a b m (k / 2) ≤ 2 * M * ((b - a) / 2 ^ m) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hk0 : k / 2 = 0 := by simp at hk; omega
      rw [hk0]
      unfold czG
      have e : dyadic a b 0 0 = Ico a b := by simp [dyadic]
      rw [e, integral_Ico_eq_integral_Ioc]
      have := integral_osc_le hosc hab
      simp only [pow_zero, div_one]
      nlinarith
    · have := hanc m hm (by omega)
      have e : m + 1 - m = 1 := by omega
      rw [e, pow_one] at this
      unfold czStop at this
      rw [not_and, not_lt] at this
      exact this hm
  have hcell := czG_mono_parent hh a b m k
  have hJ : cl a b (m + 1) k < cr a b (m + 1) k := by
    have := cr_sub_cl a b (m + 1) k
    have : 0 < (b - a) / 2 ^ (m + 1) := by positivity
    linarith
  have hA := abs_intervalMean_sub_le hh hJ (intervalMean h a b)
  have hG : ∫ t in Ioc (cl a b (m + 1) k) (cr a b (m + 1) k), |h t - intervalMean h a b| =
      czG h a b (m + 1) k := by
    unfold czG
    rw [dyadic_def, integral_Ico_eq_integral_Ioc]
    rfl
  rw [hG, cr_sub_cl] at hA
  refine hA.trans ?_
  have hw : 0 < (b - a) / 2 ^ (m + 1) := by positivity
  have hw2 : (b - a) / 2 ^ m = 2 * ((b - a) / 2 ^ (m + 1)) := by
    rw [pow_succ]; field_simp
  calc ((b - a) / 2 ^ (m + 1))⁻¹ * czG h a b (m + 1) k
      ≤ ((b - a) / 2 ^ (m + 1))⁻¹ * (2 * M * ((b - a) / 2 ^ m)) := by
        gcongr; exact hcell.trans hpar
    _ = 4 * M := by rw [hw2]; field_simp; ring


/-- The index type of selected cells. -/
abbrev CzIdx (h : ℝ → ℝ) (a b M : ℝ) := {p : ℕ × ℕ // czSel h a b M p.1 p.2}

theorem czSel_length {h : ℝ → ℝ} (hh : LocallyIntegrable h) {M : ℝ} (hM : 0 < M)
    (hosc : ∀ a b : ℝ, a < b → meanOsc h a b ≤ M) {a b : ℝ} (hab : a < b) :
    ∑' p : CzIdx h a b M, ENNReal.ofReal (cr a b p.1.1 p.1.2 - cl a b p.1.1 p.1.2) ≤
      ENNReal.ofReal ((b - a) / 2) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hdisj : Pairwise (Function.onFun Disjoint fun p : CzIdx h a b M ↦ dyadic a b p.1.1 p.1.2) :=
    fun p q hpq ↦ czSel_disjoint hab p.2 q.2 (fun e ↦ hpq (Subtype.ext e))
  have h1 : ∀ p : CzIdx h a b M, ENNReal.ofReal (2 * M * (cr a b p.1.1 p.1.2 - cl a b p.1.1 p.1.2)) ≤
      ∫⁻ x in dyadic a b p.1.1 p.1.2, ENNReal.ofReal (osc h a b x) := by
    intro p
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_osc_dyadic hh a b _ _)
      (Eventually.of_forall fun t ↦ osc_nonneg h a b t), cr_sub_cl]
    exact ENNReal.ofReal_le_ofReal p.2.2.1.2.le
  have h2 : ∑' p : CzIdx h a b M, ENNReal.ofReal (2 * M * (cr a b p.1.1 p.1.2 - cl a b p.1.1 p.1.2)) ≤
      ENNReal.ofReal (M * (b - a)) := by
    calc _ ≤ ∑' p : CzIdx h a b M, ∫⁻ x in dyadic a b p.1.1 p.1.2, ENNReal.ofReal (osc h a b x) :=
          ENNReal.tsum_le_tsum h1
      _ = ∫⁻ x in ⋃ p : CzIdx h a b M, dyadic a b p.1.1 p.1.2, ENNReal.ofReal (osc h a b x) :=
          (lintegral_iUnion (fun p ↦ measurableSet_dyadic _ _ _ _) hdisj _).symm
      _ ≤ ∫⁻ x in Ico a b, ENNReal.ofReal (osc h a b x) := by
          refine lintegral_mono_set (iUnion_subset fun p ↦ dyadic_subset hab _ p.2.1)
      _ = ENNReal.ofReal (∫ x in Ico a b, osc h a b x) := by
          rw [ofReal_integral_eq_lintegral_ofReal
            ((locInt_osc hh a b).integrableOn_isCompact isCompact_Icc |>.mono_set Ico_subset_Icc_self)
            (Eventually.of_forall fun t ↦ osc_nonneg h a b t)]
      _ ≤ _ := by
          rw [integral_Ico_eq_integral_Ioc]
          exact ENNReal.ofReal_le_ofReal (integral_osc_le hosc hab)
  have h3 : ENNReal.ofReal (2 * M) * ∑' p : CzIdx h a b M,
      ENNReal.ofReal (cr a b p.1.1 p.1.2 - cl a b p.1.1 p.1.2) ≤
      ENNReal.ofReal (2 * M) * ENNReal.ofReal ((b - a) / 2) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.tsum_mul_left]
    have e : 2 * M * ((b - a) / 2) = M * (b - a) := by ring
    rw [e]
    refine le_trans (le_of_eq ?_) h2
    refine tsum_congr fun p ↦ ?_
    exact (ENNReal.ofReal_mul (by positivity)).symm
  exact (ENNReal.mul_le_mul_iff_right (by simp [hM]) ENNReal.ofReal_ne_top).1 h3


theorem dyadicIdx_anc {a b : ℝ} (hab : a < b) {t : ℝ} (ht : t ∈ Ico a b) {j n : ℕ} (hj : j ≤ n) :
    dyadicIdx a b n t / 2 ^ (n - j) = dyadicIdx a b j t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left]
  exact (dyadic_nested hab (mem_dyadic_dyadicIdx hab j ht) (mem_dyadic_dyadicIdx hab (j + m) ht)).symm

theorem dyadicIdx_lt {a b : ℝ} (hab : a < b) {t : ℝ} (ht : t ∈ Ico a b) (n : ℕ) :
    dyadicIdx a b n t < 2 ^ n := by
  have hba : 0 < b - a := sub_pos.2 hab
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  unfold dyadicIdx
  have h0 : 0 ≤ (t - a) / (b - a) * 2 ^ n := by
    have : 0 ≤ t - a := sub_nonneg.2 ht.1
    positivity
  have : (t - a) / (b - a) * 2 ^ n < 2 ^ n := by
    have h1 : (t - a) / (b - a) < 1 := by rw [div_lt_one hba]; linarith [ht.2]
    nlinarith
  have := (Nat.floor_lt h0).2 (by exact_mod_cast this : (t - a) / (b - a) * 2 ^ n < ((2 ^ n : ℕ) : ℝ))
  exact this

theorem czStop_exists_sel {h : ℝ → ℝ} {a b M : ℝ} (hab : a < b) {t : ℝ} (ht : t ∈ Ico a b)
    (hex : ∃ n, czStop h a b M n (dyadicIdx a b n t)) :
    ∃ n, czSel h a b M n (dyadicIdx a b n t) := by
  classical
  refine ⟨Nat.find hex, dyadicIdx_lt hab ht _, Nat.find_spec hex, fun j hj1 hjn ↦ ?_⟩
  rw [dyadicIdx_anc hab ht hjn.le]
  exact Nat.find_min hex hjn


theorem czSel_good {h : ℝ → ℝ} (hh : LocallyIntegrable h) {M : ℝ} (hM : 0 < M)
    {a b : ℝ} (hab : a < b) :
    ∀ᵐ t, t ∈ Ioc a b → t ∉ (⋃ p : CzIdx h a b M, Ioc (cl a b p.1.1 p.1.2) (cr a b p.1.1 p.1.2)) →
      |h t - intervalMean h a b| ≤ 2 * M := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hLeb := IsUnifLocDoublingMeasure.ae_tendsto_average (μ := (volume : Measure ℝ))
    (locInt_osc hh a b) 1
  have hcount : (insert b (range fun p : CzIdx h a b M ↦ cl a b p.1.1 p.1.2)).Countable :=
    (Set.countable_range _).insert b
  filter_upwards [hLeb, hcount.ae_notMem volume] with t ht htS htIoc htnot
  have htb : t ≠ b := fun e ↦ htS (Or.inl e)
  have htIco : t ∈ Ico a b := ⟨htIoc.1.le, lt_of_le_of_ne htIoc.2 htb⟩
  have hne : ∀ n, 1 ≤ n → ¬ czStop h a b M n (dyadicIdx a b n t) := by
    intro n hn hst
    obtain ⟨n0, hn0⟩ := czStop_exists_sel hab htIco ⟨n, hst⟩
    have hmem := mem_dyadic_dyadicIdx hab n0 htIco
    refine htnot (mem_iUnion.2 ⟨⟨(n0, dyadicIdx a b n0 t), hn0⟩, ?_⟩)
    have hcl : cl a b n0 (dyadicIdx a b n0 t) ≠ t := fun e ↦
      htS (Or.inr ⟨⟨(n0, dyadicIdx a b n0 t), hn0⟩, e⟩)
    exact ⟨lt_of_le_of_ne hmem.1 hcl, hmem.2.le⟩
  have hbound : ∀ n : ℕ, czG h a b (n + 1) (dyadicIdx a b (n + 1) t) ≤
      2 * M * ((b - a) / 2 ^ (n + 1)) := by
    intro n
    have := hne (n + 1) (by omega)
    unfold czStop at this
    rw [not_and, not_lt] at this
    exact this (by omega)
  set k : ℕ → ℕ := fun n ↦ dyadicIdx a b (n + 1) t with hk
  set δ : ℕ → ℝ := fun n ↦ (b - a) / 2 ^ (n + 2) with hδ
  set w : ℕ → ℝ := fun n ↦ cl a b (n + 1) (k n) + δ n with hw
  have hδpos : ∀ n, 0 < δ n := fun n ↦ by positivity
  have hδlim : Tendsto δ atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hδpos⟩
    have : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ (n + 2)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp (tendsto_add_atTop_nat 2)
    exact tendsto_const_nhds.div_atTop this
  have hball : ∀ n, Metric.closedBall (w n) (δ n) = Icc (cl a b (n + 1) (k n)) (cr a b (n + 1) (k n)) := by
    intro n
    rw [Real.closedBall_eq_Icc]
    have : cr a b (n + 1) (k n) - cl a b (n + 1) (k n) = 2 * δ n := by
      rw [cr_sub_cl, hδ]; simp only [pow_succ]; ring
    congr 1 <;> simp only [hw] <;> linarith
  have hmem : ∀ n, t ∈ Metric.closedBall (w n) (1 * δ n) := by
    intro n
    rw [one_mul, hball]
    have := mem_dyadic_dyadicIdx hab (n + 1) htIco
    exact ⟨this.1, this.2.le⟩
  have hlim := ht (ι := ℕ) (l := atTop) w δ hδlim (Eventually.of_forall hmem)
  refine le_of_tendsto' hlim fun n ↦ ?_
  rw [hball, setAverage_eq, integral_Icc_eq_integral_Ico, Real.volume_real_Icc_of_le (by
    have := cr_sub_cl a b (n + 1) (k n); have : 0 < (b - a) / 2 ^ (n + 1) := by positivity
    linarith), cr_sub_cl, smul_eq_mul]
  have hG : ∫ x in Ico (cl a b (n + 1) (k n)) (cr a b (n + 1) (k n)), osc h a b x =
      czG h a b (n + 1) (k n) := rfl
  rw [hG]
  have hw2 : 0 < (b - a) / 2 ^ (n + 1) := by positivity
  calc ((b - a) / 2 ^ (n + 1))⁻¹ * czG h a b (n + 1) (k n)
      ≤ ((b - a) / 2 ^ (n + 1))⁻¹ * (2 * M * ((b - a) / 2 ^ (n + 1))) := by
        gcongr; exact hbound n
    _ = 2 * M := by field_simp


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
  have hba : 0 < b - a := sub_pos.2 hab
  have hbd : ∀ p : CzIdx h a b M, a ≤ cl a b p.1.1 p.1.2 ∧
      cl a b p.1.1 p.1.2 < cr a b p.1.1 p.1.2 ∧ cr a b p.1.1 p.1.2 ≤ b := by
    intro p
    have hk := p.2.1
    have hw : 0 < (b - a) / 2 ^ p.1.1 := by positivity
    have hk' : (p.1.2 : ℝ) + 1 ≤ 2 ^ p.1.1 := by exact_mod_cast hk
    have h2 : (2 : ℝ) ^ p.1.1 * ((b - a) / 2 ^ p.1.1) = b - a := by field_simp
    have h3 := mul_le_mul_of_nonneg_right hk' hw.le
    have h4 := cr_sub_cl a b p.1.1 p.1.2
    refine ⟨?_, by linarith, ?_⟩
    · unfold cl
      have : 0 ≤ (p.1.2 : ℝ) * ((b - a) / 2 ^ p.1.1) := by positivity
      rw [mul_div_assoc]; linarith
    · unfold cr; rw [mul_div_assoc]; linarith
  refine ⟨CzIdx h a b M, inferInstance, fun p ↦ cl a b p.1.1 p.1.2, fun p ↦ cr a b p.1.1 p.1.2,
    hbd, ?_, czSel_length hh hM hosc hab, fun p ↦ czSel_mean hh hM hosc hab p.2, czSel_good hh hM hab⟩
  intro p q hpq
  have hd := czSel_disjoint hab p.2 q.2 (fun e ↦ hpq (Subtype.ext e))
  rw [dyadic_def, dyadic_def, Set.disjoint_iff_inter_eq_empty] at hd
  rw [Set.Ioc_disjoint_Ioc]
  have := (Set.Ico_disjoint_Ico (a₁ := cl a b p.1.1 p.1.2) (a₂ := cr a b p.1.1 p.1.2)
    (b₁ := cl a b q.1.1 q.1.2) (b₂ := cr a b q.1.1 q.1.2)).1 (Set.disjoint_iff_inter_eq_empty.2 hd)
  exact this

/-! ## Iteration and conclusion -/

/-- `|{t ∈ (a,b] : |h - h_{[a,b]}| > 4Mk}| ≤ 2^{-k} (b - a)`. -/
theorem jn_iter {h : ℝ → ℝ} (hh : LocallyIntegrable h) {M : ℝ} (hM : 0 < M)
    (hosc : ∀ a b : ℝ, a < b → meanOsc h a b ≤ M) (k : ℕ) :
    ∀ a b : ℝ, a < b →
      volume {t ∈ Ioc a b | 4 * M * k < |h t - intervalMean h a b|} ≤
        ENNReal.ofReal ((1 / 2) ^ k * (b - a)) := by
  induction k with
  | zero =>
    intro a b hab
    calc _ ≤ volume (Ioc a b) := measure_mono (fun t ht ↦ ht.1)
      _ = ENNReal.ofReal ((1 / 2) ^ 0 * (b - a)) := by simp
  | succ k ih =>
    intro a b hab
    obtain ⟨ι, hι, a', b', hbd, -, hsum, hmean, hgood⟩ := cz_step hh hM hosc hab
    set m := intervalMean h a b with hm
    set Z : Set ℝ := {t | ¬ (t ∈ Ioc a b → t ∉ (⋃ i, Ioc (a' i) (b' i)) → |h t - m| ≤ 2 * M)}
      with hZdef
    have hZ : volume Z = 0 := ae_iff.1 hgood
    set F : ι → Set ℝ := fun i ↦ {t ∈ Ioc (a' i) (b' i) |
      4 * M * k < |h t - intervalMean h (a' i) (b' i)|} with hF
    have hsub : {t ∈ Ioc a b | 4 * M * ((k + 1 : ℕ) : ℝ) < |h t - m|} ⊆ Z ∪ ⋃ i, F i := by
      intro t ⟨htI, htE⟩
      by_cases hZt : t ∈ Z
      · exact Or.inl hZt
      · right
        have hZ' : t ∈ Ioc a b → t ∉ (⋃ i, Ioc (a' i) (b' i)) → |h t - m| ≤ 2 * M := by
          by_contra hc; exact hZt hc
        by_cases hU : t ∈ ⋃ i, Ioc (a' i) (b' i)
        · obtain ⟨i, hi⟩ := mem_iUnion.1 hU
          refine mem_iUnion.2 ⟨i, hi, ?_⟩
          have h1 := abs_sub_abs_le_abs_sub (h t - m) (intervalMean h (a' i) (b' i) - m)
          have h2 : h t - m - (intervalMean h (a' i) (b' i) - m) =
              h t - intervalMean h (a' i) (b' i) := by ring
          rw [h2] at h1
          have h3 := hmean i
          push_cast at htE
          nlinarith
        · have := hZ' htI hU
          push_cast at htE
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith
    calc volume {t ∈ Ioc a b | 4 * M * ((k + 1 : ℕ) : ℝ) < |h t - m|}
        ≤ volume (Z ∪ ⋃ i, F i) := measure_mono hsub
      _ ≤ volume Z + ∑' i, volume (F i) :=
          (measure_union_le _ _).trans (by gcongr; exact measure_iUnion_le _)
      _ = ∑' i, volume (F i) := by rw [hZ, zero_add]
      _ ≤ ∑' i, ENNReal.ofReal ((1 / 2) ^ k * (b' i - a' i)) :=
          ENNReal.tsum_le_tsum fun i ↦ ih _ _ (hbd i).2.1
      _ = ENNReal.ofReal ((1 / 2) ^ k) * ∑' i, ENNReal.ofReal (b' i - a' i) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun i ↦ ?_
          rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((1 / 2) ^ k) * ENNReal.ofReal ((b - a) / 2) := by gcongr
      _ = ENNReal.ofReal ((1 / 2) ^ (k + 1) * (b - a)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; rw [pow_succ]; ring

/-- **John–Nirenberg**, with `C = 2`, `c = log 2 / 4`. -/
theorem johnNirenberg_holds : JohnNirenberg := by
  refine ⟨2, Real.log 2 / 4, by norm_num, by positivity, ?_⟩
  intro h hh M hM hosc a b hab s hs
  set x : ℝ := s / (4 * M) with hx
  have hx0 : 0 < x := by positivity
  set k : ℕ := ⌈x⌉₊ - 1 with hkdef
  have hceil : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hx0).ne'
  have hk1 : k + 1 = ⌈x⌉₊ := by omega
  have hxk : x ≤ (k : ℝ) + 1 := by
    have := Nat.le_ceil x
    rw [← hk1] at this
    exact_mod_cast this
  have hkx : (k : ℝ) < x := by
    have := Nat.ceil_lt_add_one hx0.le
    have h2 : (⌈x⌉₊ : ℝ) = k + 1 := by exact_mod_cast hk1.symm
    linarith
  have hks : 4 * M * k < s := by
    have : 4 * M * (k : ℝ) < 4 * M * x := by gcongr
    have e : 4 * M * x = s := by rw [hx]; field_simp
    linarith
  have hsub : {t ∈ Icc a b | s ≤ |h t - intervalMean h a b|} ⊆
      {a} ∪ {t ∈ Ioc a b | 4 * M * k < |h t - intervalMean h a b|} := by
    intro t ⟨htI, hts⟩
    by_cases hta : t = a
    · exact Or.inl hta
    · exact Or.inr ⟨⟨lt_of_le_of_ne htI.1 (Ne.symm hta), htI.2⟩, lt_of_lt_of_le hks hts⟩
  have h1 := jn_iter hh hM hosc k a b hab
  have hpow : ((1 : ℝ) / 2) ^ k ≤ 2 * Real.exp (-(Real.log 2 / 4 * s / M)) := by
    have e1 : ((1 : ℝ) / 2) ^ k = 2 * ((1 : ℝ) / 2) ^ (k + 1) := by rw [pow_succ]; ring
    have e2 : ((1 : ℝ) / 2) ^ (k + 1) ≤ ((1 : ℝ) / 2) ^ x := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by push_cast; exact hxk)
    have e3 : ((1 : ℝ) / 2) ^ x = Real.exp (-(Real.log 2 / 4 * s / M)) := by
      rw [Real.rpow_def_of_pos (by norm_num), one_div, Real.log_inv]
      congr 1
      rw [hx]; field_simp
    rw [e1]
    have := mul_le_mul_of_nonneg_left (e2.trans e3.le) (by norm_num : (0 : ℝ) ≤ 2)
    exact this
  calc volume {t ∈ Icc a b | s ≤ |h t - intervalMean h a b|}
      ≤ volume ({a} ∪ {t ∈ Ioc a b | 4 * M * k < |h t - intervalMean h a b|}) := measure_mono hsub
    _ ≤ volume ({a} : Set ℝ) + volume {t ∈ Ioc a b | 4 * M * k < |h t - intervalMean h a b|} :=
        measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal ((1 / 2) ^ k * (b - a)) := by
        rw [Real.volume_singleton]; gcongr
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(Real.log 2 / 4 * s / M)) * (b - a)) := by
        rw [zero_add]
        apply ENNReal.ofReal_le_ofReal
        have : 0 < b - a := sub_pos.2 hab
        gcongr

end FF
