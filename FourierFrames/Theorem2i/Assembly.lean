import FourierFrames.Theorem2i.Estimates

/-!
# M08 helper: assembly of the cell-term bound

Index classes of blueprint §6.3 and the uniform finset form of `∑ |j_n| ≤ B`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

/-! ### Finset forms of the counting lemmas (black boxes; D2 / coordinator to reconcile)

TODO(theorem2i): proved by the counting fork (`Counting.lean`); stated here with index `m`
(cell `(t_{m-1}, t_m]`), `m ≥ 1`. -/

theorem RegData.K0_finset_card_near_le (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0)
    (F : Finset ℕ)
    (hF : ∀ m ∈ F, 1 ≤ m ∧ ‖z‖ / 2 < t m ∧ t m < 2 * ‖z‖ ∧
        ‖z - rCentre ψ t m‖ < K0 C * cellLen t m) :
    (F.card : ℝ) ≤ 3 * (1 + K0 C ^ 2) * M := by
  have hK0 : 0 < K0 C := by
    have := h.one_le; unfold K0 rho1; linarith
  exact h.finset_card_near_le hz0 hK0 F hF

theorem RegData.K0_finset_sum_far_le (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0)
    (F : Finset ℕ)
    (hF : ∀ m ∈ F, 1 ≤ m ∧ ‖z‖ / 2 < t m ∧ t m < 2 * ‖z‖ ∧
        K0 C * cellLen t m ≤ ‖z - rCentre ψ t m‖) :
    ∑ m ∈ F, cellLen t m ^ 2 / ‖z - rCentre ψ t m‖ ^ 2 ≤ 3 * (1 + (K0 C)⁻¹ ^ 2) * M := by
  have hK0 : 0 < K0 C := by
    have := h.one_le; unfold K0 rho1; linarith
  exact h.finset_sum_far_le hz0 hK0 F hF

theorem RegData.K0_finset_sum_far_im_le (h : RegData ψ t C M) {z : ℂ} (F : Finset ℕ)
    (hF : ∀ m ∈ F, 1 ≤ m ∧ K0 C * cellLen t m ≤ ‖z - rCentre ψ t m‖) :
    ∑ m ∈ F, cellLen t m * z.im / ‖z - rCentre ψ t m‖ ^ 2 ≤ 9 / 4 * Real.pi := by
  have hK8 : 8 ≤ K0 C := by
    have := h.one_le; unfold K0 rho1; linarith
  exact h.finset_sum_far_im_le hK8 F hF

namespace D3

theorem tele_up (a : ℕ → ℝ) (ha : Monotone a) (c : ℝ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, a (n + 1) ≤ c) : ∑ n ∈ S, (a (n + 1) - a n) ≤ c - min (a 0) c := by
  set a' : ℕ → ℝ := fun n => min (a n) c with ha'
  have hmono : Monotone a' := fun m n hmn => min_le_min (ha hmn) le_rfl
  have h1 : ∑ n ∈ S, (a (n + 1) - a n) = ∑ n ∈ S, (a' (n + 1) - a' n) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have := hS n hn
    have h2 : a n ≤ c := (ha (Nat.le_succ n)).trans this
    simp [ha', min_eq_left this, min_eq_left h2]
  rw [h1]
  have hsub : S ⊆ Finset.range (S.sup id + 1) := fun n hn =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  calc ∑ n ∈ S, (a' (n + 1) - a' n)
      ≤ ∑ n ∈ Finset.range (S.sup id + 1), (a' (n + 1) - a' n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => sub_nonneg.2 (hmono (Nat.le_succ n))
    _ = a' (S.sup id + 1) - a' 0 := Finset.sum_range_sub a' _
    _ ≤ c - min (a 0) c := by
        have : a' (S.sup id + 1) ≤ c := min_le_right _ _
        have h0 : a' 0 = min (a 0) c := rfl
        linarith

theorem tele_down (g : ℕ → ℝ) (hg : Antitone g) (hg0 : ∀ n, 0 ≤ g n) (S : Finset ℕ) :
    ∑ n ∈ S, (g n - g (n + 1)) ≤ g 0 := by
  have hsub : S ⊆ Finset.range (S.sup id + 1) := fun n hn =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  calc ∑ n ∈ S, (g n - g (n + 1))
      ≤ ∑ n ∈ Finset.range (S.sup id + 1), (g n - g (n + 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => sub_nonneg.2 (hg (Nat.le_succ n))
    _ = g 0 - g (S.sup id + 1) := Finset.sum_range_sub' g _
    _ ≤ g 0 := by linarith [hg0 (S.sup id + 1)]

theorem cellLen_succ (t : ℕ → ℝ) (n : ℕ) : cellLen t (n + 1) = t (n + 1) - t n := by
  simp [cellLen]

theorem below_sum (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0) (S : Finset ℕ)
    (hS : ∀ n ∈ S, t (n + 1) ≤ ‖z‖ / 2) : ∑ n ∈ S, cellLen t (n + 1) ≤ ‖z‖ / 2 := by
  have hz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have := tele_up t h.mono.monotone (‖z‖ / 2) S hS
  simp only [cellLen_succ]
  rw [h.t0, min_eq_left (by positivity)] at this
  linarith

theorem above_sum (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ 2 * ‖z‖ ≤ t n) :
    ∑ n ∈ S, cellLen t (n + 1) / t n ^ 2 ≤ (1 + C) * (1 / (2 * ‖z‖)) := by
  have hz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  set τ : ℝ := 2 * ‖z‖ with hτ
  have hτ0 : 0 < τ := by positivity
  set g : ℕ → ℝ := fun n => (max (t n) τ)⁻¹ with hg
  have hgpos : ∀ n, 0 < max (t n) τ := fun n => lt_max_of_lt_right hτ0
  have hanti : Antitone g := fun m n hmn =>
    inv_anti₀ (hgpos m) (max_le_max (h.mono.monotone hmn) le_rfl)
  have hg0 : ∀ n, 0 ≤ g n := fun n => (inv_pos.2 (hgpos n)).le
  have key := tele_down g hanti hg0 S
  have hterm : ∀ n ∈ S, cellLen t (n + 1) / t n ^ 2 ≤ (1 + C) * (g n - g (n + 1)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := hS n hn
    have htn : 0 < t n := lt_of_lt_of_le hτ0 hn2
    have htn1 : t n ≤ t (n + 1) := h.mono.monotone (Nat.le_succ n)
    have hmax : max (t n) τ = t n := max_eq_left hn2
    have hmax1 : max (t (n + 1)) τ = t (n + 1) := max_eq_left (hn2.trans htn1)
    have htl : t (n + 1) ≤ (1 + C) * t n := by
      have := h.t_le (n := n + 1) (by omega)
      simpa using this
    have hd : 0 ≤ cellLen t (n + 1) := by rw [cellLen_succ]; linarith
    simp only [hg, hmax, hmax1, cellLen_succ]
    have ht1 : 0 < t (n + 1) := lt_of_lt_of_le htn htn1
    rw [show (t n)⁻¹ - (t (n + 1))⁻¹ = (t (n + 1) - t n) / (t n * t (n + 1)) by
      field_simp]
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    have hd' : 0 ≤ t (n + 1) - t n := by linarith
    have : (t (n + 1) - t n) * (t n * t (n + 1)) ≤
        (1 + C) * (t (n + 1) - t n) * t n ^ 2 := by
      have : t n * t (n + 1) ≤ (1 + C) * t n * t n := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hd']
    exact this
  calc ∑ n ∈ S, cellLen t (n + 1) / t n ^ 2
      ≤ ∑ n ∈ S, (1 + C) * (g n - g (n + 1)) := Finset.sum_le_sum hterm
    _ = (1 + C) * ∑ n ∈ S, (g n - g (n + 1)) := by rw [Finset.mul_sum]
    _ ≤ (1 + C) * g 0 := by
        have : 0 ≤ 1 + C := by linarith [h.one_le]
        exact mul_le_mul_of_nonneg_left key this
    _ = (1 + C) * (1 / (2 * ‖z‖)) := by
        simp [hg, h.t0, hτ]

/-! ### Constants and index terms -/

def a1 (C : ℝ) : ℝ := 4 + 2 * (1 + C) * Real.log (1 + C)
def a2 (C : ℝ) : ℝ := 2 * Real.log (1 + C) + 2
def c1 (C : ℝ) : ℝ := 2 * rho1 C * (1 + C) ^ 3 + (3 + rho1 C)
def cnear (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C K : ℝ) : ℝ :=
  max 0 (2 * K + Real.log (K0 C + 1) + Real.log (Real.pi / (2 * cAngle ψ t C)))

/-- Not "below" and not "above". -/
def IsMid (t : ℕ → ℝ) (z : ℂ) (n : ℕ) : Prop :=
  ¬ t (n + 1) ≤ ‖z‖ / 2 ∧ ¬ (1 ≤ n ∧ 2 * ‖z‖ ≤ t n)

/-- `n`-th cell (index `n+1`) is near `z`. -/
def IsNear (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) (z : ℂ) (n : ℕ) : Prop :=
  ‖z - rCentre ψ t (n + 1)‖ < K0 C * cellLen t (n + 1)

open Classical in
def Tbelow (t : ℕ → ℝ) (C : ℝ) (z : ℂ) (n : ℕ) : ℝ :=
  if t (n + 1) ≤ ‖z‖ / 2 then a1 C * (cellLen t (n + 1) / ‖z‖) else 0

open Classical in
def Tabove (t : ℕ → ℝ) (C : ℝ) (z : ℂ) (n : ℕ) : ℝ :=
  if 1 ≤ n ∧ 2 * ‖z‖ ≤ t n then a2 C * (cellLen t (n + 1) / t n ^ 2 * ‖z‖) else 0

open Classical in
def Tnearw (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C K : ℝ) (z : ℂ) (n : ℕ) : ℝ :=
  if IsMid t z n ∧ t (n + 1) < 2 * ‖z‖ ∧ IsNear ψ t C z n then cnear ψ t C K else 0

open Classical in
def Tfarw (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) (z : ℂ) (n : ℕ) : ℝ :=
  if IsMid t z n ∧ t (n + 1) < 2 * ‖z‖ ∧ ¬ IsNear ψ t C z n then
    c1 C * (cellLen t (n + 1) ^ 2 / ‖z - rCentre ψ t (n + 1)‖ ^ 2) else 0

open Classical in
def Tone (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C K : ℝ) (z : ℂ) (n : ℕ) : ℝ :=
  if IsMid t z n ∧ 2 * ‖z‖ ≤ t (n + 1) then cnear ψ t C K + c1 C / K0 C ^ 2 else 0

open Classical in
def Ty (ψ : ℝ → ℝ) (t : ℕ → ℝ) (C : ℝ) (z : ℂ) (n : ℕ) : ℝ :=
  if IsMid t z n ∧ ¬ IsNear ψ t C z n then
    2 * (cellLen t (n + 1) * z.im / ‖z - rCentre ψ t (n + 1)‖ ^ 2) else 0

theorem one_le_one_add (h : RegData ψ t C M) : 1 ≤ 1 + C := by linarith [h.one_le]

theorem a1_nonneg (h : RegData ψ t C M) : 0 ≤ a1 C := by
  have := Real.log_nonneg (one_le_one_add h)
  have := h.one_le
  unfold a1; nlinarith

theorem a2_nonneg (h : RegData ψ t C M) : 0 ≤ a2 C := by
  have := Real.log_nonneg (one_le_one_add h)
  unfold a2; linarith

theorem rho1_pos (h : RegData ψ t C M) : 0 < rho1 C := by
  have := h.one_le; unfold rho1; linarith

theorem c1_nonneg (h : RegData ψ t C M) : 0 ≤ c1 C := by
  have := rho1_pos h
  have := h.one_le
  unfold c1; positivity

theorem K0_ge (h : RegData ψ t C M) : 16 ≤ K0 C := by
  have := h.one_le; unfold K0 rho1; linarith

theorem cellLen_pos (h : RegData ψ t C M) (n : ℕ) : 0 < cellLen t (n + 1) := by
  rw [cellLen_succ]; linarith [h.mono (Nat.lt_succ_self n)]

theorem t_pos (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) : 0 < t n := by
  have := h.mono (show 0 < n by omega); rwa [h.t0] at this

theorem cnear_nonneg : 0 ≤ cnear ψ t C K := le_max_left _ _

theorem Tbelow_nonneg (h : RegData ψ t C M) {z : ℂ} (n : ℕ) : 0 ≤ Tbelow t C z n := by
  unfold Tbelow; split_ifs
  · have := a1_nonneg h; have := cellLen_pos h n; positivity
  · exact le_rfl

theorem Tabove_nonneg (h : RegData ψ t C M) {z : ℂ} (n : ℕ) : 0 ≤ Tabove t C z n := by
  unfold Tabove; split_ifs
  · have := a2_nonneg h; have := cellLen_pos h n; positivity
  · exact le_rfl

theorem Tnearw_nonneg {z : ℂ} (n : ℕ) : 0 ≤ Tnearw ψ t C K z n := by
  unfold Tnearw; split_ifs
  · exact cnear_nonneg
  · exact le_rfl

theorem Tfarw_nonneg (h : RegData ψ t C M) {z : ℂ} (n : ℕ) : 0 ≤ Tfarw ψ t C z n := by
  unfold Tfarw; split_ifs
  · have := c1_nonneg h; positivity
  · exact le_rfl

theorem Tone_nonneg (h : RegData ψ t C M) {z : ℂ} (n : ℕ) : 0 ≤ Tone ψ t C K z n := by
  unfold Tone; split_ifs
  · have := c1_nonneg h; have := cnear_nonneg (ψ := ψ) (t := t) (C := C) (K := K); positivity
  · exact le_rfl

theorem Ty_nonneg (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) (n : ℕ) :
    0 ≤ Ty ψ t C z n := by
  unfold Ty; split_ifs
  · have := cellLen_pos h n; positivity
  · exact le_rfl

/-! ### Facts about the middle class -/

theorem near_of_first (h : RegData ψ t C M) {z : ℂ} (hmid : IsMid t z 0) :
    IsNear ψ t C z 0 := by
  obtain ⟨hb, -⟩ := hmid
  unfold IsNear
  have hr := h.rCentre_mem (n := 1) le_rfl
  simp only [Nat.zero_add, Nat.sub_self, h.t0] at hr ⊢
  rw [cellLen_succ, h.t0] at *
  have hK := K0_ge h
  have ht1 : 0 < t 1 := t_pos h le_rfl
  have : ‖z - (rCentre ψ t 1 : ℂ)‖ ≤ ‖z‖ + rCentre ψ t 1 := by
    calc _ ≤ ‖z‖ + ‖(rCentre ψ t 1 : ℂ)‖ := norm_sub_le _ _
      _ = _ := by rw [Complex.norm_real, Real.norm_of_nonneg hr.1.le]
  push Not at hb
  nlinarith [hr.2]

theorem mid_bounds (h : RegData ψ t C M) {z : ℂ} {n : ℕ} (hn : 1 ≤ n) (hmid : IsMid t z n) :
    ‖z‖ ≤ rho1 C * rCentre ψ t (n + 1) ∧ rCentre ψ t (n + 1) ≤ rho1 C * ‖z‖ := by
  obtain ⟨hb, ha⟩ := hmid
  push Not at hb ha
  have ha' := ha hn
  have hr := h.rCentre_mem (n := n + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hr
  have htl : t (n + 1) ≤ (1 + C) * t n := by
    have := h.t_le (n := n + 1) (by omega)
    simpa using this
  have h1 := one_le_one_add h
  unfold rho1
  constructor
  · nlinarith [hr.1]
  · nlinarith [hr.2]

theorem far_sq_le (h : RegData ψ t C M) {z : ℂ} {n : ℕ}
    (hfar : K0 C * cellLen t (n + 1) ≤ ‖z - rCentre ψ t (n + 1)‖) :
    cellLen t (n + 1) ^ 2 / ‖z - rCentre ψ t (n + 1)‖ ^ 2 ≤ 1 / K0 C ^ 2 := by
  have hd := cellLen_pos h n
  have hK : 0 < K0 C := by linarith [K0_ge h]
  have hu : 0 < ‖z - rCentre ψ t (n + 1)‖ := lt_of_lt_of_le (by positivity) hfar
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul hfar hfar (by positivity) hu.le]

theorem pointwise (h : RegData ψ t C M) (hK : DensBound ψ t K) {z : ℂ} (hz : 0 ≤ z.im)
    (hz0 : z ≠ 0) (n : ℕ) :
    |cellTerm ψ t C (n + 1) z| ≤ Tbelow t C z n + Tabove t C z n + Tnearw ψ t C K z n +
      Tfarw ψ t C z n + Tone ψ t C K z n + Ty ψ t C z n := by
  have n1 := Tbelow_nonneg h (z := z) n
  have n2 := Tabove_nonneg h (z := z) n
  have n3 := Tnearw_nonneg (ψ := ψ) (t := t) (C := C) (K := K) (z := z) n
  have n4 := Tfarw_nonneg h (z := z) n
  have n5 := Tone_nonneg (K := K) h (z := z) n
  have n6 := Ty_nonneg h hz n
  by_cases hb : t (n + 1) ≤ ‖z‖ / 2
  · have := h.abs_cellTerm_below (n := n + 1) (by omega) hb hz0
    have e : Tbelow t C z n = a1 C * (cellLen t (n + 1) / ‖z‖) := by simp [Tbelow, hb]
    rw [e] at n1 ⊢
    unfold a1
    linarith
  by_cases ha : 1 ≤ n ∧ 2 * ‖z‖ ≤ t n
  · have hj := h.abs_cellTerm_above (n := n + 1) (by omega) (by simpa using ha.2) hz0
    simp only [Nat.add_sub_cancel] at hj
    have e : Tabove t C z n = a2 C * (cellLen t (n + 1) / t n ^ 2 * ‖z‖) := by
      simp [Tabove, ha]
    have hmid_not : ¬ IsMid t z n := fun hm => hm.2 ha
    have e3 : Tnearw ψ t C K z n = 0 := by simp [Tnearw, hmid_not]
    have e4 : Tfarw ψ t C z n = 0 := by simp [Tfarw, hmid_not]
    have e5 : Tone ψ t C K z n = 0 := by simp [Tone, hmid_not]
    have e6 : Ty ψ t C z n = 0 := by simp [Ty, hmid_not]
    have e1 : Tbelow t C z n = 0 := by simp [Tbelow, hb]
    rw [e, e1, e3, e4, e5, e6]
    unfold a2
    have : cellLen t (n + 1) * ‖z‖ / t n ^ 2 = cellLen t (n + 1) / t n ^ 2 * ‖z‖ := by ring
    rw [this] at hj
    linarith
  have hmid : IsMid t z n := ⟨hb, ha⟩
  have e1 : Tbelow t C z n = 0 := by simp [Tbelow, hb]
  have e2 : Tabove t C z n = 0 := by simp [Tabove, ha]
  rw [e1, e2]
  by_cases hnear : IsNear ψ t C z n
  · have hj := h.abs_cellTerm_near hK (n := n + 1) (by omega) hz hnear
    have hjc : |cellTerm ψ t C (n + 1) z| ≤ cnear ψ t C K := le_trans hj (le_max_right _ _)
    have e4 : Tfarw ψ t C z n = 0 := by simp [Tfarw, hnear]
    have e6 : Ty ψ t C z n = 0 := by simp [Ty, hnear]
    rw [e4, e6]
    by_cases hw : t (n + 1) < 2 * ‖z‖
    · have e3 : Tnearw ψ t C K z n = cnear ψ t C K := by simp [Tnearw, hmid, hw, hnear]
      have e5 : Tone ψ t C K z n = 0 := by
        simp [Tone, not_le.2 hw]
      rw [e3, e5]; linarith
    · have e3 : Tnearw ψ t C K z n = 0 := by simp [Tnearw, hw]
      have hw' : 2 * ‖z‖ ≤ t (n + 1) := not_lt.1 hw
      have e5 : Tone ψ t C K z n = cnear ψ t C K + c1 C / K0 C ^ 2 := by
        simp [Tone, hmid, hw']
      have : 0 ≤ c1 C / K0 C ^ 2 := by have := c1_nonneg h; positivity
      rw [e3, e5]; linarith
  · have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact absurd (near_of_first h hmid) hnear
      · exact hpos
    obtain ⟨hz1, hz2⟩ := mid_bounds h hn1 hmid
    have hfar : K0 C * cellLen t (n + 1) ≤ ‖z - rCentre ψ t (n + 1)‖ := not_lt.1 hnear
    have hj := h.abs_cellTerm_far (n := n + 1) (by omega) hz hz1 hz2 hfar
    have e3 : Tnearw ψ t C K z n = 0 := by simp [Tnearw, hnear]
    have e6 : Ty ψ t C z n = 2 * (cellLen t (n + 1) * z.im / ‖z - rCentre ψ t (n + 1)‖ ^ 2) := by
      simp [Ty, hmid, hnear]
    rw [e3, e6]
    by_cases hw : t (n + 1) < 2 * ‖z‖
    · have e4 : Tfarw ψ t C z n =
          c1 C * (cellLen t (n + 1) ^ 2 / ‖z - rCentre ψ t (n + 1)‖ ^ 2) := by
        simp [Tfarw, hmid, hw, hnear]
      have e5 : Tone ψ t C K z n = 0 := by simp [Tone, not_le.2 hw]
      rw [e4, e5]
      have : c1 C = 2 * rho1 C * (1 + C) ^ 3 + (3 + rho1 C) := rfl
      rw [this]; linarith
    · have hw' : 2 * ‖z‖ ≤ t (n + 1) := not_lt.1 hw
      have e4 : Tfarw ψ t C z n = 0 := by simp [Tfarw, hw]
      have e5 : Tone ψ t C K z n = cnear ψ t C K + c1 C / K0 C ^ 2 := by
        simp [Tone, hmid, hw']
      have hsq := far_sq_le h hfar
      have hc := c1_nonneg h
      have hcn := cnear_nonneg (ψ := ψ) (t := t) (C := C) (K := K)
      have h2 : c1 C * (cellLen t (n + 1) ^ 2 / ‖z - rCentre ψ t (n + 1)‖ ^ 2) ≤
          c1 C / K0 C ^ 2 := by
        rw [div_eq_mul_one_div (c1 C)]
        exact mul_le_mul_of_nonneg_left hsq hc
      have : c1 C = 2 * rho1 C * (1 + C) ^ 3 + (3 + rho1 C) := rfl
      rw [e4, e5]
      rw [this] at h2 ⊢
      nlinarith

/-! ### Sums over a finset -/

theorem sum_shift (S : Finset ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ S, f (n + 1) = ∑ m ∈ S.image (· + 1), f m := by
  rw [Finset.sum_image]
  intro a _ b _ hab
  simpa using hab

theorem card_shift (S : Finset ℕ) : (S.image (· + 1)).card = S.card :=
  Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)

theorem sum_Tbelow (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0) (F : Finset ℕ) :
    ∑ n ∈ F, Tbelow t C z n ≤ a1 C / 2 := by
  classical
  have hz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  unfold Tbelow
  rw [← Finset.sum_filter, ← Finset.mul_sum, ← Finset.sum_div]
  have := below_sum h hz0 (F.filter fun n => t (n + 1) ≤ ‖z‖ / 2)
    (fun n hn => (Finset.mem_filter.1 hn).2)
  have ha := a1_nonneg h
  calc a1 C * ((∑ n ∈ F.filter (fun n => t (n + 1) ≤ ‖z‖ / 2), cellLen t (n + 1)) / ‖z‖)
    _ ≤ a1 C * ((‖z‖ / 2) / ‖z‖) := by gcongr
    _ = a1 C / 2 := by field_simp

theorem sum_Tabove (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0) (F : Finset ℕ) :
    ∑ n ∈ F, Tabove t C z n ≤ a2 C * (1 + C) / 2 := by
  classical
  have hz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  unfold Tabove
  rw [← Finset.sum_filter, ← Finset.mul_sum, ← Finset.sum_mul]
  have := above_sum h hz0 (F.filter fun n => 1 ≤ n ∧ 2 * ‖z‖ ≤ t n)
    (fun n hn => (Finset.mem_filter.1 hn).2)
  have ha := a2_nonneg h
  calc a2 C * ((∑ n ∈ F.filter (fun n => 1 ≤ n ∧ 2 * ‖z‖ ≤ t n), cellLen t (n + 1) / t n ^ 2) * ‖z‖)
      ≤ a2 C * (((1 + C) * (1 / (2 * ‖z‖))) * ‖z‖) := by gcongr
    _ = a2 C * (1 + C) / 2 := by field_simp

theorem sum_Tnearw (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0) (F : Finset ℕ) :
    ∑ n ∈ F, Tnearw ψ t C K z n ≤ cnear ψ t C K * (3 * (1 + K0 C ^ 2) * M) := by
  classical
  unfold Tnearw
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  set S := F.filter fun n => IsMid t z n ∧ t (n + 1) < 2 * ‖z‖ ∧ IsNear ψ t C z n with hS
  have hcard : ((S.image (· + 1)).card : ℝ) ≤ 3 * (1 + K0 C ^ 2) * M := by
    apply h.K0_finset_card_near_le hz0
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨hmid, hw, hnear⟩ := (Finset.mem_filter.1 hn).2
    exact ⟨by omega, by have := hmid.1; push Not at this; exact this, hw, hnear⟩
  rw [card_shift] at hcard
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left hcard cnear_nonneg

theorem sum_Tfarw (h : RegData ψ t C M) {z : ℂ} (hz0 : z ≠ 0) (F : Finset ℕ) :
    ∑ n ∈ F, Tfarw ψ t C z n ≤ c1 C * (3 * (1 + (K0 C)⁻¹ ^ 2) * M) := by
  classical
  unfold Tfarw
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  set S := F.filter fun n => IsMid t z n ∧ t (n + 1) < 2 * ‖z‖ ∧ ¬ IsNear ψ t C z n with hS
  have hsum : ∑ m ∈ S.image (· + 1), cellLen t m ^ 2 / ‖z - rCentre ψ t m‖ ^ 2 ≤
      3 * (1 + (K0 C)⁻¹ ^ 2) * M := by
    apply h.K0_finset_sum_far_le hz0
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨hmid, hw, hnear⟩ := (Finset.mem_filter.1 hn).2
    exact ⟨by omega, by have := hmid.1; push Not at this; exact this, hw, not_lt.1 hnear⟩
  rw [← sum_shift S (fun m => cellLen t m ^ 2 / ‖z - rCentre ψ t m‖ ^ 2)] at hsum
  exact mul_le_mul_of_nonneg_left hsum (c1_nonneg h)

open Classical in
theorem Tone_card (h : RegData ψ t C M) {z : ℂ} (F : Finset ℕ) :
    (F.filter fun n => IsMid t z n ∧ 2 * ‖z‖ ≤ t (n + 1)).card ≤ 1 := by
  rw [Finset.card_le_one]
  have key : ∀ a b : ℕ, a < b → IsMid t z a ∧ 2 * ‖z‖ ≤ t (a + 1) →
      IsMid t z b ∧ 2 * ‖z‖ ≤ t (b + 1) → False := by
    intro a b hab ha hb
    have h1 : t (a + 1) ≤ t b := h.mono.monotone (by omega)
    exact hb.1.2 ⟨by omega, ha.2.trans h1⟩
  intro a ha b hb
  have ha' := (Finset.mem_filter.1 ha).2
  have hb' := (Finset.mem_filter.1 hb).2
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (key a b hab ha' hb').elim
  · exact hab
  · exact (key b a hab hb' ha').elim


theorem sum_Tone (h : RegData ψ t C M) {z : ℂ} (F : Finset ℕ) :
    ∑ n ∈ F, Tone ψ t C K z n ≤ cnear ψ t C K + c1 C / K0 C ^ 2 := by
  classical
  unfold Tone
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : 0 ≤ cnear ψ t C K + c1 C / K0 C ^ 2 := by
    have := c1_nonneg h; have := cnear_nonneg (ψ := ψ) (t := t) (C := C) (K := K); positivity
  have hcard := Tone_card h (z := z) F
  have : ((F.filter fun n => IsMid t z n ∧ 2 * ‖z‖ ≤ t (n + 1)).card : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  nlinarith

theorem sum_Ty (h : RegData ψ t C M) {z : ℂ} (F : Finset ℕ) :
    ∑ n ∈ F, Ty ψ t C z n ≤ 2 * (9 / 4 * Real.pi) := by
  classical
  unfold Ty
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  set S := F.filter fun n => IsMid t z n ∧ ¬ IsNear ψ t C z n with hS
  have hsum : ∑ m ∈ S.image (· + 1), cellLen t m * z.im / ‖z - rCentre ψ t m‖ ^ 2 ≤
      9 / 4 * Real.pi := by
    apply h.K0_finset_sum_far_im_le
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
    exact ⟨by omega, not_lt.1 (Finset.mem_filter.1 hn).2.2⟩
  rw [← sum_shift S (fun m => cellLen t m * z.im / ‖z - rCentre ψ t m‖ ^ 2)] at hsum
  linarith

/-- The uniform finset bound. -/
theorem exists_finset_bound (h : RegData ψ t C M) (hK : DensBound ψ t K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, 0 ≤ z.im → ∀ F : Finset ℕ,
      ∑ n ∈ F, |cellTerm ψ t C (n + 1) z| ≤ B := by
  refine ⟨max 0 (a1 C / 2 + a2 C * (1 + C) / 2 + cnear ψ t C K * (3 * (1 + K0 C ^ 2) * M) +
    c1 C * (3 * (1 + (K0 C)⁻¹ ^ 2) * M) + (cnear ψ t C K + c1 C / K0 C ^ 2) +
    2 * (9 / 4 * Real.pi)), le_max_left _ _, ?_⟩
  intro z hz F
  by_cases hz0 : z = 0
  · subst hz0
    have : ∀ n, cellTerm ψ t C (n + 1) 0 = 0 := by
      intro n; simp [cellTerm]
    simp [this]
  calc ∑ n ∈ F, |cellTerm ψ t C (n + 1) z|
      ≤ ∑ n ∈ F, (Tbelow t C z n + Tabove t C z n + Tnearw ψ t C K z n +
        Tfarw ψ t C z n + Tone ψ t C K z n + Ty ψ t C z n) :=
        Finset.sum_le_sum fun n _ => pointwise h hK hz hz0 n
    _ ≤ _ := by
        simp only [Finset.sum_add_distrib]
        refine le_trans ?_ (le_max_right _ _)
        linarith [sum_Tbelow h hz0 F, sum_Tabove h hz0 F, sum_Tnearw (K := K) h hz0 F,
          sum_Tfarw h hz0 F, sum_Tone (K := K) h (z := z) F, sum_Ty h (z := z) F]

end D3

theorem RegData.exists_bound_cellTerm (h : RegData ψ t C M) (hK : DensBound ψ t K) :
    ∃ B : ℝ, ∀ z : ℂ, 0 ≤ z.im → ∑' n : ℕ, |cellTerm ψ t C (n + 1) z| ≤ B := by
  obtain ⟨B, hB0, hB⟩ := D3.exists_finset_bound h hK
  exact ⟨B, fun z hz => Real.tsum_le_of_sum_le (fun n => abs_nonneg _) (hB z hz)⟩

theorem RegData.exists_approx (h : RegData ψ t C M) (hK : DensBound ψ t K) :
    ∃ B : ℝ, ∀ z : ℂ, 0 ≤ z.im → |UPsi ψ z - Real.log ‖fProd ψ t C z‖| ≤ B := by
  obtain ⟨B, hB0, hB⟩ := D3.exists_finset_bound h hK
  refine ⟨B, fun z hz => ?_⟩
  have hsum : Summable fun n : ℕ => |cellTerm ψ t C (n + 1) z| :=
    summable_of_sum_le (fun n => abs_nonneg _) (hB z hz)
  have hS := (h.hasSum_cellTerm hz).tsum_eq
  rw [← hS]
  calc |∑' n : ℕ, cellTerm ψ t C (n + 1) z|
      ≤ ∑' n : ℕ, |cellTerm ψ t C (n + 1) z| := by
        simpa using norm_tsum_le_tsum_norm (f := fun n : ℕ => cellTerm ψ t C (n + 1) z)
          (by simpa using hsum)
    _ ≤ B := Real.tsum_le_of_sum_le (fun n => abs_nonneg _) (hB z hz)

end FF
