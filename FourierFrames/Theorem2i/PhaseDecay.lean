import FourierFrames.Theorem2i.Basic

/-!
# M08 helper: decay of the phase derivative

Blueprint §4.  We prove `RegData.tendsto_phaseDeriv_of_hasSum`: any function `g` that is the sum
`∑ |Im z_n| / |x - z_n|²` tends to `0` along `cocompact ℝ`.  The proof compares each term with
`E * d_n / ((x - t_n)² + d_n²)` and treats the sum over finite sets of indices (so that no
summability is assumed).
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF
namespace B2

/-- Telescoping bound over a finite set of indices `≥ m`. -/
theorem tele {f : ℕ → ℝ} {m : ℕ} (hf : ∀ n, m ≤ n → f (n + 1) ≤ f n)
    (hnn : ∀ n, m ≤ n → 0 ≤ f n) (F : Finset ℕ) (hF : ∀ n ∈ F, m ≤ n) :
    ∑ n ∈ F, (f n - f (n + 1)) ≤ f m := by
  have key : ∀ N, m ≤ N → ∑ n ∈ Finset.Ico m N, (f n - f (n + 1)) = f m - f N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih => rw [Finset.sum_Ico_succ_top hN, ih]; ring
  set N := max m (F.sup id + 1) with hNdef
  have hmN : m ≤ N := le_max_left _ _
  have hsub : F ⊆ Finset.Ico m N := by
    intro n hn
    rw [Finset.mem_Ico]
    refine ⟨hF n hn, ?_⟩
    have : n ≤ F.sup id := Finset.le_sup (f := id) hn
    exact lt_of_lt_of_le (Nat.lt_succ_of_le this) (le_max_right _ _)
  calc ∑ n ∈ F, (f n - f (n + 1))
      ≤ ∑ n ∈ Finset.Ico m N, (f n - f (n + 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => by
          have := hf n (Finset.mem_Ico.1 hn).1; linarith)
    _ = f m - f N := key N hmN
    _ ≤ f m := by have := hnn N hmN; linarith

/-- The cell lengths of a nondecreasing sequence sum to at most `t N - t 0`. -/
theorem sum_diff_le {t : ℕ → ℝ} (ht : Monotone t) (F : Finset ℕ) {N : ℕ}
    (hF : ∀ n ∈ F, n < N) : ∑ n ∈ F, (t (n + 1) - t n) ≤ t N - t 0 := by
  have hsub : F ⊆ Finset.range N := fun n hn => Finset.mem_range.2 (hF n hn)
  calc ∑ n ∈ F, (t (n + 1) - t n) ≤ ∑ n ∈ Finset.range N, (t (n + 1) - t n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by
          have := ht (Nat.le_succ n); linarith)
    _ = t N - t 0 := Finset.sum_range_sub t N

/-- Pointwise comparison of a term of the Poisson-type sum with a Cauchy-type term. -/
theorem pt_bound {c d a u x tn : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hd : 0 < d)
    (ha1 : 2 / Real.pi * (c * d) ≤ a) (ha2 : a ≤ c * d) (hua : a ≤ u)
    (hxt : |x - tn| ≤ u + c * d + d) :
    a / u ^ 2 ≤ (c * ((1 + 2 * (Real.pi / (2 * c))) ^ 2 + (Real.pi / (2 * c)) ^ 2)) *
      (d / ((x - tn) ^ 2 + d ^ 2)) := by
  have hpi := Real.pi_pos
  set L := Real.pi / (2 * c) with hL
  have hL0 : 0 < L := by positivity
  have hdL : d ≤ L * a := by
    have : d = L * (2 / Real.pi * (c * d)) := by rw [hL]; field_simp
    calc d = L * (2 / Real.pi * (c * d)) := this
      _ ≤ L * a := mul_le_mul_of_nonneg_left ha1 hL0.le
  have ha0 : 0 < a := by
    have : 0 < 2 / Real.pi * (c * d) := by positivity
    linarith
  have hu0 : 0 < u := lt_of_lt_of_le ha0 hua
  have hdu : d ≤ L * u := hdL.trans (mul_le_mul_of_nonneg_left hua hL0.le)
  have hxt' : |x - tn| ≤ (1 + 2 * L) * u := by
    have : c * d ≤ d := by nlinarith
    nlinarith
  have hsq : (x - tn) ^ 2 + d ^ 2 ≤ ((1 + 2 * L) ^ 2 + L ^ 2) * u ^ 2 := by
    have h1 : (x - tn) ^ 2 ≤ ((1 + 2 * L) * u) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hxt' 2
    have h2 : d ^ 2 ≤ (L * u) ^ 2 := pow_le_pow_left₀ hd.le hdu 2
    nlinarith
  have hpos : 0 < (x - tn) ^ 2 + d ^ 2 := by positivity
  calc a / u ^ 2 ≤ c * d / u ^ 2 := by gcongr
    _ ≤ _ := by
      rw [div_le_iff₀ (by positivity)]
      have : c * d * ((x - tn) ^ 2 + d ^ 2) ≤ c * d * (((1 + 2 * L) ^ 2 + L ^ 2) * u ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      calc c * d = (c * d * ((x - tn) ^ 2 + d ^ 2)) / ((x - tn) ^ 2 + d ^ 2) := by
              field_simp
        _ ≤ (c * d * (((1 + 2 * L) ^ 2 + L ^ 2) * u ^ 2)) / ((x - tn) ^ 2 + d ^ 2) := by
              gcongr
        _ = _ := by ring


/-- The Cauchy-type term attached to the `(n+1)`-st cell. -/
def q (t : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (t (n + 1) - t n) / ((x - t (n + 1)) ^ 2 + (t (n + 1) - t n) ^ 2)

theorem q_nonneg {t : ℕ → ℝ} (ht : Monotone t) (x : ℝ) (n : ℕ) : 0 ≤ q t x n := by
  have := ht (Nat.le_succ n)
  unfold q
  apply div_nonneg <;> nlinarith [sq_nonneg (x - t (n + 1)), sq_nonneg (t (n + 1) - t n)]

/-- `x < 0`: all cells together. -/
theorem sum_q_neg {t : ℕ → ℝ} (ht : Monotone t) (h0 : t 0 = 0) {x : ℝ} (hx : x < 0)
    (F : Finset ℕ) : ∑ n ∈ F, q t x n ≤ 1 / (-x) := by
  have htn : ∀ n, 0 ≤ t n := fun n => h0 ▸ ht (Nat.zero_le n)
  have hpos : ∀ n, 0 < t n - x := fun n => by linarith [htn n]
  have hle : ∀ n ∈ F, q t x n ≤ 1 / (t n - x) - 1 / (t (n + 1) - x) := by
    intro n _
    have hm := ht (Nat.le_succ n)
    have h1 := hpos n
    have h2 := hpos (n + 1)
    have e : 1 / (t n - x) - 1 / (t (n + 1) - x) =
        (t (n + 1) - t n) / ((t n - x) * (t (n + 1) - x)) := by
      field_simp; ring
    rw [e]
    unfold q
    have hd : 0 ≤ t (n + 1) - t n := by linarith
    apply div_le_div_of_nonneg_left hd (by positivity)
    nlinarith [sq_nonneg (t (n + 1) - t n)]
  calc ∑ n ∈ F, q t x n ≤ ∑ n ∈ F, (1 / (t n - x) - 1 / (t (n + 1) - x)) :=
        Finset.sum_le_sum hle
    _ ≤ 1 / (t 0 - x) := by
        apply tele (m := 0) (f := fun n => 1 / (t n - x))
        · intro n _
          apply one_div_le_one_div_of_le (hpos n)
          linarith [ht (Nat.le_succ n)]
        · intro n _; exact (one_div_pos.2 (hpos n)).le
        · intro n _; exact Nat.zero_le _
    _ = 1 / (-x) := by rw [h0]; simp

/-- `x > 0`: cells with `t_{n+1} ≤ x/2`. -/
theorem sum_q_low {t : ℕ → ℝ} (ht : Monotone t) (h0 : t 0 = 0) {x : ℝ} (hx : 0 < x)
    (F : Finset ℕ) (hF : ∀ n ∈ F, t (n + 1) ≤ x / 2) : ∑ n ∈ F, q t x n ≤ 2 / x := by
  have hle : ∀ n ∈ F, q t x n ≤ 4 / x ^ 2 * (t (n + 1) - t n) := by
    intro n hn
    have hm := ht (Nat.le_succ n)
    have hd : 0 ≤ t (n + 1) - t n := by linarith
    have hh := hF n hn
    have : (x / 2) ^ 2 ≤ (x - t (n + 1)) ^ 2 := by nlinarith [ht (Nat.zero_le (n+1)), h0]
    unfold q
    have hpos : 0 < (x - t (n + 1)) ^ 2 + (t (n + 1) - t n) ^ 2 := by
      have : 0 < x - t (n + 1) := by linarith
      positivity
    rw [div_le_iff₀ hpos]
    have e : 4 / x ^ 2 * (t (n + 1) - t n) = (t (n + 1) - t n) / (x / 2) ^ 2 := by
      field_simp; ring
    have h2 : (t (n + 1) - t n) / (x / 2) ^ 2 * (x / 2) ^ 2 = t (n + 1) - t n := by
      field_simp
    rw [e]
    calc t (n + 1) - t n = (t (n + 1) - t n) / (x / 2) ^ 2 * (x / 2) ^ 2 := h2.symm
      _ ≤ (t (n + 1) - t n) / (x / 2) ^ 2 * ((x - t (n + 1)) ^ 2 + (t (n + 1) - t n) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [sq_nonneg (t (n + 1) - t n)]
  have hsum : ∑ n ∈ F, (t (n + 1) - t n) ≤ x / 2 := by
    rcases F.eq_empty_or_nonempty with rfl | hne
    · simp; linarith
    · obtain ⟨n0, hn0, hsup⟩ := Finset.exists_mem_eq_sup F hne id
      have := sum_diff_le ht F (N := F.sup id + 1) (fun n hn => by
        have : n ≤ F.sup id := Finset.le_sup (f := id) hn
        omega)
      have h3 := hF n0 hn0
      have hs : F.sup id = n0 := by simpa using hsup
      rw [hs] at this
      linarith
  calc ∑ n ∈ F, q t x n ≤ ∑ n ∈ F, 4 / x ^ 2 * (t (n + 1) - t n) := Finset.sum_le_sum hle
    _ = 4 / x ^ 2 * ∑ n ∈ F, (t (n + 1) - t n) := by rw [Finset.mul_sum]
    _ ≤ 4 / x ^ 2 * (x / 2) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 / x := by field_simp; ring

/-- `x > 0`: cells with `t_n ≥ 2x`. -/
theorem sum_q_high {t : ℕ → ℝ} (ht : Monotone t) {x : ℝ} (hx : 0 < x)
    (F : Finset ℕ) (hF : ∀ n ∈ F, 2 * x ≤ t n) : ∑ n ∈ F, q t x n ≤ 2 / x := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · simp; positivity
  set m := F.min' hne with hm
  have hmF : m ∈ F := Finset.min'_mem F hne
  have hmx : 2 * x ≤ t m := hF m hmF
  have hge : ∀ n, m ≤ n → 2 * x ≤ t n := fun n hn => hmx.trans (ht hn)
  have hle : ∀ n ∈ F, q t x n ≤ 4 * (1 / t n - 1 / t (n + 1)) := by
    intro n hn
    have hmn : m ≤ n := Finset.min'_le F n hn
    have h1 := hge n hmn
    have h2 := ht (Nat.le_succ n)
    have hn0 : 0 < t n := by linarith
    have hn1 : 0 < t (n + 1) := by linarith
    have e : 4 * (1 / t n - 1 / t (n + 1)) = 4 * (t (n + 1) - t n) / (t n * t (n + 1)) := by
      field_simp
    rw [e]
    unfold q
    have hd : 0 ≤ t (n + 1) - t n := by linarith
    have hpos : 0 < (x - t (n + 1)) ^ 2 + (t (n + 1) - t n) ^ 2 := by
      have : x - t (n + 1) ≠ 0 := by linarith
      positivity
    rw [div_le_div_iff₀ hpos (by positivity)]
    have : t (n + 1) ^ 2 ≤ 4 * (x - t (n + 1)) ^ 2 := by nlinarith
    have h4 : t n * t (n + 1) ≤ t (n + 1) ^ 2 := by nlinarith
    nlinarith [mul_nonneg hd (sq_nonneg (t (n + 1) - t n)), mul_nonneg hd (sub_nonneg.2 h4),
      mul_nonneg hd (sub_nonneg.2 this)]
  calc ∑ n ∈ F, q t x n ≤ ∑ n ∈ F, 4 * (1 / t n - 1 / t (n + 1)) := Finset.sum_le_sum hle
    _ = 4 * ∑ n ∈ F, (1 / t n - 1 / t (n + 1)) := by rw [Finset.mul_sum]
    _ ≤ 4 * (1 / t m) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply tele (m := m) (f := fun n => 1 / t n)
        · intro n hn
          have := hge n hn
          apply one_div_le_one_div_of_le (by linarith) (ht (Nat.le_succ n))
        · intro n hn; have := hge n hn; exact (one_div_pos.2 (by linarith)).le
        · intro n hn; exact Finset.min'_le F n hn
    _ ≤ 4 * (1 / (2 * x)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact one_div_le_one_div_of_le (by positivity) hmx
    _ = 2 / x := by field_simp; ring


/-- The window terms `d²/((x-t)²+d²)` over a finite set of window cells sum to at most `M`. -/
theorem sum_w_le {t : ℕ → ℝ} {M : ℝ}
    (hsum : ∀ x : ℝ, 0 < x →
      ∑' n : {n : ℕ | 1 ≤ n ∧ x / 2 < t n ∧ t n < 2 * x},
        ENNReal.ofReal ((t n - t (n - 1)) ^ 2 / ((x - t n) ^ 2 + (t n - t (n - 1)) ^ 2)) ≤
      ENNReal.ofReal M) {x : ℝ} (hx : 0 < x) (F : Finset ℕ)
    (hF : ∀ n ∈ F, x / 2 < t (n + 1) ∧ t (n + 1) < 2 * x) :
    ∑ n ∈ F, (t (n + 1) - t n) ^ 2 / ((x - t (n + 1)) ^ 2 + (t (n + 1) - t n) ^ 2) ≤ max M 0 := by
  set W : ℕ → ℝ := fun k =>
    (t k - t (k - 1)) ^ 2 / ((x - t k) ^ 2 + (t k - t (k - 1)) ^ 2) with hW
  have hWn : ∀ k, 0 ≤ W k := fun k => by positivity
  set p : ℕ → Prop := fun n => n ∈ {n : ℕ | 1 ≤ n ∧ x / 2 < t n ∧ t n < 2 * x} with hp
  classical
  set G : Finset ℕ := F.image (· + 1) with hG
  have hGp : ∀ k ∈ G, p k := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hk
    exact ⟨by omega, hF n hn⟩
  have e1 : ∑ n ∈ F, (t (n + 1) - t n) ^ 2 / ((x - t (n + 1)) ^ 2 + (t (n + 1) - t n) ^ 2) =
      ∑ k ∈ G, W k := by
    rw [hG, Finset.sum_image (fun a _ b _ h => by simpa using h)]
    simp [hW]
  rw [e1]
  have h1 : ∑ k ∈ G.subtype p, ENNReal.ofReal (W k.1) ≤ ENNReal.ofReal M :=
    (ENNReal.sum_le_tsum _).trans (hsum x hx)
  rw [Finset.sum_subtype_of_mem (fun k => ENNReal.ofReal (W k)) hGp,
    ← ENNReal.ofReal_sum_of_nonneg (fun k _ => hWn k)] at h1
  have h2 : ENNReal.ofReal (∑ k ∈ G, W k) ≤ ENNReal.ofReal (max M 0) :=
    h1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 h2


theorem q_eq_w_div {t : ℕ → ℝ} (ht : StrictMono t) (x : ℝ) (n : ℕ) :
    q t x n = ((t (n + 1) - t n) ^ 2 / ((x - t (n + 1)) ^ 2 + (t (n + 1) - t n) ^ 2)) /
      (t (n + 1) - t n) := by
  have : 0 < t (n + 1) - t n := sub_pos.2 (ht (Nat.lt_succ_self n))
  unfold q
  field_simp

theorem q_le_inv {t : ℕ → ℝ} (ht : StrictMono t) (x : ℝ) (n : ℕ) :
    q t x n ≤ 1 / (t (n + 1) - t n) := by
  have hd : 0 < t (n + 1) - t n := sub_pos.2 (ht (Nat.lt_succ_self n))
  unfold q
  rw [div_le_div_iff₀ (by positivity) hd]
  nlinarith [sq_nonneg (x - t (n + 1))]

/-- `x > 0`, the cells beyond `x/2` have length `≥ D`. -/
theorem sum_q_pos {t : ℕ → ℝ} {M : ℝ} (ht : StrictMono t) (h0 : t 0 = 0)
    (hsum : ∀ x : ℝ, 0 < x →
      ∑' n : {n : ℕ | 1 ≤ n ∧ x / 2 < t n ∧ t n < 2 * x},
        ENNReal.ofReal ((t n - t (n - 1)) ^ 2 / ((x - t n) ^ 2 + (t n - t (n - 1)) ^ 2)) ≤
      ENNReal.ofReal M) {x D : ℝ} (hx : 0 < x) (hD : 0 < D)
    (hdD : ∀ n, x / 2 < t (n + 1) → D ≤ t (n + 1) - t n) (F : Finset ℕ) :
    ∑ n ∈ F, q t x n ≤ 4 / x + (max M 0 + 1) / D := by
  classical
  have hm := ht.monotone
  set A : ℕ → Prop := fun n => t (n + 1) ≤ x / 2
  set B : ℕ → Prop := fun n => 2 * x ≤ t n
  set C1 : ℕ → Prop := fun n => x / 2 < t (n + 1) ∧ t (n + 1) < 2 * x
  set C2 : ℕ → Prop := fun n => x / 2 < t (n + 1) ∧ 2 * x ≤ t (n + 1) ∧ t n < 2 * x
  have hpt : ∀ n, q t x n ≤ (if A n then q t x n else 0) + (if B n then q t x n else 0) +
      (if C1 n then q t x n else 0) + (if C2 n then q t x n else 0) := by
    intro n
    have hq := q_nonneg hm x n
    by_cases h1 : A n
    · simp [h1]; split_ifs <;> linarith
    by_cases h2 : B n
    · simp [h2]; split_ifs <;> linarith
    by_cases h3 : C1 n
    · simp [h3]; split_ifs <;> linarith
    have h4 : C2 n := by
      simp only [A, B, C1, C2, not_le, not_and, not_lt] at *
      have a1 := h1
      refine ⟨a1, ?_, h2⟩
      exact h3 a1
    simp [h4, h1, h2, h3]
  have hsF := Finset.sum_le_sum (s := F) (fun n _ => hpt n)
  simp only [Finset.sum_add_distrib] at hsF
  have sA : ∑ n ∈ F.filter A, q t x n ≤ 2 / x :=
    sum_q_low hm h0 hx _ (fun n hn => (Finset.mem_filter.1 hn).2)
  have sB : ∑ n ∈ F.filter B, q t x n ≤ 2 / x :=
    sum_q_high hm hx _ (fun n hn => (Finset.mem_filter.1 hn).2)
  have sC1 : ∑ n ∈ F.filter C1, q t x n ≤ max M 0 / D := by
    have hw := sum_w_le hsum hx (F.filter C1) (fun n hn => (Finset.mem_filter.1 hn).2)
    calc ∑ n ∈ F.filter C1, q t x n
        ≤ ∑ n ∈ F.filter C1,
          ((t (n + 1) - t n) ^ 2 / ((x - t (n + 1)) ^ 2 + (t (n + 1) - t n) ^ 2)) / D := by
          apply Finset.sum_le_sum
          intro n hn
          rw [q_eq_w_div ht]
          have hC := (Finset.mem_filter.1 hn).2
          have := hdD n hC.1
          apply div_le_div_of_nonneg_left (by positivity) hD this
      _ = (∑ n ∈ F.filter C1,
          (t (n + 1) - t n) ^ 2 / ((x - t (n + 1)) ^ 2 + (t (n + 1) - t n) ^ 2)) / D := by
          rw [Finset.sum_div]
      _ ≤ max M 0 / D := by gcongr
  have sC2 : ∑ n ∈ F.filter C2, q t x n ≤ 1 / D := by
    have hcard : (F.filter C2).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have ha' := (Finset.mem_filter.1 ha).2
      have hb' := (Finset.mem_filter.1 hb).2
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := hm (Nat.succ_le_of_lt h)
        linarith [ha'.2.1, hb'.2.2]
      · have := hm (Nat.succ_le_of_lt h)
        linarith [hb'.2.1, ha'.2.2]
    calc ∑ n ∈ F.filter C2, q t x n ≤ (F.filter C2).card • (1 / D) := by
          apply Finset.sum_le_card_nsmul
          intro n hn
          have hC := (Finset.mem_filter.1 hn).2
          exact (q_le_inv ht x n).trans (one_div_le_one_div_of_le hD (hdD n hC.1))
      _ ≤ 1 • (1 / D) := by
          apply nsmul_le_nsmul_left (by positivity) hcard
      _ = 1 / D := by simp
  simp only [Finset.sum_filter] at sA sB sC1 sC2
  have : (max M 0 + 1) / D = max M 0 / D + 1 / D := by ring
  rw [this]
  have : 4 / x = 2 / x + 2 / x := by ring
  rw [this]
  linarith


end B2

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M : ℝ}

theorem cellLen_succ' (t : ℕ → ℝ) (n : ℕ) : cellLen t (n + 1) = t (n + 1) - t n := by
  simp [cellLen]

/-- Constant of the comparison. -/
def B2.Econst (c : ℝ) : ℝ :=
  c * ((1 + 2 * (Real.pi / (2 * c))) ^ 2 + (Real.pi / (2 * c)) ^ 2)

theorem B2.Econst_pos {c : ℝ} (hc : 0 < c) : 0 < B2.Econst c := by
  unfold B2.Econst
  have := Real.pi_pos
  positivity

/-- Termwise comparison. -/
theorem RegData.term_le (h : RegData ψ t C M) (x : ℝ) (n : ℕ) :
    0 ≤ -(zPt ψ t C (n + 1)).im / ‖(x : ℂ) - zPt ψ t C (n + 1)‖ ^ 2 ∧
    -(zPt ψ t C (n + 1)).im / ‖(x : ℂ) - zPt ψ t C (n + 1)‖ ^ 2 ≤
      B2.Econst (cAngle ψ t C) * B2.q t x n := by
  have hn : 1 ≤ n + 1 := by omega
  have hc := h.cAngle_pos
  have hc1 : cAngle ψ t C ≤ 1 := by
    have := h.cAngle_lt
    have := Real.pi_le_four
    linarith
  have hd : 0 < t (n + 1) - t n := sub_pos.2 (h.mono (Nat.lt_succ_self n))
  have e := cellLen_succ' t n
  have i1 := h.im_zPt_le hn
  have i2 := h.im_zPt_ge hn
  rw [e] at i1 i2
  have hz := h.norm_zPt_sub_le hn
  rw [e] at hz
  have hr := h.rCentre_mem hn
  simp only [Nat.add_sub_cancel] at hr
  set z := zPt ψ t C (n + 1)
  set a := -z.im with ha
  have ha1 : 2 / Real.pi * (cAngle ψ t C * (t (n + 1) - t n)) ≤ a := by
    have := i1; rw [ha]; linarith
  have ha2 : a ≤ cAngle ψ t C * (t (n + 1) - t n) := by rw [ha]; linarith
  have ha0 : 0 < a := by
    have : 0 < 2 / Real.pi * (cAngle ψ t C * (t (n + 1) - t n)) := by
      have := Real.pi_pos; positivity
    linarith
  have hua : a ≤ ‖(x : ℂ) - z‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) - z)
    simp at this
    rw [ha]
    exact (le_abs_self _).trans (by rw [abs_neg]; exact this)
  refine ⟨by positivity, ?_⟩
  have hxt : |x - t (n + 1)| ≤ ‖(x : ℂ) - z‖ + cAngle ψ t C * (t (n + 1) - t n) +
      (t (n + 1) - t n) := by
    have e1 : ((x : ℂ) - ((t (n + 1) : ℝ) : ℂ)) =
        ((x : ℂ) - z) + (z - (rCentre ψ t (n + 1) : ℂ)) +
          (((rCentre ψ t (n + 1) : ℝ) : ℂ) - ((t (n + 1) : ℝ) : ℂ)) := by ring
    have e2 : ‖(x : ℂ) - ((t (n + 1) : ℝ) : ℂ)‖ = |x - t (n + 1)| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have e3 : ‖((rCentre ψ t (n + 1) : ℝ) : ℂ) - ((t (n + 1) : ℝ) : ℂ)‖ ≤ t (n + 1) - t n := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hr.1, hr.2]
    rw [← e2, e1]
    calc _ ≤ ‖((x : ℂ) - z) + (z - (rCentre ψ t (n + 1) : ℂ))‖ +
          ‖((rCentre ψ t (n + 1) : ℝ) : ℂ) - ((t (n + 1) : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ (‖(x : ℂ) - z‖ + ‖z - (rCentre ψ t (n + 1) : ℂ)‖) + (t (n + 1) - t n) := by
          gcongr; exact norm_add_le _ _
      _ ≤ _ := by linarith
  exact B2.pt_bound hc hc1 hd ha1 ha2 hua hxt

/-- **Blueprint §4.** -/
theorem RegData.tendsto_phaseDeriv_of_hasSum (h : RegData ψ t C M) {g : ℝ → ℝ}
    (hg : ∀ x : ℝ, HasSum (fun n : ℕ =>
      -(zPt ψ t C (n + 1)).im / ‖(x : ℂ) - zPt ψ t C (n + 1)‖ ^ 2) (g x)) :
    Tendsto g (cocompact ℝ) (𝓝 0) := by
  have hc := h.cAngle_pos
  set E := B2.Econst (cAngle ψ t C) with hE
  have hE0 : 0 < E := B2.Econst_pos hc
  have hm := h.mono.monotone
  -- partial sum bound
  have hbound : ∀ x : ℝ, ∀ b : ℝ, (∀ F : Finset ℕ, ∑ n ∈ F, B2.q t x n ≤ b) →
      0 ≤ g x ∧ g x ≤ E * b := by
    intro x b hb
    have hnn : 0 ≤ fun n : ℕ => -(zPt ψ t C (n + 1)).im / ‖(x : ℂ) - zPt ψ t C (n + 1)‖ ^ 2 :=
      fun n => (h.term_le x n).1
    refine ⟨(hg x).nonneg (fun n => (h.term_le x n).1), ?_⟩
    rw [← (hg x).tsum_eq]
    have hb0 : 0 ≤ b := (Finset.sum_empty (f := fun n => B2.q t x n) ▸ hb ∅)
    refine Real.tsum_le_of_sum_le hnn (fun F => ?_)
    calc _ ≤ ∑ n ∈ F, E * B2.q t x n := Finset.sum_le_sum (fun n _ => (h.term_le x n).2)
      _ = E * ∑ n ∈ F, B2.q t x n := by rw [Finset.mul_sum]
      _ ≤ E * b := mul_le_mul_of_nonneg_left (hb F) hE0.le
  rw [cocompact_eq_atBot_atTop]
  refine tendsto_sup.2 ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [eventually_le_atBot (-(2 * E / ε) - 1)] with x hx
    have hxneg : x < 0 := by
      have : 0 < 2 * E / ε := by positivity
      linarith
    obtain ⟨h1, h2⟩ := hbound x (1 / (-x)) (fun F => B2.sum_q_neg hm h.t0 hxneg F)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h1]
    have hx' : 2 * E / ε ≤ -x := by linarith
    have : E * (1 / (-x)) ≤ ε / 2 := by
      rw [mul_one_div, div_le_iff₀ (by linarith [show 0 < 2 * E / ε by positivity])]
      rw [div_le_iff₀ hε] at hx'
      nlinarith
    linarith
  · rw [Metric.tendsto_nhds]
    intro ε hε
    set M0 := max M 0 with hM0
    have hM0n : 0 ≤ M0 := le_max_right _ _
    set D := 3 * E * (M0 + 1) / ε with hD
    have hD0 : 0 < D := by positivity
    obtain ⟨N, hN⟩ := (eventually_atTop.1 (h.tendsto_cellLen.eventually_ge_atTop D))
    filter_upwards [eventually_ge_atTop (max (12 * E / ε) (2 * t N) + 1)] with x hx
    have hx1 : 12 * E / ε ≤ x := by linarith [le_max_left (12 * E / ε) (2 * t N)]
    have hx2 : 2 * t N ≤ x := by linarith [le_max_right (12 * E / ε) (2 * t N)]
    have hxpos : 0 < x := by
      have : 0 < 12 * E / ε := by positivity
      linarith
    have hdD : ∀ n, x / 2 < t (n + 1) → D ≤ t (n + 1) - t n := by
      intro n hn
      by_cases hNn : N ≤ n + 1
      · have := hN (n + 1) hNn
        rwa [cellLen_succ'] at this
      · exfalso
        have : t (n + 1) ≤ t N := hm (by omega)
        linarith
    obtain ⟨h1, h2⟩ := hbound x _ (fun F => B2.sum_q_pos h.mono h.t0 h.sum_le hxpos hD0 hdD F)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h1]
    have e1 : E * (4 / x) ≤ ε / 3 := by
      rw [mul_div_assoc', div_le_iff₀ hxpos]
      rw [div_le_iff₀ hε] at hx1
      nlinarith
    have e2 : E * ((M0 + 1) / D) = ε / 3 := by
      rw [hD]; field_simp
    have : E * (4 / x + (M0 + 1) / D) = E * (4 / x) + E * ((M0 + 1) / D) := by ring
    linarith

end FF
