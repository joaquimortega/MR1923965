import FourierFrames.Construction
import FourierFrames.LogExample.Basic
import FourierFrames.HB.Comparable
import FourierFrames.Theorem1.Sufficiency

/-!
# M06 — the example `Λ = {k + log⁺|k|}` of p. 798 and the sharpness of Landau's inequality

See `blueprint/M06_LogExample.md`.

* §1  the points `λ_k = k + log⁺|k|`, their gaps, separation, counting;
* §2  invariance of sampling / complete interpolation under real translations;
* §3  the step density `m` whose barycentre sequence is `Λ + 1/2` exactly;
* §4  the potential estimate `U(z) = π Im z + κ Re z + O(1)` for `Im z ≥ 0`;
* §5  the Hermite–Biehler function `E` with `H(E) = PW` and zero set `Λ + 1/2`;
* §6  Theorem E at the phase level `π/2`: sampling and complete interpolation;
* §7  the main statements `logExample_count`, `logExample_isCompleteInterpolating`,
  `landau_sharp`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## §1  The points `λ_k = k + log⁺|k|` -/

/-- `λ_k = k + log⁺|k|`. -/
def logLam (k : ℤ) : ℝ := (k : ℝ) + Real.posLog |(k : ℝ)|

/-- The gap `g_k = λ_{k+1} - λ_k`. -/
def logGap (k : ℤ) : ℝ := logLam (k + 1) - logLam k

theorem logExample_eq_range : logExample = Set.range logLam := rfl

theorem logLam_of_one_le {k : ℤ} (hk : 1 ≤ k) : logLam k = k + Real.log k := by
  have : (1:ℝ) ≤ k := by exact_mod_cast hk
  have h0 : |(k:ℝ)| = k := abs_of_nonneg (by linarith)
  rw [logLam, h0, Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; exact this)]

theorem logLam_of_le_zero {k : ℤ} (hk : k ≤ 0) : logLam k = k + Real.log (-k) := by
  rcases hk.lt_or_eq with h | h
  · have : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    have h0 : |(k:ℝ)| = -k := abs_of_nonpos (by linarith)
    rw [logLam, h0, Real.posLog_eq_log (by rw [abs_neg, abs_of_nonpos (by linarith)]; linarith)]
  · subst h; simp [logLam]

theorem logLam_zero : logLam 0 = 0 := by simp [logLam]
theorem logLam_one : logLam 1 = 1 := by simp [logLam]

theorem logGap_of_one_le {k : ℤ} (hk : 1 ≤ k) :
    logGap k = 1 + (Real.log ((k:ℝ) + 1) - Real.log k) := by
  rw [logGap, logLam_of_one_le (by omega), logLam_of_one_le hk]; push_cast; ring

theorem logGap_of_le_neg_two {k : ℤ} (hk : k ≤ -2) :
    logGap k = 1 - (Real.log (-(k:ℝ)) - Real.log (-(k:ℝ) - 1)) := by
  rw [logGap, logLam_of_le_zero (by omega), logLam_of_le_zero (by omega)]; push_cast
  have : -((k:ℝ) + 1) = -(k:ℝ) - 1 := by ring
  rw [this]; ring

theorem logGap_zero : logGap 0 = 1 := by simp [logGap, logLam_one, logLam_zero]
theorem logGap_neg_one : logGap (-1) = 1 := by
  simp [logGap, logLam]

/-- `1 - log 2 ≤ g_k ≤ 1 + log 2`; in particular `3/10 ≤ g_k ≤ 17/10`. -/
theorem logGap_bounds (k : ℤ) : 3 / 10 ≤ logGap k ∧ logGap k ≤ 17 / 10 := by
  have h2 := LogEx.log_two_lt
  rcases le_or_gt 1 k with h | h
  · have hk : (1:ℝ) ≤ k := by exact_mod_cast h
    obtain ⟨a, b, c⟩ := LogEx.log_sub_log_bounds (x := (k:ℝ)+1) (y := k) (by linarith) (by linarith)
      (by linarith)
    rw [logGap_of_one_le h]; constructor <;> linarith
  rcases (show k = 0 ∨ k = -1 ∨ k ≤ -2 by omega) with rfl | rfl | h
  · rw [logGap_zero]; norm_num
  · rw [logGap_neg_one]; norm_num
  · have hk : (k:ℝ) ≤ -2 := by exact_mod_cast h
    obtain ⟨a, b, c⟩ := LogEx.log_sub_log_bounds (x := -(k:ℝ)) (y := -(k:ℝ) - 1) (by linarith)
      (by linarith) (by linarith)
    rw [logGap_of_le_neg_two h]; constructor <;> linarith

/-- `|g_k - 1| ≤ 3/(1 + |k|)`. -/
theorem abs_logGap_sub_one_le (k : ℤ) : |logGap k - 1| ≤ 3 / (1 + |(k : ℝ)|) := by
  rcases le_or_gt 1 k with h | h
  · have hk : (1:ℝ) ≤ k := by exact_mod_cast h
    obtain ⟨a, b, c⟩ := LogEx.log_sub_log_bounds (x := (k:ℝ)+1) (y := k) (by linarith) (by linarith)
      (by linarith)
    rw [logGap_of_one_le h, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    have : ((k:ℝ) + 1 - k) / k = 1 / k := by ring_nf
    rw [this] at c
    refine le_trans (by linarith) ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  rcases (show k = 0 ∨ k = -1 ∨ k ≤ -2 by omega) with rfl | rfl | h
  · rw [logGap_zero]; norm_num
  · rw [logGap_neg_one]; norm_num
  · have hk : (k:ℝ) ≤ -2 := by exact_mod_cast h
    obtain ⟨a, b, c⟩ := LogEx.log_sub_log_bounds (x := -(k:ℝ)) (y := -(k:ℝ) - 1) (by linarith)
      (by linarith) (by linarith)
    rw [logGap_of_le_neg_two h, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    have : (-(k:ℝ) - (-(k:ℝ) - 1)) / (-(k:ℝ) - 1) = 1 / (-(k:ℝ) - 1) := by ring_nf
    rw [this] at c
    refine le_trans (by linarith) ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith

theorem logLam_sub_ge_of_le {a b : ℤ} (hab : a ≤ b) :
    3 / 10 * ((b : ℝ) - a) ≤ logLam b - logLam a := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  clear hab
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : logLam (a + n + 1) - logLam (a + n) = logGap (a + n) := rfl
    have := (logGap_bounds (a + n)).1
    have e : a + ((n + 1 : ℕ) : ℤ) = a + n + 1 := by push_cast; ring
    rw [e]; push_cast at ih ⊢; linarith

theorem logLam_sub_ge {a b : ℤ} (hab : a < b) : 3 / 10 * ((b : ℝ) - a) ≤ logLam b - logLam a :=
  logLam_sub_ge_of_le hab.le

theorem strictMono_logLam : StrictMono logLam := by
  intro a b hab
  have := logLam_sub_ge hab
  have : (0:ℝ) < (b:ℝ) - a := by
    have : (a:ℝ) < b := by exact_mod_cast hab
    linarith
  linarith

theorem logLam_pos_iff (k : ℤ) : 0 < logLam k ↔ 1 ≤ k := by
  constructor
  · intro h
    by_contra hk
    have : logLam k ≤ logLam 0 := strictMono_logLam.monotone (by omega)
    rw [logLam_zero] at this; linarith
  · intro h
    have : logLam 1 ≤ logLam k := strictMono_logLam.monotone h
    rw [logLam_one] at this; linarith

theorem logLam_nonpos_iff (k : ℤ) : logLam k ≤ 0 ↔ k ≤ 0 := by
  rw [← not_lt, logLam_pos_iff]; omega

theorem logExample_isSeparated : IsSeparated logExample := by
  refine ⟨3 / 10, by norm_num, ?_⟩
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
  have hne : i ≠ j := fun h => hij (by rw [h])
  show 3 / 10 ≤ |logLam i - logLam j|
  rcases lt_or_gt_of_ne hne with h | h
  · have := logLam_sub_ge h
    have : (1:ℝ) ≤ (j:ℝ) - i := by exact_mod_cast (show (1:ℤ) ≤ j - i by omega)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · have := logLam_sub_ge h
    have : (1:ℝ) ≤ (i:ℝ) - j := by exact_mod_cast (show (1:ℤ) ≤ i - j by omega)
    rw [abs_of_nonneg (by linarith)]; linarith

theorem ncard_logExample_inter_Ioc_pos (R : ℝ) :
    (logExample ∩ Ioc 0 R).ncard = {k : ℤ | 1 ≤ k ∧ (k : ℝ) + Real.log k ≤ R}.ncard := by
  have : logExample ∩ Ioc 0 R = logLam '' {k : ℤ | 1 ≤ k ∧ (k : ℝ) + Real.log k ≤ R} := by
    ext x
    constructor
    · rintro ⟨⟨k, rfl⟩, h0, hR⟩
      have hk := (logLam_pos_iff k).1 h0
      exact ⟨k, ⟨hk, by rw [← logLam_of_one_le hk]; exact hR⟩, rfl⟩
    · rintro ⟨k, ⟨hk, hR⟩, rfl⟩
      rw [← logLam_of_one_le hk] at hR
      exact ⟨⟨k, rfl⟩, (logLam_pos_iff k).2 hk, hR⟩
  rw [this, Set.ncard_image_of_injective _ strictMono_logLam.injective]

theorem ncard_logExample_inter_Ioc_neg (R : ℝ) :
    (logExample ∩ Ioc (-R) 0).ncard = {k : ℤ | k ≤ 0 ∧ -R < logLam k}.ncard := by
  have : logExample ∩ Ioc (-R) 0 = logLam '' {k : ℤ | k ≤ 0 ∧ -R < logLam k} := by
    ext x
    constructor
    · rintro ⟨⟨k, rfl⟩, h0, hR⟩
      exact ⟨k, ⟨(logLam_nonpos_iff k).1 hR, h0⟩, rfl⟩
    · rintro ⟨k, ⟨hk, hR⟩, rfl⟩
      exact ⟨⟨k, rfl⟩, hR, (logLam_nonpos_iff k).2 hk⟩
  rw [this, Set.ncard_image_of_injective _ strictMono_logLam.injective]

theorem ncard_Icc_int (a b : ℤ) : (Set.Icc a b).ncard = (b + 1 - a).toNat := by
  rw [← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]

theorem ncard_sandwich {S : Set ℤ} {a b c d : ℤ} (h1 : Set.Icc a b ⊆ S) (h2 : S ⊆ Set.Icc c d) :
    ((b + 1 - a).toNat ≤ S.ncard) ∧ S.ncard ≤ (d + 1 - c).toNat := by
  rw [← ncard_Icc_int, ← ncard_Icc_int]
  exact ⟨Set.ncard_le_ncard h1 ((Set.finite_Icc _ _).subset h2),
    Set.ncard_le_ncard h2 (Set.finite_Icc _ _)⟩

theorem card_pos_bounds {R : ℝ} (hR : 1 ≤ R) :
    |(({k : ℤ | 1 ≤ k ∧ (k : ℝ) + Real.log k ≤ R}.ncard : ℕ) : ℝ) - (R - Real.log R)| ≤ 2 := by
  set S : Set ℤ := {k : ℤ | 1 ≤ k ∧ (k : ℝ) + Real.log k ≤ R} with hS
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hlogR2 : Real.log R ≤ R / 2 := LogEx.log_le_half (by linarith)
  have hlogR1 : Real.log R ≤ R - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h2 := LogEx.log_two_lt
  have h2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set n1 : ℤ := ⌊R - Real.log R⌋ with hn1
  set n2 : ℤ := ⌊R - Real.log R + Real.log 2⌋ with hn2
  have hn1a : (n1 : ℝ) ≤ R - Real.log R := Int.floor_le _
  have hn1b : R - Real.log R - 1 < n1 := Int.sub_one_lt_floor _
  have hn2a : (n2 : ℝ) ≤ R - Real.log R + Real.log 2 := Int.floor_le _
  have hn1pos : 1 ≤ n1 := by
    rw [hn1]; apply Int.le_floor.2; push_cast; linarith
  have hn2pos : 1 ≤ n2 := by
    rw [hn2]; apply Int.le_floor.2; push_cast; linarith
  have hsub : Set.Icc 1 n1 ⊆ S := by
    intro k hk
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk.1
    have hk2 : (k:ℝ) ≤ n1 := by exact_mod_cast hk.2
    refine ⟨hk.1, ?_⟩
    have : Real.log k ≤ Real.log R := Real.log_le_log (by linarith) (by linarith)
    linarith
  have hsup : S ⊆ Set.Icc 1 n2 := by
    rintro k ⟨hk, hkR⟩
    refine ⟨hk, ?_⟩
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    rw [hn2]; apply Int.le_floor.2
    rcases le_or_gt (k:ℝ) (R / 2) with h | h
    · linarith
    · have : Real.log (R / 2) ≤ Real.log k := Real.log_le_log (by linarith) h.le
      rw [Real.log_div (by linarith) (by norm_num)] at this
      linarith
  obtain ⟨hl, hu⟩ := ncard_sandwich hsub hsup
  have e1 : (((n1 + 1 - 1).toNat : ℕ) : ℝ) = n1 := by
    have : ((n1 + 1 - 1).toNat : ℤ) = n1 := by omega
    exact_mod_cast this
  have e2 : (((n2 + 1 - 1).toNat : ℕ) : ℝ) = n2 := by
    have : ((n2 + 1 - 1).toNat : ℤ) = n2 := by omega
    exact_mod_cast this
  have hl' : (n1 : ℝ) ≤ S.ncard := by rw [← e1]; exact_mod_cast hl
  have hu' : (S.ncard : ℝ) ≤ n2 := by rw [← e2]; exact_mod_cast hu
  rw [abs_le]; constructor <;> linarith

theorem card_neg_bounds {R : ℝ} (hR : 1 ≤ R) :
    |(({k : ℤ | k ≤ 0 ∧ -R < logLam k}.ncard : ℕ) : ℝ) - (R + Real.log R)| ≤ 2 := by
  set T : Set ℤ := {k : ℤ | k ≤ 0 ∧ -R < logLam k} with hT
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have h2 := LogEx.log_two_lt
  have h2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set n1 : ℤ := ⌊R + Real.log R - 1⌋ with hn1
  set n2 : ℤ := ⌊R + Real.log R + Real.log 2⌋ with hn2
  have hn1a : (n1 : ℝ) ≤ R + Real.log R - 1 := Int.floor_le _
  have hn1b : R + Real.log R - 1 - 1 < n1 := Int.sub_one_lt_floor _
  have hn2a : (n2 : ℝ) ≤ R + Real.log R + Real.log 2 := Int.floor_le _
  have hn1pos : 0 ≤ n1 := by
    rw [hn1]; apply Int.le_floor.2; push_cast; linarith
  have hn2pos : 0 ≤ n2 := by
    rw [hn2]; apply Int.le_floor.2; push_cast; linarith
  have hsub : Set.Icc (-n1) 0 ⊆ T := by
    intro k hk
    refine ⟨hk.2, ?_⟩
    rw [logLam_of_le_zero hk.2]
    rcases (show k = 0 ∨ k ≤ -1 by have := hk.2; omega) with rfl | hk1
    · simp; linarith
    · set j : ℝ := -(k:ℝ) with hj
      have hj1 : (1:ℝ) ≤ j := by
        rw [hj]; have : (k:ℝ) ≤ -1 := by exact_mod_cast hk1
        linarith
      have hj2 : j ≤ n1 := by
        rw [hj]; have : (-n1 : ℤ) ≤ k := hk.1
        have : ((-n1 : ℤ) : ℝ) ≤ k := by exact_mod_cast this
        push_cast at this; linarith
      have hlj : 0 ≤ Real.log j := Real.log_nonneg hj1
      have hk' : (k:ℝ) = -j := by rw [hj]; ring
      rw [hk']
      rcases le_or_gt (R / 2) j with h | h
      · have : Real.log (R / 2) ≤ Real.log j := Real.log_le_log (by linarith) h
        rw [Real.log_div (by linarith) (by norm_num)] at this
        linarith
      · linarith
  have hsup : T ⊆ Set.Icc (-n2) 0 := by
    rintro k ⟨hk, hkR⟩
    refine ⟨?_, hk⟩
    rw [logLam_of_le_zero hk] at hkR
    rcases (show k = 0 ∨ k ≤ -1 by omega) with rfl | hk1
    · simpa using hn2pos
    · set j : ℝ := -(k:ℝ) with hj
      have hj1 : (1:ℝ) ≤ j := by
        rw [hj]; have : (k:ℝ) ≤ -1 := by exact_mod_cast hk1
        linarith
      have hk' : (k:ℝ) = -j := by rw [hj]; ring
      rw [hk'] at hkR
      have hjl := LogEx.log_le_half (show 0 < j by linarith)
      have hj2 : j < 2 * R := by linarith
      have : Real.log j ≤ Real.log (2 * R) := Real.log_le_log (by linarith) hj2.le
      rw [Real.log_mul (by norm_num) (by linarith)] at this
      have : -k ≤ n2 := by
        rw [hn2]; apply Int.le_floor.2; push_cast
        have : (-(k:ℝ)) = j := hj.symm
        linarith
      omega
  obtain ⟨hl, hu⟩ := ncard_sandwich hsub hsup
  have e1 : (((0 + 1 - -n1).toNat : ℕ) : ℝ) = n1 + 1 := by
    have : ((0 + 1 - -n1).toNat : ℤ) = n1 + 1 := by omega
    exact_mod_cast this
  have e2 : (((0 + 1 - -n2).toNat : ℕ) : ℝ) = n2 + 1 := by
    have : ((0 + 1 - -n2).toNat : ℤ) = n2 + 1 := by omega
    exact_mod_cast this
  have hl' : (n1 : ℝ) + 1 ≤ T.ncard := by rw [← e1]; exact_mod_cast hl
  have hu' : (T.ncard : ℝ) ≤ n2 + 1 := by rw [← e2]; exact_mod_cast hu
  rw [abs_le]; constructor <;> linarith

/-- **The example of p. 798**: `n_Λ(R) = R - log R + O(1)` and `-n_Λ(-R) = R + log R + O(1)` for
`Λ = {k + log⁺|k|}`. -/
theorem logExample_count : ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
    |((logExample ∩ Ioc 0 R).ncard : ℝ) - (R - Real.log R)| ≤ C ∧
      |((logExample ∩ Ioc (-R) 0).ncard : ℝ) - (R + Real.log R)| ≤ C := by
  refine ⟨2, fun R hR => ⟨?_, ?_⟩⟩
  · rw [ncard_logExample_inter_Ioc_pos]; exact card_pos_bounds hR
  · rw [ncard_logExample_inter_Ioc_neg]; exact card_neg_bounds hR

/-! ## §2  Translation invariance -/

theorem sampleSum_image_add (s : ℝ) (Λ : Set ℝ) (f : ℂ → ℂ) :
    sampleSum ((fun x : ℝ ↦ x + s) '' Λ) f = sampleSum Λ (fun z ↦ f (z - ((-s : ℝ) : ℂ))) := by
  unfold sampleSum
  rw [← (Equiv.Set.image (fun x : ℝ ↦ x + s) Λ (add_left_injective s)).tsum_eq]
  apply tsum_congr
  intro x
  simp [Equiv.Set.image_apply]

theorem tsum_image_add (s : ℝ) (Λ : Set ℝ) (a : ℝ → ℂ) :
    ∑' y : ((fun x : ℝ ↦ x + s) '' Λ), ‖a y‖ₑ ^ 2 = ∑' x : Λ, ‖a (x + s)‖ₑ ^ 2 := by
  rw [← (Equiv.Set.image (fun x : ℝ ↦ x + s) Λ (add_left_injective s)).tsum_eq]
  apply tsum_congr
  intro x
  simp [Equiv.Set.image_apply]

theorem isSampling_image_add (s : ℝ) {Λ : Set ℝ} (h : IsSampling Λ) :
    IsSampling ((fun x : ℝ ↦ x + s) '' Λ) := by
  obtain ⟨A, B, hA, hAB⟩ := h
  refine ⟨A, B, hA, fun f hf => ?_⟩
  have := hAB _ (hf.comp_sub_ofReal (-s))
  rw [pwNormSq_comp_sub_ofReal] at this
  rwa [sampleSum_image_add]

theorem isCompleteInterpolating_image_add (s : ℝ) {Λ : Set ℝ} (h : IsCompleteInterpolating Λ) :
    IsCompleteInterpolating ((fun x : ℝ ↦ x + s) '' Λ) := by
  intro a ha
  rw [tsum_image_add] at ha
  obtain ⟨f, ⟨hf, hfa⟩, huniq⟩ := h (fun x ↦ a (x + s)) ha
  refine ⟨fun z ↦ f (z - (s : ℂ)), ⟨hf.comp_sub_ofReal s, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := hfa x hx
    simpa using this
  · rintro g ⟨hg, hga⟩
    have hg' := hg.comp_sub_ofReal (-s)
    have := huniq (fun z ↦ g (z - ((-s : ℝ) : ℂ))) ⟨hg', fun x hx => by
      have := hga (x + s) ⟨x, hx, rfl⟩
      simpa using this⟩
    funext z
    have := congrFun this (z - s)
    simpa using this

theorem isSampling_of_image_add (s : ℝ) {Λ : Set ℝ} (h : IsSampling ((fun x : ℝ ↦ x + s) '' Λ)) :
    IsSampling Λ := by
  have := isSampling_image_add (-s) h
  rwa [Set.image_image, show (fun x : ℝ ↦ x + s + -s) = id from by funext x; simp, Set.image_id] at this

theorem isCompleteInterpolating_of_image_add (s : ℝ) {Λ : Set ℝ}
    (h : IsCompleteInterpolating ((fun x : ℝ ↦ x + s) '' Λ)) : IsCompleteInterpolating Λ := by
  have := isCompleteInterpolating_image_add (-s) h
  rwa [Set.image_image, show (fun x : ℝ ↦ x + s + -s) = id from by funext x; simp, Set.image_id] at this

/-! ## §3  The step density with barycentre sequence `Λ + 1/2` -/

/-- Partition points `p_j = (λ_{j-1} + λ_j + 1)/2` (`p_0 = 0`). -/
def logPt (j : ℤ) : ℝ := (logLam (j - 1) + logLam j + 1) / 2

/-- Target barycentres `β_j = λ_j + 1/2`. -/
def logBary (j : ℤ) : ℝ := logLam j + 1 / 2

/-- The index `j` with `p_j ≤ t < p_{j+1}`. -/
def logIdx (t : ℝ) : ℤ := sSup {j : ℤ | logPt j ≤ t}

/-- Value of the density on `[p_j, β_j)`: `2 g_j / (g_{j-1}(g_{j-1} + g_j))`. -/
def logWeightL (j : ℤ) : ℝ := 2 * logGap j / (logGap (j - 1) * (logGap (j - 1) + logGap j))

/-- Value of the density on `[β_j, p_{j+1})`: `2 g_{j-1} / (g_j(g_{j-1} + g_j))`. -/
def logWeightR (j : ℤ) : ℝ := 2 * logGap (j - 1) / (logGap j * (logGap (j - 1) + logGap j))

/-- The step density `m`. -/
def logDensity (t : ℝ) : ℝ :=
  if t < logBary (logIdx t) then logWeightL (logIdx t) else logWeightR (logIdx t)

theorem logLam_sub_logLam_pred (j : ℤ) : logLam j = logLam (j - 1) + logGap (j - 1) := by
  have : j - 1 + 1 = j := by ring
  simp [logGap, this]

theorem logPt_eq (j : ℤ) : logPt j = logBary j - logGap (j - 1) / 2 := by
  have := logLam_sub_logLam_pred j
  unfold logPt logBary; linarith

theorem logPt_succ_eq (j : ℤ) : logPt (j + 1) = logBary j + logGap j / 2 := by
  have h := logLam_sub_logLam_pred (j + 1)
  have e : j + 1 - 1 = j := by ring
  rw [e] at h
  unfold logPt logBary
  rw [e]; linarith

theorem logPt_zero : logPt 0 = 0 := by
  have h : logLam (-1) = -1 := by
    rw [logLam_of_le_zero (by norm_num)]; simp
  unfold logPt
  norm_num [h, logLam_zero]

theorem logPt_succ_sub (j : ℤ) : logPt (j + 1) - logPt j = (logGap (j - 1) + logGap j) / 2 := by
  rw [logPt_succ_eq, logPt_eq]; ring

theorem strictMono_logPt : StrictMono logPt := by
  apply strictMono_int_of_lt_succ
  intro j
  have := logPt_succ_sub j
  have := (logGap_bounds (j - 1)).1
  have := (logGap_bounds j).1
  linarith

theorem logPt_lt_logBary (j : ℤ) : logPt j < logBary j ∧ logBary j < logPt (j + 1) := by
  have := (logGap_bounds (j - 1)).1
  have := (logGap_bounds j).1
  rw [logPt_succ_eq, logPt_eq]
  constructor <;> linarith

theorem logPt_le_half (j : ℤ) (hj : j ≤ 0) : logPt j ≤ (j : ℝ) / 2 + 1 / 2 := by
  have h := (logPt_lt_logBary j).1.le
  have h2 : logLam j ≤ (j : ℝ) / 2 := by
    rw [logLam_of_le_zero hj]
    have hj' : (0:ℝ) ≤ -(j:ℝ) := by have : (j:ℝ) ≤ 0 := by exact_mod_cast hj
                                    linarith
    rcases hj'.eq_or_lt with h0 | h0
    · have : (j:ℝ) = 0 := by linarith
      rw [this]; simp
    · have := LogEx.log_le_half h0; linarith
  unfold logBary at h; linarith

theorem logPt_ge (j : ℤ) (hj : 1 ≤ j) : 3 / 10 * ((j : ℝ) - 1) ≤ logPt j := by
  have h := logLam_sub_ge_of_le (a := 0) (b := j - 1) (by omega)
  rw [logLam_zero] at h
  have h1 := (logGap_bounds (j - 1)).1
  rw [logPt_eq, logBary]
  have := logLam_sub_logLam_pred j
  push_cast at h
  simp at h
  linarith

theorem logIdx_spec (t : ℝ) : logPt (logIdx t) ≤ t ∧ t < logPt (logIdx t + 1) := by
  have hne : {j : ℤ | logPt j ≤ t}.Nonempty := by
    refine ⟨min 0 ⌊2 * t - 1⌋, ?_⟩
    have h1 : min 0 ⌊2 * t - 1⌋ ≤ 0 := min_le_left _ _
    have h2 : ((min 0 ⌊2 * t - 1⌋ : ℤ) : ℝ) ≤ 2 * t - 1 :=
      (Int.cast_le.2 (min_le_right _ _)).trans (Int.floor_le _)
    have := logPt_le_half _ h1
    show logPt _ ≤ t
    linarith
  have hbdd : BddAbove {j : ℤ | logPt j ≤ t} := by
    refine ⟨max 0 ⌈1 + 10 * t / 3⌉, fun j hj => ?_⟩
    rcases le_or_gt j 0 with h | h
    · exact h.trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have := logPt_ge j (by omega)
      have h3 : (j : ℝ) ≤ 1 + 10 * t / 3 := by
        have : logPt j ≤ t := hj
        linarith
      exact_mod_cast h3.trans (Int.le_ceil _)
  have hmem : logIdx t ∈ {j : ℤ | logPt j ≤ t} := Int.csSup_mem hne hbdd
  refine ⟨hmem, ?_⟩
  by_contra hcon
  have hcon : logPt (logIdx t + 1) ≤ t := not_lt.1 hcon
  have : logIdx t + 1 ≤ logIdx t := le_csSup hbdd (show logIdx t + 1 ∈ {j : ℤ | logPt j ≤ t} from hcon)
  omega

theorem logIdx_eq_iff {t : ℝ} {j : ℤ} : logIdx t = j ↔ t ∈ Ico (logPt j) (logPt (j + 1)) := by
  obtain ⟨h1, h2⟩ := logIdx_spec t
  constructor
  · rintro rfl; exact ⟨h1, h2⟩
  · rintro ⟨h3, h4⟩
    rcases lt_trichotomy (logIdx t) j with h | h | h
    · have : logPt (logIdx t + 1) ≤ logPt j := strictMono_logPt.monotone (by omega)
      linarith
    · exact h
    · have : logPt (j + 1) ≤ logPt (logIdx t) := strictMono_logPt.monotone (by omega)
      linarith

theorem measurable_logIdx : Measurable logIdx := by
  apply measurable_to_countable'
  intro j
  have : logIdx ⁻¹' {j} = Ico (logPt j) (logPt (j + 1)) := by
    ext t; simp [logIdx_eq_iff]
  rw [this]; exact measurableSet_Ico

theorem measurable_logDensity : Measurable logDensity := by
  unfold logDensity
  apply Measurable.ite
  · exact measurableSet_lt measurable_id ((measurable_from_top (f := logBary)).comp measurable_logIdx)
  · exact (measurable_from_top (f := logWeightL)).comp measurable_logIdx
  · exact (measurable_from_top (f := logWeightR)).comp measurable_logIdx

theorem logDensity_of_Ico_left {j : ℤ} {t : ℝ} (h1 : logPt j ≤ t) (h2 : t < logBary j) :
    logDensity t = logWeightL j := by
  have : logIdx t = j := logIdx_eq_iff.2 ⟨h1, h2.trans (logPt_lt_logBary j).2⟩
  simp [logDensity, this, h2]

theorem logDensity_of_Ico_right {j : ℤ} {t : ℝ} (h1 : logBary j ≤ t) (h2 : t < logPt (j + 1)) :
    logDensity t = logWeightR j := by
  have : logIdx t = j := logIdx_eq_iff.2 ⟨(logPt_lt_logBary j).1.le.trans h1, h2⟩
  simp [logDensity, this, not_lt.2 h1]

theorem logWeight_bounds {a b : ℝ} (ha : 3 / 10 ≤ a) (ha' : a ≤ 17 / 10) (hb : 3 / 10 ≤ b)
    (hb' : b ≤ 17 / 10) : 1 / 10 ≤ 2 * b / (a * (a + b)) ∧ 2 * b / (a * (a + b)) ≤ 20 := by
  have hpos : 0 < a * (a + b) := by positivity
  constructor
  · rw [le_div_iff₀ hpos]; nlinarith
  · rw [div_le_iff₀ hpos]; nlinarith

/-- `1/10 ≤ m ≤ 20`. -/
theorem logDensity_bounds (t : ℝ) : 1 / 10 ≤ logDensity t ∧ logDensity t ≤ 20 := by
  have ha := logGap_bounds (logIdx t - 1)
  have hb := logGap_bounds (logIdx t)
  unfold logDensity
  split_ifs
  · exact logWeight_bounds ha.1 ha.2 hb.1 hb.2
  · have := logWeight_bounds hb.1 hb.2 ha.1 ha.2
    unfold logWeightR
    rw [add_comm (logGap (logIdx t - 1))]
    exact this

theorem isMultWeight_logDensity : OCS.IsMultWeight logDensity (1 / 10) 20 :=
  ⟨measurable_logDensity, by norm_num, fun t ↦ (logDensity_bounds t).1,
    fun t ↦ (logDensity_bounds t).2⟩

theorem abs_weight_sub_one_le {a b : ℝ} (ha : 3 / 10 ≤ a) (ha' : a ≤ 17 / 10) (hb : 3 / 10 ≤ b)
    (hb' : b ≤ 17 / 10) : |2 * b / (a * (a + b)) - 1| ≤ 23 * (|b - 1| + |a - 1|) := by
  have hpos : 0 < a * (a + b) := by positivity
  have hden : 9 / 50 ≤ a * (a + b) := by nlinarith
  have e : 2 * b / (a * (a + b)) - 1 =
      ((b - 1) - 3 * (a - 1) - (a - 1) ^ 2 - (a - 1) * (b - 1)) / (a * (a + b)) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have hnum : |(b - 1) - 3 * (a - 1) - (a - 1) ^ 2 - (a - 1) * (b - 1)| ≤
      4 * (|b - 1| + |a - 1|) := by
    rcases abs_cases (b - 1) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases abs_cases (a - 1) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    · rw [h1, h2, abs_le]; constructor <;> nlinarith
  have h0 : 0 ≤ |b - 1| + |a - 1| := by positivity
  nlinarith

theorem abs_logGap_pred_le (j : ℤ) : |logGap (j - 1) - 1| ≤ 6 / (1 + |(j : ℝ)|) := by
  have := abs_logGap_sub_one_le (j - 1)
  refine this.trans ?_
  push_cast
  have h1 : |(j : ℝ)| ≤ |(j : ℝ) - 1| + 1 := by
    have := abs_sub_abs_le_abs_sub (j : ℝ) 1
    simp at this; linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [abs_nonneg ((j : ℝ) - 1), abs_nonneg (j : ℝ)]

theorem abs_logPt_le (j : ℤ) : |logPt j| ≤ 2 * |(j : ℝ)| + 1 / 2 := by
  have hl : ∀ k : ℤ, |logLam k - k| ≤ |(k : ℝ)| := fun k => by
    unfold logLam
    rw [add_sub_cancel_left, abs_of_nonneg Real.posLog_nonneg]
    rw [Real.posLog_abs]; exact Real.posLog_le_abs _
  have h1 := hl (j - 1)
  have h2 := hl j
  have h3 : |((j - 1 : ℤ) : ℝ)| ≤ |(j : ℝ)| + 1 := by
    push_cast
    have := abs_sub (j : ℝ) 1
    simpa using this
  have e : logPt j - j = ((logLam (j - 1) - ((j - 1 : ℤ) : ℝ)) + (logLam j - j)) / 2 := by
    unfold logPt; push_cast; ring
  have : |logPt j - j| ≤ |(j : ℝ)| + 1 / 2 := by
    rw [e, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), div_le_iff₀ (by norm_num)]
    have := abs_add_le (logLam (j - 1) - ((j - 1 : ℤ) : ℝ)) (logLam j - j)
    linarith
  have := abs_sub_abs_le_abs_sub (logPt j) (j : ℝ)
  linarith [abs_nonneg (j : ℝ)]

theorem one_add_abs_le_of_mem {j : ℤ} {t : ℝ} (ht : t ∈ Ico (logPt j) (logPt (j + 1))) :
    1 + |t| ≤ 5 * (1 + |(j : ℝ)|) := by
  have h1 := abs_logPt_le j
  have h2 := abs_logPt_le (j + 1)
  have h3 : |((j + 1 : ℤ) : ℝ)| ≤ |(j : ℝ)| + 1 := by
    push_cast; simpa using abs_add_le (j : ℝ) 1
  have : |t| ≤ 2 * |(j : ℝ)| + 5 / 2 := by
    have a1 := abs_le.1 h1
    have a2 := abs_le.1 h2
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, a1.1, a1.2, a2.1, a2.2, h3]
  nlinarith [abs_nonneg (j : ℝ)]

/-- `|m(t) - 1| ≤ C_m / (1 + |t|)` (one can take `C_m = 1100`). -/
theorem abs_logDensity_sub_one_le (t : ℝ) : |logDensity t - 1| ≤ 1100 / (1 + |t|) := by
  set j := logIdx t with hj
  obtain ⟨h1, h2⟩ := logIdx_spec t
  have ht : t ∈ Ico (logPt j) (logPt (j + 1)) := ⟨h1, h2⟩
  have ha := logGap_bounds (j - 1)
  have hb := logGap_bounds j
  have hea := abs_logGap_pred_le j
  have heb : |logGap j - 1| ≤ 3 / (1 + |(j : ℝ)|) := abs_logGap_sub_one_le j
  have hjp : 0 < 1 + |(j : ℝ)| := by positivity
  have hsum : |logGap j - 1| + |logGap (j - 1) - 1| ≤ 9 / (1 + |(j : ℝ)|) := by
    have : (9 : ℝ) / (1 + |(j : ℝ)|) = 3 / (1 + |(j : ℝ)|) + 6 / (1 + |(j : ℝ)|) := by ring
    linarith
  have hm : |logDensity t - 1| ≤ 207 / (1 + |(j : ℝ)|) := by
    have : |logDensity t - 1| ≤ 23 * (9 / (1 + |(j : ℝ)|)) := by
      unfold logDensity
      split_ifs
      · refine (abs_weight_sub_one_le ha.1 ha.2 hb.1 hb.2).trans ?_
        linarith
      · have := abs_weight_sub_one_le hb.1 hb.2 ha.1 ha.2
        unfold logWeightR
        rw [add_comm (logGap (logIdx t - 1))]
        refine this.trans ?_
        linarith
    have e : 23 * (9 / (1 + |(j : ℝ)|)) = 207 / (1 + |(j : ℝ)|) := by ring
    linarith
  have h5 := one_add_abs_le_of_mem ht
  have htp : 0 < 1 + |t| := by positivity
  refine hm.trans ?_
  rw [div_le_div_iff₀ hjp htp]
  nlinarith

theorem tendsto_logDensity : Tendsto logDensity (cocompact ℝ) (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun t : ℝ ↦ 1100 / (1 + |t|)) (cocompact ℝ) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ ↦ ‖t‖) (cocompact ℝ) atTop := tendsto_norm_cocompact_atTop
    have : Tendsto (fun t : ℝ ↦ 1 + |t|) (cocompact ℝ) atTop :=
      tendsto_atTop_add_const_left _ _ (by simpa [Real.norm_eq_abs] using h)
    exact this.const_div_atTop 1100
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) h0
  simpa [Real.norm_eq_abs] using abs_logDensity_sub_one_le t

theorem integral_mul_density_left (j : ℤ) {F : ℝ → ℝ} :
    ∫ t in logPt j..logBary j, F t * logDensity t = logWeightL j * ∫ t in logPt j..logBary j, F t := by
  have hle := (logPt_lt_logBary j).1.le
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(Set.countable_singleton (logBary j)).ae_notMem volume] with x hx hx'
  rw [Set.uIoc_of_le hle] at hx'
  have hx2 : x < logBary j := lt_of_le_of_ne hx'.2 (by simpa using hx)
  rw [logDensity_of_Ico_left hx'.1.le hx2]; ring

theorem integral_mul_density_right (j : ℤ) {F : ℝ → ℝ} :
    ∫ t in logBary j..logPt (j + 1), F t * logDensity t =
      logWeightR j * ∫ t in logBary j..logPt (j + 1), F t := by
  have hle := (logPt_lt_logBary j).2.le
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(Set.countable_singleton (logPt (j + 1))).ae_notMem volume] with x hx hx'
  rw [Set.uIoc_of_le hle] at hx'
  have hx2 : x < logPt (j + 1) := lt_of_le_of_ne hx'.2 (by simpa using hx)
  rw [logDensity_of_Ico_right hx'.1.le hx2]; ring

theorem integral_mul_density_split (j : ℤ) {F : ℝ → ℝ} (hF : Continuous F) :
    ∫ t in logPt j..logPt (j + 1), F t * logDensity t =
      logWeightL j * (∫ t in logPt j..logBary j, F t) +
        logWeightR j * (∫ t in logBary j..logPt (j + 1), F t) := by
  rw [← integral_mul_density_left, ← integral_mul_density_right,
    ← intervalIntegral.integral_add_adjacent_intervals
      (a := logPt j) (b := logBary j) (c := logPt (j + 1))
      (isMultWeight_logDensity.intervalIntegrable_mul (hF.intervalIntegrable _ _))
      (isMultWeight_logDensity.intervalIntegrable_mul (hF.intervalIntegrable _ _))]

theorem logWeightL_mul (j : ℤ) : logWeightL j * (logGap (j - 1) / 2) = logGap j / (logGap (j - 1) + logGap j) := by
  have := (logGap_bounds (j - 1)).1
  have := (logGap_bounds j).1
  unfold logWeightL
  field_simp

theorem logWeightR_mul (j : ℤ) : logWeightR j * (logGap j / 2) = logGap (j - 1) / (logGap (j - 1) + logGap j) := by
  have := (logGap_bounds (j - 1)).1
  have := (logGap_bounds j).1
  unfold logWeightR
  field_simp

/-- `∫_{p_j}^{p_{j+1}} m = 1`. -/
theorem integral_logDensity_logPt (j : ℤ) : ∫ t in logPt j..logPt (j + 1), logDensity t = 1 := by
  have h := integral_mul_density_split j (F := fun _ ↦ (1 : ℝ)) continuous_const
  simp only [one_mul, intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
  rw [h, logPt_succ_eq, logPt_eq]
  have e1 := logWeightL_mul j
  have e2 := logWeightR_mul j
  have := (logGap_bounds (j - 1)).1
  have := (logGap_bounds j).1
  have e3 : logBary j - (logBary j - logGap (j - 1) / 2) = logGap (j - 1) / 2 := by ring
  have e4 : logBary j + logGap j / 2 - logBary j = logGap j / 2 := by ring
  rw [e3, e4, e1, e2, ← add_div, add_comm]
  exact div_self (by positivity)

/-- `∫_{p_j}^{p_{j+1}} t m(t) dt = β_j`. -/
theorem integral_mul_logDensity_logPt (j : ℤ) :
    ∫ t in logPt j..logPt (j + 1), t * logDensity t = logBary j := by
  have h := integral_mul_density_split j (F := fun t ↦ t) continuous_id
  have i1 : ∀ a b : ℝ, ∫ t in a..b, t = (b ^ 2 - a ^ 2) / 2 := fun a b => integral_id
  rw [i1, i1] at h
  rw [h, logPt_succ_eq, logPt_eq]
  have := (logGap_bounds (j - 1)).1
  have := (logGap_bounds j).1
  unfold logWeightL logWeightR
  field_simp
  ring

theorem multPrim_logDensity_logPt_succ (j : ℤ) :
    OCS.multPrim logDensity (logPt (j + 1)) = OCS.multPrim logDensity (logPt j) + 1 := by
  have := OCS.multPrim_sub_eq isMultWeight_logDensity (logPt j) (logPt (j + 1))
  rw [integral_logDensity_logPt] at this
  linarith

theorem multPrim_logDensity_logPt (j : ℤ) : OCS.multPrim logDensity (logPt j) = j := by
  induction j using Int.induction_on with
  | zero => simp [logPt_zero, OCS.multPrim_zero]
  | succ i ih => rw [multPrim_logDensity_logPt_succ, ih]; push_cast; ring
  | pred i ih =>
    have := multPrim_logDensity_logPt_succ (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -i by ring, ih] at this
    push_cast at ih this ⊢; linarith

theorem multPt_logDensity (j : ℤ) : OCS.multPt logDensity j = logPt j :=
  OCS.multPt_eq_of isMultWeight_logDensity (multPrim_logDensity_logPt j)

theorem multBary_logDensity (j : ℤ) : OCS.multBary logDensity j = logLam j + 1 / 2 := by
  unfold OCS.multBary
  rw [multPt_logDensity, multPt_logDensity, integral_mul_logDensity_logPt]
  rfl

/-- The barycentre sequence of `m` is `Λ + 1/2`, exactly. -/
theorem multGamma_logDensity :
    OCS.multGamma logDensity = (fun x : ℝ ↦ x + 1 / 2) '' logExample := by
  ext x
  simp only [OCS.multGamma, Set.mem_range, Set.mem_image, logExample_eq_range, multBary_logDensity]
  constructor
  · rintro ⟨j, rfl⟩; exact ⟨logLam j, ⟨j, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩

/-! ## §4  The potential estimate -/

/-- `W(t) = M(t) - t` where `M = ∫_0^t m`. -/
def logW (t : ℝ) : ℝ := OCS.multPrim logDensity t - t

/-- `W` is Lipschitz with `W' = m - 1` a.e. -/
theorem logW_lipschitz : LipschitzWith 19 logW := by
  sorry

/-- `W(t) = -log⁺|t| + ρ(t)` with `|ρ(t)| ≤ C_ρ min(|t|, (1+|t|)^{-1/2})`. -/
theorem abs_logW_add_posLog_le : ∃ Cρ : ℝ, ∀ t : ℝ,
    |logW t + Real.posLog (|t|)| ≤ Cρ * min |t| (1 / Real.sqrt (1 + |t|)) := by
  sorry

/-- `κ = ∫_{|t|>1} (m(t) - 1)/t dt` (absolutely convergent). -/
def logKappa : ℝ :=
  ∫ t : ℝ, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((logDensity t - 1) / t)

theorem integrable_logKappa :
    Integrable (fun t : ℝ ↦ (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((logDensity t - 1) / t)) := by
  sorry

/-- The model computation: for `m ≡ 1`, `U(z) = π |Im z|`. -/
theorem multU_model {z : ℂ} (hz : 0 < z.im) :
    ∫ t : ℝ, OCS.multUIntegrand (fun _ ↦ 1) z t = Real.pi * z.im := by
  sorry

theorem integrable_log_mul_sub_one {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ ↦ Real.log ‖1 - z / t‖ * (logDensity t - 1)) := by
  sorry

/-- `U(z) = π Im z + κ Re z + V(z)` for `Im z > 0`, `V(z) = ∫ log|1 - z/t| (m(t) - 1) dt`. -/
theorem multU_logDensity_eq {z : ℂ} (hz : 0 < z.im) :
    OCS.multU logDensity 0 z = Real.pi * z.im + logKappa * z.re +
      ∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1) := by
  sorry

/-- The kernel `K_z(t) = (t - x)/((t - x)² + y²) - 1/t = Re(z / (t (t - z)))`. -/
def logKernel (z : ℂ) (t : ℝ) : ℝ := (t - z.re) / ((t - z.re) ^ 2 + z.im ^ 2) - 1 / t

theorem abs_logKernel_le {z : ℂ} (hz : 0 < z.im) {t : ℝ} (ht : t ≠ 0) :
    |logKernel z t| ≤ ‖z‖ / (|t| * ‖(t : ℂ) - z‖) := by
  sorry

/-- Integration by parts: `V(z) = -∫ W(t) K_z(t) dt`. -/
theorem integral_log_mul_sub_one_eq {z : ℂ} (hz : 0 < z.im) :
    ∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1) = -∫ t : ℝ, logW t * logKernel z t := by
  sorry

/-- `∫_0^∞ log((1+σ)/|1-σ|) dσ/σ < ∞` (its value is `π²/2`). -/
theorem integrableOn_log_ratio_div :
    IntegrableOn (fun σ : ℝ ↦ Real.log ((1 + σ) / |1 - σ|) / σ) (Ioi 0) := by
  sorry

/-- The Hilbert-transform estimate for `log⁺|t|`: `|∫ log⁺|t| K_z(t) dt| ≤ C` for `Im z ≥ 1`. -/
theorem abs_integral_posLog_mul_logKernel_le : ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im →
    Integrable (fun t : ℝ ↦ Real.posLog |t| * logKernel z t) ∧
      |∫ t : ℝ, Real.posLog |t| * logKernel z t| ≤ C := by
  sorry

/-- `∫ |ρ| |K_z| ≤ C` for `Im z ≥ 1`, for `ρ` as in `abs_logW_add_posLog_le`. -/
theorem integral_abs_rho_logKernel_le : ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im →
    Integrable (fun t : ℝ ↦ |logW t + Real.posLog (|t|)| * |logKernel z t|) ∧
      ∫ t : ℝ, |logW t + Real.posLog (|t|)| * |logKernel z t| ≤ C := by
  sorry

theorem abs_integral_log_mul_sub_one_le : ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im →
    |∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1)| ≤ C := by
  sorry

/-- Comparison in the strip: `|U(x + iy) - U(x + i)| ≤ 20 π` for `0 ≤ y ≤ 1`. -/
theorem abs_multU_sub_multU_le {z : ℂ} (h0 : 0 ≤ z.im) (h1 : z.im ≤ 1) :
    |OCS.multU logDensity 0 z - OCS.multU logDensity 0 ((z.re : ℂ) + Complex.I)| ≤ 20 * Real.pi := by
  sorry

/-- **The sine-type estimate**: `U(z) = π Im z + κ Re z + O(1)` for `Im z ≥ 0`. -/
theorem logDensity_U_estimate : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
    |OCS.multU logDensity 0 z - Real.pi * z.im - logKappa * z.re| ≤ C := by
  sorry

/-! ## §5  The Hermite–Biehler function -/

/-- The function `E` of the example: `H(E) = PW`, no real zeros, zero set of `E + E^*` equal to
`Λ + 1/2`, with a phase function. -/
theorem exists_E_logExample (hPW : PaleyWienerThm) :
    ∃ E : ℂ → ℂ, IsHB E ∧ (∀ x : ℝ, E x ≠ 0) ∧ HEEqPW E ∧
      (∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
        c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) ∧
      (∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ (fun x : ℝ ↦ x + 1 / 2) '' logExample, z = (γ : ℂ)) ∧
      ∃ φ : ℝ → ℝ, IsPhaseFunction E φ := by
  obtain ⟨CU, hCU⟩ := logDensity_U_estimate
  obtain ⟨E, hHB, h0, hcomp, hzero, φ, hφ, -⟩ := exists_hb_of_density_phase
    (m := logDensity) (a := 1 / 10) (b := 20) measurable_logDensity (by norm_num)
    (fun t ↦ (logDensity_bounds t).1) (fun t ↦ (logDensity_bounds t).2) tendsto_logDensity
    ⟨logKappa, CU, hCU⟩
  refine ⟨E, hHB, h0, heEqPW_of_comparable hPW hHB hcomp, hcomp, ?_, φ, hφ⟩
  rwa [multGamma_logDensity] at hzero

/-! ## §6  Theorem E at the phase level `π/2` -/

theorem phaseLevel_eq_of_zero_set {E : ℂ → ℂ} {φ : ℝ → ℝ} {Γ : Set ℝ}
    (h0 : ∀ x : ℝ, E x ≠ 0) (hφ : IsPhaseFunction E φ)
    (hΓ : ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ Γ, z = (γ : ℂ)) :
    phaseLevel φ (Real.pi / 2) = Γ := by
  sorry

/-- `E + E^*` is not in `H(E)`: `|E + E^*| = 2|E||cos φ|` is not square integrable on `ℝ`,
because `φ' ≃ 1`. -/
theorem not_memHE_sAlpha (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ} {φ : ℝ → ℝ}
    (hHB : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (hEPW : HEEqPW E) (hφ : IsPhaseFunction E φ)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) :
    ¬ MemHE E (fun z ↦ Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * E z -
      Complex.exp (-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ))) * fstar E z) := by
  sorry

theorem eq_zero_of_pwNormSq_eq_zero {f : ℂ → ℂ} (hf : MemPW f) (h : pwNormSq f = 0) :
    ∀ z, f z = 0 := by
  sorry

/-- From `H(E) = PW`, `|E| ≃ 1` on `ℝ`, `φ_E' |E|² ≃ 1`, `E + E^* ∉ H(E)`: the zero set of
`E + E^*` is sampling and complete interpolating for `PW`. -/
theorem sampling_cis_of_zero_set (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ} {φ : ℝ → ℝ}
    {Γ : Set ℝ} (hHB : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (hEPW : HEEqPW E)
    (hφ : IsPhaseFunction E φ)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im))
    (hΓ : ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ Γ, z = (γ : ℂ)) :
    IsSampling Γ ∧ IsCompleteInterpolating Γ := by
  sorry

/-! ## §7  Main statements -/

theorem logExample_shift_sampling_cis (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsSampling ((fun x : ℝ ↦ x + 1 / 2) '' logExample) ∧
      IsCompleteInterpolating ((fun x : ℝ ↦ x + 1 / 2) '' logExample) := by
  obtain ⟨E, hHB, h0, hEPW, hcomp, hzero, φ, hφ⟩ := exists_E_logExample hPW
  exact sampling_cis_of_zero_set hPW hE hHB h0 hEPW hφ hcomp hzero

/-- **The example of p. 798**: `{k + log⁺|k|}` is a complete interpolating sequence. -/
theorem logExample_isCompleteInterpolating (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsCompleteInterpolating logExample :=
  isCompleteInterpolating_of_image_add (1 / 2) (logExample_shift_sampling_cis hPW hE).2

theorem logExample_isSampling (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsSampling logExample :=
  isSampling_of_image_add (1 / 2) (logExample_shift_sampling_cis hPW hE).1

theorem finite_logExample_inter_Ioc_pos (R : ℝ) : (logExample ∩ Ioc 0 R).Finite := by
  refine ((Set.finite_Icc (1 : ℤ) ⌈R⌉).image logLam).subset ?_
  rintro _ ⟨⟨k, rfl⟩, h0, hR⟩
  have hk := (logLam_pos_iff k).1 h0
  refine ⟨k, ⟨hk, ?_⟩, rfl⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hR : logLam k ≤ R := hR
  rw [logLam_of_one_le hk] at hR
  have := Real.log_nonneg hk1
  have : (k : ℝ) ≤ R := by linarith
  exact_mod_cast this.trans (Int.le_ceil R)

/-- **Landau's inequality is best possible** (p. 798): `{k + log⁺|k|}` is a separated sampling
sequence for which the logarithmic term cannot be removed. -/
theorem landau_sharp (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsSeparated logExample ∧ IsSampling logExample ∧
      ∀ A : ℝ, A < 1 → ¬ ∃ B : ℝ, ∀ a b : ℝ, a < b →
        ENNReal.ofReal (b - a - A * Real.posLog (b - a) - B) ≤
          ((logExample ∩ Ioc a b).encard : ℝ≥0∞) := by
  refine ⟨logExample_isSeparated, logExample_isSampling hPW hE, ?_⟩
  intro A hA ⟨B, hB⟩
  obtain ⟨C, hC⟩ := logExample_count
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 1 le_rfl).1
  have h1A : 0 < 1 - A := by linarith
  set x : ℝ := (|B| + C + 1) / (1 - A) + 1 with hx
  have hxpos : 1 ≤ x := by
    have : 0 ≤ (|B| + C + 1) / (1 - A) := by positivity
    linarith
  have hxA : |B| + C + 1 < (1 - A) * x := by
    have : (1 - A) * ((|B| + C + 1) / (1 - A)) = |B| + C + 1 := by field_simp
    rw [hx]; nlinarith
  set R : ℝ := Real.exp x with hRdef
  have hRge : 1 ≤ R := by rw [hRdef]; exact Real.one_le_exp (by linarith)
  have hlogR : Real.log R = x := Real.log_exp x
  have hpl : Real.posLog R = x := by
    rw [Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; exact hRge), hlogR]
  have h := hB 0 R (by linarith)
  rw [sub_zero, hpl, ← Set.Finite.cast_ncard_eq (finite_logExample_inter_Ioc_pos R)] at h
  have h2 : R - A * x - B ≤ ((logExample ∩ Ioc 0 R).ncard : ℝ) := by
    have h' : ENNReal.ofReal (R - A * x - B) ≤ ((logExample ∩ Ioc 0 R).ncard : ℝ≥0∞) := by
      simpa using h
    have := (ENNReal.ofReal_le_iff_le_toReal (by simp)).1 h'
    simpa using this
  have h3 := (hC R hRge).1
  rw [abs_le] at h3
  rw [hlogR] at h3
  have : |B| ≥ B := le_abs_self B
  nlinarith [h3.2]

end FF
