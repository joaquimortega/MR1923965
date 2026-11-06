import FourierFrames.Construction
import FourierFrames.LogExample.Basic
import FourierFrames.LogExample.Phase
import FourierFrames.LogExample.Potential
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
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  wlog hxy : x ≤ y generalizing x y with H
  · rw [dist_comm, dist_comm x y]; exact H y x (le_of_not_ge hxy)
  obtain ⟨h1, h2⟩ := OCS.multPrim_sub_bounds isMultWeight_logDensity hxy
  rw [Real.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonpos (by linarith : x - y ≤ 0), abs_le]
  unfold logW
  push_cast
  constructor <;> nlinarith

theorem abs_log_sub_log_le {a b c : ℝ} (hc : 1 ≤ c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / c := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]; exact this hb ha (le_of_not_ge hab)
  have hb0 : 0 < b := by linarith
  have h1 : Real.log a - Real.log b = Real.log (a / b) := (Real.log_div (by linarith) hb0.ne').symm
  have h2 : 0 ≤ Real.log (a / b) := Real.log_nonneg ((one_le_div hb0).2 hab)
  have h3 := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < a) hb0)
  rw [h1, abs_of_nonneg h2, abs_of_nonneg (by linarith)]
  calc Real.log (a / b) ≤ a / b - 1 := h3
    _ = (a - b) / b := by field_simp
    _ ≤ (a - b) / c := div_le_div_of_nonneg_left (by linarith) (by linarith) hb

theorem abs_posLog_abs_sub_le {x y c : ℝ} (hc : 1 ≤ c) (hx : c ≤ |x|) (hy : c ≤ |y|) :
    |(Real.posLog |x| - Real.posLog |y|)| ≤ |x - y| / c := by
  have hx1 : Real.posLog |x| = Real.log |x| := Real.posLog_eq_log (by rw [abs_abs]; linarith)
  have hy1 : Real.posLog |y| = Real.log |y| := Real.posLog_eq_log (by rw [abs_abs]; linarith)
  rw [hx1, hy1]
  refine (abs_log_sub_log_le hc hx hy).trans ?_
  exact div_le_div_of_nonneg_right (abs_abs_sub_abs_le_abs_sub x y) (by linarith)

theorem logW_logPt (j : ℤ) :
    logW (logPt j) = -(Real.posLog |((j : ℝ) - 1)| + Real.posLog |(j : ℝ)|) / 2 := by
  unfold logW
  rw [multPrim_logDensity_logPt]
  unfold logPt logLam
  push_cast
  ring

theorem abs_logW_sub_le {s t D : ℝ} (h : ∀ u ∈ Set.uIcc s t, |logDensity u - 1| ≤ D) :
    |logW t - logW s| ≤ D * |t - s| := by
  have h1 : logW t - logW s = ∫ u in s..t, (logDensity u - 1) := by
    unfold logW
    rw [intervalIntegral.integral_sub (isMultWeight_logDensity.intervalIntegrable s t)
      intervalIntegrable_const, ← OCS.multPrim_sub_eq isMultWeight_logDensity]
    simp; ring
  rw [h1, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun u hu ↦ ?_)
  rw [Real.norm_eq_abs]
  exact h u (Set.uIoc_subset_uIcc hu)

theorem abs_logW_le (t : ℝ) : |logW t| ≤ 19 * |t| := by
  have := logW_lipschitz.dist_le_mul t 0
  have h0 : logW 0 = 0 := by simp [logW, OCS.multPrim_zero]
  simpa [Real.dist_eq, h0] using this

theorem logPt_sub_logPt_le (j : ℤ) : logPt (j + 1) - logPt j ≤ 17 / 10 := by
  rw [logPt_succ_sub]
  have := (logGap_bounds (j - 1)).2
  have := (logGap_bounds j).2
  linarith

/-- `δ_j = p_j - j`. -/
theorem logPt_sub_int (j : ℤ) :
    logPt j - j = (Real.posLog |((j : ℝ) - 1)| + Real.posLog |(j : ℝ)|) / 2 := by
  unfold logPt logLam
  push_cast
  ring

theorem log_two_add_le {J : ℝ} (hJ : 0 ≤ J) : Real.log (2 + J) ≤ J / 4 + 9 / 10 := by
  have h4 : Real.log 4 < 7 / 5 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := LogEx.log_two_lt
    linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < (2 + J) / 4 by positivity)
  have : Real.log ((2 + J) / 4) = Real.log (2 + J) - Real.log 4 := Real.log_div (by positivity) (by norm_num)
  linarith

theorem posLog_abs_le_log {x J : ℝ} (hx : |x| ≤ J + 1) : Real.posLog |x| ≤ Real.log (2 + J) := by
  have h1 : Real.posLog |x| ≤ Real.log (1 + |x|) := Real.posLog_le_log_one_add (abs_nonneg x)
  exact h1.trans (Real.log_le_log (by positivity) (by linarith))


theorem rho_big {j : ℤ} (hj : 7 ≤ |(j : ℝ)|) {t : ℝ} (ht : t ∈ Ico (logPt j) (logPt (j + 1))) :
    |(logW t + Real.posLog |t|)| ≤ (7488 + 2 * Real.log (2 + |(j : ℝ)|)) / |(j : ℝ)| := by
  set J : ℝ := |(j : ℝ)| with hJ
  have hJ0 : 0 < J := by linarith
  set L : ℝ := Real.log (2 + J) with hL
  have hLle : L ≤ J / 4 + 9 / 10 := log_two_add_le hJ0.le
  have hj1 : |((j : ℝ) - 1)| ≤ J + 1 := by
    have := abs_sub (j : ℝ) 1
    simpa [hJ] using this
  have hδ := logPt_sub_int j
  have ha0 := Real.posLog_nonneg (x := |((j : ℝ) - 1)|)
  have hb0 := Real.posLog_nonneg (x := |(j : ℝ)|)
  have ha1 : Real.posLog |((j : ℝ) - 1)| ≤ L := posLog_abs_le_log hj1
  have hb1 : Real.posLog |(j : ℝ)| ≤ L := posLog_abs_le_log (by linarith)
  set δ : ℝ := logPt j - j with hδdef
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hδ1 : δ ≤ L := by rw [hδ]; linarith
  -- size of `p_j`
  have hp : J / 2 ≤ |logPt j| := by
    have e : logPt j = j + δ := by rw [hδdef]; ring
    rcases le_or_gt 0 (j : ℝ) with h | h
    · rw [e, abs_of_nonneg (by linarith)]
      have : J = j := by rw [hJ, abs_of_nonneg h]
      linarith
    · have : J = -j := by rw [hJ, abs_of_neg h]
      rw [e, abs_of_nonpos (by linarith)]
      linarith
  have hd : 0 ≤ t - logPt j ∧ t - logPt j ≤ 17 / 10 := by
    have := logPt_sub_logPt_le j
    constructor <;> linarith [ht.1, ht.2]
  have hJ7 : 7 ≤ J := hj
  -- the three terms
  have T1 : |logW t - logW (logPt j)| ≤ 7480 / J := by
    have hmid : ∀ u ∈ Set.uIcc (logPt j) t, |logDensity u - 1| ≤ 4400 / J := by
      intro u hu
      rw [Set.uIcc_of_le (by linarith [hd.1])] at hu
      have hu1 : J / 4 ≤ |u| := by
        have : |logPt j| ≤ |u| + |u - logPt j| := by
          have := abs_sub_abs_le_abs_sub (logPt j) u
          rw [abs_sub_comm] at this
          have h2 := abs_sub_comm u (logPt j)
          linarith [abs_sub_abs_le_abs_sub (logPt j) u]
        have h3 : |u - logPt j| ≤ 17 / 10 := by
          rw [abs_of_nonneg (by linarith [hu.1])]; linarith [hu.2]
        linarith
      refine (abs_logDensity_sub_one_le u).trans ?_
      rw [div_le_div_iff₀ (by positivity) hJ0]
      nlinarith [abs_nonneg u]
    have := abs_logW_sub_le hmid
    rw [abs_of_nonneg hd.1] at this
    calc _ ≤ 4400 / J * (t - logPt j) := this
      _ ≤ 4400 / J * (17 / 10) := by gcongr; exact hd.2
      _ = 7480 / J := by ring
  have T3 : |(Real.posLog |t| - Real.posLog |logPt j|)| ≤ 68 / 10 / J := by
    have ht1 : J / 4 ≤ |t| := by
      have h3 : |t - logPt j| ≤ 17 / 10 := by
        rw [abs_of_nonneg hd.1]; exact hd.2
      have := abs_sub_abs_le_abs_sub (logPt j) t
      rw [abs_sub_comm] at this
      linarith [abs_sub_comm t (logPt j)]
    have := abs_posLog_abs_sub_le (x := t) (y := logPt j) (c := J / 4) (by linarith) ht1
      (by linarith)
    refine this.trans ?_
    rw [abs_of_nonneg hd.1]
    rw [div_le_div_iff₀ (by positivity) hJ0]
    nlinarith
  have T2 : |(Real.posLog |logPt j| + logW (logPt j))| ≤ (2 * L + 1) / J := by
    rw [logW_logPt]
    have h1 := abs_posLog_abs_sub_le (x := logPt j) (y := (j : ℝ)) (c := J / 2) (by linarith) hp
      (by rw [← hJ]; linarith)
    have h2 := abs_posLog_abs_sub_le (x := (j : ℝ)) (y := (j : ℝ) - 1) (c := J - 1) (by linarith)
      (by rw [← hJ]; linarith) (by
        have := abs_sub_abs_le_abs_sub (j : ℝ) 1
        have h5 := abs_sub_abs_le_abs_sub (j : ℝ) ((j : ℝ) - 1)
        have : |(j : ℝ)| - 1 ≤ |(j : ℝ) - 1| := by
          have := abs_sub_abs_le_abs_sub (1 : ℝ) (-(j : ℝ) + 1 - 1 + 0)
          have h6 : |(j : ℝ)| ≤ |(j : ℝ) - 1| + 1 := by
            have := abs_add_le ((j : ℝ) - 1) 1
            simpa using this
          linarith
        linarith)
    have e1 : logPt j - (j : ℝ) = δ := rfl
    rw [e1] at h1
    rw [abs_of_nonneg hδ0] at h1
    have h1' : |(Real.posLog |logPt j| - Real.posLog |(j : ℝ)|)| ≤ 2 * L / J := by
      refine h1.trans ?_
      rw [div_le_div_iff₀ (by positivity) hJ0]
      nlinarith
    have h2' : |(Real.posLog |(j : ℝ)| - Real.posLog |((j : ℝ) - 1)|)| ≤ 2 / J := by
      refine h2.trans ?_
      have : |(j : ℝ) - ((j : ℝ) - 1)| = 1 := by simp
      rw [this, div_le_div_iff₀ (by linarith) hJ0]
      linarith
    have hsplit : Real.posLog |logPt j| + -(Real.posLog |((j : ℝ) - 1)| + Real.posLog |(j : ℝ)|) / 2 =
        (Real.posLog |logPt j| - Real.posLog |(j : ℝ)|) +
          (Real.posLog |(j : ℝ)| - Real.posLog |((j : ℝ) - 1)|) / 2 := by ring
    rw [hsplit]
    calc _ ≤ |(Real.posLog |logPt j| - Real.posLog |(j : ℝ)|)| +
          |(Real.posLog |(j : ℝ)| - Real.posLog |((j : ℝ) - 1)|) / 2| := abs_add_le _ _
      _ ≤ 2 * L / J + (2 / J) / 2 := by
          gcongr
          rw [abs_div, abs_two]
          gcongr
      _ = (2 * L + 1) / J := by ring
  have hsum : logW t + Real.posLog |t| = (logW t - logW (logPt j)) +
      (Real.posLog |logPt j| + logW (logPt j)) + (Real.posLog |t| - Real.posLog |logPt j|) := by ring
  rw [hsum]
  calc _ ≤ |(logW t - logW (logPt j)) + (Real.posLog |logPt j| + logW (logPt j))| +
        |(Real.posLog |t| - Real.posLog |logPt j|)| := abs_add_le _ _
    _ ≤ |logW t - logW (logPt j)| + |(Real.posLog |logPt j| + logW (logPt j))| +
        |(Real.posLog |t| - Real.posLog |logPt j|)| := by
          gcongr; exact abs_add_le _ _
    _ ≤ 7480 / J + (2 * L + 1) / J + 68 / 10 / J := by gcongr
    _ = (7488 + 2 * L) / J - 1 / 5 / J := by ring
    _ ≤ (7488 + 2 * L) / J := by
        have : 0 ≤ 1 / 5 / J := by positivity
        linarith


theorem log_le_two_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hy)
  have h2 : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy.le
  linarith


/-- `W(t) = -log⁺|t| + ρ(t)` with `|ρ(t)| ≤ C_ρ min(|t|, (1+|t|)^{-1/2})`. -/
theorem abs_logW_add_posLog_le : ∃ Cρ : ℝ, ∀ t : ℝ,
    |logW t + Real.posLog (|t|)| ≤ Cρ * min |t| (1 / Real.sqrt (1 + |t|)) := by
  refine ⟨8000, fun t ↦ ?_⟩
  have hq0 : 0 < Real.sqrt (1 + |t|) := Real.sqrt_pos.2 (by positivity)
  set q : ℝ := Real.sqrt (1 + |t|) with hq
  have hq2 : q ^ 2 = 1 + |t| := Real.sq_sqrt (by positivity)
  rcases le_or_gt |t| 1 with h1 | h1
  · -- small `t`
    have hp : Real.posLog |t| = 0 := by
      rw [Real.posLog_abs]; exact (Real.posLog_eq_zero_iff t).2 h1
    rw [hp, add_zero]
    have hq1 : q ≤ 2 := by nlinarith [abs_nonneg t]
    have hmin : |t| / 2 ≤ min |t| (1 / q) := by
      refine le_min (by linarith [abs_nonneg t]) ?_
      rw [le_div_iff₀ hq0]; nlinarith [abs_nonneg t]
    calc |logW t| ≤ 19 * |t| := abs_logW_le t
      _ ≤ 8000 * (|t| / 2) := by nlinarith [abs_nonneg t]
      _ ≤ _ := by gcongr
  · have hmin : min |t| (1 / q) = 1 / q := by
      refine min_eq_right ?_
      have : 1 / q ≤ 1 := by
        rw [div_le_one hq0]; nlinarith
      linarith
    rw [hmin, mul_one_div, le_div_iff₀ hq0]
    obtain ⟨hj1, hj2⟩ := logIdx_spec t
    set j := logIdx t with hj
    have ht : t ∈ Ico (logPt j) (logPt (j + 1)) := ⟨hj1, hj2⟩
    have h5 := one_add_abs_le_of_mem ht
    rcases le_or_gt 7 |(j : ℝ)| with hJ | hJ
    · have hb := rho_big hJ ht
      set J : ℝ := |(j : ℝ)| with hJdef
      have hJ0 : 0 < J := by linarith
      set s : ℝ := Real.sqrt J with hs
      have hs0 : 0 < s := Real.sqrt_pos.2 hJ0
      have hs2 : s ^ 2 = J := Real.sq_sqrt hJ0.le
      have hs26 : 2.6 ≤ s := by nlinarith
      have hqs : q ≤ 5 / 2 * s := by nlinarith
      have hL : Real.log (2 + J) ≤ 3 * s := by
        have h1 := log_le_two_sqrt (show 0 < 2 + J by linarith)
        have hr0 : 0 ≤ Real.sqrt (2 + J) := Real.sqrt_nonneg _
        have hr2 : Real.sqrt (2 + J) ^ 2 = 2 + J := Real.sq_sqrt (by linarith)
        have : Real.sqrt (2 + J) ≤ 3 / 2 * s := by nlinarith
        linarith
      calc |(logW t + Real.posLog |t|)| * q ≤ ((7488 + 2 * Real.log (2 + J)) / J) * q :=
            mul_le_mul_of_nonneg_right hb hq0.le
        _ ≤ ((7488 + 6 * s) / s ^ 2) * (5 / 2 * s) := by
            have hL0 := Real.log_nonneg (show (1:ℝ) ≤ 2 + J by linarith)
            rw [hs2]
            have hn : 7488 + 2 * Real.log (2 + J) ≤ 7488 + 6 * s := by linarith
            rw [← hs2] at hn ⊢
            exact mul_le_mul (div_le_div_of_nonneg_right hn (by positivity)) hqs hq0.le (by positivity)
        _ = (7488 + 6 * s) * (5 / 2) / s := by field_simp
        _ ≤ 8000 := by
            rw [div_le_iff₀ hs0]; nlinarith
    · have hJ' : |(j : ℝ)| ≤ 7 := hJ.le
      have hq35 : q ≤ 7 := by nlinarith [abs_nonneg (j : ℝ)]
      have ht' : |t| ≤ 39 := by linarith
      have h1 := abs_logW_le t
      have h2 : Real.posLog |t| ≤ |t| := by
        have := Real.posLog_le_abs |t|
        rwa [abs_abs] at this
      have : |(logW t + Real.posLog |t|)| ≤ 20 * |t| := by
        calc _ ≤ |logW t| + abs (Real.posLog |t|) := abs_add_le _ _
          _ ≤ 19 * |t| + |t| := by
              rw [abs_of_nonneg (Real.posLog_nonneg (x := |t|))]; linarith
          _ = 20 * |t| := by ring
      calc |(logW t + Real.posLog |t|)| * q ≤ (20 * 39) * 7 :=
            mul_le_mul (this.trans (by linarith)) hq35 hq0.le (by norm_num)
        _ ≤ 8000 := by norm_num

/-- `κ = ∫_{|t|>1} (m(t) - 1)/t dt` (absolutely convergent). -/
def logKappa : ℝ :=
  ∫ t : ℝ, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((logDensity t - 1) / t)

theorem integrable_logKappa :
    Integrable (fun t : ℝ ↦ (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((logDensity t - 1) / t)) := by
  have hmeas : Measurable (fun t : ℝ ↦ (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((logDensity t - 1) / t)) :=
    (measurable_const.sub (measurable_one.indicator measurableSet_Icc)).mul
      ((measurable_logDensity.sub measurable_const).div measurable_id)
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 2200) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ↦ ?_)
  by_cases h : t ∈ Icc (-1 : ℝ) 1
  · simp [Set.indicator_of_mem h]; positivity
  · rw [Set.indicator_of_notMem h]
    have ht : 1 < |t| := by
      simp only [mem_Icc, not_and_or, not_le] at h
      rcases h with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    have h1 := abs_logDensity_sub_one_le t
    have htp : 0 < |t| := by linarith
    rw [sub_zero, one_mul, Real.norm_eq_abs, abs_div]
    calc |logDensity t - 1| / |t| ≤ (1100 / (1 + |t|)) / |t| := by gcongr
      _ ≤ 2200 * (1 + t ^ 2)⁻¹ := by
        have e : 2200 * (1 + t ^ 2)⁻¹ = 2200 / (1 + t ^ 2) := by ring
        rw [div_div, e, div_le_div_iff₀ (by positivity) (by positivity)]
        have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
        rw [this]
        nlinarith [sq_nonneg (|t| - 1)]

/-- The model computation: for `m ≡ 1`, `U(z) = π |Im z|`. -/
theorem multU_model {z : ℂ} (hz : 0 < z.im) :
    ∫ t : ℝ, OCS.multUIntegrand (fun _ ↦ 1) z t = Real.pi * z.im := by
  set f := OCS.multUIntegrand (fun _ ↦ (1 : ℝ)) z with hf
  have hint : Integrable f :=
    OCS.integrable_multUIntegrand (a := 1) (b := 1)
      ⟨measurable_const, one_pos, fun _ ↦ le_rfl, fun _ ↦ le_rfl⟩ z
  have hlim := intervalIntegral_tendsto_integral hint (tendsto_neg_atTop_atBot (G := ℝ)) tendsto_id
  have hlim2 : Tendsto (fun R : ℝ ↦ ∫ t in (-R)..R, f t) atTop (𝓝 (Real.pi * z.im)) := by
    refine (LogEx.tendsto_integral_log_norm_sub (x := z.re) hz).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    have hφ1 : ∀ t : ℝ, Real.log ‖(t : ℂ) - z‖ = Real.log ((t - z.re) ^ 2 + z.im ^ 2) / 2 := by
      intro t
      have h := OCS.norm_ofReal_sub_sq z t
      rw [norm_sub_rev] at h
      rw [← h, Real.log_pow]; push_cast; ring
    have hD : ∀ t : ℝ, 0 < (t - z.re) ^ 2 + z.im ^ 2 := fun t ↦ by positivity
    have i1 : IntervalIntegrable (fun t : ℝ ↦ Real.log ‖(t : ℂ) - z‖) volume (-R) R :=
      OCS.intervalIntegrable_log_norm_sub z (-R) R
    have i2 : IntervalIntegrable (fun t : ℝ ↦ Real.log ‖(t : ℂ) - 0‖) volume (-R) R :=
      OCS.intervalIntegrable_log_norm_sub 0 (-R) R
    have i3 : IntervalIntegrable (fun t : ℝ ↦ (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹) volume
        (-R) R := OCS.intervalIntegrable_one_sub_indicator_mul_inv (-R) R
    have h1 : ∫ t in (-R)..R, f t = ∫ t in (-R)..R, ((Real.log ‖(t : ℂ) - z‖ -
        Real.log ‖(t : ℂ) - 0‖) + z.re * ((1 - (Icc (-1 : ℝ) 1).indicator 1 t) * t⁻¹)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [OCS.multUIntegrand_ae_eq (m := fun _ ↦ (1 : ℝ)) z] with t ht _
      rw [hf]; refine ht.trans ?_; ring
    rw [h1, intervalIntegral.integral_add (i1.sub i2) (i3.const_mul _),
      intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
      LogEx.integral_oddpart, mul_zero, add_zero]
    have h2 : ∫ t in (-R)..R, Real.log ‖(t : ℂ) - z‖ =
        (LogEx.logPrimD z.re z.im R - LogEx.logPrimD z.re z.im (-R)) / 2 := by
      have : ∫ t in (-R)..R, Real.log ‖(t : ℂ) - z‖ =
          ∫ t in (-R)..R, (Real.log ((t - z.re) ^ 2 + z.im ^ 2) / 2) :=
        intervalIntegral.integral_congr fun t _ ↦ hφ1 t
      have hcont : Continuous (fun t : ℝ ↦ Real.log ((t - z.re) ^ 2 + z.im ^ 2)) :=
        Continuous.log (by fun_prop) (fun t ↦ (hD t).ne')
      rw [this, intervalIntegral.integral_div,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ LogEx.hasDerivAt_logPrimD hz t)
          (hcont.intervalIntegrable _ _)]
    have h3 : ∫ t in (-R)..R, Real.log ‖(t : ℂ) - 0‖ = 2 * R * Real.log R - 2 * R := by
      have : ∫ t in (-R)..R, Real.log ‖(t : ℂ) - 0‖ = ∫ t in (-R)..R, Real.log t := by
        apply intervalIntegral.integral_congr
        intro t _
        simp [Real.log_abs]
      rw [this, integral_log, Real.log_neg_eq_log]; ring
    rw [h2, h3]
  exact tendsto_nhds_unique hlim hlim2

theorem integrable_log_mul_sub_one {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ ↦ Real.log ‖1 - z / t‖ * (logDensity t - 1)) := by
  have _ := hz  -- (the hypothesis is not needed; the statement holds for all `z`)
  have h1 := OCS.integrable_multUIntegrand isMultWeight_logDensity z
  have h2 : Integrable (OCS.multUIntegrand (fun _ ↦ 1) z) :=
    OCS.integrable_multUIntegrand (a := 1) (b := 1)
      ⟨measurable_const, one_pos, fun _ ↦ le_rfl, fun _ ↦ le_rfl⟩ z
  have h3 := integrable_logKappa.const_mul z.re
  refine ((h1.sub h2).sub h3).congr (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [Pi.sub_apply]
  unfold OCS.multUIntegrand
  rw [Complex.div_ofReal_re]
  ring

/-- `U(z) = π Im z + κ Re z + V(z)` for `Im z > 0`, `V(z) = ∫ log|1 - z/t| (m(t) - 1) dt`. -/
theorem multU_logDensity_eq {z : ℂ} (hz : 0 < z.im) :
    OCS.multU logDensity 0 z = Real.pi * z.im + logKappa * z.re +
      ∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1) := by
  have hpt : ∀ t : ℝ, OCS.multUIntegrand logDensity z t = OCS.multUIntegrand (fun _ ↦ 1) z t +
      (Real.log ‖1 - z / t‖ * (logDensity t - 1) +
        z.re * ((1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((logDensity t - 1) / t))) := by
    intro t
    unfold OCS.multUIntegrand
    rw [Complex.div_ofReal_re]
    ring
  have h1 : Integrable (OCS.multUIntegrand (fun _ ↦ 1) z) :=
    OCS.integrable_multUIntegrand (a := 1) (b := 1) ⟨measurable_const, one_pos, fun _ ↦ le_rfl, fun _ ↦ le_rfl⟩ z
  have h2 := integrable_log_mul_sub_one hz
  have h3 := integrable_logKappa.const_mul z.re
  rw [OCS.multU_eq]
  simp_rw [hpt]
  have h23 : Integrable (fun t : ℝ ↦ Real.log ‖1 - z / t‖ * (logDensity t - 1) +
      z.re * ((1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((logDensity t - 1) / t))) := h2.add h3
  rw [integral_add h1 h23, integral_add h2 h3, integral_const_mul, multU_model hz,
    logKappa]
  ring

/-- The kernel `K_z(t) = (t - x)/((t - x)² + y²) - 1/t = Re(z / (t (t - z)))`. -/
def logKernel (z : ℂ) (t : ℝ) : ℝ := (t - z.re) / ((t - z.re) ^ 2 + z.im ^ 2) - 1 / t

theorem abs_logKernel_le {z : ℂ} (hz : 0 < z.im) {t : ℝ} (ht : t ≠ 0) :
    |logKernel z t| ≤ ‖z‖ / (|t| * ‖(t : ℂ) - z‖) := by
  have htz : (t : ℂ) - z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this; linarith
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have e1 : (1 / ((t : ℂ) - z)).re = (t - z.re) / ((t - z.re) ^ 2 + z.im ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]; simp; ring_nf
  have e2 : (1 / (t : ℂ)).re = 1 / t := by
    simp
  have e3 : logKernel z t = (z / ((t : ℂ) * ((t : ℂ) - z))).re := by
    have : z / ((t : ℂ) * ((t : ℂ) - z)) = 1 / ((t : ℂ) - z) - 1 / (t : ℂ) := by
      field_simp; ring
    rw [this, Complex.sub_re, e1, e2]; rfl
  rw [e3]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The breakpoints of the step density `m`. -/
def logBreak : Set ℝ := Set.range logPt ∪ Set.range logBary

theorem countable_logBreak : logBreak.Countable :=
  (Set.countable_range _).union (Set.countable_range _)

theorem continuousAt_logDensity {t : ℝ} (ht : t ∉ logBreak) : ContinuousAt logDensity t := by
  obtain ⟨h1, h2⟩ := logIdx_spec t
  set j := logIdx t with hj
  have hne1 : t ≠ logPt j := fun h ↦ ht (Or.inl ⟨j, h.symm⟩)
  have hne2 : t ≠ logBary j := fun h ↦ ht (Or.inr ⟨j, h.symm⟩)
  have hp1 : logPt j < t := lt_of_le_of_ne h1 (Ne.symm hne1)
  rcases lt_or_gt_of_ne hne2 with h | h
  · have : logDensity =ᶠ[𝓝 t] fun _ ↦ logWeightL j := by
      filter_upwards [Ioo_mem_nhds hp1 h] with x hx
      exact logDensity_of_Ico_left hx.1.le hx.2
    exact continuousAt_const.congr this.symm
  · have : logDensity =ᶠ[𝓝 t] fun _ ↦ logWeightR j := by
      filter_upwards [Ioo_mem_nhds h h2] with x hx
      exact logDensity_of_Ico_right hx.1.le hx.2
    exact continuousAt_const.congr this.symm

theorem hasDerivAt_logW {t : ℝ} (ht : t ∉ logBreak) : HasDerivAt logW (logDensity t - 1) t := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (isMultWeight_logDensity.intervalIntegrable 0 t)
    measurable_logDensity.stronglyMeasurable.stronglyMeasurableAtFilter
    (continuousAt_logDensity ht)
  exact h.sub (hasDerivAt_id' t)


theorem log_norm_one_sub_div_eq {z : ℂ} (hy : 0 < z.im) {t : ℝ} (ht : t ≠ 0) :
    Real.log ‖1 - z / t‖ = LogEx.phiK z t := by
  have hz1 : (t : ℂ) ≠ z := fun h ↦ by
    have := congrArg Complex.im h
    simp at this; linarith
  rw [OCS.log_norm_one_sub_div z ht hz1]
  have h := OCS.norm_ofReal_sub_sq z t
  rw [norm_sub_rev] at h
  have h1 : Real.log ‖(t : ℂ) - z‖ = Real.log ((t - z.re) ^ 2 + z.im ^ 2) / 2 := by
    rw [← h, Real.log_pow]; push_cast; ring
  unfold LogEx.phiK
  rw [h1, sub_zero, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]

theorem hasDerivAt_log_norm_one_sub_div {z : ℂ} (hy : 0 < z.im) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ Real.log ‖1 - z / s‖) (LogEx.kern z t) t := by
  refine (LogEx.hasDerivAt_phi hy ht).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds ht] with s hs
  exact log_norm_one_sub_div_eq hy hs

theorem abs_logW_le_sqrt : ∃ c : ℝ, 0 ≤ c ∧ ∀ t : ℝ, |logW t| ≤ c * |t| ∧
    |logW t| ≤ c * (1 + |t|) ^ (1 / 2 : ℝ) := by
  obtain ⟨Cρ, hρ⟩ := abs_logW_add_posLog_le
  have hC0 : 0 ≤ Cρ := by
    have h := hρ 1
    simp only [abs_one] at h
    have hm : 0 < min (1 : ℝ) (1 / Real.sqrt (1 + 1)) := lt_min one_pos (by positivity)
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hm
    linarith [abs_nonneg (logW 1 + Real.posLog 1)]
  refine ⟨19 + Cρ + 2, by positivity, fun t ↦ ⟨?_, ?_⟩⟩
  · have := abs_logW_le t
    nlinarith [abs_nonneg t]
  · have h1 := hρ t
    have h2 : min |t| (1 / Real.sqrt (1 + |t|)) ≤ 1 := by
      refine (min_le_right _ _).trans ?_
      rw [div_le_one (Real.sqrt_pos.2 (by positivity))]
      exact Real.one_le_sqrt.2 (by linarith [abs_nonneg t])
    have h3 : Real.posLog |t| ≤ 2 * Real.sqrt (1 + |t|) := by
      have h1 := Real.posLog_le_log_one_add (abs_nonneg t)
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (show 0 < 1 + |t| by positivity))
      have h' : Real.log (Real.sqrt (1 + |t|)) = Real.log (1 + |t|) / 2 :=
        Real.log_sqrt (by positivity)
      linarith [Real.sqrt_nonneg (1 + |t|)]
    have h4 : 1 ≤ Real.sqrt (1 + |t|) := Real.one_le_sqrt.2 (by linarith [abs_nonneg t])
    rw [← Real.sqrt_eq_rpow]
    have h5 : |logW t| ≤ abs (logW t + Real.posLog |t|) + Real.posLog |t| := by
      have := abs_sub (logW t + Real.posLog |t|) (Real.posLog |t|)
      rw [add_sub_cancel_right, abs_of_nonneg (Real.posLog_nonneg (x := |t|))] at this
      exact this
    nlinarith [mul_le_mul_of_nonneg_left h2 hC0]

theorem integrable_kern_mul_logW {z : ℂ} (hy : 0 < z.im) :
    Integrable (fun t : ℝ ↦ logW t * LogEx.kern z t) := by
  obtain ⟨c, hc, hb⟩ := abs_logW_le_sqrt
  exact LogEx.integrable_mul_kern hy logW_lipschitz.continuous.aestronglyMeasurable hc
    (fun t ↦ (hb t).1) (fun t ↦ (hb t).2)

theorem continuous_Psi {z : ℂ} (hy : 0 < z.im) :
    Continuous (fun t : ℝ ↦ Real.log ‖1 - z / t‖ * logW t) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t = 0
  · subst ht
    -- continuity at `0`
    set g : ℝ → ℝ := fun s ↦ s * Real.log ((s - z.re) ^ 2 + z.im ^ 2) / 2 - s * Real.log s with hg
    have hgc : Continuous g := by
      have h1 : Continuous fun s : ℝ ↦ s * Real.log ((s - z.re) ^ 2 + z.im ^ 2) :=
        continuous_id.mul (Continuous.log (by fun_prop) (fun s ↦ by positivity))
      exact (h1.div_const 2).sub Real.continuous_mul_log
    have hg0 : g 0 = 0 := by simp [hg]
    have hbound : ∀ s : ℝ, ‖Real.log ‖1 - z / s‖ * logW s‖ ≤ 19 * ‖g s‖ := by
      intro s
      by_cases hs : s = 0
      · subst hs; simp [logW, OCS.multPrim_zero]
      · have h1 : s * Real.log ‖1 - z / s‖ = g s := by
          rw [log_norm_one_sub_div_eq hy hs]; simp only [hg, LogEx.phiK]; ring
        rw [Real.norm_eq_abs, abs_mul]
        have h2 := abs_logW_le s
        have h3 : |Real.log ‖1 - z / s‖| * |s| = ‖g s‖ := by
          rw [← h1, Real.norm_eq_abs, abs_mul, mul_comm]
        calc |Real.log ‖1 - z / s‖| * |logW s| ≤ |Real.log ‖1 - z / s‖| * (19 * |s|) :=
              mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
          _ = 19 * (|Real.log ‖1 - z / s‖| * |s|) := by ring
          _ = 19 * ‖g s‖ := by rw [h3]
    have hlim : Tendsto (fun s : ℝ ↦ Real.log ‖1 - z / s‖ * logW s) (𝓝 0) (𝓝 0) := by
      refine squeeze_zero_norm hbound ?_
      have := (hgc.norm.tendsto 0).const_mul 19
      simpa [hg0] using this
    have h0 : Real.log ‖1 - z / ((0 : ℝ) : ℂ)‖ * logW 0 = 0 := by simp [logW, OCS.multPrim_zero]
    show Tendsto _ _ (𝓝 (Real.log ‖1 - z / ((0 : ℝ) : ℂ)‖ * logW 0))
    rw [h0]; exact hlim
  · exact ((hasDerivAt_log_norm_one_sub_div hy ht).continuousAt).mul
      logW_lipschitz.continuous.continuousAt

/-- The integrand of the integration by parts. -/
noncomputable def ibpDeriv (z : ℂ) (t : ℝ) : ℝ :=
  LogEx.kern z t * logW t + Real.log ‖1 - z / t‖ * (logDensity t - 1)

theorem integrable_ibpDeriv {z : ℂ} (hy : 0 < z.im) : Integrable (ibpDeriv z) := by
  have h1 := integrable_kern_mul_logW hy
  have h2 := integrable_log_mul_sub_one hy
  have h3 : Integrable (fun t : ℝ ↦ LogEx.kern z t * logW t) :=
    h1.congr (Filter.Eventually.of_forall fun t ↦ mul_comm _ _)
  exact h3.add h2

theorem ftc_Psi {z : ℂ} (hy : 0 < z.im) {R : ℝ} (hR : 0 < R) :
    ∫ t in (-R)..R, ibpDeriv z t =
      Real.log ‖1 - z / R‖ * logW R - Real.log ‖1 - z / ((-R : ℝ) : ℂ)‖ * logW (-R) := by
  have hcount : (logBreak ∪ {0}).Countable := countable_logBreak.union (Set.countable_singleton 0)
  have := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t : ℝ ↦ Real.log ‖1 - z / t‖ * logW t) (ibpDeriv z) (by linarith : -R ≤ R) hcount
    (continuous_Psi hy).continuousOn (fun t ht ↦ ?_)
    ((integrable_ibpDeriv hy).intervalIntegrable)
  · exact this
  · have ht0 : t ≠ 0 := fun h ↦ ht.2 (Or.inr h)
    have htB : t ∉ logBreak := fun h ↦ ht.2 (Or.inl h)
    exact (hasDerivAt_log_norm_one_sub_div hy ht0).mul (hasDerivAt_logW htB)

theorem tendsto_abs_log_quad_mul (b c C0 : ℝ) :
    Tendsto (fun R : ℝ ↦ |Real.log (1 + b * R⁻¹ + c * R⁻¹ ^ 2)| * (Real.log R + C0)) atTop (𝓝 0) := by
  have h1 := (LogEx.tendsto_slope_log_quad b c).abs
  have h2 : Tendsto (fun R : ℝ ↦ Real.log R / R) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h3 : Tendsto (fun R : ℝ ↦ C0 * R⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul C0
  have h4 := h1.mul (h2.add h3)
  rw [add_zero, mul_zero] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [abs_mul, abs_of_pos hR]
  field_simp

theorem tendsto_Psi {z : ℂ} (hy : 0 < z.im) :
    Tendsto (fun R : ℝ ↦ Real.log ‖1 - z / R‖ * logW R) atTop (𝓝 0) ∧
    Tendsto (fun R : ℝ ↦ Real.log ‖1 - z / ((-R : ℝ) : ℂ)‖ * logW (-R)) atTop (𝓝 0) := by
  obtain ⟨Cρ, hρ⟩ := abs_logW_add_posLog_le
  set c : ℝ := z.re ^ 2 + z.im ^ 2 with hc
  -- bound on `W` at `±R`
  have hW : ∀ R : ℝ, 1 ≤ R → |logW R| ≤ Real.log R + |Cρ| ∧ |logW (-R)| ≤ Real.log R + |Cρ| := by
    intro R hR
    have hb : ∀ t : ℝ, |t| = R → |logW t| ≤ Real.log R + |Cρ| := by
      intro t ht
      have h1 := hρ t
      have h2 : min |t| (1 / Real.sqrt (1 + |t|)) ≤ 1 := by
        refine (min_le_right _ _).trans ?_
        rw [div_le_one (Real.sqrt_pos.2 (by positivity))]
        exact Real.one_le_sqrt.2 (by linarith [abs_nonneg t])
      have h3 : Cρ * min |t| (1 / Real.sqrt (1 + |t|)) ≤ |Cρ| := by
        calc _ ≤ |Cρ| * min |t| (1 / Real.sqrt (1 + |t|)) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (le_min (abs_nonneg t) (by positivity))
          _ ≤ |Cρ| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
          _ = |Cρ| := mul_one _
      have h4 : Real.posLog |t| = Real.log R := by
        rw [Real.posLog_abs, Real.posLog_eq_log (by rw [ht]; exact hR), ← Real.log_abs, ht]
      have h5 : |logW t| ≤ abs (logW t + Real.posLog |t|) + Real.posLog |t| := by
        have := abs_sub (logW t + Real.posLog |t|) (Real.posLog |t|)
        rw [add_sub_cancel_right, abs_of_nonneg (Real.posLog_nonneg (x := |t|))] at this
        exact this
      linarith
    exact ⟨hb R (abs_of_pos (by linarith)), hb (-R) (by rw [abs_neg, abs_of_pos (by linarith)])⟩
  have hlim := (tendsto_abs_log_quad_mul (-2 * z.re) c |Cρ|).div_const 2
  have hlim2 := (tendsto_abs_log_quad_mul (-2 * -z.re) c |Cρ|).div_const 2
  rw [zero_div] at hlim hlim2
  constructor
  · refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with R hR
    have hRpos : 0 < R := by linarith
    have hφ : Real.log ‖1 - z / R‖ =
        Real.log (1 + (-2 * z.re) * R⁻¹ + c * R⁻¹ ^ 2) / 2 := by
      rw [log_norm_one_sub_div_eq hy hRpos.ne']
      unfold LogEx.phiK
      rw [LogEx.log_sq_add_sq_eq (x := z.re) (y := z.im) hRpos hy z.re (Or.inl rfl)]
      ring
    rw [Real.norm_eq_abs, abs_mul, hφ, abs_div, abs_two]
    calc |Real.log (1 + (-2 * z.re) * R⁻¹ + c * R⁻¹ ^ 2)| / 2 * |logW R|
        ≤ |Real.log (1 + (-2 * z.re) * R⁻¹ + c * R⁻¹ ^ 2)| / 2 * (Real.log R + |Cρ|) :=
          mul_le_mul_of_nonneg_left (hW R hR).1 (by positivity)
      _ = |Real.log (1 + (-2 * z.re) * R⁻¹ + c * R⁻¹ ^ 2)| * (Real.log R + |Cρ|) / 2 := by ring
  · refine squeeze_zero_norm' ?_ hlim2
    filter_upwards [eventually_ge_atTop 1] with R hR
    have hRpos : 0 < R := by linarith
    have hφ : Real.log ‖1 - z / ((-R : ℝ) : ℂ)‖ =
        Real.log (1 + (-2 * -z.re) * R⁻¹ + c * R⁻¹ ^ 2) / 2 := by
      rw [log_norm_one_sub_div_eq hy (neg_ne_zero.2 hRpos.ne')]
      unfold LogEx.phiK
      have e : (-R - z.re) ^ 2 = (R - -z.re) ^ 2 := by ring
      rw [e, LogEx.log_sq_add_sq_eq (x := z.re) (y := z.im) hRpos hy (-z.re) (Or.inr rfl),
        Real.log_neg_eq_log]
      ring
    rw [Real.norm_eq_abs, abs_mul, hφ, abs_div, abs_two]
    calc |Real.log (1 + (-2 * -z.re) * R⁻¹ + c * R⁻¹ ^ 2)| / 2 * |logW (-R)|
        ≤ |Real.log (1 + (-2 * -z.re) * R⁻¹ + c * R⁻¹ ^ 2)| / 2 * (Real.log R + |Cρ|) :=
          mul_le_mul_of_nonneg_left (hW R hR).2 (by positivity)
      _ = |Real.log (1 + (-2 * -z.re) * R⁻¹ + c * R⁻¹ ^ 2)| * (Real.log R + |Cρ|) / 2 := by ring

theorem integral_ibpDeriv_eq_zero {z : ℂ} (hy : 0 < z.im) : ∫ t : ℝ, ibpDeriv z t = 0 := by
  have hf := integrable_ibpDeriv hy
  have hlim := intervalIntegral_tendsto_integral hf (tendsto_neg_atTop_atBot (G := ℝ)) tendsto_id
  obtain ⟨h1, h2⟩ := tendsto_Psi hy
  have hlim2 : Tendsto (fun R : ℝ ↦ ∫ t in (-R)..R, ibpDeriv z t) atTop (𝓝 0) := by
    have := h1.sub h2
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact (ftc_Psi hy hR).symm
  exact tendsto_nhds_unique hlim hlim2

theorem integral_log_mul_sub_one_eq' {z : ℂ} (hz : 0 < z.im) :
    ∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1) = -∫ t : ℝ, logW t * LogEx.kern z t := by
  have h1 := integrable_log_mul_sub_one hz
  have h2 : Integrable (fun t : ℝ ↦ LogEx.kern z t * logW t) :=
    (integrable_kern_mul_logW hz).congr (Filter.Eventually.of_forall fun t ↦ mul_comm _ _)
  have h0 := integral_ibpDeriv_eq_zero hz
  unfold ibpDeriv at h0
  rw [integral_add h2 h1] at h0
  have e : ∫ t : ℝ, logW t * LogEx.kern z t = ∫ t : ℝ, LogEx.kern z t * logW t :=
    integral_congr_ae (Filter.Eventually.of_forall fun t ↦ mul_comm _ _)
  rw [e]
  linarith

/-- Integration by parts: `V(z) = -∫ W(t) K_z(t) dt`. -/
theorem integral_log_mul_sub_one_eq {z : ℂ} (hz : 0 < z.im) :
    ∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1) = -∫ t : ℝ, logW t * logKernel z t := by
  exact integral_log_mul_sub_one_eq' hz

/-- `∫_0^∞ log((1+σ)/|1-σ|) dσ/σ < ∞` (its value is `π²/2`). -/
theorem integrableOn_log_ratio_div :
    IntegrableOn (fun σ : ℝ ↦ Real.log ((1 + σ) / |1 - σ|) / σ) (Ioi 0) := by
  have hmeas : Measurable (fun σ : ℝ ↦ Real.log ((1 + σ) / |1 - σ|) / σ) := by fun_prop
  have hnn : ∀ σ : ℝ, 0 < σ → 1 ≤ (1 + σ) / |1 - σ| ∨ |1 - σ| = 0 := by
    intro σ hσ
    by_cases h : |1 - σ| = 0
    · exact Or.inr h
    · left
      have hp : 0 < |1 - σ| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h)
      rw [one_le_div hp]
      rcases abs_cases (1 - σ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hf0 : ∀ σ : ℝ, 0 < σ → 0 ≤ Real.log ((1 + σ) / |1 - σ|) := by
    intro σ hσ
    rcases hnn σ hσ with h | h
    · exact Real.log_nonneg h
    · rw [h]; simp
  -- region (0, 2]
  have hI : IntervalIntegrable (fun σ : ℝ ↦ 4 + 2 * Real.log 3 + 2 * |Real.log (1 - σ)|)
      volume 0 2 := by
    have h1 : IntervalIntegrable (fun σ : ℝ ↦ Real.log (1 - σ)) volume 0 2 := by
      have := (intervalIntegral.intervalIntegrable_log' (a := (-1 : ℝ)) (b := 1)).comp_sub_left 1
      have h2 := this.symm
      norm_num at h2
      exact h2
    exact (intervalIntegrable_const.add (h1.abs.const_mul 2))
  have hI' : IntegrableOn (fun σ : ℝ ↦ 4 + 2 * Real.log 3 + 2 * |Real.log (1 - σ)|) (Ioc 0 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hI
  have hA : IntegrableOn (fun σ : ℝ ↦ Real.log ((1 + σ) / |1 - σ|) / σ) (Ioc 0 2) := by
    refine Integrable.mono' hI' hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun σ hσ ↦ ?_
    obtain ⟨hσ0, hσ2⟩ := hσ
    have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hf0 σ hσ0) hσ0.le)]
    by_cases h1 : σ = 1
    · subst h1; simp; positivity
    have hp : 0 < |1 - σ| := abs_pos.2 (sub_ne_zero.2 (Ne.symm h1))
    have hlog : Real.log ((1 + σ) / |1 - σ|) = Real.log (1 + σ) - Real.log |1 - σ| :=
      Real.log_div (by linarith) hp.ne'
    have hA0 := hf0 σ hσ0
    have hRHS : 4 ≤ 4 + 2 * Real.log 3 + 2 * |Real.log (1 - σ)| := by
      have := abs_nonneg (Real.log (1 - σ)); linarith
    rcases le_or_gt σ (1 / 2) with hs | hs
    · have h1s : |1 - σ| = 1 - σ := abs_of_nonneg (by linarith)
      have hx := Real.log_le_sub_one_of_pos (show 0 < (1 + σ) / |1 - σ| by positivity)
      have : (1 + σ) / |1 - σ| - 1 ≤ 4 * σ := by
        rw [h1s, div_sub_one (by linarith), div_le_iff₀ (by linarith)]
        nlinarith
      rw [div_le_iff₀ hσ0]
      nlinarith
    · have hl1 : Real.log (1 + σ) ≤ Real.log 3 := Real.log_le_log (by linarith) (by linarith)
      have hl2 : -Real.log |1 - σ| ≤ |Real.log (1 - σ)| := by
        rw [← Real.log_abs (1 - σ)]; exact neg_le_abs _
      rw [div_le_iff₀ hσ0]
      nlinarith [abs_nonneg (Real.log (1 - σ))]
  -- region `(2, ∞)`
  have hB : IntegrableOn (fun σ : ℝ ↦ Real.log ((1 + σ) / |1 - σ|) / σ) (Ioi 2) := by
    have hg : IntegrableOn (fun σ : ℝ ↦ 4 * σ ^ (-2 : ℝ)) (Ioi 2) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul 4
    refine Integrable.mono' hg hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun σ hσ ↦ ?_
    have hσ2 : 2 < σ := hσ
    have hσ0 : 0 < σ := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hf0 σ hσ0) hσ0.le)]
    have h1s : |1 - σ| = σ - 1 := by rw [abs_of_nonpos (by linarith)]; ring
    have hx := Real.log_le_sub_one_of_pos (show 0 < (1 + σ) / |1 - σ| by
      rw [h1s]; apply div_pos <;> linarith)
    have : (1 + σ) / |1 - σ| - 1 ≤ 4 / σ := by
      rw [h1s, div_sub_one (by linarith), div_le_div_iff₀ (by linarith) hσ0]
      nlinarith
    rw [Real.rpow_neg hσ0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      div_le_iff₀ hσ0]
    have h4 : Real.log ((1 + σ) / |1 - σ|) ≤ 4 / σ := hx.trans this
    refine h4.trans (le_of_eq ?_)
    field_simp
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 2 by norm_num)]
  exact hA.union hB

/-- The Hilbert-transform estimate for `log⁺|t|`: `|∫ log⁺|t| K_z(t) dt| ≤ C` for `Im z ≥ 1`. -/
theorem abs_integral_posLog_mul_logKernel_le : ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im →
    Integrable (fun t : ℝ ↦ Real.posLog |t| * logKernel z t) ∧
      |∫ t : ℝ, Real.posLog |t| * logKernel z t| ≤ C := by
  have hH : IntegrableOn LogEx.Hrat (Ioi 0) := integrableOn_log_ratio_div
  refine ⟨∫ s in Ioi (0 : ℝ), LogEx.Hrat s, fun z hz ↦ ?_⟩
  have hy : 0 < z.im := by linarith
  exact ⟨LogEx.integrable_posLog_kern hy, LogEx.abs_integral_posLog_kern_le hy hH⟩

/-- `∫ |ρ| |K_z| ≤ C` for `Im z ≥ 1`, for `ρ` as in `abs_logW_add_posLog_le`. -/
theorem integral_abs_rho_logKernel_le : ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im →
    Integrable (fun t : ℝ ↦ |logW t + Real.posLog (|t|)| * |logKernel z t|) ∧
      ∫ t : ℝ, |logW t + Real.posLog (|t|)| * |logKernel z t| ≤ C := by
  obtain ⟨Cρ, hρ⟩ := abs_logW_add_posLog_le
  have hC0 : 0 ≤ Cρ := by
    have h := hρ 1
    simp only [abs_one] at h
    have hm : 0 < min (1 : ℝ) (1 / Real.sqrt (1 + 1)) := lt_min one_pos (by positivity)
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hm
    linarith [abs_nonneg (logW 1 + Real.posLog 1)]
  set I₁ : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2 : ℝ)) with hI₁
  set I₂ : ℝ := ∫ s : ℝ, (1 + s ^ 2) ^ (-(3 / 4 : ℝ)) with hI₂
  refine ⟨Cρ * (3 * I₁ + (I₁ / 3 + 2 / 3 * I₂)), fun z hz ↦ ?_⟩
  have hy : 0 < z.im := by linarith
  set ρ : ℝ → ℝ := fun t ↦ logW t + Real.posLog |t| with hρdef
  have hρc : Continuous ρ :=
    logW_lipschitz.continuous.add (Real.continuous_posLog.comp continuous_abs)
  have hρ1 : ∀ t, |ρ t| ≤ Cρ * |t| := fun t ↦
    (hρ t).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC0)
  have hρ2 : ∀ t, |ρ t| ≤ Cρ * (1 + |t|) ^ (-(1 / 2 : ℝ)) := fun t ↦ by
    refine (hρ t).trans (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (le_of_eq ?_)) hC0)
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
  have hρ3 : ∀ t, |ρ t| ≤ Cρ * (1 + |t|) ^ (1 / 2 : ℝ) := fun t ↦ by
    refine (hρ2 t).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    calc (1 + |t|) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by norm_num)
      _ ≤ (1 + |t|) ^ (1 / 2 : ℝ) :=
          Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
  have hint : Integrable (fun t : ℝ ↦ ρ t * LogEx.kern z t) :=
    LogEx.integrable_mul_kern hy hρc.aestronglyMeasurable hC0 hρ1 hρ3
  have hint' : Integrable (fun t : ℝ ↦ |logW t + Real.posLog (|t|)| * |logKernel z t|) := by
    have := hint.norm
    refine this.congr (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [norm_mul, Real.norm_eq_abs]
    rfl
  refine ⟨hint', ?_⟩
  -- the majorant
  set g : ℝ → ℝ := fun t ↦ Cρ * (3 * (1 + |t|) ^ (-(3 / 2 : ℝ)) +
    (1 + |t|) ^ (-(1 / 2 : ℝ)) * (1 + (t - z.re) ^ 2) ^ (-(1 / 2 : ℝ))) with hg
  have hgint : Integrable g :=
    ((LogEx.integrable_rpow_three_half.const_mul 3).add (LogEx.integrable_uv z.re)).const_mul Cρ
  have hw12 : ∀ t : ℝ, (1 + |t|) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (1 + |t|) := fun t ↦ by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
  have hw32 : ∀ t : ℝ, (1 + |t|) ^ (-(3 / 2 : ℝ)) = 1 / Real.sqrt (1 + |t|) ^ 3 := fun t ↦ by
    have h1 : (3 / 2 : ℝ) = (1 / 2 : ℝ) * (3 : ℕ) := by norm_num
    rw [Real.rpow_neg (by positivity), h1, Real.rpow_mul (by positivity), Real.rpow_natCast,
      ← Real.sqrt_eq_rpow, one_div]
  have hpt : ∀ t : ℝ, |logW t + Real.posLog (|t|)| * |logKernel z t| ≤ g t := by
    intro t
    have hK : |logKernel z t| ≤ (1 + (t - z.re) ^ 2) ^ (-(1 / 2 : ℝ)) + |t⁻¹| :=
      LogEx.abs_kern_le_uv hz t
    have hv0 : 0 ≤ (1 + (t - z.re) ^ 2) ^ (-(1 / 2 : ℝ)) := by positivity
    have hr0 : 0 ≤ |ρ t| := abs_nonneg _
    have hA : |ρ t| * (1 + (t - z.re) ^ 2) ^ (-(1 / 2 : ℝ)) ≤
        Cρ * ((1 + |t|) ^ (-(1 / 2 : ℝ)) * (1 + (t - z.re) ^ 2) ^ (-(1 / 2 : ℝ))) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hρ2 t) hv0
    have hB : |ρ t| * |t⁻¹| ≤ Cρ * (3 * (1 + |t|) ^ (-(3 / 2 : ℝ))) := by
      by_cases ht0 : t = 0
      · subst ht0; simp; positivity
      have htp : 0 < |t| := abs_pos.2 ht0
      set s : ℝ := Real.sqrt (1 + |t|) with hs
      have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
      have hs2 : s ^ 2 = 1 + |t| := Real.sq_sqrt (by positivity)
      rw [hw32, ← hs, abs_inv]
      rcases le_or_gt 1 |t| with h1 | h1
      · have := hρ2 t
        rw [hw12, ← hs] at this
        calc |ρ t| * |t|⁻¹ ≤ Cρ * (1 / s) * |t|⁻¹ :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ ≤ Cρ * (3 * (1 / s ^ 3)) := by
              have : |t|⁻¹ ≤ 2 / s ^ 2 := by
                rw [inv_eq_one_div, div_le_div_iff₀ htp (by positivity)]
                nlinarith
              calc Cρ * (1 / s) * |t|⁻¹ ≤ Cρ * (1 / s) * (2 / s ^ 2) :=
                    mul_le_mul_of_nonneg_left this (by positivity)
                _ = Cρ * (2 * (1 / s ^ 3)) := by field_simp
                _ ≤ _ := by
                    have : 0 ≤ Cρ * (1 / s ^ 3) := by positivity
                    nlinarith
      · have := hρ1 t
        calc |ρ t| * |t|⁻¹ ≤ Cρ * |t| * |t|⁻¹ := mul_le_mul_of_nonneg_right this (by positivity)
          _ = Cρ := by field_simp
          _ ≤ Cρ * (3 * (1 / s ^ 3)) := by
              have hs1 : s < 3 / 2 := by nlinarith
              have hs3 : s ^ 3 ≤ 3 := by nlinarith [sq_nonneg s]
              have : 1 ≤ 3 * (1 / s ^ 3) := by
                rw [← mul_div_assoc, mul_one, le_div_iff₀ (by positivity)]; linarith
              nlinarith
    calc |logW t + Real.posLog (|t|)| * |logKernel z t|
        = |ρ t| * |logKernel z t| := rfl
      _ ≤ |ρ t| * ((1 + (t - z.re) ^ 2) ^ (-(1 / 2 : ℝ)) + |t⁻¹|) :=
          mul_le_mul_of_nonneg_left hK hr0
      _ = |ρ t| * (1 + (t - z.re) ^ 2) ^ (-(1 / 2 : ℝ)) + |ρ t| * |t⁻¹| := by ring
      _ ≤ g t := by rw [hg]; simp only []; nlinarith
  calc ∫ t : ℝ, |logW t + Real.posLog (|t|)| * |logKernel z t| ≤ ∫ t, g t :=
        integral_mono hint' hgint hpt
    _ = Cρ * (3 * I₁ + ∫ t : ℝ, (1 + |t|) ^ (-(1 / 2 : ℝ)) * (1 + (t - z.re) ^ 2) ^ (-(1 / 2 : ℝ))) := by
        rw [hg, integral_const_mul, integral_add ((LogEx.integrable_rpow_three_half).const_mul 3)
          (LogEx.integrable_uv z.re), integral_const_mul]
    _ ≤ _ := by
        have := LogEx.integral_uv_le z.re
        have h2 : Cρ * (3 * I₁ + ∫ t : ℝ, (1 + |t|) ^ (-(1 / 2 : ℝ)) * (1 + (t - z.re) ^ 2) ^ (-(1 / 2 : ℝ))) ≤
            Cρ * (3 * I₁ + (I₁ / 3 + 2 / 3 * I₂)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC0
        exact h2

theorem abs_integral_log_mul_sub_one_le : ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im →
    |∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1)| ≤ C := by
  obtain ⟨C1, hC1⟩ := abs_integral_posLog_mul_logKernel_le
  obtain ⟨C2, hC2⟩ := integral_abs_rho_logKernel_le
  refine ⟨C1 + C2, fun z hz ↦ ?_⟩
  have hz0 : 0 < z.im := by linarith
  obtain ⟨hI1, hb1⟩ := hC1 z hz
  obtain ⟨hI2, hb2⟩ := hC2 z hz
  rw [integral_log_mul_sub_one_eq hz0]
  -- measurability of ρ K
  have hWc : Continuous logW := logW_lipschitz.continuous
  have hρc : Continuous (fun t : ℝ ↦ logW t + Real.posLog (|t|)) :=
    hWc.add (Real.continuous_posLog.comp continuous_abs)
  have hKm : Measurable (logKernel z) := by
    unfold logKernel
    have h1 : Measurable (fun t : ℝ ↦ (t - z.re) / ((t - z.re) ^ 2 + z.im ^ 2)) := by fun_prop
    have h2 : Measurable (fun t : ℝ ↦ 1 / t) := by fun_prop
    exact h1.sub h2
  have hI3 : Integrable (fun t : ℝ ↦ (logW t + Real.posLog (|t|)) * logKernel z t) := by
    refine Integrable.mono' hI2 (hρc.measurable.mul hKm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
  have e : ∀ t : ℝ, logW t * logKernel z t =
      (logW t + Real.posLog (|t|)) * logKernel z t - Real.posLog (|t|) * logKernel z t :=
    fun t ↦ by ring
  simp_rw [e]
  rw [integral_sub hI3 hI1]
  have h3 : |∫ t : ℝ, (logW t + Real.posLog (|t|)) * logKernel z t| ≤ C2 := by
    refine (abs_integral_le_integral_abs).trans ?_
    refine le_trans (integral_mono hI3.abs hI2 (fun t ↦ ?_)) hb2
    simp only [abs_mul, le_refl]
  have h4 := abs_le.1 hb1
  have h5 := abs_le.1 h3
  rw [neg_sub, abs_le]
  constructor <;> linarith [h4.1, h4.2, h5.1, h5.2]

/-- Comparison in the strip: `|U(x + iy) - U(x + i)| ≤ 20 π` for `0 ≤ y ≤ 1`. -/
theorem abs_multU_sub_multU_le {z : ℂ} (h0 : 0 ≤ z.im) (h1 : z.im ≤ 1) :
    |OCS.multU logDensity 0 z - OCS.multU logDensity 0 ((z.re : ℂ) + Complex.I)| ≤ 20 * Real.pi := by
  set z' : ℂ := (z.re : ℂ) + Complex.I with hz'
  have hre : z'.re = z.re := by simp [hz']
  have him : z'.im = 1 := by simp [hz']
  have hw : OCS.IsMultWeight logDensity (1 / 10) 20 := isMultWeight_logDensity
  have i1 := OCS.integrable_multUIntegrand hw z
  have i2 := OCS.integrable_multUIntegrand hw z'
  have hg : Integrable (fun t : ℝ ↦ 10 * Real.log (1 + 1 / (t - z.re) ^ 2)) :=
    (LogEx.integrable_log_one_add_inv_sq.comp_sub_right z.re).const_mul 10
  have hdiff : OCS.multU logDensity 0 z - OCS.multU logDensity 0 z' =
      ∫ t : ℝ, (OCS.multUIntegrand logDensity z t - OCS.multUIntegrand logDensity z' t) := by
    rw [OCS.multU_eq, OCS.multU_eq, integral_sub i1 i2]; ring
  have hbound : ∀ᵐ t : ℝ, ‖OCS.multUIntegrand logDensity z t - OCS.multUIntegrand logDensity z' t‖ ≤
      10 * Real.log (1 + 1 / (t - z.re) ^ 2) := by
    filter_upwards [OCS.ae_ne_real 0, OCS.ae_ne_real z.re] with t ht0 htx
    have hs : 0 < (t - z.re) ^ 2 := by
      have : t - z.re ≠ 0 := sub_ne_zero.2 htx
      positivity
    have hz1 : (t : ℂ) ≠ z := fun h ↦ htx (by simpa using congrArg Complex.re h)
    have hz2 : (t : ℂ) ≠ z' := fun h ↦ htx (by simpa [hz'] using congrArg Complex.re h)
    have hn1 : ‖(t : ℂ) - z‖ ^ 2 = (t - z.re) ^ 2 + z.im ^ 2 := by
      rw [norm_sub_rev]; exact OCS.norm_ofReal_sub_sq z t
    have hn2 : ‖(t : ℂ) - z'‖ ^ 2 = (t - z.re) ^ 2 + 1 := by
      rw [norm_sub_rev, OCS.norm_ofReal_sub_sq z' t, hre, him]; ring
    have hpos1 : 0 < ‖(t : ℂ) - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
    have hpos2 : 0 < ‖(t : ℂ) - z'‖ := norm_pos_iff.2 (sub_ne_zero.2 hz2)
    have hL1 : Real.log ‖(t : ℂ) - z‖ = Real.log ((t - z.re) ^ 2 + z.im ^ 2) / 2 := by
      rw [← hn1, Real.log_pow]; push_cast; ring
    have hL2 : Real.log ‖(t : ℂ) - z'‖ = Real.log ((t - z.re) ^ 2 + 1) / 2 := by
      rw [← hn2, Real.log_pow]; push_cast; ring
    have hre' : (z / (t : ℂ)).re = (z' / (t : ℂ)).re := by
      rw [Complex.div_ofReal_re, Complex.div_ofReal_re, hre]
    have hdi : OCS.multUIntegrand logDensity z t - OCS.multUIntegrand logDensity z' t =
        (Real.log ‖(t : ℂ) - z‖ - Real.log ‖(t : ℂ) - z'‖) * logDensity t := by
      unfold OCS.multUIntegrand
      rw [OCS.log_norm_one_sub_div z ht0 hz1, OCS.log_norm_one_sub_div z' ht0 hz2, hre']
      ring
    rw [hdi, hL1, hL2, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ((logDensity_bounds t).1.trans' (by norm_num))]
    have hy2 : z.im ^ 2 ≤ 1 := by nlinarith
    have hy0 : 0 ≤ z.im ^ 2 := sq_nonneg _
    have hA : Real.log ((t - z.re) ^ 2 + z.im ^ 2) ≤ Real.log ((t - z.re) ^ 2 + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have hB : Real.log ((t - z.re) ^ 2) ≤ Real.log ((t - z.re) ^ 2 + z.im ^ 2) :=
      Real.log_le_log hs (by linarith)
    have hC : Real.log (1 + 1 / (t - z.re) ^ 2) =
        Real.log ((t - z.re) ^ 2 + 1) - Real.log ((t - z.re) ^ 2) := by
      rw [← Real.log_div (by positivity) hs.ne']
      congr 1; field_simp
    have hm := (logDensity_bounds t).2
    have hm0 : 0 ≤ logDensity t := (logDensity_bounds t).1.trans' (by norm_num)
    have hd : |Real.log ((t - z.re) ^ 2 + z.im ^ 2) / 2 - Real.log ((t - z.re) ^ 2 + 1) / 2| ≤
        Real.log (1 + 1 / (t - z.re) ^ 2) / 2 := by
      rw [abs_le]; constructor <;> linarith
    have hg0 : 0 ≤ Real.log (1 + 1 / (t - z.re) ^ 2) / 2 := by
      have : 0 ≤ 1 / (t - z.re) ^ 2 := by positivity
      have := Real.log_nonneg (show (1:ℝ) ≤ 1 + 1 / (t - z.re) ^ 2 by linarith)
      linarith
    calc _ ≤ (Real.log (1 + 1 / (t - z.re) ^ 2) / 2) * 20 := mul_le_mul hd hm hm0 hg0
      _ = _ := by ring
  calc |OCS.multU logDensity 0 z - OCS.multU logDensity 0 z'|
      = ‖∫ t : ℝ, (OCS.multUIntegrand logDensity z t - OCS.multUIntegrand logDensity z' t)‖ := by
        rw [hdiff, Real.norm_eq_abs]
    _ ≤ ∫ t : ℝ, 10 * Real.log (1 + 1 / (t - z.re) ^ 2) :=
        norm_integral_le_of_norm_le hg hbound
    _ = 20 * Real.pi := by
        rw [integral_const_mul, integral_sub_right_eq_self
          (fun t ↦ Real.log (1 + 1 / t ^ 2)) z.re, LogEx.integral_log_one_add_inv_sq]; ring

/-- **The sine-type estimate**: `U(z) = π Im z + κ Re z + O(1)` for `Im z ≥ 0`. -/
theorem logDensity_U_estimate : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
    |OCS.multU logDensity 0 z - Real.pi * z.im - logKappa * z.re| ≤ C := by
  obtain ⟨C1, hC1⟩ := abs_integral_log_mul_sub_one_le
  refine ⟨20 * Real.pi + C1 + Real.pi, fun z hz ↦ ?_⟩
  have hπ := Real.pi_pos
  rcases le_or_gt 1 z.im with h1 | h1
  · rw [multU_logDensity_eq (by linarith)]
    have := hC1 z h1
    have e : Real.pi * z.im + logKappa * z.re +
        (∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1)) - Real.pi * z.im - logKappa * z.re =
        ∫ t : ℝ, Real.log ‖1 - z / t‖ * (logDensity t - 1) := by ring
    rw [e]
    have : 0 ≤ 20 * Real.pi + Real.pi := by positivity
    linarith
  · set z' : ℂ := (z.re : ℂ) + Complex.I with hz'
    have hre : z'.re = z.re := by simp [hz']
    have him : z'.im = 1 := by simp [hz']
    have h2 := abs_multU_sub_multU_le hz h1.le
    have h3 := hC1 z' (by rw [him])
    have hU' := multU_logDensity_eq (z := z') (by rw [him]; norm_num)
    rw [hre, him] at hU'
    have h4 : |OCS.multU logDensity 0 z' - Real.pi - logKappa * z.re| ≤ C1 := by
      rw [hU']
      have e : Real.pi * 1 + logKappa * z.re +
          (∫ t : ℝ, Real.log ‖1 - z' / t‖ * (logDensity t - 1)) - Real.pi - logKappa * z.re =
          ∫ t : ℝ, Real.log ‖1 - z' / t‖ * (logDensity t - 1) := by ring
      rw [e]; exact h3
    have h5 := abs_le.1 h2
    have h6 := abs_le.1 h4
    have h7 : 0 ≤ z.im := hz
    rw [abs_le]
    constructor <;> nlinarith [h5.1, h5.2, h6.1, h6.2]

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

theorem re_eq_norm_mul_cos {E : ℂ → ℂ} {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) (x : ℝ) :
    (E x).re = ‖E x‖ * Real.cos (φ x) := by
  have h := hφ.2 x
  conv_lhs => rw [h]
  have : Complex.exp (-(I * (φ x : ℂ))) = Complex.exp (((-φ x : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  rw [Complex.re_ofReal_mul, this, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

theorem phaseLevel_eq_of_zero_set {E : ℂ → ℂ} {φ : ℝ → ℝ} {Γ : Set ℝ}
    (h0 : ∀ x : ℝ, E x ≠ 0) (hφ : IsPhaseFunction E φ)
    (hΓ : ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ Γ, z = (γ : ℂ)) :
    phaseLevel φ (Real.pi / 2) = Γ := by
  ext x
  have h1 : x ∈ Γ ↔ E x + fstar E x = 0 := by
    rw [hΓ]
    constructor
    · intro h; exact ⟨x, h, rfl⟩
    · rintro ⟨γ, hγ, hx⟩
      have : x = γ := by exact_mod_cast hx
      rwa [this]
  rw [h1, fstar_ofReal]
  have h2 : E x + conj (E x) = ((2 * (E x).re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
  rw [h2, Complex.ofReal_eq_zero, re_eq_norm_mul_cos hφ x]
  have hn : ‖E x‖ ≠ 0 := norm_ne_zero_iff.2 (h0 x)
  simp only [phaseLevel, Set.mem_ofPred_eq]
  rw [show 2 * (‖E x‖ * Real.cos (φ x)) = 0 ↔ Real.cos (φ x) = 0 by
    constructor
    · intro h; have := mul_eq_zero.1 (by linarith : ‖E x‖ * Real.cos (φ x) = 0)
      exact this.resolve_left hn
    · intro h; rw [h]; ring]
  rw [Real.cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩

theorem enorm_sq_eq_ofReal (z : ℂ) : ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem norm_sAlpha_eq (E : ℂ → ℂ) (x : ℝ) :
    ‖Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * E x -
      Complex.exp (-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ))) * fstar E x‖ = 2 * |(E x).re| := by
  have h1 : Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
    rw [mul_comm, Complex.exp_mul_I]
    simp
  have h2 : Complex.exp (-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ))) = -Complex.I := by
    rw [Complex.exp_neg, h1, Complex.inv_I]
  rw [h1, h2, fstar_ofReal]
  have : Complex.I * E x - -Complex.I * conj (E x) = Complex.I * ((2 * (E x).re : ℝ) : ℂ) := by
    rw [neg_mul, sub_neg_eq_add, ← mul_add, Complex.add_conj]
  rw [this, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  simp

/-- `E + E^*` is not in `H(E)`: `|E + E^*| = 2|E||cos φ|` is not square integrable on `ℝ`,
because `φ' ≃ 1`. -/
theorem not_memHE_sAlpha (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ} {φ : ℝ → ℝ}
    (hHB : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (hEPW : HEEqPW E) (hφ : IsPhaseFunction E φ)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) :
    ¬ MemHE E (fun z ↦ Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * E z -
      Complex.exp (-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ))) * fstar E z) := by
  intro hS
  set S : ℂ → ℂ := fun z ↦ Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * E z -
      Complex.exp (-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ))) * fstar E z with hSdef
  obtain ⟨c, Cc, hc, hcC⟩ := hcomp
  have hEreal : ∀ x : ℝ, c ≤ ‖E x‖ ∧ ‖E x‖ ≤ Cc := fun x ↦ by
    have := hcC (x : ℂ) (by simp)
    simpa using this
  have hCc : 0 < Cc := lt_of_lt_of_le hc ((hEreal 0).1.trans (hEreal 0).2)
  obtain ⟨cφ, hcφ, hge⟩ := HEEqPW.phaseDeriv_mul_sq_ge hPW hE hHB hEPW
  obtain ⟨Cφ, hle⟩ := HEEqPW.phaseDeriv_mul_sq_le hPW hE hHB hEPW
  have hCφ : 0 < Cφ := lt_of_lt_of_le hcφ ((hge 0).trans (hle 0))
  have hderiv : ∀ x : ℝ, HasDerivAt φ (phaseDeriv E x) x := IsPhaseFunction.hasDerivAt hHB.1 h0 hφ
  have hpos : ∀ x : ℝ, 0 < ‖E x‖ := fun x ↦ norm_pos_iff.2 (h0 x)
  have hNpos : ∀ x : ℝ, 0 < ‖E x‖ ^ 2 := fun x ↦ by have := hpos x; positivity
  have hm1 : ∀ x : ℝ, cφ / Cc ^ 2 ≤ phaseDeriv E x := fun x ↦ by
    have h2 : ‖E x‖ ^ 2 ≤ Cc ^ 2 := by
      have := (hEreal x).2; nlinarith [hpos x]
    calc cφ / Cc ^ 2 ≤ cφ / ‖E x‖ ^ 2 := div_le_div_of_nonneg_left hcφ.le (hNpos x) h2
      _ ≤ phaseDeriv E x := by rw [div_le_iff₀ (hNpos x)]; linarith [hge x]
  have hM1 : ∀ x : ℝ, phaseDeriv E x ≤ Cφ / c ^ 2 := fun x ↦ by
    have h2 : c ^ 2 ≤ ‖E x‖ ^ 2 := by
      have := (hEreal x).1; nlinarith
    calc phaseDeriv E x ≤ Cφ / ‖E x‖ ^ 2 := by rw [le_div_iff₀ (hNpos x)]; linarith [hle x]
      _ ≤ Cφ / c ^ 2 := div_le_div_of_nonneg_left hCφ.le (by positivity) h2
  have hcont : Continuous (fun x : ℝ ↦ phaseDeriv E x) := by
    have hEc : Continuous E := hHB.1.continuous
    have hdc : Continuous (deriv E) := (hHB.1.contDiff (n := 1)).continuous_deriv le_rfl
    unfold phaseDeriv
    refine (Complex.continuous_im.comp ?_).neg
    exact (hdc.comp Complex.continuous_ofReal).div (hEc.comp Complex.continuous_ofReal) h0
  have hM1pos : 0 < Cφ / c ^ 2 := by positivity
  -- lower bound for the `L²` mass on `[0, T]`
  have hlow : ∀ T : ℝ, 0 ≤ T →
      ENNReal.ofReal (4 * c ^ 2 * (((cφ / Cc ^ 2) * T / 2 - 1 / 2) / (Cφ / c ^ 2))) ≤ pwNormSq S := by
    intro T hT
    have hI := LogEx.integral_cos_sq_phase_ge hderiv hcont hM1pos hm1 hM1 hT
    have hcos : Continuous (fun x : ℝ ↦ Real.cos (φ x) ^ 2) :=
      (Real.continuous_cos.comp hφ.1).pow 2
    calc ENNReal.ofReal (4 * c ^ 2 * (((cφ / Cc ^ 2) * T / 2 - 1 / 2) / (Cφ / c ^ 2)))
        ≤ ENNReal.ofReal (∫ x in Ioc (0 : ℝ) T, 4 * c ^ 2 * Real.cos (φ x) ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← intervalIntegral.integral_of_le hT, intervalIntegral.integral_const_mul]
          have : 0 < 4 * c ^ 2 := by positivity
          exact (mul_le_mul_of_nonneg_left hI this.le)
      _ = ∫⁻ x in Ioc (0 : ℝ) T, ENNReal.ofReal (4 * c ^ 2 * Real.cos (φ x) ^ 2) := by
          rw [ofReal_integral_eq_lintegral_ofReal]
          · exact ((continuous_const.mul hcos).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
          · exact Filter.Eventually.of_forall fun x ↦ by positivity
      _ ≤ ∫⁻ x in Ioc (0 : ℝ) T, ‖S x‖ₑ ^ 2 := by
          apply lintegral_mono
          intro x
          dsimp only
          rw [enorm_sq_eq_ofReal]
          apply ENNReal.ofReal_le_ofReal
          have hn := norm_sAlpha_eq E x
          have hre : (E x).re = ‖E x‖ * Real.cos (φ x) := re_eq_norm_mul_cos hφ x
          have : ‖S x‖ = 2 * (‖E x‖ * |Real.cos (φ x)|) := by
            rw [hSdef]; simp only []; rw [hn, hre, abs_mul, abs_of_nonneg (norm_nonneg _)]
          rw [this]
          have h1 : c ^ 2 ≤ ‖E x‖ ^ 2 := by have := (hEreal x).1; nlinarith
          have h2 : |Real.cos (φ x)| ^ 2 = Real.cos (φ x) ^ 2 := sq_abs _
          calc 4 * c ^ 2 * Real.cos (φ x) ^ 2 ≤ 4 * ‖E x‖ ^ 2 * Real.cos (φ x) ^ 2 := by
                gcongr
            _ = (2 * (‖E x‖ * |Real.cos (φ x)|)) ^ 2 := by rw [mul_pow, mul_pow, h2]; ring
      _ ≤ pwNormSq S := setLIntegral_le_lintegral _ _
  have hfin : pwNormSq S ≠ ⊤ := pwNormSq_ne_top ((hEPW.1 S).1 hS)
  -- choose `T` large
  set K : ℝ := 4 * c ^ 2 * ((cφ / Cc ^ 2) / 2 / (Cφ / c ^ 2)) with hK
  set K' : ℝ := 4 * c ^ 2 * ((1 / 2) / (Cφ / c ^ 2)) with hK'
  have hKpos : 0 < K := by positivity
  set T : ℝ := ((pwNormSq S).toReal + K') / K + 1 with hT
  have hT0 : 0 ≤ T := by
    have : 0 ≤ ((pwNormSq S).toReal + K') / K := by
      apply div_nonneg _ hKpos.le
      have : 0 ≤ K' := by positivity
      positivity
    linarith
  have hlow' := hlow T hT0
  have hval : 4 * c ^ 2 * (((cφ / Cc ^ 2) * T / 2 - 1 / 2) / (Cφ / c ^ 2)) = K * T - K' := by
    rw [hK, hK']; ring
  have hgt : (pwNormSq S).toReal < K * T - K' := by
    have : K * T = (pwNormSq S).toReal + K' + K := by
      rw [hT]; field_simp
    linarith
  rw [hval] at hlow'
  have := (ENNReal.lt_ofReal_iff_toReal_lt hfin).2 hgt
  exact absurd hlow' (not_le.2 this)

theorem eq_zero_of_pwNormSq_eq_zero {f : ℂ → ℂ} (hf : MemPW f) (h : pwNormSq f = 0) :
    ∀ z, f z = 0 := by
  have hcont : Continuous (fun x : ℝ ↦ f x) := hf.1.continuous.comp Complex.continuous_ofReal
  have hmeas : Measurable (fun x : ℝ ↦ ‖f x‖ₑ ^ 2) := by
    exact hcont.measurable.enorm.pow_const 2
  have h1 := (lintegral_eq_zero_iff hmeas).1 h
  have h2 : (fun x : ℝ ↦ f x) =ᵐ[volume] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [h1] with x hx
    simpa using hx
  have h3 : (fun x : ℝ ↦ f x) = fun _ ↦ (0 : ℂ) :=
    (Continuous.ae_eq_iff_eq volume hcont continuous_const).1 h2
  have h4 : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0 := by
    have ht : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    refine ht.frequently ?_
    exact Filter.Eventually.frequently (Filter.Eventually.of_forall fun x ↦ congrFun h3 x)
  have h5 : Set.EqOn f 0 Set.univ :=
    (hf.1.differentiableOn (s := Set.univ)).analyticOnNhd isOpen_univ |>.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ 0) h4
  intro z
  exact h5 (Set.mem_univ z)

theorem orthWeight_bounds (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ}
    (hHB : IsHB E) (hEPW : HEEqPW E) :
    ∃ wl wu : ℝ≥0, 0 < wl ∧ 0 < wu ∧ ∀ γ : ℝ, (wl : ℝ≥0∞) ≤ orthWeight E γ ∧
      orthWeight E γ ≤ wu := by
  obtain ⟨cφ, hcφ, hge⟩ := HEEqPW.phaseDeriv_mul_sq_ge hPW hE hHB hEPW
  obtain ⟨Cφ, hle⟩ := HEEqPW.phaseDeriv_mul_sq_le hPW hE hHB hEPW
  have hCφ : 0 < Cφ := lt_of_lt_of_le hcφ ((hge 0).trans (hle 0))
  refine ⟨(Real.pi / Cφ).toNNReal, (Real.pi / cφ).toNNReal, ?_, ?_, fun γ ↦ ?_⟩
  · simpa using div_pos Real.pi_pos hCφ
  · simpa using div_pos Real.pi_pos hcφ
  · have hd : 0 < phaseDeriv E γ * ‖E γ‖ ^ 2 := lt_of_lt_of_le hcφ (hge γ)
    unfold orthWeight
    constructor
    · change ENNReal.ofReal (Real.pi / Cφ) ≤ _
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left Real.pi_pos.le hd (hle γ))
    · change _ ≤ ENNReal.ofReal (Real.pi / cφ)
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left Real.pi_pos.le hcφ (hge γ))

/-- From `H(E) = PW`, `|E| ≃ 1` on `ℝ`, `φ_E' |E|² ≃ 1`, `E + E^* ∉ H(E)`: the zero set of
`E + E^*` is sampling and complete interpolating for `PW`. -/
theorem sampling_cis_of_zero_set (hPW : PaleyWienerThm) (hE : TheoremE) {E : ℂ → ℂ} {φ : ℝ → ℝ}
    {Γ : Set ℝ} (hHB : IsHB E) (h0 : ∀ x : ℝ, E x ≠ 0) (hEPW : HEEqPW E)
    (hφ : IsPhaseFunction E φ)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im))
    (hΓ : ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ γ ∈ Γ, z = (γ : ℂ)) :
    IsSampling Γ ∧ IsCompleteInterpolating Γ := by
  have hlev := phaseLevel_eq_of_zero_set h0 hφ hΓ
  have hstrict : IsStrictHB E := HEEqPW.isStrictHB hHB hEPW
  have hnot := not_memHE_sAlpha hPW hE hHB h0 hEPW hφ hcomp
  obtain ⟨hnorm, hinterp⟩ := hE E hstrict h0 φ hφ (Real.pi / 2) hnot
  rw [hlev] at hnorm hinterp
  subst hlev
  obtain ⟨wl, wu, hwl, hwu, hw⟩ := orthWeight_bounds hPW hE hHB hEPW
  obtain ⟨c1, C1, hc1, hnE⟩ := hEPW.2
  have hwl0 : (wl : ℝ≥0∞) ≠ 0 := by exact_mod_cast hwl.ne'
  have hwu0 : (wu : ℝ≥0∞) ≠ 0 := by exact_mod_cast hwu.ne'
  have hc10 : (c1 : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc1.ne'
  have hsumle : ∀ f : ℂ → ℂ, MemPW f →
      (wl : ℝ≥0∞) * sampleSum (phaseLevel φ (Real.pi / 2)) f ≤ heNormSq E f ∧
        heNormSq E f ≤ wu * sampleSum (phaseLevel φ (Real.pi / 2)) f := by
    intro f hf
    rw [hnorm f (hEPW.1 f |>.2 hf), sampleSum, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    constructor
    · exact ENNReal.tsum_le_tsum fun γ ↦ by gcongr; exact (hw _).1
    · exact ENNReal.tsum_le_tsum fun γ ↦ by gcongr; exact (hw _).2
  refine ⟨⟨c1 / wu, C1 / wl, by positivity, fun f hf ↦ ⟨?_, ?_⟩⟩, ?_⟩
  · have h1 := (hnE f hf).1
    have h2 := (hsumle f hf).2
    have h3 : (c1 : ℝ≥0∞) * pwNormSq f ≤ wu * sampleSum (phaseLevel φ (Real.pi / 2)) f := h1.trans h2
    have e : ((c1 / wu : ℝ≥0) : ℝ≥0∞) * pwNormSq f = ((c1 : ℝ≥0∞) * pwNormSq f) / wu := by
      rw [ENNReal.coe_div hwu.ne', div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [e]
    exact ENNReal.div_le_of_le_mul' h3
  · have h1 := (hnE f hf).2
    have h2 := (hsumle f hf).1
    have h3 : (wl : ℝ≥0∞) * sampleSum (phaseLevel φ (Real.pi / 2)) f ≤ C1 * pwNormSq f := h2.trans h1
    have e : ((C1 / wl : ℝ≥0) : ℝ≥0∞) * pwNormSq f = ((C1 : ℝ≥0∞) * pwNormSq f) / wl := by
      rw [ENNReal.coe_div hwl.ne', div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [e, ENNReal.le_div_iff_mul_le (Or.inl hwl0) (Or.inl ENNReal.coe_ne_top), mul_comm]
    exact h3
  · intro a ha
    have hfin : ∑' γ : ↑(phaseLevel φ (Real.pi / 2)), orthWeight E γ * ‖a γ‖ₑ ^ 2 < ∞ := by
      calc _ ≤ ∑' γ : ↑(phaseLevel φ (Real.pi / 2)), (wu : ℝ≥0∞) * ‖a γ‖ₑ ^ 2 :=
            ENNReal.tsum_le_tsum fun γ ↦ by gcongr; exact (hw _).2
        _ = wu * ∑' γ : ↑(phaseLevel φ (Real.pi / 2)), ‖a γ‖ₑ ^ 2 := ENNReal.tsum_mul_left
        _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top ha
    obtain ⟨f, hf, hfa⟩ := hinterp a hfin
    refine ⟨f, ⟨(hEPW.1 f).1 hf, hfa⟩, ?_⟩
    rintro g ⟨hg, hga⟩
    have hd : MemPW (f - g) := ((hEPW.1 f).1 hf).sub hg
    have hz : sampleSum (phaseLevel φ (Real.pi / 2)) (f - g) = 0 := by
      unfold sampleSum
      refine ENNReal.tsum_eq_zero.2 fun γ ↦ ?_
      have := hfa γ γ.2
      have h2 := hga γ γ.2
      simp [this, h2]
    have h1 := (hsumle _ hd).2
    rw [hz, mul_zero] at h1
    have h3 := (hnE _ hd).1
    have h4 : (c1 : ℝ≥0∞) * pwNormSq (f - g) = 0 := le_antisymm (h3.trans h1) bot_le
    have h5 : pwNormSq (f - g) = 0 := (mul_eq_zero.1 h4).resolve_left hc10
    funext z
    have := eq_zero_of_pwNormSq_eq_zero hd h5 z
    have h6 : f z = g z := by simpa [sub_eq_zero] using this
    exact h6.symm

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
