import FourierFrames.PW.PlancherelPolya
import FourierFrames.Theorem1.Sufficiency.Interlace

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF
namespace Suff

theorem sampleSum_coe_finset (s : Finset ℝ) (f : ℂ → ℂ) :
    sampleSum (↑s : Set ℝ) f = ∑ x ∈ s, ‖f (x : ℂ)‖ₑ ^ 2 := by
  unfold sampleSum
  exact Finset.tsum_subtype s (fun x : ℝ ↦ ‖f (x : ℂ)‖ₑ ^ 2)

theorem sampleSum_image_finset {u : ℤ → ℝ} (hu : Function.Injective u) (K : Finset ℤ) (f : ℂ → ℂ) :
    sampleSum (u '' (K : Set ℤ)) f = ∑ k ∈ K, ‖f (u k : ℂ)‖ₑ ^ 2 := by
  classical
  have : u '' (K : Set ℤ) = ↑(K.image u) := by simp
  rw [this, sampleSum_coe_finset, Finset.sum_image (fun a _ b _ h ↦ hu h)]

/-- Sampling sums of sets contained in the image of a finite set of indices. -/
theorem sampleSum_le_of_subset_image {u : ℤ → ℝ} (hu : Function.Injective u) (K : Finset ℤ)
    {S : Set ℝ} (hS : S ⊆ u '' (K : Set ℤ)) (f : ℂ → ℂ) :
    sampleSum S f ≤ ∑ k ∈ K, ‖f (u k : ℂ)‖ₑ ^ 2 := by
  rw [← sampleSum_image_finset hu]
  exact sampleSum_mono hS f

theorem sampleSum_split_aux (Λ : Set ℝ) (f : ℂ → ℂ) (R : ℝ) :
    sampleSum Λ f =
      sampleSum (Λ ∩ {x : ℝ | |x| < R}) f + sampleSum (Λ ∩ {x : ℝ | R ≤ |x|}) f := by
  rw [sampleSum_eq_tsum_indicator, sampleSum_eq_tsum_indicator, sampleSum_eq_tsum_indicator,
    ← ENNReal.tsum_add]
  congr 1
  ext x
  by_cases hΛ : x ∈ Λ <;> by_cases hR : |x| < R <;>
    simp [Set.indicator, hΛ, hR, not_le.mpr, not_lt.mp]

theorem exists_finset_of_bounds (a b : ℝ) :
    ∃ N : ℕ, ∀ k : ℤ, a < Real.pi / 2 + k * Real.pi → Real.pi / 2 + k * Real.pi < b →
      k ∈ Finset.Icc (-(N : ℤ)) N := by
  have hπ := Real.pi_pos
  obtain ⟨N, hN⟩ := exists_nat_gt ((max |a| |b|) / Real.pi + 1)
  refine ⟨N, fun k h1 h2 ↦ ?_⟩
  have hM : |Real.pi / 2 + k * Real.pi| ≤ max |a| |b| := by
    rw [abs_le]
    constructor
    · have := neg_abs_le a
      have := le_max_left |a| |b|
      linarith
    · have := le_abs_self b
      have := le_max_right |a| |b|
      linarith
  have h3 : |(k : ℝ)| * Real.pi ≤ max |a| |b| + Real.pi / 2 := by
    have h4 : |(k : ℝ) * Real.pi| ≤ |Real.pi / 2 + k * Real.pi| + |Real.pi / 2| := by
      have := abs_sub (Real.pi / 2 + k * Real.pi) (Real.pi / 2)
      have e : Real.pi / 2 + k * Real.pi - Real.pi / 2 = (k : ℝ) * Real.pi := by ring
      rwa [e] at this
    rw [abs_mul, abs_of_pos hπ] at h4
    rw [abs_of_pos (by positivity : 0 < Real.pi / 2)] at h4
    linarith
  have h5 : |(k : ℝ)| < N := by
    have h6 : |(k : ℝ)| ≤ max |a| |b| / Real.pi + 1 / 2 := by
      rw [← sub_nonneg]
      have : max |a| |b| / Real.pi + 1 / 2 - |(k : ℝ)| =
          (max |a| |b| + Real.pi / 2 - |(k : ℝ)| * Real.pi) / Real.pi := by
        field_simp
      rw [this]
      exact div_nonneg (by linarith) hπ.le
    linarith
  have h7 : |k| < (N : ℤ) := by
    have : ((|k| : ℤ) : ℝ) < ((N : ℤ) : ℝ) := by push_cast; exact h5
    exact_mod_cast this
  rw [Finset.mem_Icc]
  constructor <;> linarith [abs_lt.mp h7]


theorem levelSet_limit_aux (hPW : PaleyWienerThm) {ψ : ℝ → ℝ} (hψc : Continuous ψ)
    (hψm : StrictMono ψ) (hψs : Function.Surjective ψ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : IsSepBy δ (phaseLevel ψ (Real.pi / 2))) {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hεπ : ∀ n, ε n < Real.pi)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hlev : ∀ᶠ n in atTop, ∀ f : ℂ → ℂ, MemPW f →
      pwNormSq f ≤ C₀ * sampleSum (phaseLevel ψ (Real.pi / 2 + ε n)) f) :
    ∀ f : ℂ → ℂ, MemPW f → pwNormSq f ≤ C₀ * sampleSum (phaseLevel ψ (Real.pi / 2)) f := by
  intro f hf
  have hπ := Real.pi_pos
  set e : ℝ ≃o ℝ := hψm.orderIsoOfSurjective ψ hψs with he
  have he_apply : ∀ x, e x = ψ x := fun x ↦ rfl
  have hgc : Continuous fun x : ℝ ↦ ‖f (x : ℂ)‖ₑ ^ 2 :=
    (ENNReal.continuous_pow 2).comp (hf.1.continuous.comp Complex.continuous_ofReal).enorm
  set T := sampleSum (phaseLevel ψ (Real.pi / 2)) f with hT
  have main : ∀ η : ℝ≥0∞, η ≠ 0 → pwNormSq f ≤ C₀ * (T + 2 * η) := by
    intro η hη
    obtain ⟨R, hR⟩ := plancherelPolya_tail_union hPW hδ hf hη
    set κ : ℝ := ψ (-R) - ψ (-R - 1) with hκ
    have hκpos : 0 < κ := by
      have := hψm (show -R - 1 < -R by linarith)
      linarith
    obtain ⟨N, hN⟩ := exists_finset_of_bounds (ψ (-R - 1)) (ψ (R + 1))
    set K : Finset ℤ := Finset.Icc (-(N : ℤ)) N with hK
    let x : ℤ → ℝ := fun k ↦ e.symm (Real.pi / 2 + k * Real.pi)
    let u : ℕ → ℤ → ℝ := fun n k ↦ e.symm (Real.pi / 2 + ε n + k * Real.pi)
    have hxinj : Function.Injective x := by
      intro j k hjk
      have := e.symm.injective hjk
      have : (j : ℝ) = k := by nlinarith
      exact_mod_cast this
    have huinj : ∀ n, Function.Injective (u n) := by
      intro n j k hjk
      have := e.symm.injective hjk
      have : (j : ℝ) = k := by nlinarith
      exact_mod_cast this
    have hxsub : x '' (K : Set ℤ) ⊆ phaseLevel ψ (Real.pi / 2) := by
      rintro _ ⟨k, -, rfl⟩
      refine ⟨k, ?_⟩
      have := e.apply_symm_apply (Real.pi / 2 + k * Real.pi)
      rw [he_apply] at this
      exact this
    have hTK : ∑ k ∈ K, ‖f (x k : ℂ)‖ₑ ^ 2 ≤ T := by
      rw [← sampleSum_image_finset hxinj]
      exact sampleSum_mono hxsub f
    have hTKfin : ∑ k ∈ K, ‖f (x k : ℂ)‖ₑ ^ 2 ≠ ⊤ := by
      apply ne_of_lt
      apply ENNReal.sum_lt_top.mpr
      intro k _
      exact ENNReal.pow_lt_top (enorm_lt_top)
    -- convergence of the finite sums
    have hconv : Tendsto (fun n ↦ ∑ k ∈ K, ‖f (u n k : ℂ)‖ₑ ^ 2) atTop
        (𝓝 (∑ k ∈ K, ‖f (x k : ℂ)‖ₑ ^ 2)) := by
      apply tendsto_finsetSum
      intro k _
      have h1 : Tendsto (fun n ↦ Real.pi / 2 + ε n + k * Real.pi) atTop
          (𝓝 (Real.pi / 2 + 0 + k * Real.pi)) :=
        (tendsto_const_nhds.add hεlim).add tendsto_const_nhds
      have h2 : Tendsto (fun n ↦ u n k) atTop (𝓝 (x k)) := by
        have := (e.symm.continuous.tendsto _).comp h1
        simpa [u, x, Function.comp_def] using this
      exact (hgc.tendsto _).comp h2
    have hev1 : ∀ᶠ n in atTop, ∑ k ∈ K, ‖f (u n k : ℂ)‖ₑ ^ 2 <
        ∑ k ∈ K, ‖f (x k : ℂ)‖ₑ ^ 2 + η :=
      hconv.eventually (gt_mem_nhds (ENNReal.lt_add_right hTKfin hη))
    have hev2 : ∀ᶠ n in atTop, ε n < κ := hεlim.eventually (gt_mem_nhds hκpos)
    obtain ⟨n, hn1, hn2, hn3⟩ := (hlev.and (hev2.and hev1)).exists
    obtain ⟨A, B, hAB, hA, hB⟩ := phaseLevel_sepBy_two_aux hψc hψm hsep (hε0 n) (hεπ n)
    have htail : sampleSum (phaseLevel ψ (Real.pi / 2 + ε n) ∩ {x : ℝ | R ≤ |x|}) f ≤ η := by
      rw [hAB]; exact hR A B hA hB
    have hsplit := sampleSum_split_aux (phaseLevel ψ (Real.pi / 2 + ε n)) f R
    have hfin : sampleSum (phaseLevel ψ (Real.pi / 2 + ε n) ∩ {x : ℝ | |x| < R}) f ≤
        ∑ k ∈ K, ‖f (u n k : ℂ)‖ₑ ^ 2 := by
      apply sampleSum_le_of_subset_image (huinj n)
      rintro y ⟨⟨k, hk⟩, hyR⟩
      have hyR' : |y| < R := hyR
      obtain ⟨hy1, hy2⟩ := abs_lt.mp hyR'
      refine ⟨k, ?_, ?_⟩
      · apply hN k
        · have h1 : ψ (-R) < ψ y := hψm hy1
          have := hk
          linarith
        · have h1 : ψ y < ψ R := hψm hy2
          have h2 : ψ R ≤ ψ (R + 1) := hψm.monotone (by linarith)
          have := hε0 n
          linarith
      · have := e.symm_apply_apply y
        rw [he_apply, hk] at this
        exact this
    calc pwNormSq f ≤ C₀ * sampleSum (phaseLevel ψ (Real.pi / 2 + ε n)) f := hn1 f hf
      _ = C₀ * (sampleSum (phaseLevel ψ (Real.pi / 2 + ε n) ∩ {x : ℝ | |x| < R}) f +
            sampleSum (phaseLevel ψ (Real.pi / 2 + ε n) ∩ {x : ℝ | R ≤ |x|}) f) := by
          rw [← hsplit]
      _ ≤ C₀ * ((∑ k ∈ K, ‖f (x k : ℂ)‖ₑ ^ 2 + η) + η) :=
          mul_le_mul' le_rfl (add_le_add (hfin.trans hn3.le) htail)
      _ ≤ C₀ * (T + 2 * η) := by
          rw [two_mul, ← add_assoc]
          gcongr
  -- the limit `η → 0`
  have hlim : Tendsto (fun m : ℕ ↦ C₀ * (T + 2 * (((m + 1 : ℕ) : ℝ≥0∞))⁻¹)) atTop
      (𝓝 (C₀ * (T + 2 * 0))) := by
    have h0 : Tendsto (fun m : ℕ ↦ (((m + 1 : ℕ) : ℝ≥0∞))⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have h1 : Tendsto (fun m : ℕ ↦ 2 * (((m + 1 : ℕ) : ℝ≥0∞))⁻¹) atTop (𝓝 (2 * 0)) :=
      ENNReal.Tendsto.const_mul h0 (Or.inr (by norm_num))
    exact ENNReal.Tendsto.const_mul (tendsto_const_nhds.add h1) (Or.inr hC₀)
  have := ge_of_tendsto' hlim (fun m ↦ main _ (by
    simp only [ne_eq, ENNReal.inv_eq_zero]
    exact ENNReal.natCast_ne_top _))
  simpa using this

end Suff
end FF
