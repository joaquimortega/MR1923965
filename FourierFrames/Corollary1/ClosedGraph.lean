import FourierFrames.PW.Complete
import FourierFrames.PW.PlancherelPolya

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF
namespace CG

/-- The `L²(ℝ)` class of a function of `PW`. -/
noncomputable def pwLp {f : ℂ → ℂ} (hf : MemPW f) : Lp ℂ 2 (volume : Measure ℝ) :=
  hf.2.2.toLp (fun x : ℝ ↦ f x)

theorem norm_pwLp_sq {f : ℂ → ℂ} (hf : MemPW f) : ‖pwLp hf‖ ^ 2 = (pwNormSq f).toReal := by
  unfold pwLp
  rw [Lp.norm_toLp, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.2.2.aestronglyMeasurable]
  have h2 : ∀ x : ℝ, ‖f x‖ₑ ^ ((2 : ℝ≥0∞).toReal) = ‖f x‖ₑ ^ 2 := by
    intro x
    rw [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  simp_rw [h2]
  rw [← ENNReal.toReal_rpow]
  have : (0 : ℝ) ≤ (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2).toReal := ENNReal.toReal_nonneg
  rw [← Real.rpow_natCast, ← Real.rpow_mul this]
  norm_num
  rfl


theorem ell2_enorm {Λ : Set ℝ} (a : lp (fun _ : Λ ↦ ℂ) 2) :
    ∑' i : Λ, ‖a i‖ₑ ^ 2 = ENNReal.ofReal (‖a‖ ^ 2) := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hs := (memℓp_gen_iff hp).mp a.2
  have h := lp.norm_rpow_eq_tsum hp a
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs h
  rw [h, ENNReal.ofReal_tsum_of_nonneg (fun i ↦ by positivity) hs]
  congr 1; ext i
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- A function on `Λ` with finite `ℓ²` sum gives an element of `ℓ²(Λ)`. -/
theorem exists_lp_of_sum_ne_top {Λ : Set ℝ} (f : ℂ → ℂ)
    (hf : ∑' i : Λ, ‖f ((i : ℝ) : ℂ)‖ₑ ^ 2 ≠ ⊤) :
    ∃ a : lp (fun _ : Λ ↦ ℂ) 2, ∀ i : Λ, a i = f ((i : ℝ) : ℂ) := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hs : Summable fun i : Λ ↦ ‖f ((i : ℝ) : ℂ)‖ ^ 2 := by
    have := ENNReal.summable_toReal hf
    refine this.congr fun i ↦ ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.toReal_ofReal (by positivity)]
  have hm : Memℓp (fun i : Λ ↦ f ((i : ℝ) : ℂ)) 2 := by
    rw [memℓp_gen_iff hp]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs
  exact ⟨⟨_, hm⟩, fun i ↦ rfl⟩


theorem pwLp_congr {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) (h : f = g) :
    pwLp hf = pwLp hg := by
  subst h; rfl

theorem pwLp_add {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) :
    pwLp (hf.add hg) = pwLp hf + pwLp hg := by
  unfold pwLp
  exact MemLp.toLp_add hf.2.2 hg.2.2

theorem pwLp_sub {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) :
    pwLp (hf.sub hg) = pwLp hf - pwLp hg := by
  unfold pwLp
  exact MemLp.toLp_sub hf.2.2 hg.2.2

theorem pwLp_smul {f : ℂ → ℂ} (hf : MemPW f) (c : ℂ) :
    pwLp (hf.const_mul c) = c • pwLp hf := by
  unfold pwLp
  exact MemLp.toLp_const_smul c hf.2.2

section Interp

variable {Λ : Set ℝ}

open Classical in
/-- Extension by zero of an `ℓ²(Λ)` datum. -/
noncomputable def extZero (a : lp (fun _ : Λ ↦ ℂ) 2) : ℝ → ℂ :=
  fun x ↦ if h : x ∈ Λ then a ⟨x, h⟩ else 0

theorem extZero_apply (a : lp (fun _ : Λ ↦ ℂ) 2) (i : Λ) : extZero a (i : ℝ) = a i := by
  simp [extZero]

theorem extZero_sum_ne_top (a : lp (fun _ : Λ ↦ ℂ) 2) : ∑' i : Λ, ‖extZero a i‖ₑ ^ 2 < ⊤ := by
  have : ∀ i : Λ, ‖extZero a (i : ℝ)‖ₑ ^ 2 = ‖a i‖ₑ ^ 2 := fun i ↦ by rw [extZero_apply]
  rw [tsum_congr this, ell2_enorm]
  exact ENNReal.ofReal_lt_top

variable (hcis : IsCompleteInterpolating Λ)
include hcis

theorem interp_exists (a : lp (fun _ : Λ ↦ ℂ) 2) :
    ∃! f : ℂ → ℂ, MemPW f ∧ ∀ x ∈ Λ, f x = extZero a x :=
  hcis (extZero a) (extZero_sum_ne_top a)

/-- The solution of the interpolation problem for the datum `a`. -/
noncomputable def interp (a : lp (fun _ : Λ ↦ ℂ) 2) : ℂ → ℂ :=
  (interp_exists hcis a).exists.choose

theorem interp_spec (a : lp (fun _ : Λ ↦ ℂ) 2) :
    MemPW (interp hcis a) ∧ ∀ x ∈ Λ, interp hcis a x = extZero a x :=
  (interp_exists hcis a).exists.choose_spec

theorem interp_unique (a : lp (fun _ : Λ ↦ ℂ) 2) {g : ℂ → ℂ} (hg : MemPW g)
    (h : ∀ x ∈ Λ, g x = extZero a x) : g = interp hcis a :=
  (interp_exists hcis a).unique ⟨hg, h⟩ (interp_spec hcis a)

theorem interp_add (a b : lp (fun _ : Λ ↦ ℂ) 2) :
    interp hcis (a + b) = interp hcis a + interp hcis b := by
  symm
  apply interp_unique hcis (a + b) ((interp_spec hcis a).1.add (interp_spec hcis b).1)
  intro x hx
  simp only [Pi.add_apply, (interp_spec hcis a).2 x hx, (interp_spec hcis b).2 x hx]
  simp [extZero, hx]

theorem interp_smul (c : ℂ) (a : lp (fun _ : Λ ↦ ℂ) 2) :
    interp hcis (c • a) = fun z ↦ c * interp hcis a z := by
  symm
  apply interp_unique hcis (c • a) ((interp_spec hcis a).1.const_mul c)
  intro x hx
  simp only [(interp_spec hcis a).2 x hx]
  simp [extZero, hx]

/-- The inverse of the sampling map, `ℓ²(Λ) → L²(ℝ)`. -/
noncomputable def Tmap : lp (fun _ : Λ ↦ ℂ) 2 →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun a := pwLp (interp_spec hcis a).1
  map_add' a b := by
    rw [pwLp_congr (interp_spec hcis (a + b)).1 ((interp_spec hcis a).1.add (interp_spec hcis b).1)
      (interp_add hcis a b), pwLp_add]
  map_smul' c a := by
    rw [pwLp_congr (interp_spec hcis (c • a)).1 ((interp_spec hcis a).1.const_mul c)
      (interp_smul hcis c a), pwLp_smul]
    rfl


theorem Tmap_apply (a : lp (fun _ : Λ ↦ ℂ) 2) :
    Tmap hcis a = pwLp (interp_spec hcis a).1 := rfl

theorem Tmap_continuous (hPW : PaleyWienerThm) : Continuous (Tmap hcis) := by
  apply LinearMap.continuous_of_seq_closed_graph
  intro u x y hu hTu
  set f : ℕ → ℂ → ℂ := fun n ↦ interp hcis (u n) with hfdef
  have hfm : ∀ n, MemPW (f n) := fun n ↦ (interp_spec hcis (u n)).1
  have hcauchy : CauchySeq (fun n ↦ Tmap hcis (u n)) := hTu.cauchySeq
  have hsub : ∀ m n, Tmap hcis (u m) - Tmap hcis (u n) = pwLp ((hfm m).sub (hfm n)) := by
    intro m n; rw [pwLp_sub (hfm m) (hfm n)]; rfl
  have hc : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      pwNormSq (fun z ↦ f m z - f n z) < ε := by
    intro ε hε
    obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.mp (pos_iff_ne_zero.mpr hε)
    have hr : 0 < r := ENNReal.ofReal_pos.mp hr1
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hcauchy (Real.sqrt r) (Real.sqrt_pos.mpr hr)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have hd := hN m hm n hn
    rw [dist_eq_norm, hsub] at hd
    have h1 : ‖pwLp ((hfm m).sub (hfm n))‖ ^ 2 < r := by
      have := pow_lt_pow_left₀ hd (norm_nonneg _) two_ne_zero
      rwa [Real.sq_sqrt hr.le] at this
    rw [norm_pwLp_sq] at h1
    have h2 : pwNormSq (fun z ↦ f m z - f n z) = ENNReal.ofReal (pwNormSq (f m - f n)).toReal :=
      (ENNReal.ofReal_toReal (pwNormSq_ne_top ((hfm m).sub (hfm n)))).symm
    rw [h2]
    exact lt_trans ((ENNReal.ofReal_lt_ofReal_iff hr).mpr h1) hr2
  obtain ⟨g, hg, hloc, hlim⟩ := pw_complete hPW hfm hc
  -- `T u_n → pwLp g`
  have hT2 : Tendsto (fun n ↦ Tmap hcis (u n)) atTop (𝓝 (pwLp hg)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : ∀ n, ‖Tmap hcis (u n) - pwLp hg‖ =
        Real.sqrt (pwNormSq (fun z ↦ f n z - g z)).toReal := by
      intro n
      have : Tmap hcis (u n) - pwLp hg = pwLp ((hfm n).sub hg) := by
        rw [pwLp_sub (hfm n) hg]; rfl
      rw [this, ← norm_pwLp_sq, Real.sqrt_sq (norm_nonneg _)]
    simp_rw [h1]
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
    simpa [Function.comp_def] using h3
  have hy : y = pwLp hg := tendsto_nhds_unique hTu hT2
  -- `g` interpolates `x`
  have hg_eq : g = interp hcis x := by
    apply interp_unique hcis x hg
    intro l hl
    have h1 : Tendsto (fun n ↦ f n l) atTop (𝓝 (g l)) := (hloc.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ l)
    have h2 : Tendsto (fun n ↦ f n l) atTop (𝓝 (x ⟨l, hl⟩)) := by
      have : ∀ n, f n l = u n ⟨l, hl⟩ := fun n ↦ by
        rw [hfdef]; simp only
        rw [(interp_spec hcis (u n)).2 l hl]
        exact extZero_apply (u n) ⟨l, hl⟩
      simp_rw [this]
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_)
        (tendsto_iff_dist_tendsto_zero.mp hu)
      rw [dist_eq_norm, dist_eq_norm]
      have := lp.norm_apply_le_norm (by norm_num) (u n - x) ⟨l, hl⟩
      simpa using this
    rw [tendsto_nhds_unique h1 h2]
    exact (extZero_apply x ⟨l, hl⟩).symm
  rw [hy, Tmap_apply]
  exact pwLp_congr hg (interp_spec hcis x).1 hg_eq

end Interp


theorem isSampling_aux (hPW : PaleyWienerThm) {Λ : Set ℝ} (hΛ : IsSeparated Λ)
    (hcis : IsCompleteInterpolating Λ) : IsSampling Λ := by
  obtain ⟨δ, hδ, hδsep⟩ := hΛ
  obtain ⟨B, hB⟩ := plancherelPolya hPW hδ
  let T' : lp (fun _ : Λ ↦ ℂ) 2 →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
    { toLinearMap := Tmap hcis, cont := Tmap_continuous hcis hPW }
  set C : ℝ := ‖T'‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  -- the main inequality
  have key : ∀ f : ℂ → ℂ, MemPW f →
      pwNormSq f ≤ ENNReal.ofReal (C ^ 2) * sampleSum Λ f := by
    intro f hf
    have hfin : sampleSum Λ f ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (pwNormSq_ne_top hf))
        (hB Λ hδsep f hf)
    obtain ⟨a, ha⟩ := exists_lp_of_sum_ne_top (Λ := Λ) f hfin
    have hint : f = interp hcis a := by
      apply interp_unique hcis a hf
      intro x hx
      exact ((extZero_apply a ⟨x, hx⟩).trans (ha ⟨x, hx⟩)).symm
    have hTa : Tmap hcis a = pwLp hf := by
      rw [Tmap_apply]; exact pwLp_congr (interp_spec hcis a).1 hf hint.symm
    have h1 : ‖pwLp hf‖ ≤ C * ‖a‖ := by
      rw [← hTa]; exact T'.le_opNorm a
    have h2 : (pwNormSq f).toReal ≤ C ^ 2 * ‖a‖ ^ 2 := by
      rw [← norm_pwLp_sq hf]
      calc ‖pwLp hf‖ ^ 2 ≤ (C * ‖a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = C ^ 2 * ‖a‖ ^ 2 := by ring
    have h3 : sampleSum Λ f = ENNReal.ofReal (‖a‖ ^ 2) := by
      unfold sampleSum
      rw [← ell2_enorm]
      congr 1; ext i; rw [ha i]
    calc pwNormSq f = ENNReal.ofReal (pwNormSq f).toReal :=
          (ENNReal.ofReal_toReal (pwNormSq_ne_top hf)).symm
      _ ≤ ENNReal.ofReal (C ^ 2 * ‖a‖ ^ 2) := ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (C ^ 2) * sampleSum Λ f := by
          rw [h3, ENNReal.ofReal_mul (by positivity)]
  refine ⟨(C ^ 2 + 1).toNNReal⁻¹, B, ?_, fun f hf ↦ ⟨?_, hB Λ hδsep f hf⟩⟩
  · exact inv_pos.mpr (Real.toNNReal_pos.mpr (by positivity))
  · have hK : (0 : ℝ) < C ^ 2 + 1 := by positivity
    have hone : (((C ^ 2 + 1).toNNReal⁻¹ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (C ^ 2 + 1) = 1 := by
      rw [ENNReal.ofReal, ← ENNReal.coe_mul, inv_mul_cancel₀ (Real.toNNReal_pos.mpr hK).ne']
      simp
    calc (((C ^ 2 + 1).toNNReal⁻¹ : ℝ≥0) : ℝ≥0∞) * pwNormSq f
        ≤ (((C ^ 2 + 1).toNNReal⁻¹ : ℝ≥0) : ℝ≥0∞) *
            (ENNReal.ofReal (C ^ 2 + 1) * sampleSum Λ f) :=
          mul_le_mul' le_rfl ((key f hf).trans (mul_le_mul'
            (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl))
      _ = sampleSum Λ f := by rw [← mul_assoc, hone, one_mul]

end CG
end FF
