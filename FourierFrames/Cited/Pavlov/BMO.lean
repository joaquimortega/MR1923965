import FourierFrames.Cited.Pavlov.Fatou

/-!
# Elementary BMO algebra and logarithmic weights

Interval estimates for the existing BMO predicate. See `blueprint/P5_BMO.md`.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace FF.Pavlov

private theorem intervalIntegrable_of_local {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    (a b : ℝ) : IntervalIntegrable h volume a b :=
  (hh.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

theorem intervalMean_sub_const_eq {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) (c : ℝ) :
    intervalMean h a b - c =
      (b - a)⁻¹ * ∫ t in a..b, (h t - c) := by
  rw [intervalIntegral.integral_sub (intervalIntegrable_of_local hh a b)
    intervalIntegrable_const, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_sub]
  unfold intervalMean
  field_simp

theorem abs_intervalMean_sub_const_le {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) (c : ℝ) :
    |intervalMean h a b - c| ≤
      (b - a)⁻¹ * ∫ t in a..b, |h t - c| := by
  rw [intervalMean_sub_const_eq hh hab, abs_mul,
    abs_of_pos (inv_pos.mpr (sub_pos.mpr hab))]
  gcongr
  simpa only [Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_integral_norm (f := fun t ↦ h t - c) hab.le

theorem meanOsc_le_twice_comparison {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) (c : ℝ) :
    meanOsc h a b ≤ 2 * ((b - a)⁻¹ * ∫ t in a..b, |h t - c|) := by
  have hi := intervalIntegrable_of_local hh a b
  have he := abs_intervalMean_sub_const_le hh hab c
  have hb : (∫ t in a..b, |h t - intervalMean h a b|) ≤
      (∫ t in a..b, |h t - c|) + (b-a) * |intervalMean h a b - c| := by
    calc
      _ ≤ ∫ t in a..b, (|h t-c| + |intervalMean h a b-c|) := by
        apply intervalIntegral.integral_mono_on hab.le (hi.sub intervalIntegrable_const).abs
          ((hi.sub intervalIntegrable_const).abs.add intervalIntegrable_const)
        intro t _
        exact (abs_sub_le (h t) c (intervalMean h a b)).trans_eq (by rw [abs_sub_comm c])
      _ = _ := by rw [intervalIntegral.integral_add
        (hi.sub intervalIntegrable_const).abs intervalIntegrable_const,
        intervalIntegral.integral_const]; rfl
  unfold meanOsc
  have hp := inv_nonneg.mpr (sub_pos.mpr hab).le
  have hb' := mul_le_mul_of_nonneg_left hb hp
  have hne := (sub_pos.mpr hab).ne'
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hne, one_mul] at hb'
  linarith

theorem meanOsc_nonneg {h : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    0 ≤ meanOsc h a b := by
  exact mul_nonneg (inv_nonneg.mpr (sub_pos.mpr hab).le)
    (intervalIntegral.integral_nonneg hab.le (fun _ _ ↦ abs_nonneg _))

theorem memBMO_of_comparison {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {M : ℝ} (hM : ∀ a b : ℝ, a < b →
      ∃ c : ℝ, (b - a)⁻¹ * ∫ t in a..b, |h t - c| ≤ M) :
    MemBMO h := by
  refine ⟨hh, 2*M, fun a b hab ↦ ?_⟩
  obtain ⟨c, hc⟩ := hM a b hab
  exact (meanOsc_le_twice_comparison hh hab c).trans (by linarith)

private theorem intervalMean_const (c : ℝ) {a b : ℝ} (hab : a < b) :
    intervalMean (fun _ : ℝ ↦ c) a b = c := by
  simp only [intervalMean, intervalIntegral.integral_const, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (sub_pos.mpr hab).ne', one_mul]

private theorem intervalMean_add {f g : ℝ → ℝ}
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g) (a b : ℝ) :
    intervalMean (fun t ↦ f t + g t) a b = intervalMean f a b + intervalMean g a b := by
  simp only [intervalMean, intervalIntegral.integral_add
    (intervalIntegrable_of_local hf a b) (intervalIntegrable_of_local hg a b), mul_add]

private theorem intervalMean_const_mul (h : ℝ → ℝ) (c a b : ℝ) :
    intervalMean (fun t ↦ c * h t) a b = c * intervalMean h a b := by
  simp only [intervalMean, intervalIntegral.integral_const_mul]
  ring

theorem meanOsc_const (c : ℝ) {a b : ℝ} (hab : a < b) :
    meanOsc (fun _ : ℝ ↦ c) a b = 0 := by
  simp [meanOsc, intervalMean_const c hab]

theorem meanOsc_add_const {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    (c : ℝ) {a b : ℝ} (hab : a < b) :
    meanOsc (fun t ↦ h t + c) a b = meanOsc h a b := by
  have hc : LocallyIntegrable (fun _ : ℝ ↦ c) := continuous_const.locallyIntegrable
  simp only [meanOsc, intervalMean_add hh hc, intervalMean_const c hab,
    add_sub_add_right_eq_sub]

theorem meanOsc_const_mul (h : ℝ → ℝ) (c a b : ℝ) :
    meanOsc (fun t ↦ c * h t) a b = |c| * meanOsc h a b := by
  simp only [meanOsc, intervalMean_const_mul, ← mul_sub, abs_mul,
    intervalIntegral.integral_const_mul]
  ring

theorem meanOsc_add_le {f g : ℝ → ℝ}
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    {a b : ℝ} (hab : a < b) :
    meanOsc (fun t ↦ f t + g t) a b ≤ meanOsc f a b + meanOsc g a b := by
  have hi := intervalIntegrable_of_local hf a b
  have hj := intervalIntegrable_of_local hg a b
  unfold meanOsc
  rw [intervalMean_add hf hg, ← mul_add]
  gcongr
  calc
    _ ≤ ∫ t in a..b, (|f t - intervalMean f a b| + |g t - intervalMean g a b|) := by
      apply intervalIntegral.integral_mono_on hab.le
        ((hi.add hj).sub intervalIntegrable_const).abs
        ((hi.sub intervalIntegrable_const).abs.add (hj.sub intervalIntegrable_const).abs)
      intro t _
      convert abs_add_le (f t - intervalMean f a b) (g t - intervalMean g a b) using 1
      congr 1
      ring
    _ = _ := intervalIntegral.integral_add (hi.sub intervalIntegrable_const).abs
      (hj.sub intervalIntegrable_const).abs

theorem meanOsc_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g)
    (a b : ℝ) : meanOsc f a b = meanOsc g a b := by
  have hm : intervalMean f a b = intervalMean g a b := by
    unfold intervalMean
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hfg] with t ht _
    exact ht
  unfold meanOsc
  rw [hm]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hfg] with t ht _
  rw [ht]

theorem memBMO_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) :
    MemBMO f ↔ MemBMO g := by
  constructor
  · rintro ⟨hf, M, hM⟩
    exact ⟨hf.congr hfg, M, fun a b hab ↦ (meanOsc_congr_ae hfg a b) ▸ hM a b hab⟩
  · rintro ⟨hg, M, hM⟩
    exact ⟨hg.congr hfg.symm, M, fun a b hab ↦ (meanOsc_congr_ae hfg.symm a b) ▸ hM a b hab⟩

theorem memBMO_const (c : ℝ) : MemBMO (fun _ : ℝ ↦ c) := by
  exact ⟨continuous_const.locallyIntegrable, 0, fun _ _ hab ↦ (meanOsc_const c hab).le⟩

theorem memBMO_const_mul {h : ℝ → ℝ} (hh : MemBMO h) (c : ℝ) :
    MemBMO (fun t ↦ c * h t) := by
  obtain ⟨hi, M, hM⟩ := hh
  refine ⟨hi.smul c, |c| * M, fun a b hab ↦ ?_⟩
  rw [meanOsc_const_mul h c a b]
  exact mul_le_mul_of_nonneg_left (hM a b hab) (abs_nonneg c)

theorem memBMO_add {f g : ℝ → ℝ} (hf : MemBMO f) (hg : MemBMO g) :
    MemBMO (fun t ↦ f t + g t) := by
  obtain ⟨hi, M, hM⟩ := hf
  obtain ⟨hj, N, hN⟩ := hg
  refine ⟨hi.add hj, M+N, fun a b hab ↦ ?_⟩
  exact (meanOsc_add_le hi hj hab).trans (add_le_add (hM a b hab) (hN a b hab))

theorem memBMO_neg {h : ℝ → ℝ} (hh : MemBMO h) :
    MemBMO (fun t ↦ -h t) := by
  simpa only [neg_one_mul] using memBMO_const_mul hh (-1)

theorem memBMO_sub {f g : ℝ → ℝ} (hf : MemBMO f) (hg : MemBMO g) :
    MemBMO (fun t ↦ f t - g t) := by
  simpa only [sub_eq_add_neg] using memBMO_add hf (memBMO_neg hg)

theorem meanOsc_le_of_ae_abs_le {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {K : ℝ} (hK : ∀ᵐ t : ℝ, |h t| ≤ K) {a b : ℝ} (hab : a < b) :
    meanOsc h a b ≤ 2 * K := by
  have he : (∫ t in a..b, |h t|) ≤ (b-a)*K := by
    calc
      _ ≤ ∫ _ in a..b, K := intervalIntegral.integral_mono_ae hab.le
        (intervalIntegrable_of_local hh a b).abs intervalIntegrable_const hK
      _ = _ := by simp
  have hp := inv_nonneg.mpr (sub_pos.mpr hab).le
  have he' := mul_le_mul_of_nonneg_left he hp
  rw [← mul_assoc, inv_mul_cancel₀ (sub_pos.mpr hab).ne', one_mul] at he'
  have hh0 := meanOsc_le_twice_comparison hh hab 0
  simp only [sub_zero] at hh0
  exact hh0.trans (mul_le_mul_of_nonneg_left he' (by norm_num))

theorem memBMO_of_ae_abs_le {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {K : ℝ} (hK : ∀ᵐ t : ℝ, |h t| ≤ K) : MemBMO h := by
  exact ⟨hh, 2*K, fun _ _ hab ↦ meanOsc_le_of_ae_abs_le hh hK hab⟩

theorem memBMO_add_ae_bounded {f g : ℝ → ℝ} (hf : MemBMO f)
    (hg : LocallyIntegrable g) {K : ℝ} (hK : ∀ᵐ t : ℝ, |g t| ≤ K) :
    MemBMO (fun t ↦ f t + g t) :=
  memBMO_add hf (memBMO_of_ae_abs_le hg hK)

private theorem meanOsc_le_add_L1 {f g : ℝ → ℝ}
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    {a b : ℝ} (hab : a < b) :
    meanOsc f a b ≤ meanOsc g a b +
      2 * ((b - a)⁻¹ * ∫ t in a..b, |f t - g t|) := by
  have hs := meanOsc_add_le hg (hf.sub hg) hab
  have hfun : (fun t ↦ g t + (f t - g t)) = f := by ext t; ring
  change meanOsc (fun t ↦ g t + (f t - g t)) a b ≤ _ at hs
  rw [hfun] at hs
  have hc := meanOsc_le_twice_comparison (hf.sub hg) hab 0
  simp only [sub_zero] at hc
  change meanOsc (f-g) a b ≤ 2 * ((b-a)⁻¹ * ∫ t in a..b, |f t-g t|) at hc
  exact hs.trans (by linarith)

theorem abs_meanOsc_sub_le {f g : ℝ → ℝ}
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    {a b : ℝ} (hab : a < b) :
    |meanOsc f a b - meanOsc g a b| ≤
      2 * ((b - a)⁻¹ * ∫ t in a..b, |f t - g t|) := by
  have h₁ := meanOsc_le_add_L1 hf hg hab
  have h₂ := meanOsc_le_add_L1 hg hf hab
  simp_rw [abs_sub_comm (g _) (f _)] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem meanOsc_le_of_tendsto_local_L1 {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M)
    (hlim : ∀ a b : ℝ, a < b →
      Tendsto (fun n ↦ ∫ t in a..b, |f n t - g t|) atTop (𝓝 0)) :
    ∀ a b : ℝ, a < b → meanOsc g a b ≤ M := by
  intro a b hab
  have hbound : ∀ᶠ n in atTop, meanOsc g a b ≤
      M + 2 * ((b-a)⁻¹ * ∫ t in a..b, |f n t - g t|) := by
    filter_upwards [] with n
    have he := abs_meanOsc_sub_le (hf n) hg hab
    have hm := hM n a b hab
    have hl := (abs_le.mp he).1
    linarith
  have hl : Tendsto (fun n ↦ M + 2 * ((b-a)⁻¹ * ∫ t in a..b, |f n t-g t|))
      atTop (𝓝 (M + 2 * ((b-a)⁻¹ * 0))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_const_nhds.mul (hlim a b hab)))
  simpa only [mul_zero, add_zero] using ge_of_tendsto hl hbound

theorem memBMO_of_tendsto_local_L1 {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M)
    (hlim : ∀ a b : ℝ, a < b →
      Tendsto (fun n ↦ ∫ t in a..b, |f n t - g t|) atTop (𝓝 0)) :
    MemBMO g := by
  exact ⟨hg, M, meanOsc_le_of_tendsto_local_L1 hf hg hM hlim⟩

/-- Pairwise oscillation integral over a bounded interval. -/
def intervalPairIntegral (h : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, |h p.1-h p.2|
    ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))

theorem integrable_intervalPair {h : ℝ → ℝ} (hh : LocallyIntegrable h) (a b : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ |h p.1-h p.2|)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
  have hi : Integrable h (volume.restrict (Ioc a b)) :=
    (hh.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  exact ((hi.comp_fst _).sub (hi.comp_snd _)).abs

theorem meanOsc_le_pairIntegral {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) :
    meanOsc h a b ≤ (b-a)⁻¹ ^ 2 * intervalPairIntegral h a b := by
  let ρ := volume.restrict (Ioc a b)
  have hi : Integrable h ρ :=
    (hh.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hp := integrable_intervalPair hh a b
  have hinner : Integrable (fun x ↦ ∫ y, |h x-h y| ∂ρ) ρ := hp.integral_prod_left
  have hcenter : Integrable (fun x ↦ |h x-intervalMean h a b|) ρ :=
    (hi.sub (integrable_const _)).abs
  have hbound : ∀ x : ℝ, |h x-intervalMean h a b| ≤
      (b-a)⁻¹ * ∫ y, |h x-h y| ∂ρ := by
    intro x
    have he := abs_intervalMean_sub_const_le hh hab (h x)
    rw [intervalIntegral.integral_of_le hab.le] at he
    simpa only [abs_sub_comm] using he
  have he := integral_mono hcenter (hinner.const_mul _) hbound
  rw [integral_const_mul] at he
  have hp' : (∫ x, ∫ y, |h x-h y| ∂ρ ∂ρ) = intervalPairIntegral h a b :=
    integral_integral hp
  rw [hp'] at he
  have he' := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (sub_pos.mpr hab).le)
  simpa only [meanOsc, intervalIntegral.integral_of_le hab.le, ρ, sq, mul_assoc] using he'

theorem pairIntegral_le_twice_meanOsc {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) :
    intervalPairIntegral h a b ≤ 2 * (b-a)^2 * meanOsc h a b := by
  let ρ := volume.restrict (Ioc a b)
  have hi : Integrable (fun x ↦ |h x-intervalMean h a b|) ρ :=
    ((hh.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self |>.sub
      (integrable_const _)).abs
  have hbound : ∀ p : ℝ × ℝ, |h p.1-h p.2| ≤
      |h p.1-intervalMean h a b| + |h p.2-intervalMean h a b| := by
    intro p
    exact (abs_sub_le (h p.1) (intervalMean h a b) (h p.2)).trans_eq
      (by rw [abs_sub_comm (intervalMean h a b)])
  have he := integral_mono (integrable_intervalPair hh a b)
    ((hi.comp_fst ρ).add (hi.comp_snd ρ)) hbound
  simp only [Pi.add_apply] at he
  rw [integral_add (hi.comp_fst ρ) (hi.comp_snd ρ),
    integral_fun_fst (fun x ↦ |h x-intervalMean h a b|),
    integral_fun_snd (fun x ↦ |h x-intervalMean h a b|)] at he
  have hm : ρ.real univ = b-a := by
    simp only [ρ, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.toReal_ofReal (sub_pos.mpr hab).le
  rw [hm, smul_eq_mul] at he
  change intervalPairIntegral h a b ≤ _ at he
  have heq : 2 * (b-a)^2 * meanOsc h a b =
      (b-a) * (∫ x, |h x-intervalMean h a b| ∂ρ) +
      (b-a) * (∫ x, |h x-intervalMean h a b| ∂ρ) := by
    simp only [meanOsc, intervalIntegral.integral_of_le hab.le, ρ]
    field_simp
    ring
  rw [heq]
  exact he

/-- A uniform BMO bound survives an a.e. limit, up to a factor two. -/
theorem meanOsc_le_of_ae_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M) :
    ∀ a b : ℝ, a < b → meanOsc g a b ≤ 2*M := by
  intro a b hab
  let ρ := volume.restrict (Ioc a b)
  have hl : ∀ᵐ p : ℝ × ℝ ∂ρ.prod ρ,
      Tendsto (fun n ↦ |f n p.1-f n p.2|) atTop (𝓝 (|g p.1-g p.2|)) := by
    have h₁ := (Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := ρ)).ae
      (ae_restrict_of_ae hlim)
    have h₂ := (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := ρ)).ae
      (ae_restrict_of_ae hlim)
    filter_upwards [h₁, h₂] with p hp hq
    exact (hp.sub hq).abs
  have hb : ∀ n, intervalPairIntegral (f n) a b ≤ 2*(b-a)^2*M := by
    intro n
    exact (pairIntegral_le_twice_meanOsc (hf n) hab).trans
      (mul_le_mul_of_nonneg_left (hM n a b hab) (by positivity))
  have he : intervalPairIntegral g a b ≤ 2*(b-a)^2*M :=
    integral_le_of_ae_tendsto_nonneg
      (fun n ↦ integrable_intervalPair (hf n) a b) (integrable_intervalPair hg a b)
      (fun _ ↦ Eventually.of_forall fun _ ↦ abs_nonneg _)
      (Eventually.of_forall fun _ ↦ abs_nonneg _) hl hb
  have he' := mul_le_mul_of_nonneg_left he (sq_nonneg ((b-a)⁻¹))
  have hnorm : (b-a)⁻¹ ^ 2 * (2*(b-a)^2*M) = 2*M := by
    field_simp
  rw [hnorm] at he'
  exact (meanOsc_le_pairIntegral hg hab).trans he'

theorem memBMO_of_ae_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M) :
    MemBMO g := by
  exact ⟨hg, 2*M, meanOsc_le_of_ae_tendsto hf hg hlim hM⟩

theorem meanOsc_le_of_ae_tendsto_comparison
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ a b : ℝ, a < b →
      ∃ (c : ℕ → ℝ) (c₀ : ℝ), Tendsto c atTop (𝓝 c₀) ∧
        ∀ n, (b - a)⁻¹ * ∫ t in a..b, |f n t - c n| ≤ M) :
    ∀ a b : ℝ, a < b → meanOsc g a b ≤ 2*M := by
  intro a b hab
  obtain ⟨c, c₀, hc, hb⟩ := hM a b hab
  let ρ := volume.restrict (Ioc a b)
  have hi (n : ℕ) : Integrable (fun t ↦ |f n t-c n|) ρ :=
    (((hf n).integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self |>.sub
      (integrable_const _)).abs
  have hj : Integrable (fun t ↦ |g t-c₀|) ρ :=
    ((hg.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self |>.sub
      (integrable_const _)).abs
  have hl : ∀ᵐ t ∂ρ, Tendsto (fun n ↦ |f n t-c n|) atTop (𝓝 (|g t-c₀|)) := by
    filter_upwards [ae_restrict_of_ae hlim] with t ht
    exact (ht.sub hc).abs
  have hb' : ∀ n, (∫ t, |f n t-c n| ∂ρ) ≤ (b-a)*M := by
    intro n
    have he := hb n
    rw [intervalIntegral.integral_of_le hab.le] at he
    exact (inv_mul_le_iff₀ (sub_pos.mpr hab)).mp he
  have he := integral_le_of_ae_tendsto_nonneg hi hj
    (fun _ ↦ Eventually.of_forall fun _ ↦ abs_nonneg _)
    (Eventually.of_forall fun _ ↦ abs_nonneg _) hl hb'
  have he' := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (sub_pos.mpr hab).le)
  rw [← mul_assoc, inv_mul_cancel₀ (sub_pos.mpr hab).ne', one_mul] at he'
  have hx := meanOsc_le_twice_comparison hg hab c₀
  rw [intervalIntegral.integral_of_le hab.le] at hx
  exact hx.trans (mul_le_mul_of_nonneg_left he' (by norm_num))

theorem memBMO_of_ae_tendsto_comparison
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ a b : ℝ, a < b →
      ∃ (c : ℕ → ℝ) (c₀ : ℝ), Tendsto c atTop (𝓝 c₀) ∧
        ∀ n, (b - a)⁻¹ * ∫ t in a..b, |f n t - c n| ≤ M) :
    MemBMO g := by
  exact ⟨hg, 2*M, meanOsc_le_of_ae_tendsto_comparison hf hg hlim hM⟩

theorem memBMO_of_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M) :
    MemBMO g :=
  memBMO_of_ae_tendsto hf hg (Eventually.of_forall hlim) hM

theorem abs_log_le_add_inv {s : ℝ} (hs : 0 < s) :
    |Real.log s| ≤ s + s⁻¹ := by
  apply abs_le.mpr
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hs
    linarith
  · have h := Real.log_le_sub_one_of_pos hs
    have hi := inv_pos.mpr hs
    linarith

theorem locallyIntegrable_log_of_pos_inv {w : ℝ → ℝ}
    (hw : LocallyIntegrable w)
    (hwi : LocallyIntegrable (fun t ↦ (w t)⁻¹))
    (hpos : ∀ᵐ t : ℝ, 0 < w t) :
    LocallyIntegrable (fun t ↦ Real.log (w t)) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hi := (hw.integrableOn_isCompact hK).add (hwi.integrableOn_isCompact hK)
  have hm : AEStronglyMeasurable (fun t ↦ Real.log (w t)) volume :=
    (Real.measurable_log.comp_aemeasurable hw.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  refine hi.mono' (hm.restrict) ?_
  filter_upwards [ae_restrict_of_ae hpos] with t ht
  exact abs_log_le_add_inv ht

theorem intervalMean_pos_of_ae_pos {w : ℝ → ℝ}
    (hw : LocallyIntegrable w) (hpos : ∀ᵐ t : ℝ, 0 < w t)
    {a b : ℝ} (hab : a < b) : 0 < intervalMean w a b := by
  have hi : Integrable w (volume.restrict (Ioc a b)) :=
    (hw.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hp : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 < w t := ae_restrict_of_ae hpos
  have hs : Function.support w =ᵐ[volume.restrict (Ioc a b)] univ := by
    filter_upwards [hp] with t ht
    simp [Function.mem_support, ht.ne']
  have hm : 0 < (volume.restrict (Ioc a b)) (Function.support w) := by
    rw [measure_congr hs, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  have hit := (integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ ht ↦ ht.le) hi).mpr hm
  exact mul_pos (inv_pos.mpr (sub_pos.mpr hab))
    (by simpa only [intervalIntegral.integral_of_le hab.le] using hit)

theorem log_comparison_le_of_A2 {w : ℝ → ℝ}
    (hw : LocallyIntegrable w)
    (hwi : LocallyIntegrable (fun t ↦ (w t)⁻¹))
    (hpos : ∀ᵐ t : ℝ, 0 < w t)
    {C a b : ℝ} (hab : a < b)
    (hA2 : intervalMean w a b * intervalMean (fun t ↦ (w t)⁻¹) a b ≤ C) :
    (b - a)⁻¹ * ∫ t in a..b,
      |Real.log (w t) - Real.log (intervalMean w a b)| ≤ 1 + C := by
  let A := intervalMean w a b
  have hA : 0 < A := intervalMean_pos_of_ae_pos hw hpos hab
  have hwI := intervalIntegrable_of_local hw a b
  have hwiI := intervalIntegrable_of_local hwi a b
  have hlI := intervalIntegrable_of_local (locallyIntegrable_log_of_pos_inv hw hwi hpos) a b
  have hp : ∀ᵐ t : ℝ, |Real.log (w t) - Real.log A| ≤ w t / A + A * (w t)⁻¹ := by
    filter_upwards [hpos] with t ht
    rw [← Real.log_div ht.ne' hA.ne']
    convert abs_log_le_add_inv (div_pos ht hA) using 1
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  have he := intervalIntegral.integral_mono_ae hab.le
    (hlI.sub intervalIntegrable_const).abs
    ((hwI.div_const A).add (hwiI.const_mul A)) hp
  rw [intervalIntegral.integral_add (hwI.div_const A) (hwiI.const_mul A),
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul] at he
  have he' := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (sub_pos.mpr hab).le)
  have hnorm : (b-a)⁻¹ * ((∫ t in a..b, w t) / A) = 1 := by
    rw [← mul_div_assoc]
    exact div_self hA.ne'
  rw [mul_add, hnorm] at he'
  have hsecond : (b-a)⁻¹ * (A * ∫ t in a..b, (w t)⁻¹) =
      A * intervalMean (fun t ↦ (w t)⁻¹) a b := by
    unfold intervalMean
    ring
  rw [hsecond] at he'
  exact he'.trans (by dsimp [A]; linarith)

theorem meanOsc_log_le_of_A2 {w : ℝ → ℝ}
    (hw : LocallyIntegrable w)
    (hwi : LocallyIntegrable (fun t ↦ (w t)⁻¹))
    (hpos : ∀ᵐ t : ℝ, 0 < w t)
    {C a b : ℝ} (hab : a < b)
    (hA2 : intervalMean w a b * intervalMean (fun t ↦ (w t)⁻¹) a b ≤ C) :
    meanOsc (fun t ↦ Real.log (w t)) a b ≤ 2 * (1 + C) := by
  exact (meanOsc_le_twice_comparison (locallyIntegrable_log_of_pos_inv hw hwi hpos)
    hab (Real.log (intervalMean w a b))).trans
    (mul_le_mul_of_nonneg_left (log_comparison_le_of_A2 hw hwi hpos hab hA2) (by norm_num))

theorem memBMO_log_of_A2 {w : ℝ → ℝ}
    (hw : LocallyIntegrable w)
    (hwi : LocallyIntegrable (fun t ↦ (w t)⁻¹))
    (hpos : ∀ᵐ t : ℝ, 0 < w t)
    {C : ℝ} (hA2 : ∀ a b : ℝ, a < b →
      intervalMean w a b * intervalMean (fun t ↦ (w t)⁻¹) a b ≤ C) :
    MemBMO (fun t ↦ Real.log (w t)) := by
  exact ⟨locallyIntegrable_log_of_pos_inv hw hwi hpos, 2*(1+C),
    fun a b hab ↦ meanOsc_log_le_of_A2 hw hwi hpos hab (hA2 a b hab)⟩

end FF.Pavlov
