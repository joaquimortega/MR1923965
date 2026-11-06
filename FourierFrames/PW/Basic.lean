import FourierFrames.Defs

/-!
# M01 — Paley–Wiener space toolkit: basic facts

See `blueprint/M01_PW.md`.  Everything is derived from `hPW : PaleyWienerThm`; the lemmas that do
not need it (algebra of `PW`, translations, `f^*`, `mul_div_sub`) do not take it.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Notation for `L²(-π, π)` and the Fourier–Laplace transform -/

/-- `g ∈ L²(-π, π)`. -/
def MemL2pi (g : ℝ → ℂ) : Prop :=
  MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))

/-- `‖g‖²_{L²(-π,π)}`, in `ℝ≥0∞`. -/
def l2piSq (g : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ ^ 2

/-- The transform `z ↦ ∫_{-π}^{π} g(t) e^{izt} dt` of the Paley–Wiener theorem. -/
def pwFT (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * z * t)

/-- `Λ` is `δ`-separated: distinct points are at distance `≥ δ`. -/
def IsSepBy (δ : ℝ) (Λ : Set ℝ) : Prop :=
  ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ |a - b|

theorem isSeparated_iff_exists_isSepBy {Λ : Set ℝ} :
    IsSeparated Λ ↔ ∃ δ : ℝ, 0 < δ ∧ IsSepBy δ Λ := Iff.rfl

theorem IsSepBy.mono {δ δ' : ℝ} {Λ Λ' : Set ℝ} (h : IsSepBy δ Λ) (hδ : δ' ≤ δ) (hΛ : Λ' ⊆ Λ) :
    IsSepBy δ' Λ' :=
  fun a ha b hb hab ↦ hδ.trans (h a (hΛ ha) b (hΛ hb) hab)

theorem MemL2pi.integrableOn {g : ℝ → ℂ} (hg : MemL2pi g) :
    IntegrableOn g (Ioc (-Real.pi) Real.pi) :=
  hg.integrable (by norm_num)

theorem MemL2pi.integrableOn_mul_exp {g : ℝ → ℂ} (hg : MemL2pi g) (z : ℂ) :
    IntegrableOn (fun t : ℝ ↦ g t * Complex.exp (I * z * t)) (Ioc (-Real.pi) Real.pi) := by
  have h1 : IntegrableOn g (Icc (-Real.pi) Real.pi) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).2 hg.integrableOn
  have h2 : ContinuousOn (fun t : ℝ ↦ Complex.exp (I * z * t)) (Icc (-Real.pi) Real.pi) := by
    fun_prop
  exact (h1.mul_continuousOn h2 isCompact_Icc).mono_set Ioc_subset_Icc_self

theorem lintegral_enorm_sq_lt_top_of_memLp {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f 2 μ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ∞ := by
  have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num) hf.eLpNorm_lt_top
  simpa using this

theorem memLp_two_of_lintegral {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : α → ℂ} (hm : AEStronglyMeasurable f μ) (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ∞) : MemLp f 2 μ := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hm]
  simpa using h

theorem l2piSq_ne_top {g : ℝ → ℂ} (hg : MemL2pi g) : l2piSq g ≠ ⊤ :=
  (lintegral_enorm_sq_lt_top_of_memLp hg).ne

theorem measurePreserving_neg_Ioc :
    MeasurePreserving (Neg.neg : ℝ → ℝ) (volume.restrict (Ioc (-Real.pi) Real.pi))
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage_emb
    (MeasurableEquiv.neg ℝ).measurableEmbedding (Ico (-Real.pi) Real.pi)
  have e1 : (Neg.neg : ℝ → ℝ) ⁻¹' Ico (-Real.pi) Real.pi = Ioc (-Real.pi) Real.pi := by
    ext x; simp [Set.mem_Ioc]
  have e2 : (volume : Measure ℝ).restrict (Ico (-Real.pi) Real.pi) =
      volume.restrict (Ioc (-Real.pi) Real.pi) := Measure.restrict_congr_set Ico_ae_eq_Ioc
  rw [e1, e2] at h
  exact h

/-- `g ↦ g(-·)`. -/
def reflect (g : ℝ → ℂ) : ℝ → ℂ := fun t ↦ g (-t)

theorem memL2pi_reflect {g : ℝ → ℂ} (hg : MemL2pi g) : MemL2pi (reflect g) :=
  hg.comp_measurePreserving measurePreserving_neg_Ioc

theorem l2piSq_reflect (g : ℝ → ℂ) : l2piSq (reflect g) = l2piSq g :=
  measurePreserving_neg_Ioc.lintegral_comp_emb (MeasurableEquiv.neg ℝ).measurableEmbedding
    (fun t ↦ ‖g t‖ₑ ^ 2)

theorem pwFT_reflect (g : ℝ → ℂ) (z : ℂ) :
    pwFT (reflect g) z = ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (-(I * z * t)) := by
  unfold pwFT reflect
  have := intervalIntegral.integral_comp_neg (a := -Real.pi) (b := Real.pi)
    (fun s : ℝ ↦ g s * Complex.exp (-(I * z * s)))
  simp only [neg_neg, mul_neg, Complex.ofReal_neg] at this
  simpa using this

theorem intervalIntegrable_mul_exp {g : ℝ → ℂ} (hg : MemL2pi g) (z : ℂ) :
    IntervalIntegrable (fun t : ℝ ↦ g t * Complex.exp (I * z * t)) volume (-Real.pi) Real.pi :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])).2
    (hg.integrableOn_mul_exp z)

theorem pwFT_sub {g h : ℝ → ℂ} (hg : MemL2pi g) (hh : MemL2pi h) (z : ℂ) :
    pwFT (fun t ↦ g t - h t) z = pwFT g z - pwFT h z := by
  unfold pwFT
  simp_rw [sub_mul]
  exact intervalIntegral.integral_sub (intervalIntegrable_mul_exp hg z) (intervalIntegrable_mul_exp hh z)

theorem norm_exp_I_mul_le (z : ℂ) {t : ℝ} (ht : t ∈ Ioc (-Real.pi) Real.pi) :
    ‖Complex.exp (I * z * t)‖ ≤ Real.exp (Real.pi * |z.im|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have : (I * z * t).re = -(t * z.im) := by simp [mul_comm]
  rw [this]
  have h1 : |t| ≤ Real.pi := abs_le.2 ⟨ht.1.le, ht.2⟩
  calc -(t * z.im) ≤ |t * z.im| := neg_le_abs _
    _ = |t| * |z.im| := abs_mul _ _
    _ ≤ Real.pi * |z.im| := by gcongr

theorem lintegral_enorm_le_sqrt {g : ℝ → ℂ} (hg : MemL2pi g) :
    (∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ).toReal ≤ Real.sqrt (2 * Real.pi * (l2piSq g).toReal) := by
  have hm : AEMeasurable (fun t ↦ ‖g t‖ₑ) (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    (MemLp.aestronglyMeasurable hg).enorm
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc (-Real.pi) Real.pi))
    (Real.HolderConjugate.two_two) hm (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have h2 : (Real.pi - -Real.pi) = 2 * Real.pi := by ring
  simp only [Pi.mul_apply, mul_one, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioc, h2, one_pow, one_mul, ENNReal.rpow_two] at hH
  have hS : l2piSq g ≠ ⊤ := l2piSq_ne_top hg
  have hfin : (∫⁻ (a : ℝ) in Ioc (-Real.pi) Real.pi, ‖g a‖ₑ ^ 2) ^ (1 / 2 : ℝ) *
      ENNReal.ofReal (2 * Real.pi) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hS)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have := ENNReal.toReal_mono hfin hH
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity)] at this
  rw [Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) ENNReal.toReal_nonneg, mul_comm]
  exact this

theorem norm_pwFT_le {g : ℝ → ℂ} (hg : MemL2pi g) (z : ℂ) :
    ‖pwFT g z‖ ≤ Real.exp (Real.pi * |z.im|) * Real.sqrt (2 * Real.pi * (l2piSq g).toReal) := by
  set B := Real.exp (Real.pi * |z.im|) with hB
  unfold pwFT
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  have h1 : ∫⁻ t in Ioc (-Real.pi) Real.pi, ENNReal.ofReal ‖g t * Complex.exp (I * z * t)‖ ≤
      ENNReal.ofReal B * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
    rw [ofReal_norm, enorm_mul]
    rw [mul_comm]
    gcongr
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_exp_I_mul_le z ht)
  have h2 : (ENNReal.ofReal B * ∫⁻ t in Ioc (-Real.pi) Real.pi, ‖g t‖ₑ) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    exact (hg.integrableOn.2).ne
  refine (ENNReal.toReal_mono h2 h1).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_left (lintegral_enorm_le_sqrt hg) (Real.exp_pos _).le

theorem fourierCoeffOn_pwFT (g : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn (by linarith [Real.pi_pos] : -Real.pi < Real.pi) g n =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * pwFT g (-(n : ℂ)) := by
  rw [fourierCoeffOn_eq_integral (E := ℂ)]
  unfold pwFT
  have h2 : (Real.pi - -Real.pi) = 2 * Real.pi := by ring
  have key : ∫ x in (-Real.pi)..Real.pi, (fourier (-n) (x : AddCircle (Real.pi - -Real.pi))) • g x =
      ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp (I * (-(n : ℂ)) * t) := by
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [smul_eq_mul]
    rw [fourier_coe_apply, h2, mul_comm]
    congr 2
    push_cast
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [key, h2, Complex.real_smul]
  simp

theorem l2piSq_eq_ofReal_integral {g : ℝ → ℂ} (hg : MemL2pi g) :
    l2piSq g = ENNReal.ofReal (∫ x in (-Real.pi)..Real.pi, ‖g x‖ ^ 2) := by
  have hI : Integrable (fun x ↦ ‖g x‖ ^ 2) (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    (memLp_two_iff_integrable_sq_norm (MemLp.aestronglyMeasurable hg)).1 hg
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun x ↦ by positivity)]
  unfold l2piSq
  refine lintegral_congr fun x ↦ ?_
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem tsum_enorm_sq_pwFT_int {g : ℝ → ℂ} (hg : MemL2pi g) :
    ∑' k : ℤ, ‖pwFT g (k : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (2 * Real.pi) * l2piSq g := by
  have hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have hP := hasSum_sq_fourierCoeffOn hab hg
  have h2 : (Real.pi - -Real.pi) = 2 * Real.pi := by ring
  have hpi : 0 < 2 * Real.pi := by positivity
  have hS : HasSum (fun n : ℤ ↦ ‖pwFT g (-(n : ℂ))‖ ^ 2)
      (2 * Real.pi * ∫ x in (-Real.pi)..Real.pi, ‖g x‖ ^ 2) := by
    have := hP.mul_left ((2 * Real.pi) ^ 2)
    convert this using 1
    · ext n
      rw [fourierCoeffOn_pwFT, norm_mul, mul_pow]
      simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
      field_simp
    · rw [h2, smul_eq_mul]
      field_simp
  have hS' : HasSum (fun k : ℤ ↦ ‖pwFT g (k : ℂ)‖ ^ 2)
      (2 * Real.pi * ∫ x in (-Real.pi)..Real.pi, ‖g x‖ ^ 2) := by
    rw [← (Equiv.neg ℤ).hasSum_iff]
    convert hS using 2
    simp
  have hnn : ∀ k : ℤ, 0 ≤ ‖pwFT g (k : ℂ)‖ ^ 2 := fun k ↦ by positivity
  have h3 : ∀ k : ℤ, ‖pwFT g (k : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (‖pwFT g (k : ℂ)‖ ^ 2) := fun k ↦ by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp_rw [h3]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hS'.summable, hS'.tsum_eq, ENNReal.ofReal_mul hpi.le,
    l2piSq_eq_ofReal_integral hg]

theorem l2piSq_eq_of_pwFT_eq {g h : ℝ → ℂ} (hg : MemL2pi g) (hh : MemL2pi h)
    (hgh : ∀ k : ℤ, pwFT g (k : ℂ) = pwFT h (k : ℂ)) : l2piSq g = l2piSq h := by
  have hd : MemL2pi (fun t ↦ g t - h t) := MemLp.sub hg hh
  have h0 := tsum_enorm_sq_pwFT_int hd
  have : ∀ k : ℤ, ‖pwFT (fun t ↦ g t - h t) (k : ℂ)‖ₑ ^ 2 = 0 := fun k ↦ by
    rw [pwFT_sub hg hh, hgh k, sub_self]; simp
  simp_rw [this] at h0
  simp only [tsum_zero] at h0
  have hz : l2piSq (fun t ↦ g t - h t) = 0 := by
    have hpos : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
      simp [Real.pi_pos]
    exact (mul_eq_zero.1 h0.symm).resolve_left hpos
  unfold l2piSq at hz
  rw [lintegral_eq_zero_iff' (by
    have := (MemLp.aestronglyMeasurable hd).enorm
    exact this.pow_const 2)] at hz
  refine lintegral_congr_ae ?_
  filter_upwards [hz] with t ht
  simp only [Pi.zero_apply, pow_eq_zero_iff (two_ne_zero), enorm_eq_zero, sub_eq_zero] at ht
  rw [ht]

/-- Locally uniform limits (along any filter) of functions of `PW` with a uniform bound
`|F_i(z)| ≤ K e^{π|Im z|}` and bounded norms lie in `PW`, and `‖f‖² ≤ liminf ‖F_i‖²` (Fatou). -/
theorem memPW_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, MemPW (F i)) {K : ℝ} (hK : ∀ i z, ‖F i z‖ ≤ K * Real.exp (Real.pi * |z.im|))
    (hd : Differentiable ℂ f) (hlim : ∀ z, Tendsto (fun i ↦ F i z) l (nhds (f z)))
    {M : ℝ≥0∞} (hM' : M ≠ ⊤) (hM : ∀ i, pwNormSq (F i) ≤ M) :
    MemPW f ∧ pwNormSq f ≤ liminf (fun i ↦ pwNormSq (F i)) l := by
  have hfK : ∀ z, ‖f z‖ ≤ K * Real.exp (Real.pi * |z.im|) := fun z ↦
    le_of_tendsto (hlim z).norm (Eventually.of_forall fun i ↦ hK i z)
  have hFcont : ∀ i, Continuous (fun x : ℝ ↦ F i (x : ℂ)) := fun i ↦
    (hF i).1.continuous.comp Complex.continuous_ofReal
  have hfcont : Continuous (fun x : ℝ ↦ f (x : ℂ)) := hd.continuous.comp Complex.continuous_ofReal
  have hfat : ∫⁻ x : ℝ, ‖f (x : ℂ)‖ₑ ^ 2 ≤ liminf (fun i ↦ pwNormSq (F i)) l := by
    calc ∫⁻ x : ℝ, ‖f (x : ℂ)‖ₑ ^ 2 = ∫⁻ x : ℝ, liminf (fun i ↦ ‖F i (x : ℂ)‖ₑ ^ 2) l := by
          refine lintegral_congr fun x ↦ ?_
          symm
          apply Tendsto.liminf_eq
          exact ((ENNReal.continuous_pow 2).tendsto _).comp
            ((continuous_enorm.tendsto _).comp (hlim x))
      _ ≤ liminf (fun i ↦ ∫⁻ x : ℝ, ‖F i (x : ℂ)‖ₑ ^ 2) l :=
          lintegral_liminf_le fun i ↦ ((hFcont i).measurable.enorm).pow_const 2
  have hlim_le : liminf (fun i ↦ pwNormSq (F i)) l ≤ M :=
    liminf_le_of_frequently_le' (Eventually.of_forall hM).frequently
  refine ⟨⟨hd, ?_, ?_⟩, hfat⟩
  · intro ε hε
    refine ⟨|K|, fun z ↦ ?_⟩
    calc ‖f z‖ ≤ K * Real.exp (Real.pi * |z.im|) := hfK z
      _ ≤ |K| * Real.exp ((Real.pi + ε) * ‖z‖) := by
        refine mul_le_mul (le_abs_self K) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (abs_nonneg K)
        calc Real.pi * |z.im| ≤ Real.pi * ‖z‖ :=
              mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) Real.pi_pos.le
          _ ≤ (Real.pi + ε) * ‖z‖ := by nlinarith [norm_nonneg z]
  · exact memLp_two_of_lintegral hfcont.aestronglyMeasurable
      (lt_of_le_of_lt (hfat.trans hlim_le) (lt_top_iff_ne_top.2 hM'))

/-! ## Paley–Wiener, both directions, with the norm identity -/

/-- Easy half of `hPW`: every `f ∈ PW` is `pwFT g` for some `g ∈ L²(-π,π)`, with
`‖f‖² = 2π ‖g‖²`. -/
theorem exists_pwFT (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) :
    ∃ g : ℝ → ℂ, MemL2pi g ∧ f = pwFT g ∧ pwNormSq f = ENNReal.ofReal (2 * Real.pi) * l2piSq g := by
  obtain ⟨g, hg, hrep⟩ := hPW.2 f hf
  have hf' : f = pwFT g := funext hrep
  exact ⟨g, hg, hf', by rw [hf']; exact (hPW.1 g hg).2⟩

/-- **Strong form of the Paley–Wiener theorem** (see blueprint §0: `PaleyWienerThm` as stated
only gives `⇐` for `g` for which the norm identity is already known; this lemma derives the
unconditional `⇐`). For every `g ∈ L²(-π,π)`, `pwFT g ∈ PW` and `‖pwFT g‖² = 2π‖g‖²`. -/
theorem memPW_pwFT (hPW : PaleyWienerThm) {g : ℝ → ℂ} (hg : MemL2pi g) :
    MemPW (pwFT g) ∧ pwNormSq (pwFT g) = ENNReal.ofReal (2 * Real.pi) * l2piSq g := by
  exact hPW.1 g hg

/-! ## `pwNormSq` is finite; algebra of `PW` -/

theorem pwNormSq_ne_top {f : ℂ → ℂ} (hf : MemPW f) : pwNormSq f ≠ ⊤ := by
  exact (lintegral_enorm_sq_lt_top_of_memLp hf.2.2).ne

theorem isExpTypeLE_lin {τ : ℝ} {f g : ℂ → ℂ} (hf : IsExpTypeLE τ f) (hg : IsExpTypeLE τ g)
    (a b : ℂ) : IsExpTypeLE τ (fun z ↦ a * f z + b * g z) := by
  intro ε hε
  obtain ⟨C₁, h₁⟩ := hf ε hε
  obtain ⟨C₂, h₂⟩ := hg ε hε
  refine ⟨‖a‖ * |C₁| + ‖b‖ * |C₂|, fun z ↦ ?_⟩
  have e0 : 0 ≤ Real.exp ((τ + ε) * ‖z‖) := (Real.exp_pos _).le
  calc ‖a * f z + b * g z‖ ≤ ‖a‖ * ‖f z‖ + ‖b‖ * ‖g z‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ ‖a‖ * (|C₁| * Real.exp ((τ + ε) * ‖z‖)) + ‖b‖ * (|C₂| * Real.exp ((τ + ε) * ‖z‖)) := by
        gcongr
        · exact (h₁ z).trans (mul_le_mul_of_nonneg_right (le_abs_self _) e0)
        · exact (h₂ z).trans (mul_le_mul_of_nonneg_right (le_abs_self _) e0)
    _ = _ := by ring

theorem MemPW.lin {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) (a b : ℂ) :
    MemPW (fun z ↦ a * f z + b * g z) :=
  ⟨(hf.1.const_mul a).add (hg.1.const_mul b), isExpTypeLE_lin hf.2.1 hg.2.1 a b,
    (hf.2.2.const_mul a).add (hg.2.2.const_mul b)⟩

theorem memPW_zero : MemPW (fun _ : ℂ ↦ (0 : ℂ)) := by
  refine ⟨differentiable_const _, fun ε hε ↦ ⟨0, fun z ↦ by simp⟩, ?_⟩
  simp

theorem MemPW.add {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) : MemPW (f + g) := by
  convert hf.lin hg 1 1 using 1
  ext z; simp

theorem MemPW.sub {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) : MemPW (f - g) := by
  convert hf.lin hg 1 (-1) using 1
  ext z; simp [sub_eq_add_neg]

theorem MemPW.const_mul {f : ℂ → ℂ} (hf : MemPW f) (c : ℂ) : MemPW (fun z ↦ c * f z) := by
  have := hf.lin hf c 0
  simpa using this

/-! ## Real translation and `f^*` -/

theorem MemPW.comp_sub_ofReal {f : ℂ → ℂ} (hf : MemPW f) (a : ℝ) :
    MemPW (fun z ↦ f (z - a)) := by
  refine ⟨hf.1.comp (differentiable_id.sub_const _), ?_, ?_⟩
  · intro ε hε
    obtain ⟨C, hC⟩ := hf.2.1 ε hε
    refine ⟨|C| * Real.exp ((Real.pi + ε) * |a|), fun z ↦ ?_⟩
    have h1 : ‖z - (a : ℂ)‖ ≤ ‖z‖ + |a| := by
      refine (norm_sub_le _ _).trans ?_
      simp
    calc ‖f (z - a)‖ ≤ C * Real.exp ((Real.pi + ε) * ‖z - a‖) := hC _
      _ ≤ |C| * Real.exp ((Real.pi + ε) * (‖z‖ + |a|)) := by
        refine mul_le_mul (le_abs_self C) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (abs_nonneg C)
        exact mul_le_mul_of_nonneg_left h1 (by linarith [Real.pi_pos])
      _ = _ := by rw [mul_add, Real.exp_add]; ring
  · have := hf.2.2.comp_measurePreserving (measurePreserving_sub_right (volume : Measure ℝ) a)
    simpa [Function.comp_def, Complex.ofReal_sub] using this

theorem pwNormSq_comp_sub_ofReal (f : ℂ → ℂ) (a : ℝ) :
    pwNormSq (fun z ↦ f (z - a)) = pwNormSq f := by
  unfold pwNormSq
  have := lintegral_sub_right_eq_self (μ := (volume : Measure ℝ)) (fun x : ℝ ↦ ‖f (x : ℂ)‖ₑ ^ 2) a
  simpa [Complex.ofReal_sub] using this

theorem pwNormSq_fstar (f : ℂ → ℂ) : pwNormSq (FF.fstar f) = pwNormSq f := by
  unfold pwNormSq
  refine lintegral_congr fun x ↦ ?_
  simp [FF.fstar, Complex.conj_ofReal]

theorem MemPW.fstar {f : ℂ → ℂ} (hf : MemPW f) : MemPW (FF.fstar f) := by
  have hd : Differentiable ℂ (FF.fstar f) := fun z ↦ by
    exact differentiableAt_conj_conj_iff.2 (hf.1 (conj z))
  refine ⟨hd, ?_, ?_⟩
  · intro ε hε
    obtain ⟨C, hC⟩ := hf.2.1 ε hε
    refine ⟨C, fun z ↦ ?_⟩
    simpa [FF.fstar] using hC (conj z)
  · refine memLp_two_of_lintegral (hd.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable ?_
    have := pwNormSq_fstar f
    unfold pwNormSq at this
    rw [this]
    exact lt_top_iff_ne_top.2 (pwNormSq_ne_top hf)

/-! ## Division by a zero -/

theorem norm_dslope_mul_norm_sub {f : ℂ → ℂ} {a z : ℂ} (ha : f a = 0) (hz : z ≠ a) :
    ‖dslope f a z‖ * ‖z - a‖ = ‖f z‖ := by
  rw [dslope_of_ne _ hz, slope_def_field, ha, sub_zero, norm_div]
  have : ‖z - a‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hz)
  field_simp

theorem norm_dslope_le_add {f : ℂ → ℂ} {a : ℂ} (ha : f a = 0) {Ma : ℝ}
    (hMa : ∀ z ∈ Metric.closedBall a 1, ‖dslope f a z‖ ≤ Ma) (z : ℂ) :
    ‖dslope f a z‖ ≤ ‖f z‖ + |Ma| := by
  by_cases hz : 1 ≤ ‖z - a‖
  · have hne : z ≠ a := by
      intro h; simp [h] at hz; linarith
    have := norm_dslope_mul_norm_sub ha hne
    have h2 : ‖dslope f a z‖ ≤ ‖f z‖ := by
      rw [← this]
      exact le_mul_of_one_le_right (norm_nonneg _) hz
    linarith [abs_nonneg Ma]
  · rw [not_le] at hz
    have : z ∈ Metric.closedBall a 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hz.le
    linarith [hMa z this, le_abs_self Ma, norm_nonneg (f z)]

/-- If `f ∈ PW` vanishes at `a`, then `z ↦ f(z)(z - b)/(z - a)`, extended at `a` by `dslope`,
is in `PW`. -/
theorem MemPW.mul_div_sub {f : ℂ → ℂ} (hf : MemPW f) {a : ℂ} (ha : f a = 0) (b : ℂ) :
    MemPW (fun z ↦ dslope f a z * (z - b)) := by
  have hdsl : Differentiable ℂ (dslope f a) :=
    differentiableOn_univ.1 ((differentiableOn_dslope Filter.univ_mem).2 hf.1.differentiableOn)
  have hdif : Differentiable ℂ (fun z ↦ dslope f a z * (z - b)) :=
    hdsl.mul (differentiable_id.sub_const b)
  obtain ⟨Ma, hMa⟩ := (isCompact_closedBall a 1).exists_bound_of_continuousOn
    hdsl.continuous.continuousOn
  refine ⟨hdif, ?_, ?_⟩
  · intro ε hε
    obtain ⟨C, hC⟩ := hf.2.1 (ε / 2) (by positivity)
    refine ⟨(|C| + |Ma|) * (2 / ε + ‖b‖), fun z ↦ ?_⟩
    set x := ‖z‖ with hx
    have hx0 : 0 ≤ x := norm_nonneg z
    have hE1 : 1 ≤ Real.exp ((Real.pi + ε / 2) * x) :=
      Real.one_le_exp (by have := Real.pi_pos; positivity)
    have hE2 : 1 + ε / 2 * x ≤ Real.exp (ε / 2 * x) := by
      have := Real.add_one_le_exp (ε / 2 * x); linarith
    have hE : Real.exp ((Real.pi + ε) * x) =
        Real.exp ((Real.pi + ε / 2) * x) * Real.exp (ε / 2 * x) := by
      rw [← Real.exp_add]; congr 1; ring
    have h1 : ‖dslope f a z‖ ≤ (|C| + |Ma|) * Real.exp ((Real.pi + ε / 2) * x) := by
      refine (norm_dslope_le_add ha hMa z).trans ?_
      have := hC z
      have h2 : ‖f z‖ ≤ |C| * Real.exp ((Real.pi + ε / 2) * x) :=
        this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
      nlinarith [abs_nonneg Ma, abs_nonneg C]
    have h3 : ‖z - b‖ ≤ (2 / ε + ‖b‖) * Real.exp (ε / 2 * x) := by
      have h4 : ‖z - b‖ ≤ x + ‖b‖ := norm_sub_le _ _
      have h5 : x ≤ 2 / ε * Real.exp (ε / 2 * x) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hε]
        nlinarith [hE2]
      have hE3 : 1 ≤ Real.exp (ε / 2 * x) := Real.one_le_exp (by positivity)
      have h6 : ‖b‖ ≤ ‖b‖ * Real.exp (ε / 2 * x) :=
        le_mul_of_one_le_right (norm_nonneg _) hE3
      nlinarith
    rw [norm_mul, hE]
    calc ‖dslope f a z‖ * ‖z - b‖
        ≤ ((|C| + |Ma|) * Real.exp ((Real.pi + ε / 2) * x)) *
          ((2 / ε + ‖b‖) * Real.exp (ε / 2 * x)) :=
          mul_le_mul h1 h3 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · set A : ℝ := 1 + ‖a - b‖ with hA
    have hhc : Continuous (fun x : ℝ ↦ dslope f a (x : ℂ) * ((x : ℂ) - b)) := by
      exact hdif.continuous.comp Complex.continuous_ofReal
    have hhm : AEStronglyMeasurable (fun x : ℝ ↦ dslope f a (x : ℂ) * ((x : ℂ) - b)) volume :=
      hhc.aestronglyMeasurable
    obtain ⟨Mh, hMh⟩ := (isCompact_Icc (a := a.re - 1) (b := a.re + 1)).exists_bound_of_continuousOn
      hhc.continuousOn
    have hG : MemLp (fun x : ℝ ↦ A * ‖f (x : ℂ)‖ +
        (Set.Icc (a.re - 1) (a.re + 1)).indicator (fun _ ↦ |Mh|) x) 2 volume :=
      (hf.2.2.norm.const_mul A).add
        (memLp_indicator_const 2 measurableSet_Icc.nullMeasurableSet |Mh|
          (Or.inr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
    refine hG.of_le hhm (Filter.Eventually.of_forall fun x ↦ ?_)
    have hfn : 0 ≤ A * ‖f (x : ℂ)‖ := by positivity
    have hind : 0 ≤ (Set.Icc (a.re - 1) (a.re + 1)).indicator (fun _ ↦ |Mh|) x :=
      Set.indicator_nonneg (fun _ _ ↦ abs_nonneg _) x
    rw [Real.norm_of_nonneg (add_nonneg hfn hind)]
    by_cases hxI : x ∈ Set.Icc (a.re - 1) (a.re + 1)
    · rw [Set.indicator_of_mem hxI]
      linarith [hMh x hxI, le_abs_self Mh]
    · have h1 : 1 < ‖(x : ℂ) - a‖ := by
        have : |x - a.re| ≤ ‖(x : ℂ) - a‖ := by
          have := Complex.abs_re_le_norm ((x : ℂ) - a)
          simpa using this
        have h2 : 1 < |x - a.re| := by
          simp only [Set.mem_Icc, not_and_or, not_le] at hxI
          rcases hxI with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        linarith
      have hne : (x : ℂ) ≠ a := by
        intro h; rw [h, sub_self, norm_zero] at h1; linarith
      have h2 := norm_dslope_mul_norm_sub ha hne
      have h3 : ‖(x : ℂ) - b‖ ≤ ‖(x : ℂ) - a‖ * A := by
        calc ‖(x : ℂ) - b‖ = ‖((x : ℂ) - a) + (a - b)‖ := by ring_nf
          _ ≤ ‖(x : ℂ) - a‖ + ‖a - b‖ := norm_add_le _ _
          _ ≤ ‖(x : ℂ) - a‖ * A := by
            rw [hA]; nlinarith [norm_nonneg (a - b)]
      rw [norm_mul]
      calc ‖dslope f a (x : ℂ)‖ * ‖(x : ℂ) - b‖
          ≤ ‖dslope f a (x : ℂ)‖ * (‖(x : ℂ) - a‖ * A) := by gcongr
        _ = ‖f (x : ℂ)‖ * A := by rw [← mul_assoc, h2]
        _ = A * ‖f (x : ℂ)‖ := mul_comm _ _
        _ ≤ _ := by linarith

/-- (H1): for nonreal `a`, the multiplier `(z - ā)/(z - a)` is unimodular on `ℝ`, so the norm is
preserved. -/
theorem pwNormSq_mul_div_sub_conj (f : ℂ → ℂ) {a : ℂ} (ha : a.im ≠ 0) (ha0 : f a = 0) :
    pwNormSq (fun z ↦ dslope f a z * (z - conj a)) = pwNormSq f := by
  unfold pwNormSq
  refine lintegral_congr fun x ↦ ?_
  have hne : (x : ℂ) ≠ a := fun h ↦ ha (by rw [← h]; simp)
  have h2 := norm_dslope_mul_norm_sub ha0 hne
  have h3 : ‖(x : ℂ) - conj a‖ = ‖(x : ℂ) - a‖ := by
    rw [← Complex.norm_conj ((x : ℂ) - a)]; simp
  have key : ‖dslope f a (x : ℂ) * ((x : ℂ) - conj a)‖ = ‖f (x : ℂ)‖ := by
    rw [norm_mul, h3, h2]
  rw [← ofReal_norm, ← ofReal_norm (f _), key]

/-- A separated set meets bounded sets in finite sets (moved here from `Perturbation.lean` and
`Theorem1/Necessity.lean` at assembly). -/
theorem IsSeparated.finite_inter_Icc {Λ : Set ℝ} (h : IsSeparated Λ) (R : ℝ) :
    (Λ ∩ Icc (-R) R).Finite := by
  obtain ⟨δ, hδ, hsep⟩ := h
  have hfin : (Set.Icc ⌊-R / δ⌋ ⌊R / δ⌋ : Set ℤ).Finite := Set.finite_Icc _ _
  refine Set.Finite.of_injOn (f := fun x : ℝ ↦ ⌊x / δ⌋) (t := Set.Icc ⌊-R / δ⌋ ⌊R / δ⌋) ?_ ?_ hfin
  · intro x hx
    simp only [Set.mem_Icc]
    exact ⟨Int.floor_mono (by gcongr; exact hx.2.1), Int.floor_mono (by gcongr; exact hx.2.2)⟩
  · intro x hx y hy hxy
    by_contra hne
    have h1 := hsep x hx.1 y hy.1 hne
    simp only at hxy
    have h2 : |x / δ - y / δ| < 1 := by
      have := Int.abs_sub_lt_one_of_floor_eq_floor hxy
      exact this
    rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at h2
    linarith

/-- `‖f‖_{PW} = 0` forces `f = 0` (added at assembly; requested by M03). -/
theorem MemPW.eq_zero_of_pwNormSq_eq_zero {f : ℂ → ℂ} (hf : MemPW f) (h : pwNormSq f = 0) :
    f = 0 := by
  have hc : Continuous (fun x : ℝ ↦ f (x : ℂ)) := hf.1.continuous.comp Complex.continuous_ofReal
  unfold pwNormSq at h
  rw [lintegral_eq_zero_iff (hc.measurable.enorm.pow_const 2)] at h
  have h0 : ∀ x : ℝ, f (x : ℂ) = 0 := by
    have : (fun x : ℝ ↦ f (x : ℂ)) = fun _ ↦ 0 := by
      refine (hc.ae_eq_iff_eq (volume : Measure ℝ) continuous_const).1 ?_
      filter_upwards [h] with x hx
      simpa using hx
    exact fun x ↦ congrFun this x
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0 := by
    have ht : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx using by simpa using hx
    exact ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall h0))
  have hA : AnalyticOnNhd ℂ f Set.univ := fun z _ ↦ Differentiable.analyticAt hf.1 z
  have := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ (0 : ℂ)) hfreq
  funext z
  exact this (Set.mem_univ z)

end FF
