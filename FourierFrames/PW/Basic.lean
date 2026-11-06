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
  sorry

/-! ## Paley–Wiener, both directions, with the norm identity -/

/-- Easy half of `hPW`: every `f ∈ PW` is `pwFT g` for some `g ∈ L²(-π,π)`, with
`‖f‖² = 2π ‖g‖²`. -/
theorem exists_pwFT (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) :
    ∃ g : ℝ → ℂ, MemL2pi g ∧ f = pwFT g ∧ pwNormSq f = ENNReal.ofReal (2 * Real.pi) * l2piSq g := by
  sorry

/-- **Strong form of the Paley–Wiener theorem** (see blueprint §0: `PaleyWienerThm` as stated
only gives `⇐` for `g` for which the norm identity is already known; this lemma derives the
unconditional `⇐`). For every `g ∈ L²(-π,π)`, `pwFT g ∈ PW` and `‖pwFT g‖² = 2π‖g‖²`. -/
theorem memPW_pwFT (hPW : PaleyWienerThm) {g : ℝ → ℂ} (hg : MemL2pi g) :
    MemPW (pwFT g) ∧ pwNormSq (pwFT g) = ENNReal.ofReal (2 * Real.pi) * l2piSq g := by
  sorry

/-! ## `pwNormSq` is finite; algebra of `PW` -/

theorem pwNormSq_ne_top {f : ℂ → ℂ} (hf : MemPW f) : pwNormSq f ≠ ⊤ := by
  sorry

theorem memPW_zero : MemPW (fun _ : ℂ ↦ (0 : ℂ)) := by
  sorry

theorem MemPW.add {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) : MemPW (f + g) := by
  sorry

theorem MemPW.sub {f g : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) : MemPW (f - g) := by
  sorry

theorem MemPW.const_mul {f : ℂ → ℂ} (hf : MemPW f) (c : ℂ) : MemPW (fun z ↦ c * f z) := by
  sorry

/-! ## Real translation and `f^*` -/

theorem MemPW.comp_sub_ofReal {f : ℂ → ℂ} (hf : MemPW f) (a : ℝ) :
    MemPW (fun z ↦ f (z - a)) := by
  sorry

theorem pwNormSq_comp_sub_ofReal (f : ℂ → ℂ) (a : ℝ) :
    pwNormSq (fun z ↦ f (z - a)) = pwNormSq f := by
  sorry

theorem MemPW.fstar {f : ℂ → ℂ} (hf : MemPW f) : MemPW (FF.fstar f) := by
  sorry

theorem pwNormSq_fstar (f : ℂ → ℂ) : pwNormSq (FF.fstar f) = pwNormSq f := by
  sorry

/-! ## Division by a zero -/

/-- If `f ∈ PW` vanishes at `a`, then `z ↦ f(z)(z - b)/(z - a)`, extended at `a` by `dslope`,
is in `PW`. -/
theorem MemPW.mul_div_sub {f : ℂ → ℂ} (hf : MemPW f) {a : ℂ} (ha : f a = 0) (b : ℂ) :
    MemPW (fun z ↦ dslope f a z * (z - b)) := by
  sorry

/-- (H1): for nonreal `a`, the multiplier `(z - ā)/(z - a)` is unimodular on `ℝ`, so the norm is
preserved. -/
theorem pwNormSq_mul_div_sub_conj (f : ℂ → ℂ) {a : ℂ} (ha : a.im ≠ 0) (ha0 : f a = 0) :
    pwNormSq (fun z ↦ dslope f a z * (z - conj a)) = pwNormSq f := by
  sorry

/-- A separated set meets bounded sets in finite sets (moved here from `Perturbation.lean` and
`Theorem1/Necessity.lean` at assembly). -/
theorem IsSeparated.finite_inter_Icc {Λ : Set ℝ} (h : IsSeparated Λ) (R : ℝ) :
    (Λ ∩ Icc (-R) R).Finite := by
  sorry

/-- `‖f‖_{PW} = 0` forces `f = 0` (added at assembly; requested by M03). -/
theorem MemPW.eq_zero_of_pwNormSq_eq_zero {f : ℂ → ℂ} (hf : MemPW f) (h : pwNormSq f = 0) :
    f = 0 := by
  sorry

end FF
