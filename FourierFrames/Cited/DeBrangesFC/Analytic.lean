import FourierFrames.Cited.DeBrangesDE

/-!
# P4, Part C: complex-analysis helpers and the real zeros of `E`

See `blueprint/P4_DeBrangesFC.md`, §1.1–1.2.  Identity theorem in the forms used, the order
drop under `(z - ζ̄)/(z - ζ)`, Fatou on horizontal lines, and the extension `divExt E f` of `f/E`
across the real zeros of `E` (Mathlib's meromorphic normal form).
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## 1.1 General helpers -/

/-- Identity theorem: entire functions that agree near one point are equal. -/
theorem eq_of_eventuallyEq_entire {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {z₀ : ℂ} (h : f =ᶠ[𝓝 z₀] g) : f = g :=
  AnalyticOnNhd.eq_of_eventuallyEq (fun z _ ↦ hf.analyticAt z) (fun z _ ↦ hg.analyticAt z) h

/-- Entire functions that agree on a nonempty open set are equal. -/
theorem eq_of_eqOn_open {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h : EqOn f g U) : f = g :=
  eq_of_eventuallyEq_entire hf hg (Filter.eventually_of_mem (hU.mem_nhds hz₀) h)

/-- Entire functions that agree off a finite set are equal. -/
theorem eq_of_eq_off_finite {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {s : Set ℂ} (hs : s.Finite) (h : ∀ z, z ∉ s → f z = g z) : f = g := by
  obtain ⟨z₀, hz₀⟩ := hs.infinite_compl.nonempty
  exact eq_of_eqOn_open hf hg hs.isClosed.isOpen_compl hz₀ fun z hz ↦ h z hz

/-- Identity theorem in the form used twice: entire functions that agree on `ℂ₊` are equal. -/
theorem eq_of_eqOn_upper {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ z : ℂ, 0 < z.im → f z = g z) : f = g :=
  eq_of_eqOn_open hf hg (isOpen_lt continuous_const Complex.continuous_im) (z₀ := I)
    (by simp) fun z hz ↦ h z hz

theorem sub_conj_ne_zero {ζ : ℂ} (hζ : ζ.im ≠ 0) : ζ - conj ζ ≠ 0 := by
  rw [Complex.sub_conj]
  simp [hζ]

/-- C.2, induction step: multiplying by `(z - ζ̄)/(z - ζ)` lowers the order at the nonreal
point `ζ` by one. -/
theorem analyticOrderAt_eq_of_mul_div {F G : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G) {ζ : ℂ} (hζ : ζ.im ≠ 0) {n : ℕ}
    (hn : analyticOrderAt F ζ = (n + 1 : ℕ))
    (hFG : ∀ z : ℂ, z ≠ ζ → G z = F z * (z - conj ζ) / (z - ζ)) :
    analyticOrderAt G ζ = n := by
  obtain ⟨u, hu, hu0, hFu⟩ := (hF.analyticAt ζ).analyticOrderAt_eq_natCast.mp hn
  rw [(hG.analyticAt ζ).analyticOrderAt_eq_natCast]
  refine ⟨fun z ↦ u z * (z - conj ζ), hu.mul (by fun_prop), mul_ne_zero hu0 (sub_conj_ne_zero hζ),
    ?_⟩
  have hne : G =ᶠ[𝓝[≠] ζ] fun z ↦ (z - ζ) ^ n • (u z * (z - conj ζ)) := by
    filter_upwards [nhdsWithin_le_nhds hFu, self_mem_nhdsWithin] with z hz hzne
    have hz0 : z - ζ ≠ 0 := sub_ne_zero.mpr hzne
    rw [hFG z hzne, hz, smul_eq_mul, smul_eq_mul]
    field_simp
    ring
  exact (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (hG.continuous.continuousAt)
    (by fun_prop : ContinuousAt (fun z ↦ (z - ζ) ^ n • (u z * (z - conj ζ))) ζ)).mp hne

/-- Fatou's lemma on a horizontal line `Im z = y > 0`. -/
theorem lintegral_line_le_liminf {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y)
    (hlim : ∀ x : ℝ, Tendsto (fun n ↦ F n ((x : ℂ) + (y : ℂ) * I)) atTop
      (𝓝 (G ((x : ℂ) + (y : ℂ) * I)))) :
    ∫⁻ x : ℝ, ‖G ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤
      liminf (fun n ↦ ∫⁻ x : ℝ, ‖F n ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2) atTop := by
  have hpt : ∀ x : ℝ, liminf (fun n ↦ ‖F n ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2) atTop =
      ‖G ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 := fun x ↦
    (((ENNReal.continuous_pow 2).tendsto _).comp
      ((continuous_enorm.tendsto _).comp (hlim x))).liminf_eq
  calc ∫⁻ x : ℝ, ‖G ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2
      = ∫⁻ x : ℝ, liminf (fun n ↦ ‖F n ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2) atTop := by
        simp_rw [hpt]
    _ ≤ _ := lintegral_liminf_le fun n ↦ measurable_line_sq (hF n) hy

/-! ## 1.2 Real zeros of `E` (R9 F5) -/

/-- `E t ≠ 0` for a.e. real `t` (`countable_real_zeros`; `E ≠ 0` on `ℂ₊`). -/
theorem IsHB.ae_ne_zero {E : ℂ → ℂ} (hE : IsHB E) : ∀ᵐ t : ℝ, E t ≠ 0 := by
  have hnull : volume {t : ℝ | E (t : ℂ) = 0} = 0 :=
    (countable_real_zeros hE.1 ⟨I, hE.2.1 I (by simp)⟩).measure_zero _
  rw [ae_iff]
  simpa using hnull

/-- The meromorphic normal form of `f/E` on `ℂ`: it equals `f/E` where `E ≠ 0`, and is the
removable extension at the zeros of `E` where `f` vanishes to at least the same order. -/
def divExt (E f : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun z ↦ f z / E z) Set.univ

theorem meromorphicOn_div_entire {E f : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hf : Differentiable ℂ f) : MeromorphicOn (fun z ↦ f z / E z) univ := fun z _ ↦
  (hf.analyticAt z).meromorphicAt.div (hE.analyticAt z).meromorphicAt

theorem divExt_eq_of_ne {E f : ℂ → ℂ} (hE : Differentiable ℂ E) (hf : Differentiable ℂ f)
    {z : ℂ} (hz : E z ≠ 0) : divExt E f z = f z / E z := by
  have hm := meromorphicOn_div_entire hE hf
  rw [divExt, toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ z)]
  have ha : AnalyticAt ℂ (fun z ↦ f z / E z) z := (hf.analyticAt z).div (hE.analyticAt z) hz
  rw [toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]

/-- The order of `divExt E f` is the difference of the orders. -/
theorem meromorphicOrderAt_divExt {E f : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hf : Differentiable ℂ f) (z : ℂ) :
    meromorphicOrderAt (divExt E f) z =
      (analyticOrderAt f z).map (↑) - (analyticOrderAt E z).map (↑) := by
  have hm := meromorphicOn_div_entire hE hf
  rw [divExt, meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ z),
    fun_meromorphicOrderAt_div (hf.analyticAt z).meromorphicAt (hE.analyticAt z).meromorphicAt,
    (hf.analyticAt z).meromorphicOrderAt_eq, (hE.analyticAt z).meromorphicOrderAt_eq]

theorem analyticAt_divExt {E f : ℂ → ℂ} (hE : Differentiable ℂ E) (hf : Differentiable ℂ f)
    {z : ℂ} (hle : analyticOrderAt E z ≤ analyticOrderAt f z) :
    AnalyticAt ℂ (divExt E f) z := by
  have hNF : MeromorphicNFAt (divExt E f) z :=
    meromorphicNFOn_toMeromorphicNFOn _ univ (mem_univ z)
  rw [← hNF.meromorphicOrderAt_nonneg_iff_analyticAt, meromorphicOrderAt_divExt hE hf z]
  cases h1 : analyticOrderAt f z using ENat.recTopCoe with
  | top => simp
  | coe m =>
    cases h2 : analyticOrderAt E z using ENat.recTopCoe with
    | top =>
      rw [h1, h2] at hle
      simp at hle
    | coe n =>
      rw [h1, h2] at hle
      have hnm : n ≤ m := by exact_mod_cast hle
      simp only [ENat.map_natCast]
      rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
      exact_mod_cast (by omega : (0 : ℤ) ≤ (m : ℤ) - n)

/-- The order of the analytic function `divExt E f` at a point where `ord E ≤ ord f < ∞`. -/
theorem analyticOrderAt_divExt {E f : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hf : Differentiable ℂ f) {z : ℂ} {m n : ℕ} (hfm : analyticOrderAt f z = m)
    (hEn : analyticOrderAt E z = n) (hnm : n ≤ m) :
    analyticOrderAt (divExt E f) z = (m - n : ℕ) := by
  have ha := analyticAt_divExt hE hf (z := z) (by rw [hfm, hEn]; exact_mod_cast hnm)
  have h1 := ha.meromorphicOrderAt_eq
  rw [meromorphicOrderAt_divExt hE hf z, hfm, hEn] at h1
  simp only [ENat.map_natCast] at h1
  rw [← WithTop.LinearOrderedAddCommGroup.coe_sub] at h1
  cases h2 : analyticOrderAt (divExt E f) z using ENat.recTopCoe with
  | top =>
    rw [h2] at h1
    simp at h1
  | coe k =>
    rw [h2, ENat.map_natCast] at h1
    have hk : ((m : ℤ) - n) = (k : ℤ) := by exact_mod_cast h1
    have : k = m - n := by omega
    rw [this]

/-- `f/E ∈ H²` forces `f` to vanish at each real zero of `E` at least to the same order
(order version of `not_isH2Upper_div_of_zero`). -/
theorem analyticOrderAt_le_of_isH2Upper_div {E f : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hf : Differentiable ℂ f) (hE0 : ∀ z : ℂ, 0 < z.im → E z ≠ 0)
    (h : IsH2Upper (fun z ↦ f z / E z)) (x₀ : ℝ) :
    analyticOrderAt E (x₀ : ℂ) ≤ analyticOrderAt f (x₀ : ℂ) := by
  set x : ℂ := (x₀ : ℂ) with hx
  have hEtop : analyticOrderAt E x ≠ ⊤ := by
    intro htop
    have hE' := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero x fun z ↦ hE.analyticAt z).mp htop
    exact hE0 I (by simp) (by rw [hE']; rfl)
  by_contra hlt
  push Not at hlt
  have hftop : analyticOrderAt f x ≠ ⊤ := (hlt.trans_le le_top).ne
  obtain ⟨k₀, hk₀⟩ := ENat.ne_top_iff_exists.mp hftop
  obtain ⟨m₀, hm₀⟩ := ENat.ne_top_iff_exists.mp hEtop
  rw [← hk₀, ← hm₀] at hlt
  have hkm : k₀ < m₀ := by exact_mod_cast hlt
  set P : ℂ → ℂ := fun z ↦ (z - x) ^ k₀ with hPdef
  have hP : Differentiable ℂ P := by fun_prop
  have hPx : analyticOrderAt P x = k₀ := analyticOrderAt_centeredMonomial
  have hPne : ∀ z, z ≠ x → P z ≠ 0 := fun z hz ↦ pow_ne_zero _ (sub_ne_zero.mpr hz)
  have hPz : ∀ z, z ≠ x → analyticOrderAt P z = 0 := fun z hz ↦
    analyticOrderAt_eq_zero.mpr (Or.inr (hPne z hz))
  have hle : ∀ (g : ℂ → ℂ), analyticOrderAt P x ≤ analyticOrderAt g x →
      ∀ z, analyticOrderAt P z ≤ analyticOrderAt g z := by
    intro g hg z
    by_cases hz : z = x
    · rw [hz]; exact hg
    · rw [hPz z hz]; exact bot_le
  have hfa : ∀ z, AnalyticAt ℂ (divExt P f) z := fun z ↦
    analyticAt_divExt hP hf (hle f (by rw [hPx, ← hk₀]) z)
  have hf₁ : Differentiable ℂ (divExt P f) := fun z ↦ (hfa z).differentiableAt
  have hE₁ : Differentiable ℂ (divExt P E) := fun z ↦
    (analyticAt_divExt hP hE (hle E (by rw [hPx, ← hm₀]; exact_mod_cast hkm.le) z)).differentiableAt
  have hf₁x : divExt P f x ≠ 0 := by
    have h0 := analyticOrderAt_divExt hP hf hk₀.symm hPx le_rfl
    rw [Nat.sub_self, Nat.cast_zero, analyticOrderAt_eq_zero] at h0
    exact h0.resolve_left (not_not.mpr (hfa x))
  have hE₁x : divExt P E x = 0 := by
    have h0 := analyticOrderAt_divExt hP hE hm₀.symm hPx hkm.le
    refine apply_eq_zero_of_analyticOrderAt_ne_zero ?_
    rw [h0]
    exact_mod_cast (by omega : m₀ - k₀ ≠ 0)
  have hupper : ∀ z : ℂ, 0 < z.im → z ≠ x := fun z hz hzx ↦ by
    rw [hzx, hx] at hz
    simp at hz
  have hE₁0 : ∀ z : ℂ, 0 < z.im → divExt P E z ≠ 0 := fun z hz ↦ by
    rw [divExt_eq_of_ne hP hE (hPne z (hupper z hz))]
    exact div_ne_zero (hE0 z hz) (hPne z (hupper z hz))
  have h₁ : IsH2Upper (fun z ↦ divExt P f z / divExt P E z) := by
    refine h.congr fun z hz ↦ ?_
    have hPz' := hPne z (hupper z hz)
    have hEz := hE0 z hz
    rw [divExt_eq_of_ne hP hE hPz', divExt_eq_of_ne hP hf hPz']
    field_simp
  exact not_isH2Upper_div_of_zero hE₁ hf₁ hE₁0 hE₁x hf₁x h₁

/-- The extension of `f/E` is `IsH2Cont` when `f/E ∈ H²`. -/
theorem isH2Cont_divExt {E f : ℂ → ℂ} (hE : IsHB E) (hf : Differentiable ℂ f)
    (h : IsH2Upper (fun z ↦ f z / E z)) : IsH2Cont (divExt E f) :=
  ⟨h.congr fun z hz ↦ (divExt_eq_of_ne hE.1 hf (hE.2.1 z hz)).symm, fun t ↦
    (analyticAt_divExt hE.1 hf
      (analyticOrderAt_le_of_isH2Upper_div hE.1 hf hE.2.1 h t)).continuousAt⟩

/-- R9 F5: the form in which P3's `heInner_kernel_upper_of_isH2Cont` is called. -/
theorem exists_isH2Cont_of_memHE {E f : ℂ → ℂ} (hE : IsHB E) (hf : MemHE E f) :
    ∃ A B : ℂ → ℂ, IsH2Cont A ∧ IsH2Cont B ∧
      (∀ z : ℂ, 0 < z.im → A z = f z / E z) ∧
      (∀ z : ℂ, 0 < z.im → B z = fstar f z / E z) ∧
      (∀ x : ℝ, E x ≠ 0 → A x = f x / E x ∧ B x = fstar f x / E x) :=
  ⟨divExt E f, divExt E (fstar f), isH2Cont_divExt hE hf.1 hf.2.1,
    isH2Cont_divExt hE (Differentiable.fstar hf.1) hf.2.2,
    fun z hz ↦ divExt_eq_of_ne hE.1 hf.1 (hE.2.1 z hz),
    fun z hz ↦ divExt_eq_of_ne hE.1 (Differentiable.fstar hf.1) (hE.2.1 z hz),
    fun _ hx ↦ ⟨divExt_eq_of_ne hE.1 hf.1 hx, divExt_eq_of_ne hE.1 (Differentiable.fstar hf.1) hx⟩⟩

/-- `f/E = divExt E f` a.e. on `ℝ`. -/
theorem divExt_ae_eq {E f : ℂ → ℂ} (hE : IsHB E) (hf : Differentiable ℂ f) :
    (fun t : ℝ ↦ divExt E f t) =ᵐ[volume] fun t : ℝ ↦ f t / E t := by
  filter_upwards [hE.ae_ne_zero] with t ht
  exact divExt_eq_of_ne hE.1 hf ht

/-- `‖f‖²_E` is the boundary `L²` norm of the extension `divExt E f`. -/
theorem heNormSq_eq_lintegral_divExt {E f : ℂ → ℂ} (hE : IsHB E) (hf : Differentiable ℂ f) :
    heNormSq E f = ∫⁻ t : ℝ, ‖divExt E f t‖ₑ ^ 2 := by
  unfold heNormSq
  refine lintegral_congr_ae ?_
  filter_upwards [divExt_ae_eq hE hf] with t ht
  rw [ht]

end FF
