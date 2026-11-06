import FourierFrames.HB.DeBranges
import FourierFrames.PW.Complete
import OrtegaCerdaSeip.Products.Canonical
import FourierFrames.Theorem1.Necessity.Sep

/-!
# M03 — Theorem 1, necessity

See `blueprint/M03_Necessity.md`.  Paper pp. 795–796: a separated sampling sequence `Λ` is the
zero set of `E F + E^* F^*` with `E, F ∈ \overline{HB}` and `H(E) = PW`.

Outline (details in the blueprint):
1. `H = PW` with the norm `(∑_{λ ∈ Λ} |f(λ)|²)^{1/2}` is a Hilbert space satisfying (H1)–(H3);
   Theorem C gives `E`.
2. Theorem F applied to `μ = ∑ |E(λ)|² δ_λ` gives `A, p`.
3. Herglotz representation, with the repaired normalisation (`hk`).
4. `G` = genus-one product with zero set `Λ`; the entire functions `W = G M`, `P = W - G`,
   `Q = W + G`; `F` obtained from `P/E^*` (no meromorphic functions are used).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## 0. Elementary generalities -/

/-- If `∑' i, F i` has summable bounds off a finite set of indices, on an open set `U`, it is
differentiable on `U`. -/
theorem differentiableOn_tsum_of_cofinite_bound {ι : Type*} {F : ι → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) {u : ι → ℝ} (hu : Summable u)
    (hb : ∀ᶠ i in cofinite, ∀ w ∈ U, ‖F i w‖ ≤ u i) :
    DifferentiableOn ℂ (fun w ↦ ∑' i, F i w) U := by
  classical
  set s : Set ι := {i | ¬ ∀ w ∈ U, ‖F i w‖ ≤ u i} with hs_def
  have hsfin : s.Finite := Filter.eventually_cofinite.1 hb
  let G : ι → ℂ → ℂ := fun i w ↦ if i ∈ s then 0 else F i w
  have hGd : ∀ i, DifferentiableOn ℂ (G i) U := by
    intro i
    by_cases h : i ∈ s
    · simp only [G, h, ite_true]; exact differentiableOn_const _
    · simp only [G, h, ite_false]; exact hF i
  have hGb : ∀ i, ∀ w ∈ U, ‖G i w‖ ≤ |u i| := by
    intro i w hw
    by_cases h : i ∈ s
    · simp only [G, h, ite_true, norm_zero]; exact abs_nonneg _
    · simp only [G, h, ite_false]
      have : ‖F i w‖ ≤ u i := by
        by_contra hc
        exact h (fun h' ↦ hc (h' w hw))
      exact this.trans (le_abs_self _)
  have hG := differentiableOn_tsum_of_summable_norm hu.abs hGd hU hGb
  have hfin : DifferentiableOn ℂ (fun w ↦ ∑ i ∈ hsfin.toFinset, F i w) U :=
    DifferentiableOn.fun_sum fun i _ ↦ hF i
  refine (hfin.add hG).congr fun w hw ↦ ?_
  have hsum : Summable fun i ↦ F i w :=
    hu.of_norm_bounded_eventually (by
      filter_upwards [hb] with i hi using hi w hw)
  have hsumG : Summable fun i ↦ G i w :=
    Summable.of_norm_bounded hu.abs (fun i ↦ hGb i w hw)
  have hsum1 : Summable fun i ↦ (if i ∈ s then F i w else 0) :=
    summable_of_ne_finset_zero (s := hsfin.toFinset) (fun i hi ↦ by
      have : i ∉ s := by simpa using hi
      simp [this])
  have hsplit : (fun i ↦ F i w) = fun i ↦ (if i ∈ s then F i w else 0) + G i w := by
    funext i
    by_cases h : i ∈ s <;> simp [G, h]
  show ∑' i, F i w = (∑ i ∈ hsfin.toFinset, F i w) + ∑' i, G i w
  rw [hsplit, hsum1.tsum_add hsumG]
  congr 1
  rw [tsum_eq_sum (s := hsfin.toFinset) (fun i hi ↦ by
    have : i ∉ s := by simpa using hi
    simp [this])]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have : i ∈ s := by simpa using hi
  simp [G, this]

/-- Two entire functions that agree on the open upper half-plane are equal. -/
theorem Differentiable.eq_of_eqOn_upper {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h : ∀ z : ℂ, 0 < z.im → f z = g z) : f = g := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : f =ᶠ[𝓝 I] g :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds (by simp)) (fun z hz ↦ h z hz)
  funext z
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (fun w _ ↦ hf.analyticAt w) (fun w _ ↦ hg.analyticAt w) isPreconnected_univ (mem_univ I) hev
    (mem_univ z)

/-- A holomorphic function on the upper half-plane with vanishing real part is a constant
imaginary number. -/
theorem exists_const_of_re_eq_zero {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D {z : ℂ | 0 < z.im})
    (hre : ∀ z : ℂ, 0 < z.im → (D z).re = 0) :
    ∃ a : ℝ, ∀ z : ℂ, 0 < z.im → D z = a * I := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hpre : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hI : (I : ℂ) ∈ {z : ℂ | 0 < z.im} := by simp
  have han : AnalyticOnNhd ℂ D {z : ℂ | 0 < z.im} := hD.analyticOnNhd hU
  rcases han.is_constant_or_isOpen hpre with ⟨w, hw⟩ | hopen
  · refine ⟨(D I).im, fun z hz ↦ ?_⟩
    rw [hw z hz]
    have h1 := hw I hI
    have h2 := hre I (by simp)
    apply Complex.ext
    · simp [← h1, h2]
    · simp [← h1]
  · exfalso
    have hopen' := hopen _ (Subset.refl _) hU
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen' (D I) ⟨I, hI, rfl⟩
    have hmem : D I + ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (D I) r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp [abs_of_pos hr]
      linarith
    obtain ⟨z, hz, hzeq⟩ := hball hmem
    have := hre z hz
    rw [hzeq] at this
    simp [hre I (by simp)] at this
    linarith

/-! ## 1. Separated sets -/

/-- `∑_{λ ∈ Λ} 1/(1+λ²) < ∞` for a separated `Λ`. -/
theorem IsSeparated.summable_inv_one_add_sq {Λ : Set ℝ} (h : IsSeparated Λ) :
    Summable fun x : Λ ↦ 1 / (1 + (x : ℝ) ^ 2) := by
  obtain ⟨δ, hδ, hsep⟩ := h
  exact IsSeparated.summable_inv_one_add_sq' hδ hsep

/-- Off a finite set, the points of a separated `Λ` have `|λ| ≥ r`. -/
theorem IsSeparated.eventually_le_abs {Λ : Set ℝ} (h : IsSeparated Λ) (r : ℝ) :
    ∀ᶠ x : Λ in cofinite, r ≤ |(x : ℝ)| := by
  rw [Filter.eventually_cofinite]
  have hfin := h.finite_inter_Icc (|r|)
  refine (hfin.preimage Subtype.val_injective.injOn).subset fun x hx ↦ ?_
  simp only [Set.mem_ofPred_eq, not_le] at hx
  simp only [mem_preimage, mem_inter_iff, mem_Icc]
  refine ⟨x.2, ?_, ?_⟩
  · have := neg_abs_le r
    have := abs_lt.1 hx
    linarith [le_abs_self r, this.1]
  · have := abs_lt.1 hx
    linarith [le_abs_self r]

/-! ## 2. The sampling Hilbert space -/

/-- The vector space `PW` as a submodule of `ℂ → ℂ`. -/
def PWSub : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | MemPW f}
  add_mem' := fun hf hg ↦ MemPW.add hf hg
  zero_mem' := memPW_zero
  smul_mem' := fun c _ hf ↦ MemPW.const_mul hf c

/-- A copy of `↥PWSub` (a `def`, so that no topology/uniformity is inherited from `ℂ → ℂ`). -/
def PWFun : Type := ↥PWSub

instance : AddCommGroup PWFun := inferInstanceAs (AddCommGroup ↥PWSub)
instance : Module ℂ PWFun := inferInstanceAs (Module ℂ ↥PWSub)

/-- The underlying function, as a linear map. -/
def PWFun.val : PWFun →ₗ[ℂ] (ℂ → ℂ) := PWSub.subtype

theorem PWFun.memPW (h : PWFun) : MemPW (PWFun.val h) := h.2

theorem PWFun.val_injective : Function.Injective PWFun.val := Subtype.val_injective

/-- Build an element of `PWFun` from a function in `PW`. -/
def PWFun.mk (f : ℂ → ℂ) (hf : MemPW f) : PWFun := ⟨f, hf⟩

@[simp] theorem PWFun.val_mk (f : ℂ → ℂ) (hf : MemPW f) : PWFun.val (PWFun.mk f hf) = f := rfl

/-- The sampling inner product `⟨f, g⟩ = ∑_{λ ∈ Λ} conj (f λ) g λ` (Mathlib's convention:
conjugate-linear in the first slot). -/
def sampInner (Λ : Set ℝ) (f g : ℂ → ℂ) : ℂ :=
  ∑' x : Λ, conj (f ((x : ℝ) : ℂ)) * g ((x : ℝ) : ℂ)

section Sampling

variable {Λ : Set ℝ} (hs : IsSampling Λ) {f g : ℂ → ℂ}
include hs

theorem sampleSum_ne_top (hf : MemPW f) : sampleSum Λ f ≠ ∞ := by
  obtain ⟨A, B, _, h⟩ := hs
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (pwNormSq_ne_top hf))
    (h f hf).2

theorem summable_sq_norm_samp (hf : MemPW f) :
    Summable fun x : Λ ↦ ‖f ((x : ℝ) : ℂ)‖ ^ 2 := by
  have h := ENNReal.summable_toReal (f := fun x : Λ ↦ ‖f ((x : ℝ) : ℂ)‖ₑ ^ 2)
    (sampleSum_ne_top hs hf)
  refine h.congr fun x ↦ ?_
  simp [ENNReal.toReal_pow]

theorem sampleSum_eq_ofReal_tsum (hf : MemPW f) :
    sampleSum Λ f = ENNReal.ofReal (∑' x : Λ, ‖f ((x : ℝ) : ℂ)‖ ^ 2) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun x ↦ by positivity) (summable_sq_norm_samp hs hf)]
  unfold sampleSum
  refine tsum_congr fun x ↦ ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem summable_samp_inner (hf : MemPW f) (hg : MemPW g) :
    Summable fun x : Λ ↦ conj (f ((x : ℝ) : ℂ)) * g ((x : ℝ) : ℂ) := by
  refine Summable.of_norm_bounded
    (((summable_sq_norm_samp hs hf).add (summable_sq_norm_samp hs hg)).mul_left (1 / 2 : ℝ))
    fun x ↦ ?_
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖f ((x : ℝ) : ℂ)‖ - ‖g ((x : ℝ) : ℂ)‖)]

theorem sampInner_self (hf : MemPW f) :
    sampInner Λ f f = ((∑' x : Λ, ‖f ((x : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  unfold sampInner
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun x ↦ ?_
  rw [Complex.conj_mul']
  push_cast; rfl

theorem sampInner_conj_symm (hf : MemPW f) (hg : MemPW g) :
    conj (sampInner Λ g f) = sampInner Λ f g := by
  unfold sampInner
  rw [Complex.conj_tsum]
  refine tsum_congr fun x ↦ ?_
  simp [mul_comm]

theorem sampInner_add_left {h : ℂ → ℂ} (hf : MemPW f) (hg : MemPW g) (hh : MemPW h) :
    sampInner Λ (f + g) h = sampInner Λ f h + sampInner Λ g h := by
  unfold sampInner
  rw [← (summable_samp_inner hs hf hh).tsum_add (summable_samp_inner hs hg hh)]
  refine tsum_congr fun x ↦ ?_
  simp [add_mul]

theorem sampInner_smul_left (c : ℂ) (hf : MemPW f) (hg : MemPW g) :
    sampInner Λ (c • f) g = conj c * sampInner Λ f g := by
  unfold sampInner
  rw [← tsum_mul_left]
  refine tsum_congr fun x ↦ ?_
  simp [mul_assoc]

/-- Positive definiteness (uses the lower sampling bound and
`MemPW.eq_zero_of_pwNormSq_eq_zero`). -/
theorem sampInner_definite (hf : MemPW f) (h : sampInner Λ f f = 0) : f = 0 := by
  rw [sampInner_self hs hf] at h
  have h0 : ∑' x : Λ, ‖f ((x : ℝ) : ℂ)‖ ^ 2 = 0 := by exact_mod_cast h
  have hS : sampleSum Λ f = 0 := by rw [sampleSum_eq_ofReal_tsum hs hf, h0]; simp
  obtain ⟨A, B, hA, hb⟩ := hs
  have h1 := (hb f hf).1
  rw [hS, nonpos_iff_eq_zero, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (by exact_mod_cast hA.ne')
  · exact hf.eq_zero_of_pwNormSq_eq_zero h1

set_option warn.classDefReducibility false in
/-- The `InnerProductSpace.Core` on `PWFun` given by the sampling inner product. -/
def sampCore : InnerProductSpace.Core ℂ PWFun where
  inner f g := sampInner Λ (PWFun.val f) (PWFun.val g)
  conj_inner_symm f g := sampInner_conj_symm hs f.memPW g.memPW
  re_inner_nonneg f := by
    have h := sampInner_self hs f.memPW
    show 0 ≤ (sampInner Λ (PWFun.val f) (PWFun.val f)).re
    rw [h, Complex.ofReal_re]
    exact tsum_nonneg fun x ↦ by positivity
  add_left f g h := sampInner_add_left hs f.memPW g.memPW h.memPW
  smul_left f g c := sampInner_smul_left hs c f.memPW g.memPW
  definite f h := PWFun.val_injective (by simpa using sampInner_definite hs f.memPW h)

/-- Completeness in the sampling norm, stated without any instance: a sequence in `PW` that is
Cauchy for `sampleSum Λ (f m - f n)` has a limit in `PW` for the same quantity. -/
theorem samp_cauchy_converges (hPW : PaleyWienerThm) {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemPW (f n))
    (hc : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      sampleSum Λ (fun z ↦ f m z - f n z) < ε) :
    ∃ g : ℂ → ℂ, MemPW g ∧ Tendsto (fun n ↦ sampleSum Λ (fun z ↦ f n z - g z)) atTop (𝓝 0) := by
  obtain ⟨A, B, hA, hb⟩ := hs
  have hA0 : (A : ℝ≥0∞) ≠ 0 := by exact_mod_cast hA.ne'
  have hc' : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      pwNormSq (fun z ↦ f m z - f n z) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc (A * ε) (mul_ne_zero hA0 hε)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have h1 := (hb (fun z ↦ f m z - f n z) ((hf m).sub (hf n))).1
    exact (ENNReal.mul_lt_mul_iff_right hA0 ENNReal.coe_ne_top).1 (h1.trans_lt (hN m hm n hn))
  obtain ⟨g, hg, _, ht⟩ := pw_complete hPW hf hc'
  refine ⟨g, hg, ?_⟩
  have h2 : Tendsto (fun n ↦ (B : ℝ≥0∞) * pwNormSq (fun z ↦ f n z - g z)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ht (Or.inr (ENNReal.coe_ne_top (r := B)))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ ↦ zero_le)
    (fun n ↦ ?_)
  exact (hb _ ((hf n).sub hg)).2

/-- (H1) at the level of functions: for `f ∈ PW` with a nonreal zero `ζ`, the function
`(z - ζ̄) f(z)/(z - ζ)` is in `PW` and has the same sampling sum. -/
theorem samp_H1 (hf : MemPW f) {ζ : ℂ} (hζ : ζ.im ≠ 0) (hz : f ζ = 0) :
    MemPW (fun z ↦ dslope f ζ z * (z - conj ζ)) ∧
      sampleSum Λ (fun z ↦ dslope f ζ z * (z - conj ζ)) = sampleSum Λ f := by
  refine ⟨hf.mul_div_sub hz _, ?_⟩
  unfold sampleSum
  refine tsum_congr fun x ↦ ?_
  have hne : ((x : ℝ) : ℂ) ≠ ζ := fun h ↦ hζ (by rw [← h]; simp)
  have hne' : ((x : ℝ) : ℂ) - ζ ≠ 0 := sub_ne_zero.2 hne
  beta_reduce
  rw [dslope_of_ne f hne, slope_def_field, hz]
  have : ‖(f ((x : ℝ) : ℂ) - 0) / (((x : ℝ) : ℂ) - ζ) * (((x : ℝ) : ℂ) - conj ζ)‖ =
      ‖f ((x : ℝ) : ℂ)‖ := by
    have hc : ((x : ℝ) : ℂ) - conj ζ = conj (((x : ℝ) : ℂ) - ζ) := by simp
    rw [norm_mul, norm_div, hc, Complex.norm_conj, sub_zero]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.2 hne')
  rw [← ofReal_norm, this, ofReal_norm]

/-- (H2) quantitatively: `|f(ζ)|² ≤ e^{2π|Im ζ|} A⁻¹ ∑|f(λ)|²`. -/
theorem samp_H2 (hPW : PaleyWienerThm) (ζ : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℂ → ℂ, MemPW f → ‖f ζ‖ ^ 2 ≤ C * (sampleSum Λ f).toReal := by
  obtain ⟨A, B, hA, hb⟩ := hs
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  refine ⟨Real.exp (2 * Real.pi * |ζ.im|) / A, by positivity, fun f hf ↦ ?_⟩
  have h1 := pw_norm_sq_le hPW hf ζ
  have hne : sampleSum Λ f ≠ ∞ := sampleSum_ne_top ⟨A, B, hA, hb⟩ hf
  have h2 : (A : ℝ) * (pwNormSq f).toReal ≤ (sampleSum Λ f).toReal := by
    have := ENNReal.toReal_mono hne (hb f hf).1
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at this
  have h3 : (pwNormSq f).toReal ≤ (sampleSum Λ f).toReal / A := by
    rw [le_div_iff₀ hA']; linarith
  calc ‖f ζ‖ ^ 2 ≤ Real.exp (2 * Real.pi * |ζ.im|) * (pwNormSq f).toReal := h1
    _ ≤ Real.exp (2 * Real.pi * |ζ.im|) * ((sampleSum Λ f).toReal / A) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = _ := by ring

/-- (H3) at the level of functions. -/
theorem samp_H3 (hf : MemPW f) : sampleSum Λ (fstar f) = sampleSum Λ f := by
  unfold sampleSum
  refine tsum_congr fun x ↦ ?_
  rw [fstar_ofReal, ← ofReal_norm, ← ofReal_norm, Complex.norm_conj]

/-- **The sampling Hilbert space.** `PW` with the norm `(∑_{λ ∈ Λ} |f(λ)|²)^{1/2}` satisfies all
the hypotheses of Theorem C. -/
theorem exists_samplingHilbertSpace (hPW : PaleyWienerThm) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ι : H →ₗ[ℂ] (ℂ → ℂ)), Function.Injective ι ∧ (∀ h : H, Differentiable ℂ (ι h)) ∧
      (∀ h : H, ∀ ζ : ℂ, ζ.im ≠ 0 → ι h ζ = 0 →
        ∃ g : H, ‖g‖ = ‖h‖ ∧ ∀ z : ℂ, z ≠ ζ → ι g z = ι h z * (z - conj ζ) / (z - ζ)) ∧
      (∀ ζ : ℂ, ζ.im ≠ 0 → Continuous fun h : H ↦ ι h ζ) ∧
      (∀ h : H, ∃ g : H, ‖g‖ = ‖h‖ ∧ ι g = fstar (ι h)) ∧ (∃ h : H, h ≠ 0) ∧
      (∀ f : ℂ → ℂ, f ∈ Set.range ι ↔ MemPW f) ∧
      ∀ h : H, ENNReal.ofReal (‖h‖ ^ 2) = sampleSum Λ (ι h) := by
  let i1 : NormedAddCommGroup PWFun := (sampCore hs).toNormedAddCommGroup
  let i2 : InnerProductSpace ℂ PWFun := InnerProductSpace.ofCore (sampCore hs).toCore
  have hsq : ∀ h : PWFun, ‖h‖ ^ 2 = ∑' x : Λ, ‖PWFun.val h ((x : ℝ) : ℂ)‖ ^ 2 := by
    intro h
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) h]
    have := sampInner_self hs h.memPW
    change (sampInner Λ (PWFun.val h) (PWFun.val h)).re = _
    rw [this, Complex.ofReal_re]
  have hnorm : ∀ h : PWFun, ENNReal.ofReal (‖h‖ ^ 2) = sampleSum Λ (PWFun.val h) := by
    intro h
    rw [hsq h, sampleSum_eq_ofReal_tsum hs h.memPW]
  have hnorm' : ∀ h : PWFun, ‖h‖ ^ 2 = (sampleSum Λ (PWFun.val h)).toReal := by
    intro h
    rw [← hnorm h, ENNReal.toReal_ofReal (by positivity)]
  have hnorm_eq : ∀ g h : PWFun, sampleSum Λ (PWFun.val g) = sampleSum Λ (PWFun.val h) →
      ‖g‖ = ‖h‖ := by
    intro g h hgh
    have : ‖g‖ ^ 2 = ‖h‖ ^ 2 := by rw [hnorm' g, hnorm' h, hgh]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  have hcomplete : CompleteSpace PWFun := by
    refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
    have hc : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
        sampleSum Λ (fun z ↦ PWFun.val (u m) z - PWFun.val (u n) z) < ε := by
      intro ε hε
      obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 (pos_iff_ne_zero.2 hε)
      have hrpos : 0 < r := by
        rcases hr0.eq_or_lt with h | h
        · rw [← h] at hr1; simp at hr1
        · exact h
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu (Real.sqrt r) (Real.sqrt_pos.2 hrpos)
      refine ⟨N, fun m hm n hn ↦ ?_⟩
      have h1 := hN m hm n hn
      rw [dist_eq_norm] at h1
      have h2 : ‖u m - u n‖ ^ 2 < r := by
        have := pow_lt_pow_left₀ h1 (norm_nonneg _) (two_ne_zero)
        rwa [Real.sq_sqrt hrpos.le] at this
      have h3 := hnorm (u m - u n)
      have h4 : PWFun.val (u m - u n) = fun z ↦ PWFun.val (u m) z - PWFun.val (u n) z := by
        funext z; simp
      rw [h4] at h3
      rw [← h3]
      exact lt_trans ((ENNReal.ofReal_lt_ofReal_iff hrpos).2 h2) hr2
    obtain ⟨g, hg, ht⟩ := samp_cauchy_converges hs hPW (fun n ↦ (u n).memPW) hc
    refine ⟨PWFun.mk g hg, ?_⟩
    rw [tendsto_iff_dist_tendsto_zero]
    have h5 : ∀ n, dist (u n) (PWFun.mk g hg) =
        Real.sqrt ((sampleSum Λ (fun z ↦ PWFun.val (u n) z - g z)).toReal) := by
      intro n
      rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg (u n - PWFun.mk g hg)), hnorm']
      congr 3
    simp_rw [h5]
    have := (ENNReal.tendsto_toReal (ENNReal.zero_ne_top)).comp ht
    have h6 := (Real.continuous_sqrt.tendsto _).comp this
    simp only [ENNReal.toReal_zero, Real.sqrt_zero] at h6
    exact h6
  refine ⟨PWFun, i1, i2, hcomplete, PWFun.val, PWFun.val_injective, fun h ↦ h.memPW.1, ?_, ?_, ?_,
    ?_, ?_, hnorm⟩
  · intro h ζ hζ hz
    obtain ⟨hm, hS⟩ := samp_H1 hs h.memPW hζ hz
    refine ⟨PWFun.mk _ hm, hnorm_eq _ _ (by simpa using hS), fun z hzz ↦ ?_⟩
    simp only [PWFun.val_mk]
    have hne : z - ζ ≠ 0 := sub_ne_zero.2 hzz
    rw [dslope_of_ne _ hzz, slope_def_field, hz]
    field_simp
    ring
  · intro ζ hζ
    obtain ⟨C, hC0, hC⟩ := samp_H2 hs hPW ζ
    let L : PWFun →ₗ[ℂ] ℂ := (LinearMap.proj ζ).comp PWFun.val
    refine (AddMonoidHomClass.continuous_of_bound L (Real.sqrt C) fun h ↦ ?_)
    change ‖PWFun.val h ζ‖ ≤ _
    have h1 := hC _ h.memPW
    rw [← hnorm' h] at h1
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt hC0]
    exact h1
  · intro h
    refine ⟨PWFun.mk _ h.memPW.fstar, hnorm_eq _ _ ?_, rfl⟩
    simpa using samp_H3 hs h.memPW
  · obtain ⟨g, hg, hg0⟩ := exists_memPW_eval_ne_zero
    refine ⟨PWFun.mk g hg, fun h ↦ ?_⟩
    have := congrFun (congrArg PWFun.val h) 0
    simp [hg0] at this
  · intro f
    exact ⟨fun ⟨h, hh⟩ ↦ hh ▸ h.memPW, fun hf ↦ ⟨PWFun.mk f hf, rfl⟩⟩

end Sampling

/-! ## 3. Theorem C: the function `E` -/

section StepE

/-- Steps 1–2 of the proof: Theorem C applied to the sampling Hilbert space. -/
theorem exists_E (hPW : PaleyWienerThm) (hC : TheoremC) {Λ : Set ℝ} (hs : IsSampling Λ) :
    ∃ E : ℂ → ℂ, IsHB E ∧ HEEqPW E ∧ (∀ f : ℂ → ℂ, MemHE E f ↔ MemPW f) ∧
      ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Λ f := by
  obtain ⟨H, i1, i2, i3, ι, hinj, hdiff, h1, h2, h3, hne, hrange, hnorm⟩ :=
    exists_samplingHilbertSpace hs hPW
  obtain ⟨E, hE, hmem, hn⟩ := @hC H i1 i2 i3 ι hinj hdiff h1 h2 h3 hne
  have hmem' : ∀ f : ℂ → ℂ, MemHE E f ↔ MemPW f := fun f ↦ (hmem f).trans (hrange f)
  have hnormPW : ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Λ f := by
    intro f hf
    obtain ⟨h, rfl⟩ := (hrange f).2 hf
    rw [← hn h, hnorm h]
  obtain ⟨A, B, hA, hb⟩ := hs
  refine ⟨E, hE, ⟨hmem', A, B, hA, fun f hf ↦ ?_⟩, hmem', hnormPW⟩
  rw [hnormPW f hf]
  exact hb f hf

end StepE

/-! ## 4. The measure `μ = ∑ |E(λ)|² δ_λ` and Theorem F -/

section StepF

/-- `μ = ∑_{λ ∈ Λ} |E(λ)|² δ_λ`. -/
def sampMeasure (Λ : Set ℝ) (E : ℂ → ℂ) : Measure ℝ :=
  Measure.sum fun x : Λ ↦ ENNReal.ofReal (‖E ((x : ℝ) : ℂ)‖ ^ 2) • Measure.dirac (x : ℝ)

theorem lintegral_sampMeasure (Λ : Set ℝ) (E : ℂ → ℂ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ t, g t ∂(sampMeasure Λ E) =
      ∑' x : Λ, ENNReal.ofReal (‖E ((x : ℝ) : ℂ)‖ ^ 2) * g (x : ℝ) := by
  unfold sampMeasure
  rw [lintegral_sum_measure]
  refine tsum_congr fun x ↦ ?_
  rw [lintegral_smul_measure, lintegral_dirac]
  rfl

/-- `∫ |f/E|² dμ = ∑_{λ ∈ Λ} |f(λ)|²` when `E` has no real zeros. -/
theorem lintegral_sampMeasure_div {Λ : Set ℝ} {E : ℂ → ℂ} (hE0 : ∀ x : ℝ, E (x : ℂ) ≠ 0)
    (f : ℂ → ℂ) : ∫⁻ t : ℝ, ‖f t / E t‖ₑ ^ 2 ∂(sampMeasure Λ E) = sampleSum Λ f := by
  rw [lintegral_sampMeasure]
  unfold sampleSum
  refine tsum_congr fun x ↦ ?_
  have h0 : ‖E ((x : ℝ) : ℂ)‖ ≠ 0 := by simpa using hE0 x
  rw [← ofReal_norm (f ((x : ℝ) : ℂ) / E ((x : ℝ) : ℂ)), ← ofReal_norm (f ((x : ℝ) : ℂ)),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [norm_div]
  field_simp

theorem poissonInt_sampMeasure (Λ : Set ℝ) (E : ℂ → ℂ) (z : ℂ) :
    poissonInt (sampMeasure Λ E) z =
      ∑' x : Λ, ENNReal.ofReal (‖E ((x : ℝ) : ℂ)‖ ^ 2) *
        ENNReal.ofReal (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2))) :=
  lintegral_sampMeasure Λ E _

/-- The quotient `(E + E^* A)/(E - E^* A)` of Theorem F. -/
def hbQuot (E A : ℂ → ℂ) (z : ℂ) : ℂ :=
  (E z + fstar E z * A z) / (E z - fstar E z * A z)

/-- The denominator does not vanish on `ℂ₊` (this uses strictness of `E`). -/
theorem denom_ne_zero {E A : ℂ → ℂ} (hE : IsStrictHB E) {z : ℂ} (hz : 0 < z.im)
    (hA : ‖A z‖ ≤ 1) : E z - fstar E z * A z ≠ 0 := by
  intro h
  have h1 : E z = fstar E z * A z := sub_eq_zero.1 h
  have h2 := hE.2 z hz
  rw [← norm_fstar] at h2
  have h3 : ‖E z‖ ≤ ‖fstar E z‖ := by
    rw [h1, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hA
  linarith

theorem differentiableOn_hbQuot {E A : ℂ → ℂ} (hE : IsStrictHB E)
    (hA : DifferentiableOn ℂ A {z : ℂ | 0 < z.im}) (hA1 : ∀ z : ℂ, 0 < z.im → ‖A z‖ ≤ 1) :
    DifferentiableOn ℂ (hbQuot E A) {z : ℂ | 0 < z.im} := by
  have hEd : Differentiable ℂ E := hE.1.1
  have h1 : DifferentiableOn ℂ E {z : ℂ | 0 < z.im} := hEd.differentiableOn
  have h2 : DifferentiableOn ℂ (fstar E) {z : ℂ | 0 < z.im} := (Differentiable.fstar hEd).differentiableOn
  unfold hbQuot
  exact (h1.add (h2.mul hA)).div (h1.sub (h2.mul hA)) fun z hz ↦ denom_ne_zero hE hz (hA1 z hz)

/-- Step 3: Theorem F, with all the consequences used later (real-valued reformulation of the
Poisson integral and summability of `|E(λ)|²/(1+λ²)`). -/
theorem exists_herglotz_data (hF : TheoremF) (Λ : Set ℝ) {E : ℂ → ℂ} (hE : IsStrictHB E)
    (hE0 : ∀ x : ℝ, E (x : ℂ) ≠ 0)
    (hnorm : ∀ f : ℂ → ℂ, MemHE E f → heNormSq E f = sampleSum Λ f) :
    ∃ A : ℂ → ℂ, DifferentiableOn ℂ A {z : ℂ | 0 < z.im} ∧ (∀ z : ℂ, 0 < z.im → ‖A z‖ ≤ 1) ∧
      ∃ p : ℝ, 0 ≤ p ∧
        Summable (fun x : Λ ↦ ‖E ((x : ℝ) : ℂ)‖ ^ 2 / (1 + (x : ℝ) ^ 2)) ∧
        ∀ z : ℂ, 0 < z.im →
          Summable (fun x : Λ ↦ ‖E ((x : ℝ) : ℂ)‖ ^ 2 *
            (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2)))) ∧
          (∑' x : Λ, ‖E ((x : ℝ) : ℂ)‖ ^ 2 *
            (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2)))) + p * z.im =
            (hbQuot E A z).re := by
  have hμ : ∀ f : ℂ → ℂ, MemHE E f →
      ∫⁻ t : ℝ, ‖f t / E t‖ₑ ^ 2 ∂(sampMeasure Λ E) = heNormSq E f := by
    intro f hf
    rw [lintegral_sampMeasure_div hE0, hnorm f hf]
  obtain ⟨A, hAd, hA1, p, hp, hP⟩ := hF (sampMeasure Λ E) E hE hE0 hμ
  -- real reformulation of the Poisson integral
  have hreal : ∀ z : ℂ, 0 < z.im →
      Summable (fun x : Λ ↦ ‖E ((x : ℝ) : ℂ)‖ ^ 2 *
        (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2)))) ∧
      (poissonInt (sampMeasure Λ E) z).toReal =
        ∑' x : Λ, ‖E ((x : ℝ) : ℂ)‖ ^ 2 *
          (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2))) := by
    intro z hz
    have hne := (hP z hz).1
    have hnn : ∀ x : Λ, 0 ≤ ‖E ((x : ℝ) : ℂ)‖ ^ 2 *
        (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2))) := fun x ↦ by positivity
    have hpois : poissonInt (sampMeasure Λ E) z = ∑' x : Λ, ENNReal.ofReal
        (‖E ((x : ℝ) : ℂ)‖ ^ 2 * (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2)))) := by
      rw [poissonInt_sampMeasure]
      refine tsum_congr fun x ↦ ?_
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [hpois] at hne ⊢
    have hs1 := ENNReal.summable_toReal hne
    have hs2 : Summable (fun x : Λ ↦ ‖E ((x : ℝ) : ℂ)‖ ^ 2 *
        (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2)))) :=
      hs1.congr fun x ↦ ENNReal.toReal_ofReal (hnn x)
    refine ⟨hs2, ?_⟩
    rw [ENNReal.tsum_toReal_eq (fun x ↦ ENNReal.ofReal_ne_top)]
    exact tsum_congr fun x ↦ ENNReal.toReal_ofReal (hnn x)
  refine ⟨A, hAd, hA1, p, hp, ?_, fun z hz ↦ ⟨(hreal z hz).1, ?_⟩⟩
  · have h1 := (hreal I (by simp)).1.mul_left Real.pi
    refine h1.congr fun x ↦ ?_
    simp only [Complex.I_re, Complex.I_im, sub_zero]
    have : (1 : ℝ) + (x : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  · rw [← (hreal z hz).2]
    exact (hP z hz).2

end StepF

/-! ## 5. The Herglotz kernel (repaired normalisation) -/

section Kernel

/-- The convergence-factor kernel `1/(λ - z) - λ/(1+λ²)` (defined for all `λ ∈ ℝ`, including
`λ = 0`). -/
def hk (x : ℝ) (z : ℂ) : ℂ := 1 / ((x : ℂ) - z) - ((x / (1 + x ^ 2) : ℝ) : ℂ)

/-- `hk x z = (1 + x z)/((x - z)(1 + x²))` for `z ≠ x`. -/
theorem hk_eq {x : ℝ} {z : ℂ} (hz : z ≠ x) :
    hk x z = (1 + x * z) / (((x : ℂ) - z) * (1 + (x : ℂ) ^ 2)) := by
  have h1 : (x : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  have h2 : (1 : ℂ) + (x : ℂ) ^ 2 ≠ 0 := by
    have : (1 : ℂ) + (x : ℂ) ^ 2 = ((1 + x ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast (by positivity : (1 + x ^ 2 : ℝ) ≠ 0)
  unfold hk
  push_cast
  field_simp
  ring

/-- Uniform bound for the tail: `|z| ≤ R`, `2R ≤ |λ|`, `R ≥ 1/2` give
`|hk λ z| ≤ 2(1+R)/(1+λ²)`. -/
theorem norm_hk_le {R : ℝ} (hR : 1 / 2 ≤ R) {x : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) (hx : 2 * R ≤ |x|) :
    ‖hk x z‖ ≤ 2 * (1 + R) / (1 + x ^ 2) := by
  have hxa : 1 ≤ |x| := by linarith
  have hzx : z ≠ x := by
    intro h
    rw [h] at hz
    simp only [Complex.norm_real, Real.norm_eq_abs] at hz
    linarith
  rw [hk_eq hzx]
  have h1 : |x| / 2 ≤ ‖(x : ℂ) - z‖ := by
    have := norm_sub_norm_le (x : ℂ) z
    simp only [Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  have h2 : ‖(1 : ℂ) + x * z‖ ≤ 1 + |x| * R := by
    calc ‖(1 : ℂ) + x * z‖ ≤ ‖(1 : ℂ)‖ + ‖(x : ℂ) * z‖ := norm_add_le _ _
      _ ≤ 1 + |x| * R := by
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr
  have h3 : ‖(1 : ℂ) + (x : ℂ) ^ 2‖ = 1 + x ^ 2 := by
    have : (1 : ℂ) + (x : ℂ) ^ 2 = ((1 + x ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hpos : 0 < ‖(x : ℂ) - z‖ := by linarith
  rw [norm_div, norm_mul, h3, div_le_div_iff₀ (mul_pos hpos (by positivity)) (by positivity)]
  have h4 : 1 + |x| * R ≤ 2 * (1 + R) * ‖(x : ℂ) - z‖ := by nlinarith
  have h5 : (0 : ℝ) ≤ 1 + x ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h4 h5, mul_le_mul_of_nonneg_right h2 h5]

/-- `Re(-i · hk λ z) = y/|λ - z|²` for `y = Im z ≠ 0`. -/
theorem re_neg_I_mul_hk {x : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    (-I * hk x z).re = z.im / (((x : ℝ) - z.re) ^ 2 + z.im ^ 2) := by
  have hpos : 0 < ((x : ℝ) - z.re) ^ 2 + z.im ^ 2 := by positivity
  have h0 : ((x : ℂ) / (1 + (x : ℂ) ^ 2)).im = 0 := by
    have : ((x : ℂ) / (1 + (x : ℂ) ^ 2)) = ((x / (1 + x ^ 2) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_im]
  simp [hk, Complex.inv_im, Complex.normSq_apply, h0]
  ring

/-- The series `∑_{λ ∈ Λ} c_λ hk λ z`. -/
def herglotzSum (Λ : Set ℝ) (c : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∑' x : Λ, (c x : ℂ) * hk (x : ℝ) z

/-- Absolute convergence of the series for `z ∉ Λ`. -/
theorem summable_norm_herglotz {Λ : Set ℝ} (hΛ : IsSeparated Λ) {c : ℝ → ℝ}
    (hcs : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2)) {z : ℂ} (hz : z.im ≠ 0) :
    Summable fun x : Λ ↦ ‖(c x : ℂ) * hk (x : ℝ) z‖ := by
  have hR : (1 : ℝ) / 2 ≤ max ‖z‖ (1 / 2) := le_max_right _ _
  refine Summable.of_norm_bounded_eventually (hcs.mul_left (2 * (1 + max ‖z‖ (1 / 2)))) ?_
  filter_upwards [hΛ.eventually_le_abs (2 * max ‖z‖ (1 / 2))] with x hx
  rw [norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have := norm_hk_le hR (le_max_left ‖z‖ (1 / 2)) hx
  calc |c x| * ‖hk (x : ℝ) z‖ ≤ |c x| * (2 * (1 + max ‖z‖ (1 / 2)) / (1 + (x : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = _ := by ring

/-- `Re(-i/π · S(z)) = (1/π) ∑ c_λ y/|λ - z|²` on `ℂ₊`. -/
theorem re_herglotzSum {Λ : Set ℝ} (hΛ : IsSeparated Λ) {c : ℝ → ℝ}
    (hcs : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2)) {z : ℂ} (hz : 0 < z.im) :
    ((-I / Real.pi) * herglotzSum Λ c z).re =
      ∑' x : Λ, c x * (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2))) := by
  have hsum := (summable_norm_herglotz hΛ hcs hz.ne').of_norm
  unfold herglotzSum
  rw [← tsum_mul_left, Complex.re_tsum (hsum.mul_left _)]
  refine tsum_congr fun x ↦ ?_
  have h1 := re_neg_I_mul_hk (x := (x : ℝ)) hz.ne'
  have h2 : (-I / (Real.pi : ℂ)) * ((c x : ℂ) * hk (x : ℝ) z) =
      ((c x / Real.pi : ℝ) : ℂ) * (-I * hk (x : ℝ) z) := by
    push_cast; ring
  rw [h2, Complex.re_ofReal_mul, h1, div_mul_div_comm, mul_div_assoc]

/-- The entire continuation of `G(z)·hk λ z` when `G(λ) = 0`. -/
def entTerm (G : ℂ → ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  -dslope G (x : ℂ) z - ((x / (1 + x ^ 2) : ℝ) : ℂ) * G z

theorem differentiable_entTerm {G : ℂ → ℂ} (hG : Differentiable ℂ G) (x : ℝ) :
    Differentiable ℂ (entTerm G x) := by
  have h1 : Differentiable ℂ (dslope G (x : ℂ)) :=
    differentiableOn_univ.1 ((differentiableOn_dslope Filter.univ_mem).2 hG.differentiableOn)
  unfold entTerm
  exact h1.neg.sub (hG.const_mul _)

theorem entTerm_eq {G : ℂ → ℂ} {x : ℝ} (hGx : G (x : ℂ) = 0) {z : ℂ} (hz : z ≠ (x : ℂ)) :
    entTerm G x z = G z * hk x z := by
  unfold entTerm hk
  rw [dslope_of_ne _ hz, slope_def_field, hGx]
  have h1 : z - (x : ℂ) ≠ 0 := sub_ne_zero.2 hz
  have h2 : (x : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  push_cast
  field_simp
  ring

/-- The entire function `∑ c_λ · entTerm G λ`. -/
def entSum (Λ : Set ℝ) (c : ℝ → ℝ) (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' x : Λ, (c x : ℂ) * entTerm G (x : ℝ) z

theorem differentiable_entSum {Λ : Set ℝ} (hΛ : IsSeparated Λ) {c : ℝ → ℝ}
    (hcs : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2)) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0) :
    Differentiable ℂ (entSum Λ c G) := by
  intro z0
  suffices h : ∀ R : ℝ, 1 / 2 ≤ R → DifferentiableOn ℂ (entSum Λ c G) (Metric.ball 0 R) by
    refine (h (max (‖z0‖ + 1) (1 / 2)) (le_max_right _ _)).differentiableAt
      (Metric.isOpen_ball.mem_nhds ?_)
    rw [mem_ball_zero_iff]
    exact lt_max_of_lt_left (by linarith)
  intro R hR
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hG.continuous.continuousOn
  unfold entSum
  refine differentiableOn_tsum_of_cofinite_bound
    (u := fun x : Λ ↦ |M| * (2 * (1 + R)) * (|c x| / (1 + (x : ℝ) ^ 2)))
    Metric.isOpen_ball (fun x ↦ ((differentiable_entTerm hG x).const_mul _).differentiableOn)
    (hcs.mul_left _) ?_
  filter_upwards [hΛ.eventually_le_abs (2 * R)] with x hx w hw
  rw [mem_ball_zero_iff] at hw
  have hwx : w ≠ ((x : ℝ) : ℂ) := by
    intro h
    rw [h] at hw
    simp only [Complex.norm_real, Real.norm_eq_abs] at hw
    linarith
  rw [entTerm_eq (hG0 _ x.2) hwx, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := norm_hk_le hR hw.le hx
  have h2 : ‖G w‖ ≤ |M| := (hM w (mem_closedBall_zero_iff.2 hw.le)).trans (le_abs_self _)
  calc |c x| * (‖G w‖ * ‖hk (x : ℝ) w‖) ≤ |c x| * (|M| * (2 * (1 + R) / (1 + (x : ℝ) ^ 2))) := by
        gcongr
    _ = _ := by ring

theorem entSum_eq {Λ : Set ℝ} (hΛ : IsSeparated Λ) {c : ℝ → ℝ}
    (hcs : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2)) {G : ℂ → ℂ}
    (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0) {z : ℂ} (hz : z.im ≠ 0) :
    entSum Λ c G z = G z * herglotzSum Λ c z := by
  unfold entSum herglotzSum
  rw [← tsum_mul_left]
  refine tsum_congr fun x ↦ ?_
  have hzx : z ≠ ((x : ℝ) : ℂ) := fun h ↦ hz (by rw [h]; simp)
  rw [entTerm_eq (hG0 _ x.2) hzx]
  ring

/-- `(entSum)^* = entSum` when `G^* = G` (all `c_λ`, `λ` are real). -/
theorem fstar_entSum {Λ : Set ℝ} (hΛ : IsSeparated Λ) {c : ℝ → ℝ}
    (hcs : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2)) {G : ℂ → ℂ}
    (hGd : Differentiable ℂ G) (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0) (hGs : fstar G = G) :
    fstar (entSum Λ c G) = entSum Λ c G := by
  refine Differentiable.eq_of_eqOn_upper (Differentiable.fstar (differentiable_entSum hΛ hcs hGd hG0))
    (differentiable_entSum hΛ hcs hGd hG0) fun z hz ↦ ?_
  have hz' : (conj z).im ≠ 0 := by simp; exact hz.ne'
  have hkc : ∀ x : ℝ, conj (hk x (conj z)) = hk x z := fun x ↦ by simp [hk]
  have hS : conj (herglotzSum Λ c (conj z)) = herglotzSum Λ c z := by
    unfold herglotzSum
    rw [Complex.conj_tsum]
    refine tsum_congr fun x ↦ ?_
    rw [map_mul, hkc, Complex.conj_ofReal]
  have hGz : conj (G (conj z)) = G z := congrFun hGs z
  show conj (entSum Λ c G (conj z)) = entSum Λ c G z
  rw [entSum_eq hΛ hcs hG0 hz', entSum_eq hΛ hcs hG0 hz.ne', map_mul, hGz, hS]

end Kernel

/-! ## 6. The canonical product `G` with zero set `Λ` -/

section Product

/-- The zeros of `G` other than `0`, as a subset of `ℂ`. -/
def zeroSet (Λ : Set ℝ) : Set ℂ := Complex.ofReal '' (Λ \ {0})

open scoped Classical in
/-- `G(z) = z^{[0 ∈ Λ]} ∏_{λ ∈ Λ∖{0}} (1 - z/λ) e^{z/λ}`. -/
def genProd (Λ : Set ℝ) (z : ℂ) : ℂ :=
  (if (0 : ℝ) ∈ Λ then z else 1) * OCS.canonicalProd (zeroSet Λ) (fun a ↦ a⁻¹) z

theorem isGenusOneData_zeroSet {Λ : Set ℝ} (hΛ : IsSeparated Λ) :
    OCS.IsGenusOneData (zeroSet Λ) (fun a ↦ a⁻¹) := by
  refine ⟨?_, ?_, by simp⟩
  · rintro ⟨y, hy, hy0⟩
    exact hy.2 (by simpa using hy0)
  · have hg : Summable fun x : Λ ↦ (‖(((x : ℝ)) : ℂ)‖⁻¹) ^ 2 := by
      refine Summable.of_norm_bounded_eventually (hΛ.summable_inv_one_add_sq.mul_left 2) ?_
      filter_upwards [hΛ.eventually_le_abs 1] with x hx
      rw [Real.norm_of_nonneg (by positivity), Complex.norm_real, Real.norm_eq_abs]
      have hx2 : 1 ≤ (x : ℝ) ^ 2 := by nlinarith [abs_nonneg (x : ℝ), sq_abs (x : ℝ)]
      have hpos : 0 < |(x : ℝ)| := by linarith
      rw [inv_pow, sq_abs, mul_one_div, inv_eq_one_div, div_le_div_iff₀ (by positivity)
        (by positivity)]
      linarith
    have hh := hg.comp_injective (Set.inclusion_injective (Set.sdiff_subset (s := Λ) (t := {0})))
    let e : (Λ \ {0} : Set ℝ) ≃ zeroSet Λ :=
      Equiv.Set.image Complex.ofReal _ Complex.ofReal_injective
    exact e.summable_iff.1 (by exact hh)

theorem differentiable_genProd {Λ : Set ℝ} (hΛ : IsSeparated Λ) :
    Differentiable ℂ (genProd Λ) := by
  have h := OCS.differentiable_canonicalProd (isGenusOneData_zeroSet hΛ)
  unfold genProd
  by_cases h0 : (0 : ℝ) ∈ Λ
  · simp only [h0, ite_true]
    exact differentiable_id.mul h
  · simp only [h0, ite_false]
    exact (differentiable_const _).mul h

theorem genProd_eq_zero_iff {Λ : Set ℝ} (hΛ : IsSeparated Λ) (z : ℂ) :
    genProd Λ z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  unfold genProd
  rw [mul_eq_zero, OCS.canonicalProd_eq_zero_iff (isGenusOneData_zeroSet hΛ)]
  unfold zeroSet
  by_cases h0 : (0 : ℝ) ∈ Λ
  · simp only [h0, ite_true]
    constructor
    · rintro (rfl | ⟨y, hy, rfl⟩)
      · exact ⟨0, h0, by simp⟩
      · exact ⟨y, hy.1, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      by_cases hx0 : x = 0
      · left; simp [hx0]
      · right; exact ⟨x, ⟨hx, hx0⟩, rfl⟩
  · simp only [h0, ite_false, one_ne_zero, false_or]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy.1, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, ⟨hx, fun h ↦ h0 (h ▸ hx)⟩, rfl⟩

theorem fstar_genProd {Λ : Set ℝ} (hΛ : IsSeparated Λ) : fstar (genProd Λ) = genProd Λ := by
  have h := isGenusOneData_zeroSet hΛ
  have hZ : ∀ a ∈ zeroSet Λ, conj a ∈ zeroSet Λ := by
    rintro a ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp⟩
  have hc : ∀ a ∈ zeroSet Λ, (fun a : ℂ ↦ a⁻¹) (conj a) = conj ((fun a : ℂ ↦ a⁻¹) a) :=
    fun a _ ↦ (map_inv₀ _ a).symm
  funext z
  unfold fstar genProd
  rw [OCS.canonicalProd_conj h hZ hc z]
  split_ifs <;> simp

theorem genProd_ne_zero_of_im_ne_zero {Λ : Set ℝ} (hΛ : IsSeparated Λ) {z : ℂ} (hz : z.im ≠ 0) :
    genProd Λ z ≠ 0 := by
  intro h
  obtain ⟨x, _, rfl⟩ := (genProd_eq_zero_iff hΛ z).1 h
  simp at hz

end Product

/-! ## 7. The entire functions `W = G M`, `P = W - G`, `Q = W + G` -/

section Entire

/-- `W = G·M`, where `M(z) = (-i/π) ∑ c_λ hk λ z - i p z + i a`, as an entire function. -/
def herglotzEnt (Λ : Set ℝ) (c : ℝ → ℝ) (G : ℂ → ℂ) (p a : ℝ) (z : ℂ) : ℂ :=
  (-I / Real.pi) * entSum Λ c G z - I * p * z * G z + I * a * G z

theorem differentiable_herglotzEnt {Λ : Set ℝ} (hΛ : IsSeparated Λ) {c : ℝ → ℝ}
    (hcs : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2)) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0) (p a : ℝ) :
    Differentiable ℂ (herglotzEnt Λ c G p a) := by
  have h1 := differentiable_entSum hΛ hcs hG hG0
  unfold herglotzEnt
  exact ((h1.const_mul _).sub (((differentiable_const _).mul differentiable_id).mul hG)).add
    (hG.const_mul _)

/-- `W^* = -W`. -/
theorem fstar_herglotzEnt {Λ : Set ℝ} (hΛ : IsSeparated Λ) {c : ℝ → ℝ}
    (hcs : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2)) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0) (hGs : fstar G = G) (p a : ℝ) :
    fstar (herglotzEnt Λ c G p a) = fun z ↦ -herglotzEnt Λ c G p a z := by
  funext z
  have h1 : conj (entSum Λ c G (conj z)) = entSum Λ c G z :=
    congrFun (fstar_entSum hΛ hcs hG hG0 hGs) z
  have h2 : conj (G (conj z)) = G z := congrFun hGs z
  unfold fstar herglotzEnt
  simp only [map_add, map_sub, map_mul, map_div₀, map_neg, Complex.conj_I, Complex.conj_ofReal,
    Complex.conj_conj, h1, h2]
  ring

/-- Herglotz normalisation: for a suitable real `a`, on `ℂ₊`,
`(E + E^*A)/(E - E^*A) = (-i/π) ∑ c_λ hk λ z - i p z + i a`.  (Two holomorphic functions on `ℂ₊`
with the same real part differ by an imaginary constant.) -/
theorem exists_herglotz_const {Λ : Set ℝ} (hΛ : IsSeparated Λ) {E A G : ℂ → ℂ} {p : ℝ}
    (hE : IsStrictHB E) (hA : DifferentiableOn ℂ A {z : ℂ | 0 < z.im})
    (hA1 : ∀ z : ℂ, 0 < z.im → ‖A z‖ ≤ 1)
    (hcs : Summable fun x : Λ ↦ ‖E ((x : ℝ) : ℂ)‖ ^ 2 / (1 + (x : ℝ) ^ 2))
    (hre : ∀ z : ℂ, 0 < z.im →
      (∑' x : Λ, ‖E ((x : ℝ) : ℂ)‖ ^ 2 *
            (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2)))) + p * z.im =
            (hbQuot E A z).re)
    (hG : Differentiable ℂ G) (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0) (hGne : ∀ z : ℂ, 0 < z.im → G z ≠ 0) :
    ∃ a : ℝ, ∀ z : ℂ, 0 < z.im →
      hbQuot E A z = (-I / Real.pi) * herglotzSum Λ (fun x ↦ ‖E (x : ℂ)‖ ^ 2) z
        - I * p * z + I * a := by
  set c : ℝ → ℝ := fun x ↦ ‖E (x : ℂ)‖ ^ 2 with hc
  have hcs' : Summable fun x : Λ ↦ |c x| / (1 + (x : ℝ) ^ 2) := by
    refine hcs.congr fun x ↦ ?_
    simp only [hc]
    rw [abs_of_nonneg (by positivity)]
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hW₀ : Differentiable ℂ (fun z ↦ (-I / Real.pi) * entSum Λ c G z - I * p * z * G z) :=
    ((differentiable_entSum hΛ hcs' hG hG0).const_mul _).sub
      (((differentiable_const _).mul differentiable_id).mul hG)
  have hM₀ : DifferentiableOn ℂ (fun z ↦ (-I / Real.pi) * herglotzSum Λ c z - I * p * z)
      {z : ℂ | 0 < z.im} := by
    refine (hW₀.differentiableOn.div hG.differentiableOn fun z hz ↦ hGne z hz).congr fun z hz ↦ ?_
    have hz' : 0 < z.im := hz
    have := hGne z hz'
    simp only [Pi.div_apply]
    rw [entSum_eq hΛ hcs' hG0 hz'.ne']
    field_simp
  have hD := (differentiableOn_hbQuot hE hA hA1).sub hM₀
  obtain ⟨a, ha⟩ := exists_const_of_re_eq_zero hD (fun z hz ↦ by
    have h1 : ((-I / Real.pi) * herglotzSum Λ c z).re =
        ∑' x : Λ, ‖E ((x : ℝ) : ℂ)‖ ^ 2 *
          (z.im / (Real.pi * (((x : ℝ) - z.re) ^ 2 + z.im ^ 2))) := re_herglotzSum hΛ hcs' hz
    have h2 := hre z hz
    simp only [Pi.sub_apply, Complex.sub_re]
    have h3 : (I * (p : ℂ) * z).re = -(p * z.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [h3, h1]
    linarith)
  refine ⟨a, fun z hz ↦ ?_⟩
  have := ha z hz
  simp only [Pi.sub_apply] at this
  linear_combination this

/-- On `ℂ₊`: `W = G · (E + E^*A)/(E - E^*A)`. -/
theorem herglotzEnt_eq {Λ : Set ℝ} (hΛ : IsSeparated Λ) {E A G : ℂ → ℂ} {p a : ℝ}
    (hcs : Summable fun x : Λ ↦ ‖E ((x : ℝ) : ℂ)‖ ^ 2 / (1 + (x : ℝ) ^ 2))
    (hG0 : ∀ x ∈ Λ, G (x : ℂ) = 0)
    (ha : ∀ z : ℂ, 0 < z.im → hbQuot E A z =
      (-I / Real.pi) * herglotzSum Λ (fun x ↦ ‖E (x : ℂ)‖ ^ 2) z - I * p * z + I * a)
    {z : ℂ} (hz : 0 < z.im) :
    herglotzEnt Λ (fun x ↦ ‖E (x : ℂ)‖ ^ 2) G p a z = G z * hbQuot E A z := by
  have hcs' : Summable fun x : Λ ↦ |(fun x : ℝ ↦ ‖E (x : ℂ)‖ ^ 2) x| / (1 + (x : ℝ) ^ 2) := by
    refine hcs.congr fun x ↦ ?_
    rw [abs_of_nonneg (by positivity)]
  unfold herglotzEnt
  rw [entSum_eq (c := fun x : ℝ ↦ ‖E (x : ℂ)‖ ^ 2) hΛ hcs' hG0 hz.ne', ha z hz]
  ring

/-- Algebra on `ℂ₊`: from `W = G H`, `H = (E + E^*A)/(E - E^*A)`, `P = W - G`, `Q = W + G`:
`P E = Q E^* A` and `Q (E - E^*A) = 2 G E`. -/
theorem PQ_relations {E A G W : ℂ → ℂ} (hE : IsStrictHB E)
    (hA1 : ∀ z : ℂ, 0 < z.im → ‖A z‖ ≤ 1) (hW : ∀ z : ℂ, 0 < z.im → W z = G z * hbQuot E A z)
    {z : ℂ} (hz : 0 < z.im) :
    (W z - G z) * E z = (W z + G z) * (fstar E z * A z) ∧
      (W z + G z) * (E z - fstar E z * A z) = 2 * G z * E z := by
  have hD := denom_ne_zero hE hz (hA1 z hz)
  rw [hW z hz]
  unfold hbQuot
  constructor
  · field_simp
    ring
  · field_simp
    ring

end Entire

/-! ## 8. The function `F` (removable singularities, no meromorphic functions) -/

section StepFunctionF

/-- `F` is obtained from `P/E^*` (equal to `QA/E` on `ℂ₊`): `E F = Q`, `E^*F^* = -P`,
`F^* = -A F` on `ℂ₊`. -/
theorem exists_F {E A P Q : ℂ → ℂ} (hE : IsHB E) (hE0 : ∀ x : ℝ, E (x : ℂ) ≠ 0)
    (hA : DifferentiableOn ℂ A {z : ℂ | 0 < z.im}) (hP : Differentiable ℂ P)
    (hQ : Differentiable ℂ Q) (hPQ : fstar P = fun z ↦ -Q z)
    (hrel : ∀ z : ℂ, 0 < z.im → P z * E z = Q z * (fstar E z * A z)) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ z : ℂ, E z * F z = Q z) ∧
      (∀ z : ℂ, fstar E z * fstar F z = -P z) ∧
      ∀ z : ℂ, 0 < z.im → fstar F z = -(A z * F z) := by
  classical
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hEd : Differentiable ℂ E := hE.1
  have hEne : ∀ z : ℂ, 0 < z.im → E z ≠ 0 := hE.2.1
  have hEsne : ∀ z : ℂ, z.im ≤ 0 → fstar E z ≠ 0 := by
    intro z hz
    unfold fstar
    rw [map_ne_zero]
    have him : 0 ≤ (conj z).im := by simp; linarith
    rcases him.lt_or_eq with h | h
    · exact hEne _ h
    · have : conj z = (((conj z).re : ℝ) : ℂ) :=
        Complex.ext (by simp) (by simpa using h.symm)
      rw [this]; exact hE0 _
  let Φ : ℂ → ℂ := fun z ↦ if 0 < z.im then Q z * A z / E z else P z / fstar E z
  have hΦeq : ∀ z : ℂ, 0 < z.im → fstar E z ≠ 0 → Q z * A z / E z = P z / fstar E z := by
    intro z hz hne
    rw [div_eq_div_iff (hEne z hz) hne]
    linear_combination -(hrel z hz)
  have hΦd : Differentiable ℂ Φ := by
    intro z0
    by_cases h0 : 0 < z0.im
    · have hev : Φ =ᶠ[𝓝 z0] fun z ↦ Q z * A z / E z :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds h0) (fun z (hz : 0 < z.im) ↦ by simp [Φ, hz])
      have hd : DifferentiableAt ℂ (fun z ↦ Q z * A z / E z) z0 :=
        ((hQ z0).mul (hA.differentiableAt (hU.mem_nhds h0))).div (hEd z0) (hEne z0 h0)
      exact hd.congr_of_eventuallyEq hev
    · have hz0 : fstar E z0 ≠ 0 := hEsne z0 (not_lt.1 h0)
      have hV : IsOpen {z : ℂ | fstar E z ≠ 0} :=
        isOpen_ne_fun (Differentiable.fstar hEd).continuous continuous_const
      have hev : Φ =ᶠ[𝓝 z0] fun z ↦ P z / fstar E z := by
        refine Filter.eventuallyEq_of_mem (hV.mem_nhds hz0) (fun z hz ↦ ?_)
        by_cases h : 0 < z.im
        · simp only [Φ, h, ite_true]
          exact hΦeq z h hz
        · simp only [Φ, h, ite_false]
      have hd : DifferentiableAt ℂ (fun z ↦ P z / fstar E z) z0 :=
        (hP z0).div ((Differentiable.fstar hEd) z0) hz0
      exact hd.congr_of_eventuallyEq hev
  have hkey : ∀ z : ℂ, fstar E z * Φ z = P z := by
    intro z
    by_cases h : 0 < z.im
    · have hne := hEne z h
      simp only [Φ, h, ite_true]
      field_simp
      linear_combination -(hrel z h)
    · simp only [Φ, h, ite_false]
      exact mul_div_cancel₀ _ (hEsne z (not_lt.1 h))
  have hFstar : fstar (fstar (fun z ↦ -Φ z)) = fun z ↦ -Φ z := fstar_fstar _
  have hEF : ∀ z : ℂ, E z * fstar (fun z ↦ -Φ z) z = Q z := by
    intro z
    have h1 := congrArg conj (hkey (conj z))
    rw [map_mul] at h1
    have h2 : conj (fstar E (conj z)) = E z := by simp [fstar]
    have h3 : conj (P (conj z)) = -Q z := congrFun hPQ z
    rw [h2, h3] at h1
    show E z * conj (-Φ (conj z)) = Q z
    rw [map_neg]
    linear_combination -h1
  refine ⟨fstar (fun z ↦ -Φ z), Differentiable.fstar hΦd.neg, hEF, ?_, ?_⟩
  · intro z
    rw [congrFun hFstar z]
    linear_combination -(hkey z)
  · intro z hz
    rw [congrFun hFstar z]
    have hFz : fstar (fun z ↦ -Φ z) z = Q z / E z := by
      rw [eq_div_iff (hEne z hz)]
      linear_combination hEF z
    rw [hFz]
    simp only [Φ, hz, ite_true]
    ring

/-- `F ∈ \overline{HB}`. -/
theorem isHB_F {E A F G Q : ℂ → ℂ} (hE : IsStrictHB E) (hF : Differentiable ℂ F)
    (hA1 : ∀ z : ℂ, 0 < z.im → ‖A z‖ ≤ 1) (hEF : ∀ z : ℂ, E z * F z = Q z)
    (hFA : ∀ z : ℂ, 0 < z.im → fstar F z = -(A z * F z))
    (hQ : ∀ z : ℂ, 0 < z.im → Q z * (E z - fstar E z * A z) = 2 * G z * E z)
    (hG : ∀ z : ℂ, 0 < z.im → G z ≠ 0) : IsHB F := by
  refine ⟨hF, fun z hz h0 ↦ ?_, fun z hz ↦ ?_⟩
  · have hEz : E z ≠ 0 := hE.1.2.1 z hz
    have h1 := hQ z hz
    rw [← hEF z, h0] at h1
    have h2 : E z * (2 * G z) = 0 := by linear_combination -h1
    rcases mul_eq_zero.1 h2 with h | h
    · exact hEz h
    · exact hG z hz (by linear_combination h / 2)
  · rw [← norm_fstar, hFA z hz, norm_neg, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hA1 z hz)

end StepFunctionF

/-! ## 9. Theorem 1, necessity -/

/-- **Theorem 1** (p. 795), necessity: a separated sampling sequence is the zero set of
`EF + E^*F^*` with `E, F ∈ \overline{HB}` and `H(E) = PW`. -/
theorem theorem1_necessity (hPW : PaleyWienerThm) (hC : TheoremC) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  -- Steps 1-2: Theorem C
  obtain ⟨E, hEHB, hEPW, hmem, hnorm⟩ := exists_E hPW hC hs
  have hEs : IsStrictHB E := HEEqPW.isStrictHB hEHB hEPW
  have hE0 : ∀ x : ℝ, E (x : ℂ) ≠ 0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  -- Step 3: Theorem F
  obtain ⟨A, hAd, hA1, p, hp, hcs, hpo⟩ :=
    exists_herglotz_data hF Λ hEs hE0 (fun f hf ↦ hnorm f ((hmem f).1 hf))
  have hcs' : Summable fun x : Λ ↦ |‖E ((x : ℝ) : ℂ)‖ ^ 2| / (1 + (x : ℝ) ^ 2) := by
    refine hcs.congr fun x ↦ ?_
    rw [abs_of_nonneg (by positivity)]
  -- Step 5: the product G
  have hGd : Differentiable ℂ (genProd Λ) := differentiable_genProd hΛ
  have hGs : fstar (genProd Λ) = genProd Λ := fstar_genProd hΛ
  have hG0 : ∀ x ∈ Λ, genProd Λ (x : ℂ) = 0 := fun x hx ↦
    (genProd_eq_zero_iff hΛ _).2 ⟨x, hx, rfl⟩
  have hGne : ∀ z : ℂ, 0 < z.im → genProd Λ z ≠ 0 := fun z hz ↦
    genProd_ne_zero_of_im_ne_zero hΛ hz.ne'
  have hzero := genProd_eq_zero_iff hΛ
  generalize genProd Λ = G at hGd hGs hG0 hGne hzero
  -- Step 4: Herglotz normalisation
  obtain ⟨a, ha⟩ := exists_herglotz_const hΛ hEs hAd hA1 hcs (fun z hz ↦ (hpo z hz).2) hGd hG0
    hGne
  have hWd := differentiable_herglotzEnt (c := fun x ↦ ‖E (x : ℂ)‖ ^ 2) hΛ hcs' hGd hG0 p a
  have hWs := fstar_herglotzEnt (c := fun x ↦ ‖E (x : ℂ)‖ ^ 2) hΛ hcs' hGd hG0 hGs p a
  have hWeq : ∀ z : ℂ, 0 < z.im → herglotzEnt Λ (fun x ↦ ‖E (x : ℂ)‖ ^ 2) G p a z =
      G z * hbQuot E A z := fun z hz ↦ herglotzEnt_eq hΛ hcs hG0 ha hz
  suffices key : ∀ W : ℂ → ℂ, Differentiable ℂ W → fstar W = (fun z ↦ -W z) →
      (∀ z : ℂ, 0 < z.im → W z = G z * hbQuot E A z) →
      ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
        ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) from
    key _ hWd hWs hWeq
  intro W hWd hWs hWeq
  have hPd : Differentiable ℂ (fun z ↦ W z - G z) := hWd.sub hGd
  have hQd : Differentiable ℂ (fun z ↦ W z + G z) := hWd.add hGd
  have hPQ : fstar (fun z ↦ W z - G z) = fun z ↦ -(W z + G z) := by
    funext z
    have h1 := congrFun hWs z
    have h2 := congrFun hGs z
    simp only [fstar] at h1 h2 ⊢
    rw [map_sub, h1, h2]
    ring
  have hrel : ∀ z : ℂ, 0 < z.im → (W z - G z) * E z = (W z + G z) * (fstar E z * A z) :=
    fun z hz ↦ (PQ_relations hEs hA1 hWeq hz).1
  obtain ⟨F, hFd, hEF, hEFs, hFA⟩ := exists_F hEHB hE0 hAd hPd hQd hPQ hrel
  refine ⟨E, F, hEHB, isHB_F hEs hFd hA1 hEF hFA
    (fun z hz ↦ (PQ_relations hEs hA1 hWeq hz).2) hGne, hEPW, fun z ↦ ?_⟩
  have h2G : E z * F z + fstar E z * fstar F z = 2 * G z := by
    rw [hEF, hEFs]; ring
  rw [h2G, mul_eq_zero, hzero]
  simp


end FF
