import FourierFrames.Cited.DeBrangesDE.Orthogonal
import FourierFrames.Cited.DeBrangesDE.EntireHerglotz

/-!
# P3 — Theorem E, part 2: completeness, the norm identity, interpolation

See `blueprint/P3_DeBrangesDE.md`, §7–§8.  Key proposition (`eq_zero_of_level_zero`): if
`S_α ∉ H(E)` and `f ∈ H(E)` vanishes on `Γ`, then `f = 0`.  Proof: the entire Pick function
`h = D/S` is linear (`entire_pick_linear`), `h = p z + q`; `p > 0` would put `S` in `H(E)` (the
defect kernel `Q_i` is an element of `H(E)` and equals `(p/π) conj S(i) · S`); so `p = 0`, the
defect kernel vanishes on the diagonal, `‖Q_w‖ = 0`, `K_w` is the norm limit of its orthogonal
expansion, and `f(w) = ⟨f, K_w⟩ = 0`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {E : ℂ → ℂ} {φ : ℝ → ℝ} {α : ℝ}

/-! ## 7.1 Exhaustion and convergence of partial sums -/

/-- `Γ` is exhausted by the finite sets `Γ ∩ [-n, n]`. -/
theorem exists_exhaustion (D : DBData E φ) (α : ℝ) :
    ∃ F : ℕ → Finset (phaseLevel φ α), Monotone F ∧ ∀ γ : phaseLevel φ α, ∃ n, γ ∈ F n := by
  have hfin : ∀ n : ℕ, {γ : phaseLevel φ α | |(γ : ℝ)| < n + 1}.Finite := fun n ↦
    finite_level_abs_lt D α (n + 1)
  refine ⟨fun n ↦ (hfin n).toFinset, fun m n hmn γ hγ ↦ ?_, fun γ ↦ ⟨⌈|(γ : ℝ)|⌉₊, ?_⟩⟩
  · rw [Set.Finite.mem_toFinset] at hγ ⊢
    have h1 : |(γ : ℝ)| < m + 1 := hγ
    have h2 : (m : ℝ) ≤ n := by exact_mod_cast hmn
    show |(γ : ℝ)| < n + 1
    linarith
  · rw [Set.Finite.mem_toFinset]
    show |(γ : ℝ)| < ⌈|(γ : ℝ)|⌉₊ + 1
    linarith [Nat.le_ceil |(γ : ℝ)|]

/-- Partial sums along an exhaustion converge to the `tsum`. -/
theorem tendsto_sum_exhaustion {ι M : Type*} [AddCommMonoid M] [TopologicalSpace M] [T2Space M]
    {f : ι → M} (hf : Summable f) {F : ℕ → Finset ι} (hF : Monotone F) (hex : ∀ i, ∃ n, i ∈ F n) :
    Tendsto (fun n ↦ ∑ i ∈ F n, f i) atTop (𝓝 (∑' i, f i)) :=
  hf.hasSum.comp (Filter.tendsto_atTop_finset_of_monotone hF hex)

/-- `‖f - g‖_E = ‖g - f‖_E`. -/
theorem heNormSq_sub_comm (f g : ℂ → ℂ) :
    heNormSq E (fun z ↦ f z - g z) = heNormSq E (fun z ↦ g z - f z) := by
  unfold heNormSq
  refine lintegral_congr fun t ↦ ?_
  show ‖(f t - g t) / E t‖ₑ ^ 2 = ‖(g t - f t) / E t‖ₑ ^ 2
  rw [← neg_sub, neg_div, enorm_neg]

/-- For `F n ⊆ F m`: `‖s_{F m} - s_{F n}‖² = Σ_{F m \ F n} wt |a|²`. -/
theorem heNormSq_partialSum_sub (D : DBData E φ) (a : ℝ → ℂ) {F G : Finset (phaseLevel φ α)}
    (hFG : F ⊆ G) :
    (heNormSq E (fun z ↦ partialSum E φ α a G z - partialSum E φ α a F z)).toReal =
      ∑ γ ∈ G \ F, wt E γ * ‖a γ‖ ^ 2 := by
  have h : (fun z ↦ partialSum E φ α a G z - partialSum E φ α a F z) =
      partialSum E φ α a (G \ F) := by
    funext z
    unfold partialSum
    rw [← Finset.sum_sdiff hFG]
    ring
  rw [h, heNormSq_partialSum D]

/-- If `Σ wt |a|² < ∞` the partial sums along an exhaustion are Cauchy in `H(E)`
(Pythagoras `heNormSq_partialSum` on the difference `s_{F m} - s_{F n} = s_{F m \ F n}`). -/
theorem cauchy_partialSum (D : DBData E φ) {a : ℝ → ℂ}
    (ha : Summable fun γ : phaseLevel φ α ↦ wt E γ * ‖a γ‖ ^ 2)
    {F : ℕ → Finset (phaseLevel φ α)} (hF : Monotone F) (hex : ∀ γ, ∃ n, γ ∈ F n) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      heNormSq E (fun z ↦ partialSum E φ α a (F m) z - partialSum E φ α a (F n) z) ≤
        ENNReal.ofReal ε := by
  set u : phaseLevel φ α → ℝ := fun γ ↦ wt E γ * ‖a γ‖ ^ 2 with hu
  have hu0 : ∀ γ, 0 ≤ u γ := fun γ ↦ mul_nonneg (wt_pos D γ).le (by positivity)
  have hlim := tendsto_sum_exhaustion ha hF hex
  -- the main estimate, for `n ≤ m`
  have hle : ∀ m n, n ≤ m →
      heNormSq E (fun z ↦ partialSum E φ α a (F m) z - partialSum E φ α a (F n) z) ≤
        ENNReal.ofReal (∑' γ, u γ - ∑ γ ∈ F n, u γ) := by
    intro m n hnm
    have hfin : heNormSq E (fun z ↦ partialSum E φ α a (F m) z - partialSum E φ α a (F n) z)
        ≠ ⊤ :=
      (MemHE.heNormSq_lt_top D.strict.1.1 D.noZero
        ((memHE_partialSum D a (F m)).sub (memHE_partialSum D a (F n)))).ne
    rw [← ENNReal.ofReal_toReal hfin, heNormSq_partialSum_sub D a (hF hnm)]
    apply ENNReal.ofReal_le_ofReal
    have h1 := Finset.sum_sdiff (f := u) (hF hnm)
    have h2 := ha.sum_le_tsum (F m) (fun γ _ ↦ hu0 γ)
    simp only [hu] at h1 h2 ⊢
    linarith
  intro ε hε
  have hev : ∀ᶠ n in atTop, ∑' γ, u γ - ∑ γ ∈ F n, u γ < ε := by
    have h1 : Tendsto (fun n ↦ ∑' γ, u γ - ∑ γ ∈ F n, u γ) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := ∑' γ, u γ)).sub hlim
      rwa [sub_self] at this
    exact (tendsto_order.1 h1).2 ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  rcases le_total n m with hnm | hmn
  · exact (hle m n hnm).trans (ENNReal.ofReal_le_ofReal (hN n hn).le)
  · rw [heNormSq_sub_comm]
    exact (hle n m hmn).trans (ENNReal.ofReal_le_ofReal (hN m hm).le)

/-- AM–GM summability: `Σ |u v| w ≤ (Σ w|u|² + Σ w|v|²)/2`. -/
theorem summable_mul_wt_mul {ι : Type*} {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {u v : ι → ℂ}
    (hu : Summable fun i ↦ w i * ‖u i‖ ^ 2) (hv : Summable fun i ↦ w i * ‖v i‖ ^ 2) :
    Summable fun i ↦ u i * (w i : ℂ) * v i := by
  refine Summable.of_norm_bounded ((hu.add hv).div_const 2) fun i ↦ ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
  nlinarith [mul_nonneg (hw i) (sq_nonneg (‖u i‖ - ‖v i‖))]

/-- **Series limit** (completeness of `H(E)` + orthogonality): for `Σ wt|a|² < ∞` there is
`g ∈ H(E)` with `g(z) = Σ_γ a_γ wt(γ) K(γ, z)` for every `z`, `g(γ) = a_γ` on `Γ`,
`‖g‖² = Σ wt |a_γ|²`, and `⟨f, g⟩ = Σ conj(a_γ) wt(γ) f(γ)` for `f ∈ H(E)`. -/
theorem exists_series_limit (D : DBData E φ) {a : ℝ → ℂ}
    (ha : Summable fun γ : phaseLevel φ α ↦ wt E γ * ‖a γ‖ ^ 2) :
    ∃ g : ℂ → ℂ, MemHE E g ∧
      (∀ z : ℂ, HasSum (fun γ : phaseLevel φ α ↦
        a γ * ((wt E γ : ℝ) : ℂ) * deBrangesKernel E (γ : ℂ) z) (g z)) ∧
      (∀ γ ∈ phaseLevel φ α, g γ = a γ) ∧
      (heNormSq E g).toReal = ∑' γ : phaseLevel φ α, wt E γ * ‖a γ‖ ^ 2 ∧
      ∀ f : ℂ → ℂ, MemHE E f →
        HasSum (fun γ : phaseLevel φ α ↦ conj (a γ) * (wt E γ : ℂ) * f γ) (heInner E f g) := by
  have hE := D.strict.1
  have h0 := D.noZero
  have hw0 : ∀ γ : phaseLevel φ α, 0 ≤ wt E γ := fun γ ↦ (wt_pos D γ).le
  obtain ⟨F, hF, hex⟩ := exists_exhaustion D α
  set s : ℕ → ℂ → ℂ := fun n ↦ partialSum E φ α a (F n) with hs_def
  have hs : ∀ n, MemHE E (s n) := fun n ↦ memHE_partialSum D a (F n)
  obtain ⟨g, hg, hpt, hnorm⟩ := memHE_of_cauchy hE h0 s hs (cauchy_partialSum D ha hF hex)
  -- the coefficient sums `⟨f, s_n⟩`
  have hinner : ∀ f : ℂ → ℂ, MemHE E f →
      HasSum (fun γ : phaseLevel φ α ↦ conj (a γ) * (wt E γ : ℂ) * f γ) (heInner E f g) := by
    intro f hf
    have hsum : Summable (fun γ : phaseLevel φ α ↦ conj (a γ) * (wt E γ : ℂ) * f γ) :=
      summable_mul_wt_mul hw0 (by simpa using ha) (bessel D hf).1
    have h1 := tendsto_sum_exhaustion hsum hF hex
    have h2 := tendsto_heInner_right hE h0 hf hg hs hnorm
    have h3 : (fun n ↦ heInner E f (s n)) =
        fun n ↦ ∑ γ ∈ F n, conj (a γ) * (wt E γ : ℂ) * f γ := by
      funext n; exact heInner_partialSum D hf a (F n)
    rw [h3] at h2
    rw [← tendsto_nhds_unique h1 h2]
    exact hsum.hasSum
  refine ⟨g, hg, ?_, ?_, ?_, hinner⟩
  · -- pointwise expansion
    intro z
    have hK : Summable (fun γ : phaseLevel φ α ↦ wt E γ * ‖deBrangesKernel E (γ : ℂ) z‖ ^ 2) := by
      have := (summable_cLev_dslope_sq (α := α) D z).1
      refine this.congr fun γ ↦ ?_
      rw [wt_mul_norm_kernel_level_sq D γ.2]
    have hsum := summable_mul_wt_mul hw0 ha hK
    have h1 := tendsto_sum_exhaustion hsum hF hex
    have h2 := hpt z
    rw [← tendsto_nhds_unique h1 h2]
    exact hsum.hasSum
  · -- values on `Γ`
    intro γ hγ
    obtain ⟨n₀, hn₀⟩ := hex ⟨γ, hγ⟩
    have h1 : ∀ᶠ n in atTop, s n γ = a γ := by
      filter_upwards [eventually_ge_atTop n₀] with n hn
      exact partialSum_level D a (hF hn hn₀)
    exact tendsto_nhds_unique (hpt γ) (tendsto_const_nhds.congr' (h1.mono fun n h ↦ h.symm))
  · -- norm
    have h1 := hinner g hg
    have hval : ∀ γ : phaseLevel φ α, conj (a γ) * (wt E γ : ℂ) * g γ =
        ((wt E γ * ‖a γ‖ ^ 2 : ℝ) : ℂ) := by
      intro γ
      obtain ⟨n₀, hn₀⟩ := hex γ
      have hgγ : g γ = a γ := by
        have h2 : ∀ᶠ n in atTop, s n γ = a γ := by
          filter_upwards [eventually_ge_atTop n₀] with n hn
          exact partialSum_level D a (hF hn hn₀)
        exact tendsto_nhds_unique (hpt γ) (tendsto_const_nhds.congr' (h2.mono fun n h ↦ h.symm))
      rw [hgγ, conj_mul_wt_mul]
    simp_rw [hval] at h1
    rw [heInner_self hE hg] at h1
    have h2 := h1.tsum_eq
    rw [← Complex.ofReal_tsum] at h2
    exact_mod_cast h2.symm

/-! ## 7.2 The defect kernel as an element of `H(E)`; `h` is linear; `S ∈ H(E)` if `p > 0` -/

/-- The series part `g_w` of the defect kernel: `Q_w = K_w - g_w` with `g_w ∈ H(E)` the series
limit for `a_γ = K(w, γ)`. -/
theorem exists_defect_decomp (D : DBData E φ) (w : ℂ) :
    ∃ g : ℂ → ℂ, MemHE E g ∧
      (∀ z, defectKer E φ α w z = deBrangesKernel E w z - g z) ∧
      (heNormSq E g).toReal = ∑' γ : phaseLevel φ α, wt E γ * ‖deBrangesKernel E w γ‖ ^ 2 ∧
      ∀ f : ℂ → ℂ, MemHE E f →
        HasSum (fun γ : phaseLevel φ α ↦ conj (deBrangesKernel E w γ) * (wt E γ : ℂ) * f γ)
          (heInner E f g) := by
  have hb := bessel (α := α) D (memHE_deBrangesKernel D.strict.1 D.noZero w)
  obtain ⟨g, hg, hpt, -, hn, hinner⟩ :=
    exists_series_limit (α := α) D (a := fun t ↦ deBrangesKernel E w t) hb.1
  refine ⟨g, hg, fun z ↦ ?_, hn, hinner⟩
  unfold defectKer
  rw [← (hpt z).tsum_eq]
  congr 1
  exact tsum_congr fun γ ↦ by ring

/-- The defect kernel is an element of `H(E)`: `Q_w = K_w - g_w` with `g_w` the series limit for
`a_γ = K(w, γ)` (`Σ wt |K(w,γ)|² < ∞` by Bessel), and `‖Q_w‖² = Q(w, w)`. -/
theorem memHE_defectKer (D : DBData E φ) (w : ℂ) :
    MemHE E (fun z ↦ defectKer E φ α w z) ∧
      (heNormSq E (fun z ↦ defectKer E φ α w z)).toReal = (defectKer E φ α w w).re := by
  have hE := D.strict.1
  have h0 := D.noZero
  obtain ⟨g, hg, hQ, hn, hinner⟩ := exists_defect_decomp (α := α) D w
  have hK := memHE_deBrangesKernel hE h0 w
  have hfun : (fun z ↦ defectKer E φ α w z) = fun z ↦ deBrangesKernel E w z - g z :=
    funext hQ
  rw [hfun]
  refine ⟨hK.sub hg, ?_⟩
  rw [heNormSq_sub hE h0 hK hg, heNormSq_kernel hE h0, hn, defectKer_diag w]
  have h1 := hinner _ hK
  have hval : ∀ γ : phaseLevel φ α,
      conj (deBrangesKernel E w γ) * (wt E γ : ℂ) * deBrangesKernel E w γ =
        ((wt E γ * ‖deBrangesKernel E w γ‖ ^ 2 : ℝ) : ℂ) := fun γ ↦ by
    rw [conj_mul_wt_mul]
  simp_rw [hval] at h1
  rw [← h1.tsum_eq, ← Complex.ofReal_tsum, Complex.ofReal_re]
  ring

/-- `⟨f, Q_w⟩ = f(w)` for every `f ∈ H(E)` vanishing on `Γ` (`⟨f, g_w⟩ = Σ ... f(γ) = 0`). -/
theorem heInner_defectKer_of_level_zero (D : DBData E φ) {f : ℂ → ℂ} (hf : MemHE E f)
    (hz : ∀ γ ∈ phaseLevel φ α, f γ = 0) (w : ℂ) :
    heInner E f (fun z ↦ defectKer E φ α w z) = f w := by
  have hE := D.strict.1
  have h0 := D.noZero
  obtain ⟨g, hg, hQ, -, hinner⟩ := exists_defect_decomp (α := α) D w
  have hK := memHE_deBrangesKernel hE h0 w
  have hfun : (fun z ↦ defectKer E φ α w z) = fun z ↦ deBrangesKernel E w z - g z :=
    funext hQ
  rw [hfun, heInner_sub_right hE h0 hf hK hg, heInner_kernel hE h0 hf]
  have h1 := hinner f hf
  have hzero : (fun γ : phaseLevel φ α ↦
      conj (deBrangesKernel E w γ) * (wt E γ : ℂ) * f γ) = fun _ ↦ 0 := by
    funext γ
    rw [hz γ γ.2, mul_zero]
  rw [hzero] at h1
  rw [h1.unique hasSum_zero, sub_zero]

/-- `h` is `p z + q` with `p ≥ 0` (apply `entire_pick_linear` to `h` of `exists_hFun`, using
`im_hFun_nonneg`). -/
theorem hFun_linear (D : DBData E φ) {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) (hreal : ∀ z, h (conj z) = conj (h z)) :
    ∃ p q : ℝ, 0 ≤ p ∧ ∀ z, h z = p * z + q :=
  entire_pick_linear hd hreal fun _ hz ↦ im_hFun_nonneg D hh hz

/-- For linear `h = p z + q`: `Q(w, z) = (p/π) S(z) conj S(w)` for `z ≠ w̄`
(divide `defectKer_mul` by `π (z - w̄)`). -/
theorem defectKer_eq_of_linear (D : DBData E φ) {h : ℂ → ℂ}
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) {p q : ℝ} (hlin : ∀ z, h z = p * z + q)
    {w z : ℂ} (hz : z ≠ conj w) :
    defectKer E φ α w z = (p / Real.pi : ℝ) * sFun E α z * conj (sFun E α w) := by
  have h1 := defectKer_mul D hh w z
  rw [hlin z, hlin w, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal] at h1
  have hzw : z - conj w ≠ 0 := sub_ne_zero.mpr hz
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2 : defectKer E φ α w z * (Real.pi * (z - conj w)) =
      ((p / Real.pi : ℝ) * sFun E α z * conj (sFun E α w)) * (Real.pi * (z - conj w)) := by
    rw [h1]
    push_cast
    field_simp
    ring
  exact mul_right_cancel₀ (mul_ne_zero hπ hzw) h2

/-- If `p > 0`, then `S ∈ H(E)`: `S = (π / (p conj S(i))) Q_i` off `z = -i`, hence everywhere by
continuity, and `Q_i ∈ H(E)`. -/
theorem memHE_sFun_of_pos (D : DBData E φ) {h : ℂ → ℂ}
    (hh : ∀ z, dFun E φ α z = h z * sFun E α z) {p q : ℝ} (hp : 0 < p)
    (hlin : ∀ z, h z = p * z + q) : MemHE E (sFun E α) := by
  have hQ := (memHE_defectKer (α := α) D I).1
  set κ : ℂ := ((p / Real.pi : ℝ) : ℂ) * conj (sFun E α I) with hκ
  have hκ0 : κ ≠ 0 := by
    refine mul_ne_zero ?_ ((map_ne_zero _).mpr (sFun_ne_zero D (by simp)))
    exact Complex.ofReal_ne_zero.mpr (div_pos hp Real.pi_pos).ne'
  have heq : (fun z ↦ defectKer E φ α I z) = fun z ↦ κ * sFun E α z := by
    refine Continuous.ext_on (dense_compl_singleton (conj I)) hQ.1.continuous
      ((differentiable_sFun D.strict.1.1 α).continuous.const_smul κ) fun z hz ↦ ?_
    rw [defectKer_eq_of_linear D hh hlin hz, hκ]
    ring
  rw [heq] at hQ
  exact MemHE.of_const_mul hκ0 hQ

/-! ## 7.3 The key proposition and the norm identity -/

/-- **Key proposition**: if `S_α ∉ H(E)`, no nonzero `f ∈ H(E)` vanishes on `Γ`. -/
theorem eq_zero_of_level_zero (D : DBData E φ)
    (hα : ¬ MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z))
    {f : ℂ → ℂ} (hf : MemHE E f) (hz : ∀ γ ∈ phaseLevel φ α, f γ = 0) : ∀ z, f z = 0 := by
  have hE := D.strict.1
  have h0 := D.noZero
  obtain ⟨h, hd, hh, hreal⟩ := exists_hFun D α
  obtain ⟨p, q, hp, hlin⟩ := hFun_linear D hd hh hreal
  have hp0 : p = 0 := by
    rcases hp.lt_or_eq with hpos | heq
    · exfalso
      apply hα
      rw [sAlpha_eq]
      exact (memHE_sFun_of_pos D hh hpos hlin).const_mul _
    · exact heq.symm
  have hnonreal : ∀ w : ℂ, w.im ≠ 0 → f w = 0 := by
    intro w hw
    have hne : w ≠ conj w := fun h ↦ hw (by
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith)
    have hQ : defectKer E φ α w w = 0 := by
      rw [defectKer_eq_of_linear D hh hlin hne, hp0]
      simp
    obtain ⟨hQm, hQn⟩ := memHE_defectKer (α := α) D w
    rw [hQ, Complex.zero_re] at hQn
    have h1 := norm_heInner_sq_le hE h0 hf hQm
    rw [heInner_defectKer_of_level_zero D hf hz w, hQn, mul_zero] at h1
    have h2 : ‖f w‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
    simpa using h2
  intro z
  by_cases hzi : z.im = 0
  · have hw : Tendsto (fun n : ℕ ↦ z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 z) := by
      have h1 : Tendsto (fun n : ℕ ↦ ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).ofReal
        rwa [Complex.ofReal_zero] at this
      simpa using tendsto_const_nhds.add (h1.mul_const I)
    have hlim := (hf.1.continuous.tendsto z).comp hw
    have hzero : (f ∘ fun n : ℕ ↦ z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) = fun _ ↦ 0 := by
      funext n
      apply hnonreal
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, hzi]
      positivity
    rw [hzero] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  · exact hnonreal z hzi

/-- Norm identity (real form): `‖f‖²_E = Σ_γ wt(γ) |f(γ)|²`. -/
theorem heNormSq_eq_tsum (D : DBData E φ)
    (hα : ¬ MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z))
    {f : ℂ → ℂ} (hf : MemHE E f) :
    Summable (fun γ : phaseLevel φ α ↦ wt E γ * ‖f γ‖ ^ 2) ∧
      (heNormSq E f).toReal = ∑' γ : phaseLevel φ α, wt E γ * ‖f γ‖ ^ 2 := by
  have hb := bessel (α := α) D hf
  obtain ⟨g, hg, -, hgl, hgn, -⟩ := exists_series_limit (α := α) D (a := fun t ↦ f t) hb.1
  have hfg : ∀ z, f z - g z = 0 :=
    eq_zero_of_level_zero D hα (hf.sub hg) fun γ hγ ↦ by rw [hgl γ hγ, sub_self]
  have hgf : g = f := funext fun z ↦ (sub_eq_zero.mp (hfg z)).symm
  rw [hgf] at hgn
  exact ⟨hb.1, hgn⟩

/-- `orthWeight(γ) |a(γ)|²` as `ofReal (wt(γ) |a(γ)|²)`. -/
theorem orthWeight_mul_enorm_sq (D : DBData E φ) (x : ℝ) (c : ℂ) :
    orthWeight E x * ‖c‖ₑ ^ 2 = ENNReal.ofReal (wt E x * ‖c‖ ^ 2) := by
  rw [orthWeight_eq, ENNReal.ofReal_mul (wt_pos D x).le, enorm_sq_eq_ofReal]

/-- **Theorem E, part 1** in the form of `TheoremE`. -/
theorem theoremE_norm (D : DBData E φ)
    (hα : ¬ MemHE E (fun z ↦ Complex.exp (I * α) * E z - Complex.exp (-(I * α)) * fstar E z))
    {f : ℂ → ℂ} (hf : MemHE E f) :
    heNormSq E f = ∑' γ : phaseLevel φ α, orthWeight E γ * ‖f γ‖ₑ ^ 2 := by
  obtain ⟨hs, heq⟩ := heNormSq_eq_tsum D hα hf
  have hfin := MemHE.heNormSq_lt_top D.strict.1.1 D.noZero hf
  rw [← ENNReal.ofReal_toReal hfin.ne, heq,
    ENNReal.ofReal_tsum_of_nonneg
      (fun γ : phaseLevel φ α ↦ mul_nonneg (wt_pos D γ).le (by positivity)) hs]
  exact tsum_congr fun γ ↦ (orthWeight_mul_enorm_sq D γ (f γ)).symm

/-- **Theorem E, part 2** (interpolation; needs neither the key proposition nor `S_α ∉ H(E)`). -/
theorem theoremE_interp (D : DBData E φ) (a : ℝ → ℂ)
    (ha : ∑' γ : phaseLevel φ α, orthWeight E γ * ‖a γ‖ₑ ^ 2 < ∞) :
    ∃ f : ℂ → ℂ, MemHE E f ∧ ∀ γ ∈ phaseLevel φ α, f γ = a γ := by
  simp_rw [orthWeight_mul_enorm_sq D] at ha
  have hs : Summable (fun γ : phaseLevel φ α ↦ wt E γ * ‖a γ‖ ^ 2) := by
    have := ENNReal.summable_toReal ha.ne
    refine this.congr fun γ ↦ ?_
    rw [ENNReal.toReal_ofReal (mul_nonneg (wt_pos D γ).le (by positivity))]
  obtain ⟨g, hg, -, hgl, -⟩ := exists_series_limit D hs
  exact ⟨g, hg, hgl⟩

end FF
