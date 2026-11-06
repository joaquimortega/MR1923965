import FourierFrames.Defs

/-!
# M02 — `f^*`, the Hermite–Biehler class

See `blueprint/M02_HB.md`, §2–§3.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Algebra of `f^*` -/

@[simp] theorem fstar_apply (f : ℂ → ℂ) (z : ℂ) : fstar f z = conj (f (conj z)) := rfl

@[simp] theorem fstar_fstar (f : ℂ → ℂ) : fstar (fstar f) = f := by
  funext z; simp [fstar]

theorem fstar_mul (f g : ℂ → ℂ) :
    fstar (fun z ↦ f z * g z) = fun z ↦ fstar f z * fstar g z := by
  funext z; simp [fstar]

theorem fstar_add (f g : ℂ → ℂ) :
    fstar (fun z ↦ f z + g z) = fun z ↦ fstar f z + fstar g z := by
  funext z; simp [fstar]

theorem fstar_sub (f g : ℂ → ℂ) :
    fstar (fun z ↦ f z - g z) = fun z ↦ fstar f z - fstar g z := by
  funext z; simp [fstar]

theorem fstar_const_mul (c : ℂ) (f : ℂ → ℂ) :
    fstar (fun z ↦ c * f z) = fun z ↦ conj c * fstar f z := by
  funext z; simp [fstar]

theorem fstar_div (f g : ℂ → ℂ) :
    fstar (fun z ↦ f z / g z) = fun z ↦ fstar f z / fstar g z := by
  funext z; simp [fstar]

/-- `f^*(x) = conj (f x)` for real `x`. -/
theorem fstar_ofReal (f : ℂ → ℂ) (x : ℝ) : fstar f (x : ℂ) = conj (f (x : ℂ)) := by
  simp [fstar]

theorem norm_fstar (f : ℂ → ℂ) (z : ℂ) : ‖fstar f z‖ = ‖f (conj z)‖ := by
  simp [fstar]

theorem Differentiable.fstar {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (FF.fstar f) := by
  intro z
  have h := (hf (conj z)).conj_conj
  rw [Complex.conj_conj] at h
  exact h

/-- `(f^*)'(z) = conj (f'(z̄))`. -/
theorem deriv_fstar (f : ℂ → ℂ) (z : ℂ) :
    deriv (fstar f) z = conj (deriv f (conj z)) := by
  have h := congrFun (deriv_conj_conj (𝕜 := ℂ) (f := f)) z
  exact h

/-- For real `x`: `(f^*)'(x) = conj (f'(x))`. -/
theorem deriv_fstar_ofReal (f : ℂ → ℂ) (x : ℝ) :
    deriv (fstar f) (x : ℂ) = conj (deriv f (x : ℂ)) := by
  simp [deriv_fstar]

/-! ## The class `\overline{HB}` -/

theorem isHB_one : IsHB (fun _ : ℂ ↦ (1 : ℂ)) := by
  refine ⟨differentiable_const _, fun _ _ ↦ one_ne_zero, fun _ _ ↦ le_rfl⟩

theorem IsHB.mul {E F : ℂ → ℂ} (hE : IsHB E) (hF : IsHB F) : IsHB (fun z ↦ E z * F z) := by
  obtain ⟨hEd, hE0, hE1⟩ := hE
  obtain ⟨hFd, hF0, hF1⟩ := hF
  refine ⟨hEd.mul hFd, fun z hz ↦ mul_ne_zero (hE0 z hz) (hF0 z hz), fun z hz ↦ ?_⟩
  simp only [norm_mul]
  exact mul_le_mul (hE1 z hz) (hF1 z hz) (norm_nonneg _) (norm_nonneg _)

/-- The zeros of `E ∈ \overline{HB}` lie in `Im z ≤ 0`, and `|E^*(z)| ≤ |E(z)|` on `Im z > 0`. -/
theorem IsHB.norm_fstar_le {E : ℂ → ℂ} (hE : IsHB E) {z : ℂ} (hz : 0 < z.im) :
    ‖fstar E z‖ ≤ ‖E z‖ := by
  rw [norm_fstar]; exact hE.2.2 z hz

/-- **Dichotomy** for `E ∈ \overline{HB}`: either `|E(z̄)| < |E(z)|` on `Im z > 0` (`E` strict) or
`E^* = c E` with `|c| = 1`.  (Maximum modulus for `E^*/E`, then the identity theorem.) -/
theorem IsHB.isStrictHB_or_fstar_eq {E : ℂ → ℂ} (hE : IsHB E) :
    IsStrictHB E ∨ ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z : ℂ, fstar E z = c * E z := by
  by_cases h : ∀ z : ℂ, 0 < z.im → ‖E (conj z)‖ < ‖E z‖
  · exact Or.inl ⟨hE, h⟩
  right
  push Not at h
  obtain ⟨z1, hz1, hle⟩ := h
  have hEz1 : E z1 ≠ 0 := hE.2.1 z1 hz1
  have heq : ‖E (conj z1)‖ = ‖E z1‖ := le_antisymm (hE.2.2 z1 hz1) hle
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hfd : Differentiable ℂ (fstar E) := Differentiable.fstar hE.1
  have hGd : DifferentiableOn ℂ (fun z ↦ fstar E z / E z) U := fun z hz ↦
    ((hfd z).div (hE.1 z) (hE.2.1 z hz)).differentiableWithinAt
  have hmax : IsMaxOn (fun z ↦ ‖fstar E z / E z‖) U z1 := by
    intro z hz
    have hz' : 0 < z.im := hz
    show ‖fstar E z / E z‖ ≤ ‖fstar E z1 / E z1‖
    have h1 : ‖fstar E z1 / E z1‖ = 1 := by
      rw [norm_div, norm_fstar, heq, div_self (norm_ne_zero_iff.mpr hEz1)]
    rw [h1, norm_div, div_le_one (norm_pos_iff.mpr (hE.2.1 z hz'))]
    exact hE.norm_fstar_le hz'
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_halfSpace_im_gt 0).isPreconnected hUo hGd hz1 hmax
  set c := fstar E z1 / E z1 with hc
  have hcn : ‖c‖ = 1 := by
    rw [hc, norm_div, norm_fstar, heq, div_self (norm_ne_zero_iff.mpr hEz1)]
  have hUeq : ∀ z ∈ U, fstar E z = c * E z := by
    intro z hz
    have := hconst hz
    simp only [Function.const_apply] at this
    rw [← this]; field_simp [hE.2.1 z hz]
  refine ⟨c, hcn, fun z ↦ ?_⟩
  have hana : AnalyticOnNhd ℂ (fun z ↦ fstar E z - c * E z) univ :=
    fun z _ ↦ (hfd.sub (hE.1.const_mul c)).analyticAt z
  have hz0 := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ z1) (Filter.mem_of_superset (hUo.mem_nhds hz1) fun w hw ↦ by
      show fstar E w - c * E w = 0
      rw [hUeq w hw, sub_self]) (mem_univ z)
  simpa [sub_eq_zero] using hz0

/-- If `E ∈ \overline{HB}` is strict at one point of `Im z > 0`, it is strict everywhere. -/
theorem IsHB.isStrictHB_of_exists_lt {E : ℂ → ℂ} (hE : IsHB E)
    (h : ∃ z : ℂ, 0 < z.im ∧ ‖E (conj z)‖ < ‖E z‖) : IsStrictHB E := by
  rcases hE.isStrictHB_or_fstar_eq with h' | ⟨c, hc, hfc⟩
  · exact h'
  · exfalso
    obtain ⟨z, hz, hlt⟩ := h
    have : ‖E (conj z)‖ = ‖E z‖ := by
      have := hfc z
      have h2 : ‖fstar E z‖ = ‖E (conj z)‖ := norm_fstar E z
      rw [← h2, this, norm_mul, hc, one_mul]
    linarith

/-- **Hurwitz-type closure.**  A locally uniform limit of functions of `\overline{HB}` is in
`\overline{HB}` unless it vanishes identically. -/
theorem IsHB.of_tendstoLocallyUniformly {ι : Type*} {p : Filter ι} [p.NeBot]
    {E : ι → ℂ → ℂ} {E₀ : ℂ → ℂ} (hE : ∀ i, IsHB (E i))
    (hlim : TendstoLocallyUniformly E E₀ p) (hne : ∃ z, E₀ z ≠ 0) : IsHB E₀ := by
  have hd : Differentiable ℂ E₀ := by
    have := (hlim.tendstoLocallyUniformlyOn (s := univ)).differentiableOn
      (Filter.Eventually.of_forall fun i ↦ (hE i).1.differentiableOn) isOpen_univ
    exact differentiableOn_univ.mp this
  refine ⟨hd, ?_, fun z hz ↦ ?_⟩
  · intro z0 hz0 h0
    have hana : AnalyticAt ℂ E₀ z0 := hd.analyticAt z0
    rcases hana.eventually_eq_zero_or_eventually_ne_zero with h | h
    · obtain ⟨w, hw⟩ := hne
      have : AnalyticOnNhd ℂ E₀ univ := fun z _ ↦ hd.analyticAt z
      exact hw (this.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (mem_univ z0) h (mem_univ w))
    · obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.mp h
      set r : ℝ := min (ε / 2) (z0.im / 2) with hr
      have hrpos : 0 < r := lt_min (by linarith) (by linarith)
      have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hrim : r < z0.im := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hcb : ∀ w ∈ closedBall z0 r, 0 < w.im := by
        intro w hw
        rw [mem_closedBall, dist_eq_norm] at hw
        have h1 : |(w - z0).im| ≤ ‖w - z0‖ := Complex.abs_im_le_norm _
        have h2 : -(w - z0).im ≤ |(w - z0).im| := neg_le_abs _
        simp only [Complex.sub_im] at h1 h2
        linarith
      have hsph : ∀ w ∈ sphere z0 r, E₀ w ≠ 0 := by
        intro w hw
        have hw' : w ∈ ball z0 ε ∩ {z0}ᶜ := by
          refine ⟨?_, ?_⟩
          · rw [mem_ball]; rw [mem_sphere] at hw; linarith
          · intro h'; rw [mem_singleton_iff] at h'; subst h'; simp at hw; linarith
        exact hεs hw'
      obtain ⟨w0, hw0, hmin⟩ := (isCompact_sphere z0 r).exists_isMinOn
        (NormedSpace.sphere_nonempty.mpr hrpos.le) hd.continuous.norm.continuousOn
      set m := ‖E₀ w0‖ with hm
      have hmpos : 0 < m := norm_pos_iff.mpr (hsph w0 hw0)
      have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hlim) (closedBall z0 r)
        (isCompact_closedBall z0 r)
      rw [Metric.tendstoUniformlyOn_iff] at hu
      have hev1 := hu (m / 2) (by linarith)
      have hev2 : ∀ᶠ i in p, ‖E i z0‖ < m / 2 := by
        have := ((hlim.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ z0)).norm
        rw [h0, norm_zero] at this
        exact this.eventually (gt_mem_nhds (by linarith))
      obtain ⟨i, hi1, hi2⟩ := (hev1.and hev2).exists
      have hnz : ∀ w ∈ closedBall z0 r, E i w ≠ 0 := fun w hw ↦ (hE i).2.1 w (hcb w hw)
      have hdiff : DiffContOnCl ℂ (fun z ↦ (E i z)⁻¹) (ball z0 r) := by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball z0 hrpos.ne']
        exact (hE i).1.differentiableOn.inv hnz
      have hbound : ∀ w ∈ frontier (ball z0 r), ‖(E i w)⁻¹‖ ≤ 2 / m := by
        intro w hw
        rw [frontier_ball z0 hrpos.ne'] at hw
        have h1 : m ≤ ‖E₀ w‖ := hmin hw
        have h2 := hi1 w (sphere_subset_closedBall hw)
        rw [dist_eq_norm] at h2
        have h3 : m / 2 ≤ ‖E i w‖ := by
          have := norm_sub_norm_le (E₀ w) (E i w)
          linarith
        rw [norm_inv]
        calc (‖E i w‖)⁻¹ ≤ (m / 2)⁻¹ := inv_anti₀ (by linarith) h3
          _ = 2 / m := by field_simp
      have := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hdiff hbound
        (subset_closure (mem_ball_self hrpos))
      rw [norm_inv] at this
      have hpos : 0 < ‖E i z0‖ := norm_pos_iff.mpr (hnz z0 (mem_closedBall_self hrpos.le))
      have : (m / 2)⁻¹ < (‖E i z0‖)⁻¹ := inv_strictAnti₀ hpos hi2
      have h4 : (m / 2)⁻¹ = 2 / m := by field_simp
      linarith
  · have h1 := ((hlim.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ (conj z))).norm
    have h2 := ((hlim.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ z)).norm
    exact le_of_tendsto_of_tendsto h1 h2 (Filter.Eventually.of_forall fun i ↦ (hE i).2.2 z hz)

/-- Added at assembly (requested by M04): `E` strict, `F ∈ \overline{HB}` ⇒ `E F` strict.
(`|E F (z̄)| ≤ |E(z̄)| |F(z)| < |E(z)| |F(z)|`, using `F(z) ≠ 0` for `Im z > 0`.) -/
theorem IsStrictHB.mul_isHB {E F : ℂ → ℂ} (hE : IsStrictHB E) (hF : IsHB F) :
    IsStrictHB (fun z ↦ E z * F z) := by
  obtain ⟨hF1, hF0, hF2⟩ := hF
  refine ⟨hE.1.mul ⟨hF1, hF0, hF2⟩, fun z hz ↦ ?_⟩
  simp only [norm_mul]
  have h1 := hE.2 z hz
  have h2 := hF2 z hz
  have h3 : 0 < ‖F z‖ := norm_pos_iff.mpr (hF0 z hz)
  calc ‖E (conj z)‖ * ‖F (conj z)‖ ≤ ‖E (conj z)‖ * ‖F z‖ :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ < ‖E z‖ * ‖F z‖ := mul_lt_mul_of_pos_right h1 h3

/-- Added at assembly (moved from `Corollary1.lean` / `Corollary2.lean`): a unimodular constant
factor preserves `\overline{HB}`. -/
theorem IsHB.rotate {E : ℂ → ℂ} (hE : IsHB E) (θ : ℝ) :
    IsHB (fun z ↦ Complex.exp (I * θ) * E z) := by
  obtain ⟨hd, h0, h1⟩ := hE
  have hn : ∀ w : ℂ, ‖Complex.exp (I * θ) * E w‖ = ‖E w‖ := fun w ↦ by
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  refine ⟨hd.const_mul _, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [← norm_pos_iff, hn]; exact norm_pos_iff.mpr (h0 z hz)
  · rw [hn, hn]; exact h1 z hz

end FF
