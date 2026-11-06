import OrtegaCerdaSeip.Bernstein.PhragmenLindelof

/-!
# M02 (Bernstein) — The Bernstein-type estimate of Lemma 5 (p. 413)

See `blueprint/M02_Bernstein.md`, §1.5.

For `f ∈ 𝓑_τ` with `|f| ≤ M` on `ℝ`, put `h(z) = |f(z)| e^{-τ|Im z|}` and `g = f e^{iτz}`.  On
`{Im ≥ 0}` we have `h = |g|`, and `|g| ≤ e^{2τ} M` on `{Im ≥ -1}` (Phragmén–Lindelöf).  Two forms:

* **Lipschitz form** (`abs_sub_le`): `|h(z) - h(w)| ≤ e^{2τ} M |z - w|`.  The Cauchy estimate on
  circles of radius `1` gives `|g'| ≤ e^{2τ} M` on `{Im ≥ 0}`.  The mean value inequality on that
  convex set and `||g(z)| - |g(w)|| ≤ |g(z) - g(w)|` give the bound there.  The lower half-plane
  follows by the reflection `z ↦ -z`, and a segment crossing `ℝ` is split at its real point.
* **`σ`-form** (`abs_sub_le_sigmaDist`, as printed on p. 413):
  `|h(z) - h(w)| ≤ 8 e^{2τ} M σ(z, w)` with `σ(z, w) = |z - w|/(1 + |z - w̄|)`.  This does *not*
  follow from the Lipschitz form far from `ℝ` (for `z = iy`, `w = iy + 1`, `σ → 0`); it needs the
  sharper Cauchy estimate `|g'(ζ)| ≤ e^{2τ} M/(1 + Im ζ)` (radius `1 + Im ζ`).  See the docstring of
  `abs_sub_le_sigmaDist`.

The paper states the `σ`-form "for `σ(z, w) < 1`".  That restriction is unnecessary, and it is not
vacuous: `σ` can exceed `1` across `ℝ` (`σ(i, -i) = 2`).  For `σ ≥ 1` the inequality is trivial.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

variable {f : ℂ → ℂ} {τ : ℝ}

/-- Cauchy estimate for `g = f e^{iτz}` on the closed upper half-plane. -/
theorem MemBernstein.norm_deriv_mul_cexp_le (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖deriv (fun w ↦ f w * Complex.exp (I * τ * w)) z‖ ≤ Real.exp (2 * τ) * M := by
  have hgd : Differentiable ℂ (fun w ↦ f w * Complex.exp (I * τ * w)) := hf.1.mul (by fun_prop)
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hgd.diffContOnCl (c := z)
    (C := Real.exp (2 * τ) * M) fun w hw ↦ ?_
  · simpa using this
  · have hw1 : -1 ≤ w.im := by
      have h2 := Complex.abs_im_le_norm (w - z)
      rw [sub_im, ← Complex.dist_eq, mem_sphere.1 hw] at h2
      linarith [neg_abs_le (w.im - z.im)]
    refine (hf.norm_mul_cexp_le_of_le_im hτ hM (-1) hw1).trans (le_of_eq ?_)
    simp [mul_comm]

/-- The Lipschitz bound on the closed upper half-plane. -/
theorem MemBernstein.abs_sub_le_of_im_nonneg (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) {z w : ℂ} (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)| ≤
      Real.exp (2 * τ) * M * ‖z - w‖ := by
  have hgd : Differentiable ℂ (fun w ↦ f w * Complex.exp (I * τ * w)) := hf.1.mul (by fun_prop)
  have hh : ∀ u : ℂ, 0 ≤ u.im →
      ‖f u‖ * Real.exp (-τ * |u.im|) = ‖f u * Complex.exp (I * τ * u)‖ := by
    intro u hu
    rw [norm_mul, norm_cexp_I_mul_ofReal_mul, abs_of_nonneg hu]
  rw [hh z hz, hh w hw]
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := {c : ℂ | 0 ≤ c.im})
    (fun x _ ↦ hgd x) (fun x hx ↦ hf.norm_deriv_mul_cexp_le hτ hM hx) (convex_halfSpace_im_ge 0)
    hw hz
  exact (abs_norm_sub_norm_le _ _).trans this

/-- **Bernstein-type inequality** (p. 413), Lipschitz form: `h = |f| e^{-τ|Im z|}` is
`e^{2τ} M`-Lipschitz on `ℂ`. -/
theorem MemBernstein.abs_sub_le (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) (z w : ℂ) :
    |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)| ≤
      Real.exp (2 * τ) * M * ‖z - w‖ := by
  have down : ∀ z w : ℂ, z.im ≤ 0 → w.im ≤ 0 →
      |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)| ≤
        Real.exp (2 * τ) * M * ‖z - w‖ := by
    intro z w hz hw
    have := (hf.comp_neg).abs_sub_le_of_im_nonneg hτ (fun x ↦ by simpa using hM (-x))
      (z := -z) (w := -w) (by simpa using hz) (by simpa using hw)
    rw [show -z - -w = -(z - w) by ring, norm_neg] at this
    simpa using this
  have cross : ∀ z w : ℂ, 0 ≤ z.im → w.im ≤ 0 →
      |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)| ≤
        Real.exp (2 * τ) * M * ‖z - w‖ := by
    intro z w hz hw
    rcases eq_or_lt_of_le (sub_nonneg.2 (hw.trans hz)) with hd | hd
    · exact hf.abs_sub_le_of_im_nonneg hτ hM hz (by linarith)
    · set s : ℝ := z.im / (z.im - w.im) with hs
      have hs0 : 0 ≤ s := div_nonneg hz hd.le
      have hs1 : s ≤ 1 := (div_le_one hd).2 (by linarith)
      set p : ℂ := z + s * (w - z) with hp
      have hpim : p.im = 0 := by
        rw [hp, hs]
        simp only [add_im, mul_im, ofReal_re, ofReal_im, sub_im, sub_re, zero_mul, add_zero]
        field_simp
        ring
      have hzp : ‖z - p‖ = s * ‖z - w‖ := by
        rw [hp, show z - (z + (s : ℂ) * (w - z)) = (s : ℂ) * (z - w) by ring, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg hs0]
      have hpw : ‖p - w‖ = (1 - s) * ‖z - w‖ := by
        rw [hp, show z + (s : ℂ) * (w - z) - w = ((1 - s : ℝ) : ℂ) * (z - w) by push_cast; ring,
          norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      calc |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)|
          ≤ |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f p‖ * Real.exp (-τ * |p.im|)| +
            |‖f p‖ * Real.exp (-τ * |p.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)| :=
            _root_.abs_sub_le _ _ _
        _ ≤ Real.exp (2 * τ) * M * ‖z - p‖ + Real.exp (2 * τ) * M * ‖p - w‖ :=
            add_le_add (hf.abs_sub_le_of_im_nonneg hτ hM hz hpim.ge) (down p w hpim.le hw)
        _ = Real.exp (2 * τ) * M * ‖z - w‖ := by rw [hzp, hpw]; ring
  rcases le_total 0 z.im with hz | hz <;> rcases le_total 0 w.im with hw | hw
  · exact hf.abs_sub_le_of_im_nonneg hτ hM hz hw
  · exact cross z w hz hw
  · rw [abs_sub_comm, norm_sub_rev]
    exact cross w z hw hz
  · exact down z w hz hw

/-! ### Auxiliary lemmas for the `σ`-form -/

/-- `σ(-z, -w) = σ(z, w)`. -/
private theorem sigmaDist_neg_neg (z w : ℂ) : sigmaDist (-z) (-w) = sigmaDist z w := by
  unfold sigmaDist
  rw [map_neg, show -z - -w = -(z - w) by ring, show -z - -conj w = -(z - conj w) by ring,
    norm_neg, norm_neg]

/-- Across `ℝ` (`Im z · Im w ≤ 0`), `|z - w̄| ≤ |z - w|`. -/
private theorem norm_sub_conj_le_of_im_mul_nonpos {z w : ℂ} (h : z.im * w.im ≤ 0) :
    ‖z - conj w‖ ≤ ‖z - w‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    normSq_apply, normSq_apply]
  simp only [sub_re, sub_im, conj_re, conj_im]
  nlinarith

/-- In the closed upper half-plane, `|z - w̄| ≤ |z - w| + 2 Im w`. -/
private theorem norm_sub_conj_le_add_two_mul_im (z w : ℂ) (hw : 0 ≤ w.im) :
    ‖z - conj w‖ ≤ ‖z - w‖ + 2 * w.im := by
  calc ‖z - conj w‖ ≤ ‖z - w‖ + ‖w - conj w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖z - w‖ + 2 * w.im := by
        rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (by linarith)]

/-- The `σ`-form, same closed upper half-plane (blueprint Lemma 1.5.4, Case 1; constant
`3 e^{2τ}`, stated with `8 e^{2τ}`).  Sharper Cauchy estimate on discs of radius `1 + Im ζ`, mean
value inequality on `{Im ≥ m}`, `m = min(Im z, Im w)`. -/
theorem MemBernstein.abs_sub_le_sigmaDist_of_im_nonneg (hf : MemBernstein τ f) (hτ : 0 ≤ τ)
    {M : ℝ} (hM : ∀ x : ℝ, ‖f x‖ ≤ M) {z w : ℂ} (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)| ≤
      8 * Real.exp (2 * τ) * M * sigmaDist z w := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have he1 : 1 ≤ Real.exp (2 * τ) := Real.one_le_exp (by positivity)
  set B := Real.exp (2 * τ) * M with hB
  have hB0 : 0 ≤ B := by positivity
  have hMB : M ≤ B := by rw [hB]; nlinarith
  set m := min z.im w.im with hm
  have hm0 : 0 ≤ m := le_min hz hw
  set g : ℂ → ℂ := fun u ↦ f u * Complex.exp (I * τ * u) with hg
  have hgd : Differentiable ℂ g := hf.1.mul (by fun_prop)
  -- Step 1: `|g'(ζ)| ≤ B / (1 + m)` on `{Im ≥ m}`
  have hder : ∀ ζ ∈ {c : ℂ | m ≤ c.im}, ‖deriv g ζ‖ ≤ B / (1 + m) := by
    intro ζ hζ
    have hζ' : m ≤ ζ.im := hζ
    have hR : 0 < 1 + ζ.im := by linarith
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hgd.diffContOnCl (c := ζ)
      (C := B) fun ξ hξ ↦ ?_
    · exact this.trans (div_le_div_of_nonneg_left hB0 (by linarith) (by linarith))
    · have hξ1 : -1 ≤ ξ.im := by
        have h2 := Complex.abs_im_le_norm (ξ - ζ)
        rw [sub_im, ← Complex.dist_eq, mem_sphere.1 hξ] at h2
        linarith [neg_abs_le (ξ.im - ζ.im)]
      refine (hf.norm_mul_cexp_le_of_le_im hτ hM (-1) hξ1).trans (le_of_eq ?_)
      rw [hB]
      simp [mul_comm]
  -- Steps 2–3: mean value inequality and `h = |g|` on `{Im ≥ 0}`
  have hh : ∀ u : ℂ, 0 ≤ u.im → ‖f u‖ * Real.exp (-τ * |u.im|) = ‖g u‖ := by
    intro u hu
    rw [hg, norm_mul, norm_cexp_I_mul_ofReal_mul, abs_of_nonneg hu]
  have hmz : z ∈ {c : ℂ | m ≤ c.im} := show m ≤ z.im from min_le_left _ _
  have hmw : w ∈ {c : ℂ | m ≤ c.im} := show m ≤ w.im from min_le_right _ _
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ ↦ hgd x) hder
    (convex_halfSpace_im_ge m) hmw hmz
  set t := ‖z - w‖ with ht
  have hΔ : |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)| ≤ B / (1 + m) * t := by
    rw [hh z hz, hh w hw]
    exact (abs_norm_sub_norm_le _ _).trans hmv
  have hΔM : |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)| ≤ M := by
    have h1 := hf.norm_mul_exp_le hτ hM z
    have h2 := hf.norm_mul_exp_le hτ hM w
    have h3 : 0 ≤ ‖f z‖ * Real.exp (-τ * |z.im|) := by positivity
    have h4 : 0 ≤ ‖f w‖ * Real.exp (-τ * |w.im|) := by positivity
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  set Δ := |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)| with hΔdef
  have hΔ0 : 0 ≤ Δ := abs_nonneg _
  -- Step 4: geometry, `|z - w̄| ≤ t + 2m`
  have hgeo : ‖z - conj w‖ ≤ t + 2 * m := by
    rcases le_total z.im w.im with hzw | hzw
    · have hmz' : m = z.im := min_eq_left hzw
      have e : ‖z - conj w‖ = ‖w - conj z‖ := by
        rw [← Complex.norm_conj, map_sub, Complex.conj_conj, norm_sub_rev]
      rw [e, hmz', ht, norm_sub_rev z w]
      exact norm_sub_conj_le_add_two_mul_im w z hz
    · have hmw' : m = w.im := min_eq_right hzw
      rw [hmw']
      exact norm_sub_conj_le_add_two_mul_im z w hw
  -- Steps 5–6
  have hD : 0 < 1 + ‖z - conj w‖ := by positivity
  unfold sigmaDist
  rw [← ht, mul_div_assoc', le_div_iff₀ hD]
  have ht0 : 0 ≤ t := norm_nonneg _
  rcases le_or_gt t (1 + m) with h1 | h1
  · have hΔ' : Δ * (1 + m) ≤ B * t := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at hΔ
      exact hΔ
    have hBt : 0 ≤ B * t := by positivity
    calc Δ * (1 + ‖z - conj w‖) ≤ Δ * (3 * (1 + m)) := by
          gcongr
          linarith
      _ = 3 * (Δ * (1 + m)) := by ring
      _ ≤ 3 * (B * t) := by gcongr
      _ ≤ 8 * Real.exp (2 * τ) * M * t := by rw [hB]; nlinarith
  · calc Δ * (1 + ‖z - conj w‖) ≤ M * (3 * t) := by
          apply mul_le_mul hΔM (by linarith) hD.le hM0
      _ ≤ 8 * Real.exp (2 * τ) * M * t := by nlinarith [mul_nonneg hM0 ht0]

/-- The `σ`-form across `ℝ` (blueprint Lemma 1.5.4, Case 3): from the Lipschitz form and
`|z - w̄| ≤ |z - w|`. -/
theorem MemBernstein.abs_sub_le_sigmaDist_of_im_mul_nonpos (hf : MemBernstein τ f) (hτ : 0 ≤ τ)
    {M : ℝ} (hM : ∀ x : ℝ, ‖f x‖ ≤ M) {z w : ℂ} (hzw : z.im * w.im ≤ 0) :
    |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)| ≤
      8 * Real.exp (2 * τ) * M * sigmaDist z w := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have he1 : 1 ≤ Real.exp (2 * τ) := Real.one_le_exp (by positivity)
  have hΔ := hf.abs_sub_le hτ hM z w
  have hΔM : |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)| ≤ M := by
    have h1 := hf.norm_mul_exp_le hτ hM z
    have h2 := hf.norm_mul_exp_le hτ hM w
    have h3 : 0 ≤ ‖f z‖ * Real.exp (-τ * |z.im|) := by positivity
    have h4 : 0 ≤ ‖f w‖ * Real.exp (-τ * |w.im|) := by positivity
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  set Δ := |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)| with hΔdef
  have hΔ0 : 0 ≤ Δ := abs_nonneg _
  have hgeo := norm_sub_conj_le_of_im_mul_nonpos hzw
  set t := ‖z - w‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hD : 0 < 1 + ‖z - conj w‖ := by positivity
  unfold sigmaDist
  rw [← ht, mul_div_assoc', le_div_iff₀ hD]
  set e := Real.exp (2 * τ)
  have heM : M ≤ e * M := by nlinarith
  rcases le_total t 1 with h1 | h1
  · calc Δ * (1 + ‖z - conj w‖) ≤ (e * M * t) * 2 := by
          apply mul_le_mul hΔ (by linarith) hD.le (by positivity)
      _ ≤ 8 * e * M * t := by nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ e) hM0) ht0]
  · calc Δ * (1 + ‖z - conj w‖) ≤ M * (2 * t) := by
          apply mul_le_mul hΔM (by linarith) hD.le hM0
      _ ≤ 8 * e * M * t := by nlinarith [mul_nonneg hM0 ht0]

/-- **Bernstein-type inequality** (p. 413), as printed:
`||f(z)| e^{-τ|Im z|} - |f(w)| e^{-τ|Im w|}| ≲ σ(z, w) ‖f‖`, for all `z, w`, with
`σ(z, w) = |z − w|/(1 + |z − w̄|)`.  Proof (blueprint M02, Lemma 1.5.4; constant `3 e^{2τ}`), with
`g = f e^{iτz}`, `B = e^{2τ} M`, `t = |z − w|`:
* *Same closed upper half-plane*, `m = min(Im z, Im w) ≥ 0`.  The disc of radius `1 + Im ζ` about
  `ζ` lies in `{Im ≥ −1}`, where `|g| ≤ B`, so the Cauchy estimate gives `|g'(ζ)| ≤ B/(1 + m)` on
  the convex set `{Im ≥ m}`.  The mean value inequality gives `|Δh| ≤ |Δg| ≤ B t/(1 + m)`, and
  `|z − w̄| ≤ t + 2m`.  If `t ≤ 1 + m`, then `1 + |z − w̄| ≤ 3(1 + m)`, so `|Δh| ≤ 3Bσ`.  If
  `t > 1 + m`, then `σ > 1/3`, and the trivial `|Δh| ≤ M` gives `|Δh| ≤ 3Mσ`.
* *Same closed lower half-plane*: apply this to `f(−·)`; `z ↦ −z` preserves `σ`.
* *Opposite half-planes*: `|z − w̄| ≤ |z − w|`, so `σ ≥ t/(1 + t) ≥ min(1, t)/2`.  `abs_sub_le`
  and `|Δh| ≤ M` give `|Δh| ≤ B min(1, t) ≤ 2Bσ`.
(Schwarz–Pick on `{Im > −1}` gives `4√2 e^{2τ}` instead, but needs a half-plane Schwarz–Pick lemma,
which Mathlib lacks.) -/
theorem MemBernstein.abs_sub_le_sigmaDist (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) (z w : ℂ) :
    |‖f z‖ * Real.exp (-τ * |z.im|) - ‖f w‖ * Real.exp (-τ * |w.im|)| ≤
      8 * Real.exp (2 * τ) * M * sigmaDist z w := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have he1 : 1 ≤ Real.exp (2 * τ) := Real.one_le_exp (by positivity)
  rcases le_total 0 z.im with hz | hz <;> rcases le_total 0 w.im with hw | hw
  · exact hf.abs_sub_le_sigmaDist_of_im_nonneg hτ hM hz hw
  · exact hf.abs_sub_le_sigmaDist_of_im_mul_nonpos hτ hM (mul_nonpos_of_nonneg_of_nonpos hz hw)
  · exact hf.abs_sub_le_sigmaDist_of_im_mul_nonpos hτ hM (mul_nonpos_of_nonpos_of_nonneg hz hw)
  · have := (hf.comp_neg).abs_sub_le_sigmaDist_of_im_nonneg hτ (fun x ↦ by simpa using hM (-x))
      (z := -z) (w := -w) (by simpa using hz) (by simpa using hw)
    rw [sigmaDist_neg_neg] at this
    simpa using this

end OCS
