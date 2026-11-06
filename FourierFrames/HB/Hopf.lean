import FourierFrames.Defs

/-!
# M02 helper — Hopf-type boundary lemma for self-maps of the upper half-plane

Elementary version used for `φ_E' > 0` (`blueprint/M02_HB.md`, §5.2): if `Θ = c + (z-x₀)^n g(z)`
near a real point `x₀` with `‖c‖ = 1`, `g(x₀) ≠ 0`, `n ≥ 1`, and `‖Θ‖ ≤ 1` on `Im z > 0`, then
`n = 1` and `g(x₀)/c` is a positive multiple of `i`.
-/

open Complex Filter Topology Set

noncomputable section

namespace FF

/-- Trigonometric part. -/
theorem hopf_trig {h0 : ℂ} (hh0 : h0 ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hle : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, (Complex.exp (I * ((n : ℝ) * θ : ℝ)) * h0).re ≤ 0) :
    n = 1 ∧ h0.re = 0 ∧ 0 < h0.im := by
  have hform : ∀ θ : ℝ, (Complex.exp (I * ((n : ℝ) * θ : ℝ)) * h0).re =
      h0.re * Real.cos ((n : ℝ) * θ) - h0.im * Real.sin ((n : ℝ) * θ) := by
    intro θ
    have : I * (((n : ℝ) * θ : ℝ) : ℂ) = (((n : ℝ) * θ : ℝ) : ℂ) * I := mul_comm _ _
    rw [this, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  have hIcc : ∀ θ ∈ Icc (0 : ℝ) Real.pi,
      h0.re * Real.cos ((n : ℝ) * θ) - h0.im * Real.sin ((n : ℝ) * θ) ≤ 0 := by
    have hcl : IsClosed {θ : ℝ | h0.re * Real.cos ((n : ℝ) * θ) - h0.im * Real.sin ((n : ℝ) * θ) ≤ 0} :=
      isClosed_le (by fun_prop) continuous_const
    have hsub : Ioo (0 : ℝ) Real.pi ⊆ {θ : ℝ | h0.re * Real.cos ((n : ℝ) * θ) -
        h0.im * Real.sin ((n : ℝ) * θ) ≤ 0} := fun θ hθ ↦ by
      have := hle θ hθ; rwa [hform] at this
    have := closure_minimal hsub hcl
    rw [closure_Ioo Real.pi_pos.ne] at this
    exact this
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha1 := hIcc 0 ⟨le_rfl, Real.pi_pos.le⟩
  have ha2 := hIcc (Real.pi / n) ⟨by positivity, by
    rw [div_le_iff₀ hnpos]; nlinarith [Real.pi_pos]⟩
  have hb1 := hIcc (Real.pi / (2 * n)) ⟨by positivity, by
    rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_pos]⟩
  have e2 : (n : ℝ) * (Real.pi / n) = Real.pi := by field_simp
  have e3 : (n : ℝ) * (Real.pi / (2 * n)) = Real.pi / 2 := by field_simp
  rw [e2] at ha2
  rw [e3] at hb1
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, Real.cos_pi, Real.sin_pi,
    Real.cos_pi_div_two, Real.sin_pi_div_two] at ha1 ha2 hb1
  have ha : h0.re = 0 := by linarith
  have hb : 0 ≤ h0.im := by linarith
  have hbne : h0.im ≠ 0 := by
    intro h; apply hh0; apply Complex.ext <;> simp [ha, h]
  have hbpos : 0 < h0.im := lt_of_le_of_ne hb (Ne.symm hbne)
  refine ⟨?_, ha, hbpos⟩
  by_contra hne
  have hn2 : (2 : ℝ) ≤ n := by
    have : 2 ≤ n := by omega
    exact_mod_cast this
  have hc := hIcc (3 * Real.pi / (2 * n)) ⟨by positivity, by
    rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_pos]⟩
  have e4 : (n : ℝ) * (3 * Real.pi / (2 * n)) = 3 * Real.pi / 2 := by field_simp
  rw [e4] at hc
  have hs : Real.sin (3 * Real.pi / 2) = -1 := by
    have : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
    rw [this, Real.sin_add_pi, Real.sin_pi_div_two]
  have hco : Real.cos (3 * Real.pi / 2) = 0 := by
    have : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
    rw [this, Real.cos_add_pi, Real.cos_pi_div_two]; simp
  rw [hs, hco, ha] at hc
  linarith

/-- **Boundary lemma.** -/
theorem hopf_boundary {Θ g : ℂ → ℂ} {x₀ : ℝ} {c : ℂ} (hc : ‖c‖ = 1) {n : ℕ} (hn : 1 ≤ n)
    (hg : ContinuousAt g x₀) (hg0 : g x₀ ≠ 0)
    (hΘ : ∀ᶠ z in 𝓝 (x₀ : ℂ), Θ z = c + (z - x₀) ^ n * g z)
    (hle : ∀ z : ℂ, 0 < z.im → ‖Θ z‖ ≤ 1) :
    n = 1 ∧ (g x₀ / c).re = 0 ∧ 0 < (g x₀ / c).im := by
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have hh0 : g x₀ / c ≠ 0 := div_ne_zero hg0 hc0
  apply hopf_trig hh0 hn
  intro θ hθ
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  -- path `t ↦ x₀ + t e^{iθ}`
  set γ : ℝ → ℂ := fun t ↦ (x₀ : ℂ) + (t : ℂ) * Complex.exp (θ * I) with hγ
  have hγc : Continuous γ := by fun_prop
  have hγ0 : γ 0 = x₀ := by simp [hγ]
  have hγt : Tendsto γ (𝓝[>] 0) (𝓝 (x₀ : ℂ)) := by
    rw [← hγ0]; exact (hγc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), Θ (γ t) = c + (γ t - x₀) ^ n * g (γ t) := hγt.eventually hΘ
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  set u : ℝ → ℂ := fun t ↦ Complex.exp (I * ((n : ℝ) * θ : ℝ)) * (g (γ t) / c) with hu
  have hu0 : Tendsto u (𝓝[>] 0) (𝓝 (Complex.exp (I * ((n : ℝ) * θ : ℝ)) * (g x₀ / c))) := by
    have : Tendsto (fun t ↦ g (γ t)) (𝓝[>] 0) (𝓝 (g x₀)) := hg.tendsto.comp hγt
    exact (this.div_const c).const_mul _
  have hev3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 2 * (u t).re + t ^ n * ‖u t‖ ^ 2 ≤ 0 := by
    filter_upwards [hev1, hev2] with t h1 h2
    have himγ : 0 < (γ t).im := by
      have e : (Complex.exp (θ * I)).im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ
      have e2 : (Complex.exp (θ * I)).re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ
      simp only [hγ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, e, e2,
        zero_mul, add_zero, zero_add]
      exact mul_pos h2 hsin
    have h3 := hle (γ t) himγ
    rw [h1] at h3
    have hw : c + (γ t - x₀) ^ n * g (γ t) = c * (1 + (t : ℂ) ^ n * u t) := by
      have : γ t - x₀ = t * Complex.exp (θ * I) := by simp [hγ]
      rw [this, mul_pow, ← Complex.exp_nat_mul, hu]
      have : Complex.exp (I * ((n : ℝ) * θ : ℝ)) = Complex.exp (n * (θ * I)) := by
        congr 1; push_cast; ring
      rw [this]
      field_simp
    rw [hw, norm_mul, hc, one_mul] at h3
    have h4 : ‖1 + (t : ℂ) ^ n * u t‖ ^ 2 = 1 + 2 * (t ^ n * (u t).re) + t ^ (2 * n) * ‖u t‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re,
        Complex.mul_im, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, add_zero, zero_add]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, pow_mul']
      ring
    have h5 : ‖1 + (t : ℂ) ^ n * u t‖ ^ 2 ≤ 1 := by
      have := norm_nonneg (1 + (t : ℂ) ^ n * u t)
      nlinarith
    rw [h4] at h5
    have htn : 0 < t ^ n := pow_pos h2 n
    have : t ^ (2 * n) = t ^ n * t ^ n := by rw [two_mul, pow_add]
    rw [this] at h5
    by_contra hcon
    push Not at hcon
    nlinarith
  have hlim : Tendsto (fun t ↦ 2 * (u t).re + t ^ n * ‖u t‖ ^ 2) (𝓝[>] 0)
      (𝓝 (2 * (Complex.exp (I * ((n : ℝ) * θ : ℝ)) * (g x₀ / c)).re + 0 ^ n * ‖Complex.exp (I * ((n : ℝ) * θ : ℝ)) * (g x₀ / c)‖ ^ 2)) := by
    refine Tendsto.add ((Complex.continuous_re.tendsto _).comp hu0 |>.const_mul 2) ?_
    refine Tendsto.mul ?_ ((hu0.norm).pow 2)
    exact ((continuous_pow n).tendsto 0).mono_left nhdsWithin_le_nhds
  have := le_of_tendsto hlim hev3
  rw [zero_pow (by omega)] at this
  linarith
