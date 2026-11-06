import OrtegaCerdaSeip.Bernstein.Basic

/-!
# M02 (Bernstein) — The Phragmén–Lindelöf bound `|f(z)| ≤ ‖f‖ e^{τ|Im z|}` and its consequences

See `blueprint/M02_Bernstein.md`, §1.3–§1.5.

The paper (p. 401) uses: if `f ∈ 𝓑_τ` then `|f(z)| ≤ ‖f‖_{L^∞(ℝ)} e^{τ|Im z|}` for all `z`
("the Phragmén–Lindelöf principle implies").  We derive it from Mathlib's
`PhragmenLindelof.right_half_plane_of_bounded_on_real`, applied to
`g(w) = f(I w) e^{-(τ+ε) w}` (the upper half-plane after the rotation `z = I w`; boundedness of
`g` on the positive real axis uses the type bound with `ε/2`), then `ε → 0` (`ge_of_tendsto`);
the lower half-plane follows by applying the upper case to `z ↦ f(-z)`.  The rotation
bookkeeping follows `OC.norm_mul_exp_neg_le_of_entire` (`OrtegaCerdaMultipliers/Theorem3.lean`
of the companion project `../MR1949832`, same author), which uses the `tendsto_zero` variant.

Consequences: the identity `sup_ℂ |f| e^{-τ|Im z|} = sup_ℝ |f|` (in `ℝ≥0∞`, in the exact shape of
`IsSampling`), the converse `|f(z)| ≤ M e^{τ|Im z|} ⇒ f ∈ 𝓑_τ`, boundedness of `f e^{±iτz}` in the
closed half-planes (restriction to `H^∞`), complex translations (vertical shifts with the factor
`e^{τ|a|}`), derivatives (Cauchy estimate), and completeness of `𝓑_τ` for the sup norm on `ℝ`
("this inequality also shows that `𝓑_τ` is complete", p. 401).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

variable {f : ℂ → ℂ} {τ : ℝ}

/-! ### Phragmén–Lindelöf -/

/-- **Phragmén–Lindelöf in the closed upper half-plane.** -/
theorem norm_le_mul_exp_im_of_im_nonneg (hd : Differentiable ℂ f) (he : IsExpTypeLE τ f)
    (hτ : 0 ≤ τ) {M : ℝ} (hM : ∀ x : ℝ, ‖f x‖ ≤ M) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖f z‖ ≤ M * Real.exp (τ * z.im) := by
  have key : ∀ ε > 0, ‖f z‖ ≤ M * Real.exp ((τ + ε) * z.im) := by
    intro ε hε
    set τ' := τ + ε with hτ'
    have hτ'0 : 0 ≤ τ' := by linarith
    set g : ℂ → ℂ := fun w ↦ f (I * w) * Complex.exp (-(τ' : ℂ) * w) with hg
    have hgd : Differentiable ℂ g :=
      (hd.comp (differentiable_id.const_mul I)).mul
        (Complex.differentiable_exp.comp (differentiable_id.const_mul _))
    have hnorm : ∀ w, ‖g w‖ = ‖f (I * w)‖ * Real.exp (-τ' * w.re) := by
      intro w
      simp only [hg, norm_mul, Complex.norm_exp, neg_mul, neg_re, mul_re, ofReal_re, ofReal_im,
        zero_mul, sub_zero]
    obtain ⟨C₁, hC₁0, hC₁⟩ := he.exists_nonneg (half_pos hε)
    obtain ⟨C₂, hC₂0, hC₂⟩ := he.exists_nonneg hε
    have hexp : ∃ c < (2 : ℝ), ∃ B,
        g =O[Bornology.cobounded ℂ ⊓ 𝓟 {w | 0 < w.re}] fun w ↦ Real.exp (B * ‖w‖ ^ c) := by
      refine ⟨1, by norm_num, 2 * τ',
        Asymptotics.IsBigO.of_bound C₂ (Filter.Eventually.of_forall fun w ↦ ?_)⟩
      rw [Real.rpow_one, Real.norm_of_nonneg (Real.exp_pos _).le, hnorm]
      have h1 := hC₂ (I * w)
      rw [norm_mul, Complex.norm_I, one_mul] at h1
      have h2 : -τ' * w.re ≤ τ' * ‖w‖ := by
        nlinarith [Complex.abs_re_le_norm w, neg_abs_le w.re]
      calc ‖f (I * w)‖ * Real.exp (-τ' * w.re)
          ≤ C₂ * Real.exp (τ' * ‖w‖) * Real.exp (τ' * ‖w‖) := by gcongr
        _ = C₂ * Real.exp (2 * τ' * ‖w‖) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
    have hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ ↦ ‖g x‖ := by
      refine ⟨C₁, Filter.eventually_map.2 ?_⟩
      filter_upwards [eventually_ge_atTop 0] with x hx
      rw [hnorm]
      have h1 := hC₁ (I * x)
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hx] at h1
      simp only [ofReal_re]
      calc ‖f (I * x)‖ * Real.exp (-τ' * x)
          ≤ C₁ * Real.exp ((τ + ε / 2) * x) * Real.exp (-τ' * x) := by gcongr
        _ = C₁ * Real.exp (-(ε / 2 * x)) := by
          rw [mul_assoc, ← Real.exp_add, hτ']; ring_nf
        _ ≤ C₁ := by
          refine mul_le_of_le_one_right hC₁0 (Real.exp_le_one_iff.2 ?_)
          have : 0 ≤ ε / 2 * x := by positivity
          linarith
    have him : ∀ y : ℝ, ‖g (y * I)‖ ≤ M := by
      intro y
      rw [hnorm]
      have e : I * (y * I) = ((-y : ℝ) : ℂ) := by
        push_cast; ring_nf; simp [I_sq]
      rw [e]
      simpa using hM (-y)
    have hw : 0 ≤ (-I * z).re := by simpa using hz
    have h := PhragmenLindelof.right_half_plane_of_bounded_on_real hgd.diffContOnCl hexp hre
      him hw
    rw [hnorm] at h
    have e : I * (-I * z) = z := by ring_nf; simp
    have e2 : (-I * z).re = z.im := by simp
    rw [e, e2] at h
    calc ‖f z‖ = ‖f z‖ * Real.exp (-τ' * z.im) * Real.exp (τ' * z.im) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ M * Real.exp (τ' * z.im) := by gcongr
  have ht : Tendsto (fun ε ↦ M * Real.exp ((τ + ε) * z.im)) (𝓝[>] 0)
      (𝓝 (M * Real.exp (τ * z.im))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    have hc : Continuous (fun ε ↦ M * Real.exp ((τ + ε) * z.im)) := by fun_prop
    simpa using hc.tendsto 0
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε ↦ key ε hε)

/-- **Phragmén–Lindelöf** (p. 401): an entire function of exponential type `≤ τ` bounded by `M`
on `ℝ` satisfies `|f(z)| ≤ M e^{τ|Im z|}`. -/
theorem norm_le_mul_exp_abs_im (hd : Differentiable ℂ f) (he : IsExpTypeLE τ f) (hτ : 0 ≤ τ)
    {M : ℝ} (hM : ∀ x : ℝ, ‖f x‖ ≤ M) (z : ℂ) : ‖f z‖ ≤ M * Real.exp (τ * |z.im|) := by
  rcases le_or_gt 0 z.im with h | h
  · rw [abs_of_nonneg h]
    exact norm_le_mul_exp_im_of_im_nonneg hd he hτ hM h
  · have := norm_le_mul_exp_im_of_im_nonneg (f := fun w ↦ f (-w)) (hd.comp differentiable_neg)
      he.comp_neg hτ (fun x ↦ by simpa using hM (-x)) (z := -z) (by simp; linarith)
    simpa [abs_of_neg h] using this

theorem MemBernstein.norm_le (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) (z : ℂ) : ‖f z‖ ≤ M * Real.exp (τ * |z.im|) :=
  norm_le_mul_exp_abs_im hf.1 hf.2.1 hτ hM z

/-- The weighted modulus `|f(z)| e^{-τ|Im z|}` is bounded by `sup_ℝ |f|`. -/
theorem MemBernstein.norm_mul_exp_le (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) (z : ℂ) : ‖f z‖ * Real.exp (-τ * |z.im|) ≤ M := by
  have h := hf.norm_le hτ hM z
  calc ‖f z‖ * Real.exp (-τ * |z.im|) ≤ M * Real.exp (τ * |z.im|) * Real.exp (-τ * |z.im|) := by
        gcongr
    _ = M := by
        rw [mul_assoc, ← Real.exp_add, show τ * |z.im| + -τ * |z.im| = 0 by ring, Real.exp_zero,
          mul_one]

/-- `sup_{z ∈ ℂ} |f(z)| e^{-τ|Im z|} = sup_{x ∈ ℝ} |f(x)|` (the left side is the one in
`IsSampling`). -/
theorem MemBernstein.iSup_eq (hf : MemBernstein τ f) (hτ : 0 ≤ τ) :
    (⨆ z : ℂ, ENNReal.ofReal (‖f z‖ * Real.exp (-τ * |z.im|))) = ⨆ x : ℝ, ENNReal.ofReal ‖f x‖ := by
  apply le_antisymm
  · set S := ⨆ x : ℝ, ENNReal.ofReal ‖f x‖ with hSdef
    obtain ⟨M, -, hM⟩ := hf.exists_bound
    have hS : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le fun x ↦ ENNReal.ofReal_le_ofReal (hM x))
    have hx : ∀ x : ℝ, ‖f x‖ ≤ S.toReal := fun x ↦
      (ENNReal.ofReal_le_iff_le_toReal hS).1 (le_iSup (fun x : ℝ ↦ ENNReal.ofReal ‖f x‖) x)
    calc (⨆ z : ℂ, ENNReal.ofReal (‖f z‖ * Real.exp (-τ * |z.im|)))
        ≤ ENNReal.ofReal S.toReal :=
          iSup_le fun z ↦ ENNReal.ofReal_le_ofReal (hf.norm_mul_exp_le hτ hx z)
      _ = S := ENNReal.ofReal_toReal hS
  · refine iSup_le fun x ↦ le_iSup_of_le (x : ℂ) ?_
    simp

theorem MemBernstein.iSup_le (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) :
    (⨆ z : ℂ, ENNReal.ofReal (‖f z‖ * Real.exp (-τ * |z.im|))) ≤ ENNReal.ofReal M := by
  exact _root_.iSup_le fun z ↦ ENNReal.ofReal_le_ofReal (hf.norm_mul_exp_le hτ hM z)

theorem MemBernstein.iSup_ne_top (hf : MemBernstein τ f) (hτ : 0 ≤ τ) :
    (⨆ z : ℂ, ENNReal.ofReal (‖f z‖ * Real.exp (-τ * |z.im|))) ≠ ⊤ := by
  obtain ⟨M, -, hM⟩ := hf.exists_bound
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hf.iSup_le hτ hM)

/-- Converse of Phragmén–Lindelöf: an entire function with `|f(z)| ≤ M e^{τ|Im z|}` is in
`𝓑_τ` (and `|f| ≤ M` on `ℝ`). -/
theorem memBernstein_of_norm_le (hd : Differentiable ℂ f) (hτ : 0 ≤ τ) {M : ℝ}
    (h : ∀ z, ‖f z‖ ≤ M * Real.exp (τ * |z.im|)) : MemBernstein τ f := by
  refine ⟨hd, IsExpTypeLE.of_bound (C := M) fun z ↦ (h z).trans ?_,
    ⟨M, fun x ↦ by simpa using h x⟩⟩
  have hM0 : 0 ≤ M := by
    have := h 0
    simp only [zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  gcongr
  exact Complex.abs_im_le_norm z

/-! ### Restriction to the half-planes (`H^∞`) -/

/-- `|e^{iτz}| = e^{-τ Im z}` for real `τ`. -/
theorem norm_cexp_I_mul_ofReal_mul (τ : ℝ) (z : ℂ) :
    ‖Complex.exp (I * τ * z)‖ = Real.exp (-τ * z.im) := by
  rw [Complex.norm_exp]
  simp

/-- `f(z) e^{iτz}` is bounded by `sup_ℝ |f|` on the closed upper half-plane. -/
theorem MemBernstein.norm_mul_cexp_le_of_im_nonneg (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖f z * Complex.exp (I * τ * z)‖ ≤ M := by
  rw [norm_mul, norm_cexp_I_mul_ofReal_mul, ← abs_of_nonneg hz]
  exact hf.norm_mul_exp_le hτ hM z

/-- `f(z) e^{-iτz}` is bounded by `sup_ℝ |f|` on the closed lower half-plane. -/
theorem MemBernstein.norm_mul_cexp_le_of_im_nonpos (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) {z : ℂ} (hz : z.im ≤ 0) :
    ‖f z * Complex.exp (-(I * τ * z))‖ ≤ M := by
  have := (hf.comp_neg).norm_mul_cexp_le_of_im_nonneg hτ (fun x ↦ by simpa using hM (-x))
    (z := -z) (by simpa using hz)
  simpa using this

/-- `f(z) e^{iτz}` is bounded on every upper half-plane `ℂ⁺_a = {Im z ≥ a}` (p. 403). -/
theorem MemBernstein.norm_mul_cexp_le_of_le_im (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) (a : ℝ) {z : ℂ} (hz : a ≤ z.im) :
    ‖f z * Complex.exp (I * τ * z)‖ ≤ M * Real.exp (2 * τ * |a|) := by
  have h1 := hf.norm_le hτ hM z
  have h2 : τ * |z.im| + -τ * z.im ≤ 2 * τ * |a| := by
    have : |z.im| - z.im ≤ 2 * |a| := by
      rcases le_or_gt 0 z.im with h | h
      · rw [abs_of_nonneg h, sub_self]
        positivity
      · rw [abs_of_neg h]
        linarith [neg_le_abs a]
    nlinarith
  rw [norm_mul, norm_cexp_I_mul_ofReal_mul]
  calc ‖f z‖ * Real.exp (-τ * z.im) ≤ M * Real.exp (τ * |z.im|) * Real.exp (-τ * z.im) := by
        gcongr
    _ = M * Real.exp (τ * |z.im| + -τ * z.im) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ M * Real.exp (2 * τ * |a|) := by
        have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
        gcongr

/-- `f(z) e^{-iτz}` is bounded on every lower half-plane `ℂ⁻_a = {Im z ≤ a}` (p. 403). -/
theorem MemBernstein.norm_mul_cexp_le_of_im_le (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) (a : ℝ) {z : ℂ} (hz : z.im ≤ a) :
    ‖f z * Complex.exp (-(I * τ * z))‖ ≤ M * Real.exp (2 * τ * |a|) := by
  have := (hf.comp_neg).norm_mul_cexp_le_of_le_im hτ (fun x ↦ by simpa using hM (-x)) (-a)
    (z := -z) (by simpa using hz)
  simpa using this

/-! ### Complex translations -/

/-- Translation by any `c ∈ ℂ` maps `𝓑_τ` into itself. -/
theorem MemBernstein.comp_sub (hf : MemBernstein τ f) (hτ : 0 ≤ τ) (c : ℂ) :
    MemBernstein τ (fun z ↦ f (z - c)) := by
  obtain ⟨M, -, hM⟩ := hf.exists_bound
  exact ⟨hf.1.comp (differentiable_id.sub_const c), hf.2.1.comp_sub c,
    ⟨M * Real.exp (τ * |c.im|), fun x ↦ by simpa using hf.norm_le hτ hM ((x : ℂ) - c)⟩⟩

/-- The bound on `ℝ` of a translate: `|f(x - c)| ≤ M e^{τ|Im c|}`. -/
theorem MemBernstein.norm_comp_sub_le (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) (c : ℂ) (x : ℝ) : ‖f ((x : ℂ) - c)‖ ≤ M * Real.exp (τ * |c.im|) := by
  simpa using hf.norm_le hτ hM ((x : ℂ) - c)

/-- Vertical shifts: `|f(x - i a)| ≤ M e^{τ|a|}` on `ℝ`. -/
theorem MemBernstein.norm_comp_sub_I_mul_le (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) (a x : ℝ) : ‖f ((x : ℂ) - I * a)‖ ≤ M * Real.exp (τ * |a|) := by
  simpa using hf.norm_comp_sub_le hτ hM (I * a) x

/-! ### Derivatives -/

/-- Cauchy estimate on the unit circle: `|f'(z)| ≤ M e^{τ} e^{τ|Im z|}`. -/
theorem MemBernstein.norm_deriv_le (hf : MemBernstein τ f) (hτ : 0 ≤ τ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖f x‖ ≤ M) (z : ℂ) :
    ‖deriv f z‖ ≤ M * Real.exp τ * Real.exp (τ * |z.im|) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hf.1.diffContOnCl (c := z)
    (C := M * Real.exp τ * Real.exp (τ * |z.im|)) fun w hw ↦ ?_
  · simpa using this
  · refine (hf.norm_le hτ hM w).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    have h1 : |w.im| ≤ 1 + |z.im| := by
      have h2 := Complex.abs_im_le_norm (w - z)
      rw [sub_im, ← Complex.dist_eq, mem_sphere.1 hw] at h2
      linarith [abs_sub_abs_le_abs_sub w.im z.im]
    gcongr
    nlinarith

theorem MemBernstein.memBernstein_deriv (hf : MemBernstein τ f) (hτ : 0 ≤ τ) :
    MemBernstein τ (deriv f) := by
  obtain ⟨M, -, hM⟩ := hf.exists_bound
  have hd : Differentiable ℂ (deriv f) := fun z ↦ ((hf.1.analyticAt z).deriv).differentiableAt
  exact memBernstein_of_norm_le hd hτ (M := M * Real.exp τ) fun z ↦ hf.norm_deriv_le hτ hM z

/-! ### Completeness (p. 401) -/

/-- **`𝓑_τ` is complete for the sup norm on `ℝ`.**  A sequence in `𝓑_τ` that is uniformly Cauchy
on `ℝ` converges, in the weighted norm `sup_ℂ |·| e^{-τ|Im z|}`, to some `f ∈ 𝓑_τ`. -/
theorem MemBernstein.exists_tendsto_of_cauchy {F : ℕ → ℂ → ℂ} (hτ : 0 ≤ τ)
    (hF : ∀ n, MemBernstein τ (F n))
    (hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ x : ℝ, ‖F m x - F n x‖ ≤ ε) :
    ∃ f, MemBernstein τ f ∧
      ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z : ℂ, ‖F n z - f z‖ ≤ ε * Real.exp (τ * |z.im|) := by
  -- the Cauchy bound extends to `ℂ` (Phragmén–Lindelöf for `F m - F n`)
  have hCz : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ z : ℂ,
      ‖F m z - F n z‖ ≤ ε * Real.exp (τ * |z.im|) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    exact ⟨N, fun m hm n hn z ↦ ((hF m).sub (hF n)).norm_le hτ (hN m hm n hn) z⟩
  -- pointwise limits
  have hcs : ∀ z, CauchySeq (fun n ↦ F n z) := by
    intro z
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hCz (ε / 2 / Real.exp (τ * |z.im|)) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [dist_eq_norm]
    calc ‖F n z - F N z‖ ≤ ε / 2 / Real.exp (τ * |z.im|) * Real.exp (τ * |z.im|) :=
          hN n hn N le_rfl z
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε
  choose f hf using fun z ↦ cauchySeq_tendsto_of_complete (hcs z)
  have hlim : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z : ℂ, ‖F n z - f z‖ ≤ ε * Real.exp (τ * |z.im|) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hCz ε hε
    refine ⟨N, fun n hn z ↦ ?_⟩
    have ht : Tendsto (fun m ↦ ‖F n z - F m z‖) atTop (𝓝 ‖F n z - f z‖) :=
      ((hf z).const_sub (F n z)).norm
    exact le_of_tendsto ht (eventually_atTop.2 ⟨N, fun m hm ↦ hN n hn m hm z⟩)
  -- `f` is entire: the convergence is locally uniform
  have hTLU : TendstoLocallyUniformlyOn F f atTop univ := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x _
    refine ⟨ball x 1, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x one_pos), ?_⟩
    set K := Real.exp (τ * (|x.im| + 1)) with hK
    have hK0 : K ≠ 0 := by rw [hK]; positivity
    obtain ⟨N, hN⟩ := hlim (ε / 2 / K) (by positivity)
    filter_upwards [eventually_ge_atTop N] with n hn y hy
    rw [dist_eq_norm, norm_sub_rev]
    have hy1 : |y.im| ≤ |x.im| + 1 := by
      have h2 := Complex.abs_im_le_norm (y - x)
      rw [sub_im, ← Complex.dist_eq] at h2
      linarith [abs_sub_abs_le_abs_sub y.im x.im, mem_ball.1 hy]
    calc ‖F n y - f y‖ ≤ ε / 2 / K * Real.exp (τ * |y.im|) := hN n hn y
      _ ≤ ε / 2 / K * K := by
          rw [hK]
          gcongr
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε
  have hfd : Differentiable ℂ f := by
    rw [← differentiableOn_univ]
    exact hTLU.differentiableOn (Eventually.of_forall fun n ↦ (hF n).1.differentiableOn)
      isOpen_univ
  -- `f ∈ 𝓑_τ`
  obtain ⟨N, hN⟩ := hlim 1 one_pos
  obtain ⟨M, -, hM⟩ := (hF N).exists_bound
  refine ⟨f, memBernstein_of_norm_le hfd hτ (M := M + 1) fun z ↦ ?_, hlim⟩
  calc ‖f z‖ ≤ ‖F N z‖ + ‖F N z - f z‖ := norm_le_insert (F N z) (f z)
    _ ≤ M * Real.exp (τ * |z.im|) + 1 * Real.exp (τ * |z.im|) :=
        add_le_add ((hF N).norm_le hτ hM z) (hN N le_rfl z)
    _ = (M + 1) * Real.exp (τ * |z.im|) := by ring

end OCS
