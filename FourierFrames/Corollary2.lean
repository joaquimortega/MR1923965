import FourierFrames.Construction
import FourierFrames.Perturbation
import FourierFrames.Theorem1.Sufficiency
import FourierFrames.HB.Comparable
import FourierFrames.Corollary2.Affine
import FourierFrames.Corollary2.Kernel
import FourierFrames.Corollary2.Density
import FourierFrames.Corollary2.LogInt
import FourierFrames.Corollary2.Reflection
import FourierFrames.Corollary2.PotC

/-!
# M07 — Corollary 2 (p. 800)

See `blueprint/M07_Corollary2.md`, §3.

`Λ(ψ)` is sampling if there is `f ∈ \overline{HB}` with `φ_f' → 0` and `U_ψ - log|f| = O(1)` on
`Im z ≥ 0`.  Proof: with `ω' = 1 + ψ' - φ_f'/π` (modified on a compact set to be `≃ 1`), the
construction of `Construction.lean` gives `E ∈ \overline{HB}` with `|E| ≃ e^{π Im z}` and
`φ_E + φ_f = π(x + ψ(x)) + c + o(1)`; the zero set of `E f + E^* f^*` is sampling by
`theorem1_sufficiency` and is a perturbation (`IsSampling.of_perturbation`) of `Λ(ψ)`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## Rotating `E` by a unimodular constant -/

section Rotation

theorem phaseDeriv_rotate (E : ℂ → ℂ) (β : ℝ) (x : ℝ) :
    phaseDeriv (fun z ↦ Complex.exp (Complex.I * β) * E z) x = phaseDeriv E x := by
  unfold phaseDeriv
  rw [deriv_const_mul_field']
  have h : Complex.exp (Complex.I * β) ≠ 0 := Complex.exp_ne_zero _
  rw [mul_div_mul_left _ _ h]

end Rotation

/-! ## The potentials `U_g = OCS.multU g 0` of bounded densities -/

section Potentials

/-- `U_ψ` is the potential `OCS.multU` of the density `ψ'` (same integrand, constant `0`). -/
theorem UPsi_eq_multU (ψ : ℝ → ℝ) (z : ℂ) : UPsi ψ z = OCS.multU (deriv ψ) 0 z := by
  simp [UPsi, OCS.multU]

/-- The integrand of `multU` is integrable for every bounded measurable density (for weights this is
`OCS.integrable_multUIntegrand`; a bounded `g` is `(g + K) - K` with `g + K ≥ 1`). -/
theorem integrable_multU_integrand_of_bdd {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ t, |g t| ≤ M) (z : ℂ) :
    Integrable fun t : ℝ ↦
      (Real.log ‖1 - z / t‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).re) * g t :=
  integrable_potKernel_mul hg hM z

theorem multU_add {g h : ℝ → ℝ} (hg : Measurable g) (hh : Measurable h) {M : ℝ}
    (hgM : ∀ t, |g t| ≤ M) (hhM : ∀ t, |h t| ≤ M) (z : ℂ) :
    OCS.multU (fun t ↦ g t + h t) 0 z = OCS.multU g 0 z + OCS.multU h 0 z := by
  simp only [multU_eq_integral, mul_add]
  exact integral_add (integrable_potKernel_mul hg hgM z) (integrable_potKernel_mul hh hhM z)

theorem multU_const_mul {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) (c : ℝ)
    (z : ℂ) : OCS.multU (fun t ↦ c * g t) 0 z = c * OCS.multU g 0 z := by
  have _ := hg
  have _ := hM
  simp only [multU_eq_integral]
  rw [← integral_const_mul]
  congr 1; funext t; ring

/-- The potential of Lebesgue measure: `U_1(z) = π |Im z|`.  (Compute
`∫_{-T}^{T} log|1 - z/t| dt` with the antiderivative of `½ log(u² + y²)` and let `T → ∞`;
the odd term `Re(z/t)` integrates to `0` over `[-T, T] ∖ [-1, 1]`.) -/
theorem multU_one (z : ℂ) : OCS.multU (fun _ ↦ (1 : ℝ)) 0 z = Real.pi * |z.im| := by
  sorry

/-- Growth of potentials of bounded densities. -/
theorem abs_multU_le_of_bdd {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    ∃ K : ℝ, ∀ z : ℂ, |OCS.multU g 0 z| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
  refine ⟨45 * M, fun z ↦ ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  calc |OCS.multU g 0 z| ≤ M * potBound z := abs_multU_le_potBound hg hM z
    _ ≤ M * (45 * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by gcongr; exact potBound_le z
    _ = 45 * M * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by ring

/-- Potential of a compactly supported bounded density of total mass `0`: bounded up to the linear
term `(∫_{|t| > 1} h(t)/t dt) Re z` coming from the `Re(z/t)` normalisation. -/
theorem multU_compact_sub_linear {h : ℝ → ℝ} (hh : Measurable h) {M R : ℝ}
    (hM : ∀ t, |h t| ≤ M) (hR : ∀ t, R < |t| → h t = 0) (h0 : ∫ t, h t = 0) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU h 0 z - (∫ t, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (h t / t)) * z.re| ≤ C := by
  obtain ⟨C, hC⟩ := multU_compact_aux hh hM hR h0
  exact ⟨C, fun z _ ↦ hC z⟩

end Potentials

/-! ## `log|f|` is the potential of `φ_f'/π` up to an affine function -/

section LogPotential

/-- Continuity of the potential of a bounded density. -/
theorem continuous_multU_of_bdd {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    Continuous (OCS.multU g 0) := by
  sorry

/-- The boundary-continuous argument: for `t < 0` the number `1 - z/t` has `Im ≥ 0` when
`Im z ≥ 0` and we take `arg ∈ [0, π]`; for `t > 0` it has `Im ≤ 0` and we take
`-arg (conj (1 - z/t)) ∈ [-π, 0]`.  This is the branch of `Im Log(1 - z/t)` continuous on
`Im z ≥ 0`, `z ≠ t`. -/
def argUp (z : ℂ) (t : ℝ) : ℝ :=
  if t < 0 then Complex.arg (1 - z / t) else -Complex.arg (conj (1 - z / t))

/-- The complex potential `Q_g(z) = ∫ [log|1 - z/t| + i argUp z t + 1_{|t|>1} z/t] g(t) dt`
(`= ∫ [Log(1 - z/t) + 1_{|t|>1} z/t] g(t) dt` on `Im z > 0`; `π P = Q_g`). -/
def potC (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (((Real.log ‖1 - z / t‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).re : ℝ) : ℂ) +
    Complex.I * ((argUp z t + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).im : ℝ) : ℂ)) *
      (g t : ℂ)

theorem potC_re {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) (z : ℂ) :
    (potC g z).re = OCS.multU g 0 z := by
  exact potC'_re hg hM z

theorem differentiableOn_potC {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    DifferentiableOn ℂ (potC g) {z : ℂ | 0 < z.im} := by
  sorry

theorem continuousOn_potC {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    ContinuousOn (potC g) {z : ℂ | 0 ≤ z.im} := by
  sorry

/-- On the real axis `Im Q_g(x) = -π (φ(x) - φ(0))` when `φ' = g`
(`argUp x t = -π` for `0 < t < x` or `x < t < 0` with sign `±`, and `0` otherwise). -/
theorem potC_im_ofReal {g φ : ℝ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ t, |g t| ≤ M)
    (hφ : ∀ x, HasDerivAt φ (g x) x) (x : ℝ) :
    (potC g (x : ℂ)).im = -Real.pi * (φ x - φ 0) := by
  exact potC'_im_ofReal hg hM hφ x

/-- **Schwarz reflection** (via Morera on discs and the rectangle theorem for functions continuous
on a closed half-disc): `H` continuous on `Im z ≥ 0`, holomorphic on `Im z > 0`, with `Im H = c`
on `ℝ`, extends to an entire function with `H(z̄) = conj H(z) + 2ic`... precisely
`H^ext(z) = conj (H (conj z)) + 2 i c` for `Im z < 0`. -/
theorem exists_entire_reflection {H : ℂ → ℂ} (hc : ContinuousOn H {z : ℂ | 0 ≤ z.im})
    (hd : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) {c : ℝ} (him : ∀ x : ℝ, (H x).im = c) :
    ∃ Ĥ : ℂ → ℂ, Differentiable ℂ Ĥ ∧ (∀ z : ℂ, 0 ≤ z.im → Ĥ z = H z) ∧
      ∀ z : ℂ, Ĥ (conj z) = conj (Ĥ z) + 2 * Complex.I * c := by
  exact exists_entire_reflection_aux hc hd him

/-- An entire function whose real part grows like `|z|^{3/2}` is affine
(Borel–Carathéodory, then Cauchy's estimate for `H''`). -/
theorem entire_affine_of_re_growth {H : ℂ → ℂ} (hH : Differentiable ℂ H) {K : ℝ}
    (hK : ∀ z : ℂ, |(H z).re| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ)) :
    ∃ α β : ℂ, ∀ z : ℂ, H z = α + β * z := by
  obtain ⟨C, hC0, hC⟩ := norm_le_of_re_growth hH hK
  have hH' : Differentiable ℂ (deriv H) := hH.deriv
  -- bound on the derivative
  have hder : ∀ R : ℝ, 1 ≤ R → ∀ w : ℂ, ‖w‖ ≤ 2 * R →
      ‖deriv H w‖ ≤ C * (3 * R) ^ (3 / 2 : ℝ) / R := by
    intro R hR w hw
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith) hH.diffContOnCl
      (fun u hu ↦ ?_)
    have hu' : ‖u - w‖ = R := by simpa [dist_eq_norm] using hu
    have : ‖u‖ ≤ 3 * R := by
      calc ‖u‖ = ‖(u - w) + w‖ := by ring_nf
        _ ≤ ‖u - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ 3 * R := by linarith
    exact hC (3 * R) (by linarith) u this
  have hsecond : ∀ c : ℂ, deriv (deriv H) c = 0 := by
    intro c
    have hbound : ∀ R : ℝ, 1 + ‖c‖ ≤ R → ‖deriv (deriv H) c‖ ≤ C * 3 ^ (3 / 2 : ℝ) / Real.sqrt R := by
      intro R hR
      have hR1 : 1 ≤ R := by linarith [norm_nonneg c]
      have hRpos : 0 < R := by linarith
      refine (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hH'.diffContOnCl
        (C := C * (3 * R) ^ (3 / 2 : ℝ) / R) (fun u hu ↦ ?_)).trans ?_
      · have hu' : ‖u - c‖ = R := by simpa [dist_eq_norm] using hu
        refine hder R hR1 u ?_
        calc ‖u‖ = ‖(u - c) + c‖ := by ring_nf
          _ ≤ ‖u - c‖ + ‖c‖ := norm_add_le _ _
          _ ≤ 2 * R := by linarith
      · have hsq : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hRpos.le
        have hsqpos : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRpos
        have h32 : R ^ (3 / 2 : ℝ) = R * Real.sqrt R := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hRpos.le (by norm_num)]
          norm_num
        rw [Real.mul_rpow (by norm_num) hRpos.le, h32]
        have : C * (3 ^ (3 / 2 : ℝ) * (R * Real.sqrt R)) / R / R = C * 3 ^ (3 / 2 : ℝ) / Real.sqrt R := by
          field_simp
          nlinarith [hsq]
        rw [this]
    have hlim : Tendsto (fun R : ℝ ↦ C * 3 ^ (3 / 2 : ℝ) / Real.sqrt R) atTop (𝓝 0) := by
      have : Tendsto (fun R : ℝ ↦ Real.sqrt R) atTop atTop := by
        simpa [Real.sqrt_eq_rpow] using tendsto_rpow_atTop (show (0:ℝ) < 1 / 2 by norm_num)
      exact this.const_div_atTop _ |>.congr' (by filter_upwards with R; rfl)
    have := ge_of_tendsto hlim (eventually_atTop.mpr ⟨1 + ‖c‖, fun R hR ↦ hbound R hR⟩)
    exact norm_le_zero_iff.mp this
  have hconst : ∀ z, deriv H z = deriv H 0 := fun z ↦
    is_const_of_deriv_eq_zero hH' hsecond z 0
  refine ⟨H 0, deriv H 0, fun z ↦ ?_⟩
  have h2 : Differentiable ℂ (fun z ↦ H z - deriv H 0 * z) := hH.sub (differentiable_const _ |>.mul differentiable_id)
  have h3 : ∀ z, deriv (fun z ↦ H z - deriv H 0 * z) z = 0 := fun z ↦ by
    have hd : HasDerivAt (fun z ↦ H z - deriv H 0 * z) (deriv H z - deriv H 0 * 1) z :=
      (hH z).hasDerivAt.sub ((hasDerivAt_id z).const_mul _)
    rw [hd.deriv, hconst z]; ring
  have := is_const_of_deriv_eq_zero h2 h3 z 0
  simp at this
  linear_combination this

/-- **Key identity** (the harmonic correction is affine).  Let `f` be entire without zeros on
`Im z ≥ 0` with phase function `φ`, `φ' = g` continuous and bounded, and `|log|f|| ≲ (1+|z|)^{3/2}`
on `Im z ≥ 0`.  Then `log|f| = U_g/π + b Re z + c` on `Im z ≥ 0` for real `b, c`.

Proof (blueprint §3.2): `P(z) = (1/π) ∫ [Log(1 - z/t) + 1_{|t|>1} z/t] g(t) dt` is holomorphic on
`Im z > 0`, continuous on `Im z ≥ 0`, `Re P = U_g/π`, `Im P(x) = -(φ(x) - φ(0))`; a holomorphic
logarithm `L` of `f` on `Im z ≥ 0` has `Im L(x) = -φ(x) + const`; so `H = L - P` has constant
imaginary part on `ℝ`, extends by Schwarz reflection to an entire function with
`|Re H| ≲ (1 + |z|)^{3/2}`; Borel–Carathéodory and Cauchy's estimates give `H(z) = α + β z`,
`β` real. -/
theorem log_norm_eq_multU_add_affine {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : ∀ z : ℂ, 0 ≤ z.im → f z ≠ 0) {φ g : ℝ → ℝ} (hφ : IsPhaseFunction f φ)
    (hφ' : ∀ x, HasDerivAt φ (g x) x) (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    (hgrow : ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |Real.log ‖f z‖| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ)) :
    ∃ b c : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.log ‖f z‖ = OCS.multU g 0 z / Real.pi + b * z.re + c := by
  sorry

end LogPotential

/-! ## The density `m` and the phase comparison -/

section Density

/-- **Modification on a compact set.**  Given a continuous `w → 0` and `β ∈ ℝ`, there are `R > 0`
and a measurable `m` with `a ≤ m ≤ b`, `m = 1 + w` for `|t| > R`, `∫ (m - 1 - w) = 0` and
`∫_{|t|>1} (m - 1 - w)(t)/t dt = -β`.  (Take `m = c + s sgn(t) 1_{1<|t|<R}` on `[-R, R]` with
`c = (2R)⁻¹ ∫_{-R}^{R} (1 + w)`, `s = (-β + ∫_{1<|t|<R} (1+w)/t) / (2 log R)`.) -/
theorem exists_modified_density {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : Tendsto w (cocompact ℝ) (𝓝 0)) (β : ℝ) :
    ∃ (R : ℝ) (m : ℝ → ℝ) (a b : ℝ), 0 < R ∧ 0 < a ∧ Measurable m ∧ (∀ t, a ≤ m t) ∧
      (∀ t, m t ≤ b) ∧ (∀ t, R < |t| → m t = 1 + w t) ∧
      (∫ t, (m t - (1 + w t)) = 0) ∧
      (∫ t, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * ((m t - (1 + w t)) / t)) = -β := by
  obtain ⟨B, hB⟩ := bounded_of_tendsto_cocompact hw hw0
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hwm : Measurable w := hw.measurable
  set P : ℝ → ℝ := fun R ↦ ∫ t in Icc (-R) R, rho t with hPdef
  set A : ℝ → ℝ := fun R ↦ ∫ t in Icc (-R) R, rho t * (sig t * w t) with hAdef
  set W : ℝ → ℝ := fun R ↦ ∫ t in Icc (-R) R, w t with hWdef
  have hPt : Tendsto P atTop atTop := rho_tendsto
  have hPpos : ∀ᶠ R in atTop, 0 < P R := hPt.eventually (eventually_gt_atTop 0)
  -- Cesàro for `w`
  have hW : Tendsto (fun R ↦ W R / (2 * R)) atTop (𝓝 0) := by
    have := weighted_cesaro (ρ := fun _ ↦ (1 : ℝ)) (u := w) (fun _ ↦ zero_le_one)
      (fun R ↦ integrableOn_const (by simp)) hwm hB hw0
      (by
        refine tendsto_atTop_mono' atTop (eventually_atTop.mpr ⟨0, fun R hR ↦ ?_⟩)
          (tendsto_id.const_mul_atTop (show (0:ℝ) < 2 by norm_num))
        simp only [setIntegral_const, smul_eq_mul, mul_one, id,
          Real.volume_real_Icc_of_le (by linarith : -R ≤ R)]
        linarith)
    refine this.congr' (eventually_atTop.mpr ⟨0, fun R hR ↦ ?_⟩)
    simp only [setIntegral_const, smul_eq_mul, mul_one, one_mul, Real.volume_real_Icc_of_le (by linarith : -R ≤ R)]
    simp only [hWdef]
    ring_nf
  -- Cesàro for `σ w` against `ρ`
  have hA : Tendsto (fun R ↦ A R / P R) atTop (𝓝 0) := by
    refine weighted_cesaro (ρ := rho) (u := fun t ↦ sig t * w t) rho_nonneg integrableOn_rho
      (measurable_sig.mul hwm) (B := B) (fun t ↦ ?_) ?_ rho_tendsto
    · rw [abs_mul]
      calc |sig t| * |w t| ≤ 1 * B := by gcongr; exact abs_sig_le t; exact hB t
        _ = B := one_mul B
    · refine squeeze_zero_norm (a := fun t ↦ ‖w t‖) (fun t ↦ ?_) (by simpa using hw0.norm)
      rw [norm_mul]
      calc ‖sig t‖ * ‖w t‖ ≤ 1 * ‖w t‖ := by
            gcongr; simpa using abs_sig_le t
        _ = _ := one_mul _
  have hs : Tendsto (fun R ↦ (A R - β) / P R) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R ↦ β / P R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hPt
    have := hA.sub h1
    simp only [sub_zero] at this
    refine this.congr' (hPpos.mono fun R hR ↦ ?_)
    field_simp
  -- eventually good `R`
  have hX : ∃ X : ℝ, ∀ t, X ≤ |t| → |w t| ≤ 1 / 4 := by
    have h1 : {t : ℝ | |w t| < 1 / 4} ∈ cocompact ℝ := by
      have := hw0.eventually (Metric.ball_mem_nhds 0 (show (0:ℝ) < 1 / 4 by norm_num))
      filter_upwards [this] with t ht
      simpa using ht
    obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.mp h1
    obtain ⟨X, hX⟩ := hK.isBounded.subset_closedBall 0
    refine ⟨|X| + 1, fun t ht ↦ ?_⟩
    have : t ∉ K := fun h ↦ by
      have := hX h
      simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      linarith [le_abs_self X, abs_nonneg X]
    exact (hKs this).le
  obtain ⟨X, hX⟩ := hX
  have hgood : ∀ᶠ R in atTop, 1 < R ∧ |W R / (2 * R)| ≤ 1 / 4 ∧ 0 < P R ∧
      |(A R - β) / P R| ≤ 1 / 8 ∧ X ≤ R := by
    have e1 := eventually_gt_atTop (1 : ℝ)
    have e2 := (Metric.tendsto_nhds.mp hW) (1 / 4) (by norm_num)
    have e3 := (Metric.tendsto_nhds.mp hs) (1 / 8) (by norm_num)
    have e4 := eventually_ge_atTop X
    filter_upwards [e1, e2, hPpos, e3, e4] with R h1 h2 h3 h4 h5
    refine ⟨h1, ?_, h3, ?_, h5⟩
    · rw [Real.dist_eq, sub_zero] at h2; exact h2.le
    · rw [Real.dist_eq, sub_zero] at h4; exact h4.le
  obtain ⟨R, hR1, hWc, hP, hsb, hXR⟩ := hgood.exists
  set c : ℝ := 1 + W R / (2 * R) with hc
  set s : ℝ := (A R - β) / P R with hsdef
  have hR0 : 0 < R := by linarith
  refine ⟨R, modDens w R c s, 5 / 8, 2 + B, hR0, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- measurable
    unfold modDens
    refine Measurable.ite (measurableSet_le measurable_id.abs measurable_const) ?_ ?_
    · exact measurable_const.add (measurable_const.mul measurable_sig)
    · exact measurable_const.add hwm
  · intro t
    unfold modDens
    split_ifs with h
    · have h1 := abs_sig_le t
      have h2 : |s| ≤ 1 / 8 := hsb
      have h3 : |W R / (2 * R)| ≤ 1 / 4 := hWc
      have h4 : |s * sig t| ≤ 1 / 8 := by
        rw [abs_mul]; calc |s| * |sig t| ≤ 1 / 8 * 1 := by gcongr
          _ = 1 / 8 := by norm_num
      have := abs_le.mp h4
      have := abs_le.mp h3
      linarith
    · push Not at h
      have := abs_le.mp (hX t (hXR.trans h.le))
      linarith
  · intro t
    unfold modDens
    split_ifs with h
    · have h1 := abs_sig_le t
      have h2 : |s| ≤ 1 / 8 := hsb
      have h3 : |W R / (2 * R)| ≤ 1 / 4 := hWc
      have h4 : |s * sig t| ≤ 1 / 8 := by
        rw [abs_mul]; calc |s| * |sig t| ≤ 1 / 8 * 1 := by gcongr
          _ = 1 / 8 := by norm_num
      have := abs_le.mp h4
      have := abs_le.mp h3
      linarith
    · have := (abs_le.mp (hB t)).2
      linarith
  · intro t ht
    unfold modDens
    simp only [not_le.mpr ht, ↓reduceIte]
  · refine integral_modDens_sub_zero hw hR0 ?_
    rw [hc]; field_simp; ring
  · refine integral_modDens_moment hw hB hR0 ?_
    show s * P R = A R - β
    rw [hsdef]; field_simp

/-- **Good density.**  Under the hypotheses of Corollary 2 and for a phase function `φ_f`, there
are a density `m` (`a ≤ m ≤ b`, `m → 1`) with `U_m - π Im z = O(1)` on `Im z ≥ 0` and a constant `κ`
with `π M(x) + φ_f(x) = π (x + ψ(x)) + κ` for `|x| ≥ R` (`M = OCS.multPrim m`). -/
theorem exists_good_density {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {f : ℂ → ℂ} (hf : IsHB f)
    (hφ : Tendsto (phaseDeriv f) (cocompact ℝ) (𝓝 0))
    (happ : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.exp (UPsi ψ z - C) ≤ ‖f z‖ ∧ ‖f z‖ ≤ Real.exp (UPsi ψ z + C))
    {φf : ℝ → ℝ} (hφf : IsPhaseFunction f φf) (hφf' : ∀ x, HasDerivAt φf (phaseDeriv f x) x) :
    ∃ (m : ℝ → ℝ) (a b κ R : ℝ), Measurable m ∧ 0 < a ∧ (∀ t, a ≤ m t) ∧ (∀ t, m t ≤ b) ∧
      Tendsto m (cocompact ℝ) (𝓝 1) ∧
      (∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → |OCS.multU m 0 z - Real.pi * z.im| ≤ C) ∧
      ∀ x : ℝ, R ≤ |x| → Real.pi * OCS.multPrim m x + φf x = Real.pi * (x + ψ x) + κ := by
  obtain ⟨C, hC⟩ := happ
  have hf0z : ∀ z : ℂ, 0 ≤ z.im → f z ≠ 0 := fun z hz h0 ↦ by
    have := (hC z hz).1
    rw [h0, norm_zero] at this
    exact absurd this (not_le.mpr (Real.exp_pos _))
  have hf0 : ∀ x : ℝ, f x ≠ 0 := fun x ↦ hf0z (x : ℂ) (by simp)
  set g : ℝ → ℝ := phaseDeriv f with hgdef
  have hgc : Continuous g := continuous_phaseDeriv hf.1 hf0
  obtain ⟨Mg, hMg⟩ := bounded_of_tendsto_cocompact hgc hφ
  set ψ' : ℝ → ℝ := deriv ψ with hψ'def
  have hψ'c : Continuous ψ' := hψ.1.continuous_deriv le_rfl
  obtain ⟨Mψ, hMψ⟩ := bounded_of_tendsto_cocompact hψ'c hψ.2.2.2
  have hψd : ∀ x, HasDerivAt ψ (ψ' x) x := fun x ↦
    ((hψ.1.differentiable one_ne_zero) x).hasDerivAt
  -- growth of `log |f|`
  have hgrow : ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.im → |Real.log ‖f z‖| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
    obtain ⟨K1, hK1⟩ := abs_multU_le_of_bdd hψ'c.measurable hMψ
    refine ⟨|K1| + |C|, fun z hz ↦ ?_⟩
    have hpos : 0 < ‖f z‖ := norm_pos_iff.mpr (hf0z z hz)
    have h1 := Real.log_le_log (Real.exp_pos _) (hC z hz).1
    have h2 := Real.log_le_log hpos (hC z hz).2
    rw [Real.log_exp] at h1 h2
    have hU : |UPsi ψ z| ≤ K1 * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
      rw [UPsi_eq_multU]; exact hK1 z
    have hX : 1 ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) :=
      Real.one_le_rpow (by linarith [norm_nonneg z]) (by norm_num)
    have : |Real.log ‖f z‖| ≤ |UPsi ψ z| + |C| := by
      rw [abs_le]; constructor <;> cases abs_cases (UPsi ψ z) <;> cases abs_cases C <;> linarith
    calc |Real.log ‖f z‖| ≤ K1 * (1 + ‖z‖) ^ (3 / 2 : ℝ) + |C| := this.trans (by linarith)
      _ ≤ (|K1| + |C|) * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
          nlinarith [le_abs_self K1, abs_nonneg C, abs_nonneg K1]
  obtain ⟨b₀, c₀, hlog⟩ := log_norm_eq_multU_add_affine hf.1 hf0z hφf hφf' hgc hMg hgrow
  -- the density
  set w : ℝ → ℝ := fun t ↦ ψ' t - g t / Real.pi with hwdef
  have hwc : Continuous w := hψ'c.sub (hgc.div_const _)
  have hw0 : Tendsto w (cocompact ℝ) (𝓝 0) := by
    have := hψ.2.2.2.sub (hφ.div_const Real.pi)
    simpa using this
  obtain ⟨R, m, a, b, hR, ha, hmeas, hlow, hup, hmw, hint0, hmom⟩ :=
    exists_modified_density hwc hw0 b₀
  obtain ⟨Bw, hBw⟩ := bounded_of_tendsto_cocompact hwc hw0
  set h : ℝ → ℝ := fun t ↦ m t - (1 + w t) with hhdef
  have hhm : Measurable h := hmeas.sub (measurable_const.add hwc.measurable)
  have hhb : ∀ t, |h t| ≤ b + 1 + Bw + 1 := fun t ↦ by
    have h1 := hlow t; have h2 := hup t; have h3 := hBw t
    have := abs_le.mp h3
    rw [abs_le]; simp only [hhdef]; constructor <;> linarith
  have hhR : ∀ t, R < |t| → h t = 0 := fun t ht ↦ by simp [hhdef, hmw t ht]
  have hπ : 0 < Real.pi := Real.pi_pos
  -- `m` as a sum
  have hm_eq : ∀ t, m t = ((1 + ψ' t) + (-(1 / Real.pi)) * g t) + h t := fun t ↦ by
    simp only [hhdef, hwdef]; ring
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  have hMψ0 : 0 ≤ Mψ := (abs_nonneg _).trans (hMψ 0)
  have hMh0 : 0 ≤ b + 1 + Bw + 1 := (abs_nonneg _).trans (hhb 0)
  set Mall : ℝ := 1 + Mψ + Mg + (b + 1 + Bw + 1) with hMall
  have hπ1 : 1 / Real.pi ≤ 1 := by rw [div_le_one hπ]; linarith [Real.pi_gt_three]
  have hu1 : ∀ t : ℝ, |(1 : ℝ)| ≤ Mall := fun t ↦ by simp only [abs_one, hMall]; linarith
  have hu2 : ∀ t, |ψ' t| ≤ Mall := fun t ↦ (hMψ t).trans (by simp only [hMall]; linarith)
  have hu3' : ∀ t, |(-(1 / Real.pi)) * g t| ≤ Mg := fun t ↦ by
    rw [abs_mul, abs_neg, abs_of_pos (by positivity)]
    calc 1 / Real.pi * |g t| ≤ 1 * Mg := by gcongr; exact hMg t
      _ = Mg := one_mul _
  have hu3 : ∀ t, |(-(1 / Real.pi)) * g t| ≤ Mall := fun t ↦
    (hu3' t).trans (by simp only [hMall]; linarith)
  have hu4 : ∀ t, |h t| ≤ Mall := fun t ↦ (hhb t).trans (by simp only [hMall]; linarith)
  have hu12' : ∀ t, |1 + ψ' t| ≤ 1 + Mψ := fun t ↦ by
    calc |1 + ψ' t| ≤ |(1 : ℝ)| + |ψ' t| := abs_add_le _ _
      _ ≤ 1 + Mψ := by rw [abs_one]; linarith [hMψ t]
  have hu12 : ∀ t, |1 + ψ' t| ≤ Mall := fun t ↦
    (hu12' t).trans (by simp only [hMall]; linarith)
  have hu123 : ∀ t, |(1 + ψ' t) + (-(1 / Real.pi)) * g t| ≤ Mall := fun t ↦ by
    calc |(1 + ψ' t) + (-(1 / Real.pi)) * g t| ≤ |1 + ψ' t| + |(-(1 / Real.pi)) * g t| :=
          abs_add_le _ _
      _ ≤ (1 + Mψ) + Mg := add_le_add (hu12' t) (hu3' t)
      _ ≤ Mall := by simp only [hMall]; linarith
  have hsplit : ∀ z : ℂ, OCS.multU m 0 z = OCS.multU (fun _ ↦ (1 : ℝ)) 0 z + OCS.multU ψ' 0 z
      + (-(1 / Real.pi)) * OCS.multU g 0 z + OCS.multU h 0 z := by
    intro z
    have hmf : m = fun t ↦ ((1 + ψ' t) + (-(1 / Real.pi)) * g t) + h t := funext hm_eq
    have e1 := multU_add (g := fun t ↦ (1 + ψ' t) + (-(1 / Real.pi)) * g t) (h := h)
      ((measurable_const.add hψ'c.measurable).add (measurable_const.mul hgc.measurable)) hhm hu123 hu4 z
    have e2 := multU_add (g := fun t ↦ 1 + ψ' t) (h := fun t ↦ (-(1 / Real.pi)) * g t)
      (measurable_const.add hψ'c.measurable) (measurable_const.mul hgc.measurable) hu12 hu3 z
    have e3 := multU_add (g := fun _ ↦ (1 : ℝ)) (h := ψ') measurable_const hψ'c.measurable hu1 hu2 z
    have e4 := multU_const_mul hgc.measurable hMg (-(1 / Real.pi)) z
    beta_reduce at e1 e2 e3
    rw [hmf, e1, e2, e3, e4]
  -- the potential
  obtain ⟨Ch, hCh⟩ := multU_compact_sub_linear hhm hhb hhR hint0
  have hmom' : (∫ t, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (h t / t)) = -b₀ := hmom
  have hpot : ∃ C' : ℝ, ∀ z : ℂ, 0 ≤ z.im → |OCS.multU m 0 z - Real.pi * z.im| ≤ C' := by
    refine ⟨C + |c₀| + Ch, fun z hz ↦ ?_⟩
    rw [hsplit z, multU_one, abs_of_nonneg hz, ← UPsi_eq_multU]
    have h1 := hlog z hz
    have h2 := hCh z hz
    rw [hmom'] at h2
    have h3 := (hC z hz)
    have hpos : 0 < ‖f z‖ := norm_pos_iff.mpr (hf0z z hz)
    have h4 := Real.log_le_log (Real.exp_pos _) h3.1
    have h5 := Real.log_le_log hpos h3.2
    rw [Real.log_exp] at h4 h5
    have e : OCS.multU g 0 z = Real.pi * (Real.log ‖f z‖ - b₀ * z.re - c₀) := by
      rw [h1]; field_simp; ring
    rw [e]
    have : -(1 / Real.pi) * (Real.pi * (Real.log ‖f z‖ - b₀ * z.re - c₀)) =
        -(Real.log ‖f z‖) + b₀ * z.re + c₀ := by field_simp; ring
    have hexp : Real.pi * z.im + UPsi ψ z + -(1 / Real.pi) * (Real.pi * (Real.log ‖f z‖ - b₀ * z.re - c₀)) +
        OCS.multU h 0 z - Real.pi * z.im =
        (UPsi ψ z - Real.log ‖f z‖) + c₀ + (OCS.multU h 0 z - -b₀ * z.re) := by
      rw [this]; ring
    rw [hexp]
    have h6 := abs_le.mp h2
    rw [abs_le]
    constructor <;> cases abs_cases c₀ <;> linarith [abs_nonneg c₀, h6.1, h6.2]
  obtain ⟨C', hC'⟩ := hpot
  -- limit
  have hlim : Tendsto m (cocompact ℝ) (𝓝 1) := by
    have h1 : Tendsto (fun t ↦ 1 + w t) (cocompact ℝ) (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hw0
    refine h1.congr' ?_
    have hev : ∀ᶠ t : ℝ in cocompact ℝ, R < |t| :=
      (tendsto_norm_cocompact_atTop (E := ℝ)).eventually (eventually_gt_atTop R)
    filter_upwards [hev] with t ht
    exact (hmw t ht).symm
  -- phase
  have hhint := intervalIntegrable_of_abs_le hhm hhb
  have h1int : ∀ x y : ℝ, IntervalIntegrable (fun t : ℝ ↦ 1 + w t) volume x y := fun x y ↦
    (continuous_const.add hwc).intervalIntegrable x y
  have hmsplit : ∀ t, m t = (1 + w t) + h t := fun t ↦ by simp only [hhdef]; ring
  refine ⟨m, a, b, -Real.pi * ψ 0 + φf 0 + Real.pi * ∫ t in (0 : ℝ)..R, h t, R, hmeas, ha, hlow, hup,
    hlim, ⟨C', hC'⟩, fun x hx ↦ ?_⟩
  have hx0 := integral_zero_of_mass_zero hhm hhb hR.le hhR hint0 hx
  have hψint : ∫ t in (0 : ℝ)..x, ψ' t = ψ x - ψ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hψd t) (hψ'c.intervalIntegrable _ _)
  have hφint : ∫ t in (0 : ℝ)..x, g t = φf x - φf 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hφf' t) (hgc.intervalIntegrable _ _)
  have hwint : ∫ t in (0 : ℝ)..x, (1 + w t) = x + (ψ x - ψ 0) - (φf x - φf 0) / Real.pi := by
    rw [intervalIntegral.integral_add (intervalIntegrable_const) (hwc.intervalIntegrable _ _)]
    simp only [hwdef]
    rw [intervalIntegral.integral_sub (hψ'c.intervalIntegrable _ _) ((hgc.div_const _).intervalIntegrable _ _),
      intervalIntegral.integral_div, hψint, hφint]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    ring
  have hM : OCS.multPrim m x = x + (ψ x - ψ 0) - (φf x - φf 0) / Real.pi + ∫ t in (0 : ℝ)..R, h t := by
    unfold OCS.multPrim
    simp_rw [hmsplit]
    rw [intervalIntegral.integral_add (h1int _ _) (hhint _ _), hwint, hx0]
  rw [hM]
  field_simp
  ring

end Density

/-! ## From the phase to a perturbation of `Λ(ψ)` -/

section PhasePerturbation

/-- `x ↦ x + ψ(x)` is a strictly increasing, `1`-expanding bijection of `ℝ`. -/
theorem strictMono_add_psi {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) :
    StrictMono (fun x ↦ x + ψ x) ∧ Function.Surjective (fun x ↦ x + ψ x) ∧
      ∀ x y : ℝ, x ≤ y → y - x ≤ (y + ψ y) - (x + ψ x) := by
  have hexp : ∀ x y : ℝ, x ≤ y → y - x ≤ (y + ψ y) - (x + ψ x) := fun x y hxy ↦ by
    have := hψ.2.1 hxy; linarith
  have hsm : StrictMono (fun x ↦ x + ψ x) := fun x y hxy ↦ by
    have := hexp x y hxy.le; simp only; linarith
  refine ⟨hsm, ?_, hexp⟩
  have hc : Continuous (fun x ↦ x + ψ x) := continuous_id.add hψ.1.continuous
  refine hc.surjective ?_ ?_
  · refine tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono fun y hy ↦ ?_)
      (tendsto_id.atTop_add (tendsto_const_nhds (x := ψ 0)))
    have := hψ.2.1 hy
    simp only [id]; linarith
  · refine tendsto_atBot_mono' atBot ((eventually_le_atBot 0).mono fun y hy ↦ ?_)
      (tendsto_id.atBot_add (tendsto_const_nhds (x := ψ 0)))
    have := hψ.2.1 hy
    simp only [id]; linarith

/-- **Matching the zero set with `Λ(ψ)`.**  Let `Θ` be a continuous strictly increasing bijection
of `ℝ` with `Θ(x)/π - (x + ψ(x)) → 0` as `|x| → ∞`.  Then `Λ(ψ) = {x + δ(x) : Θ(x) ∈ π ℤ}` for a
`δ` that is injective on `{Θ ∈ π ℤ}` and tends to `0` at infinity (`δ(x) = Ψ⁻¹(Θ(x)/π) - x`,
`Ψ(x) = x + ψ(x)`, with `|δ(x)| ≤ |Θ(x)/π - Ψ(x)|`). -/
theorem exists_perturbation_of_phase {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {Θ : ℝ → ℝ}
    (hΘ : StrictMono Θ) (hΘs : Function.Surjective Θ)
    (hlim : Tendsto (fun x ↦ Θ x / Real.pi - (x + ψ x)) (cocompact ℝ) (𝓝 0)) :
    ∃ δ : ℝ → ℝ, InjOn (fun x ↦ x + δ x) {x | ∃ k : ℤ, Θ x = k * Real.pi} ∧
      (fun x ↦ x + δ x) '' {x | ∃ k : ℤ, Θ x = k * Real.pi} = LambdaPsi ψ ∧
      Tendsto δ (cocompact ℝ) (𝓝 0) := by
  obtain ⟨hsm, hsurj, hexp⟩ := strictMono_add_psi hψ
  set Ψ : ℝ → ℝ := fun x ↦ x + ψ x with hΨ
  set Ψi : ℝ → ℝ := Function.surjInv hsurj with hΨi
  have h1 : ∀ y, Ψ (Ψi y) = y := Function.surjInv_eq hsurj
  have h2 : ∀ x, Ψi (Ψ x) = x := fun x ↦ hsm.injective (h1 (Ψ x))
  have hlt : ∀ a b : ℝ, a < b → Ψi a < Ψi b := fun a b hab ↦ by
    by_contra h
    push Not at h
    have := hsm.monotone h
    rw [h1, h1] at this
    linarith
  have hmono : Monotone Ψi := fun a b hab ↦ by
    rcases eq_or_lt_of_le hab with rfl | h
    · exact le_rfl
    · exact (hlt a b h).le
  have hlip : ∀ a b : ℝ, a ≤ b → Ψi b - Ψi a ≤ b - a := fun a b hab ↦ by
    have := hexp _ _ (hmono hab)
    have e1 := h1 a
    have e2 := h1 b
    simp only [hΨ] at e1 e2
    linarith
  have hΘ' : StrictMono fun x ↦ Θ x / Real.pi := fun x y h ↦
    div_lt_div_of_pos_right (hΘ h) Real.pi_pos
  have hcomp : StrictMono fun x ↦ Ψi (Θ x / Real.pi) := fun x y h ↦ hlt _ _ (hΘ' h)
  refine ⟨fun x ↦ Ψi (Θ x / Real.pi) - x, ?_, ?_, ?_⟩
  · intro x _ y _ h
    simp only [add_sub_cancel] at h
    exact hcomp.injective h
  · ext y
    simp only [mem_image, mem_ofPred_eq, add_sub_cancel, LambdaPsi]
    constructor
    · rintro ⟨x, ⟨k, hk⟩, rfl⟩
      refine ⟨k, ?_⟩
      have : Θ x / Real.pi = k := by rw [hk]; field_simp
      have := h1 (Θ x / Real.pi)
      rw [‹Θ x / Real.pi = k›] at this ⊢
      exact this
    · rintro ⟨k, hk⟩
      obtain ⟨x, hx⟩ := hΘs (k * Real.pi)
      refine ⟨x, ⟨k, hx⟩, ?_⟩
      have : Θ x / Real.pi = k := by rw [hx]; field_simp
      rw [this]
      have := h2 y
      rw [show Ψ y = k from hk] at this
      exact this
  · refine squeeze_zero_norm (a := fun x ↦ ‖Θ x / Real.pi - (x + ψ x)‖) (fun x ↦ ?_) (by simpa using hlim.norm)
    have e : Ψi (Θ x / Real.pi) - x = Ψi (Θ x / Real.pi) - Ψi (Ψ x) := by rw [h2]
    rw [e, Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total (Θ x / Real.pi) (Ψ x) with h | h
    · have := hlip _ _ h
      have h3 := hmono h
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by simp only [hΨ] at h; linarith)]
      simp only [hΨ] at this ⊢; linarith
    · have := hlip _ _ h
      have h3 := hmono h
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by simp only [hΨ] at h; linarith)]
      simp only [hΨ] at this ⊢; linarith


/-- If `Θ` is strictly increasing with `Θ(y) - Θ(x) ≤ C (y - x)` for `x ≤ y`, then `{Θ ∈ π ℤ}`
is separated (by `π / C`). -/
theorem isSeparated_levelSet {Θ : ℝ → ℝ} (hΘ : StrictMono Θ) {C : ℝ} (hC : 0 < C)
    (hlip : ∀ x y : ℝ, x ≤ y → Θ y - Θ x ≤ C * (y - x)) :
    IsSeparated {x | ∃ k : ℤ, Θ x = k * Real.pi} := by
  refine ⟨Real.pi / C, by positivity, ?_⟩
  have key : ∀ x y : ℝ, (∃ k : ℤ, Θ x = k * Real.pi) → (∃ k : ℤ, Θ y = k * Real.pi) → x < y →
      Real.pi / C ≤ |x - y| := by
    rintro x y ⟨k, hk⟩ ⟨l, hl⟩ hxy
    have h1 := hΘ hxy
    rw [hk, hl] at h1
    have h2 : (k : ℝ) < l := lt_of_mul_lt_mul_right h1 Real.pi_pos.le
    have h3 : (k : ℝ) + 1 ≤ l := by exact_mod_cast Int.add_one_le_iff.mpr (by exact_mod_cast h2)
    have h4 := hlip x y hxy.le
    rw [hk, hl] at h4
    have h5 : Real.pi ≤ C * (y - x) := by nlinarith [Real.pi_pos]
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    rw [div_le_iff₀ hC]; linarith
  rintro x ⟨k, hk⟩ y ⟨l, hl⟩ hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y ⟨k, hk⟩ ⟨l, hl⟩ h
  · rw [abs_sub_comm]; exact key y x ⟨l, hl⟩ ⟨k, hk⟩ h

/-- A derivative bound gives the Lipschitz bound (`image_sub_le_mul_sub_of_deriv_le`). -/
theorem sub_le_mul_sub_of_hasDerivAt {Θ d : ℝ → ℝ} (hΘ : ∀ x, HasDerivAt Θ (d x) x) {C : ℝ}
    (hd : ∀ x, d x ≤ C) {x y : ℝ} (hxy : x ≤ y) : Θ y - Θ x ≤ C * (y - x) :=
  image_sub_le_mul_sub_of_deriv_le (fun x ↦ (hΘ x).differentiableAt)
    (fun x ↦ by rw [(hΘ x).deriv]; exact hd x) hxy

end PhasePerturbation

/-! ## Corollary 2 -/

/-- **Corollary 2** (p. 800): `Λ(ψ)` is sampling for `PW` if there is `f ∈ \overline{HB}` with
`φ_f'(x) → 0` as `|x| → ∞` and `|U_ψ(z) - log|f(z)|| ≲ 1` for `Im z ≥ 0`. -/
theorem corollary2 (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {f : ℂ → ℂ} (hf : IsHB f)
    (hφ : Tendsto (phaseDeriv f) (cocompact ℝ) (𝓝 0))
    (happ : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.exp (UPsi ψ z - C) ≤ ‖f z‖ ∧ ‖f z‖ ≤ Real.exp (UPsi ψ z + C)) :
    IsSampling (LambdaPsi ψ) := by
  -- Step 1: `f`
  obtain ⟨C₀, hC₀⟩ := happ
  have hf0 : ∀ x : ℝ, f x ≠ 0 := fun x h0 ↦ by
    have := (hC₀ (x : ℂ) (by simp)).1
    rw [h0, norm_zero] at this
    exact absurd this (not_le.mpr (Real.exp_pos _))
  have happ : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.exp (UPsi ψ z - C) ≤ ‖f z‖ ∧ ‖f z‖ ≤ Real.exp (UPsi ψ z + C) := ⟨C₀, hC₀⟩
  obtain ⟨φf, hφf, hφf'⟩ := exists_isPhaseFunction hf.1 hf0
  have hgcont := continuous_phaseDeriv hf.1 hf0
  have hgnn : ∀ x, 0 ≤ phaseDeriv f x := fun x ↦ hf.phaseDeriv_nonneg (hf0 x)
  obtain ⟨Mg, hMg⟩ := bounded_of_tendsto_cocompact hgcont hφ
  have hφfmono : Monotone φf := monotone_of_deriv_nonneg
    (fun x ↦ (hφf' x).differentiableAt) (fun x ↦ by rw [(hφf' x).deriv]; exact hgnn x)
  -- Step 2: the density
  obtain ⟨m, a, b, κ, R, hmeas, ha, hlow, hup, hlim, hU, hph⟩ :=
    exists_good_density hψ hf hφ happ hφf hφf'
  -- Step 3: `E`
  obtain ⟨E, hEHB, hE0, hcomp, -, φE, hφE, hφE', hφEsm, c₀, hc₀⟩ :=
    exists_hb_of_density_phase hmeas ha hlow hup hlim
      (by obtain ⟨C, hC⟩ := hU; exact ⟨0, C, fun z hz ↦ by simpa using hC z hz⟩)
  -- Step 5: rotation
  set β : ℝ := κ + c₀ - Real.pi / 2 with hβ
  set Eβ : ℂ → ℂ := fun z ↦ Complex.exp (Complex.I * β) * E z with hEβ
  have hEβHB : IsHB Eβ := hEHB.rotate β
  have hEβ0 : ∀ x : ℝ, Eβ x ≠ 0 := fun x ↦ mul_ne_zero (Complex.exp_ne_zero _) (hE0 x)
  have hnormβ : ∀ z, ‖Eβ z‖ = ‖E z‖ := fun z ↦ by
    simp only [hEβ, norm_mul]
    rw [show Complex.I * (β : ℂ) = (β : ℂ) * Complex.I by ring, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hEPW : HEEqPW E := heEqPW_of_comparable hPW hEHB hcomp
  have hEβPW : HEEqPW Eβ := heEqPW_of_comparable hPW hEβHB
    (by obtain ⟨c, C, hc, h⟩ := hcomp; exact ⟨c, C, hc, fun z hz ↦ by rw [hnormβ]; exact h z hz⟩)
  have hEβS : IsStrictHB Eβ := HEEqPW.isStrictHB hEβHB hEβPW
  have hφEβ : IsPhaseFunction Eβ (fun x ↦ φE x - β) := hφE.rotate β
  set Θ : ℝ → ℝ := fun x ↦ (φE x - β) + φf x - Real.pi / 2 with hΘ
  have hΘcont : Continuous Θ := ((hφE.1.sub continuous_const).add hφf.1).sub continuous_const
  have hΘsm : StrictMono Θ := fun x y hxy ↦ by
    have := hφEsm hxy; have := hφfmono hxy.le; simp only [hΘ]; linarith
  have hlim : Tendsto (fun x ↦ Θ x / Real.pi - (x + ψ x)) (cocompact ℝ) (𝓝 0) := by
    have h1 : Tendsto (fun x ↦ (φE x - Real.pi * OCS.multPrim m x - c₀) / Real.pi) (cocompact ℝ)
        (𝓝 0) := by
      have := (hc₀.sub_const c₀).div_const Real.pi
      simpa using this
    refine h1.congr' ?_
    have hev : ∀ᶠ x : ℝ in cocompact ℝ, R ≤ |x| :=
      (tendsto_norm_cocompact_atTop (E := ℝ)).eventually (eventually_ge_atTop R)
    filter_upwards [hev] with x hx
    have := hph x hx
    simp only [hΘ, hβ]
    field_simp
    linarith
  obtain ⟨hΨsm, hΨsurj, hΨexp⟩ := strictMono_add_psi hψ
  have hΘsurj : Function.Surjective Θ := by
    have hΨtop : Tendsto (fun x : ℝ ↦ x + ψ x) atTop atTop := by
      refine tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono fun y hy ↦ ?_)
        (tendsto_id.atTop_add (tendsto_const_nhds (x := ψ 0)))
      have := hψ.2.1 hy
      simp only [id]; linarith
    have hΨbot : Tendsto (fun x : ℝ ↦ x + ψ x) atBot atBot := by
      refine tendsto_atBot_mono' atBot ((eventually_le_atBot 0).mono fun y hy ↦ ?_)
        (tendsto_id.atBot_add (tendsto_const_nhds (x := ψ 0)))
      have := hψ.2.1 hy
      simp only [id]; linarith
    refine hΘcont.surjective ?_ ?_
    · have h1 : Tendsto (fun x ↦ (x + ψ x) + (Θ x / Real.pi - (x + ψ x))) atTop atTop :=
        hΨtop.atTop_add (hlim.mono_left atTop_le_cocompact)
      have h2 : Tendsto (fun x ↦ Real.pi * (Θ x / Real.pi)) atTop atTop :=
        (h1.congr fun x ↦ by ring).const_mul_atTop Real.pi_pos
      exact h2.congr fun x ↦ by field_simp
    · have h1 : Tendsto (fun x ↦ (x + ψ x) + (Θ x / Real.pi - (x + ψ x))) atBot atBot :=
        hΨbot.atBot_add (hlim.mono_left atBot_le_cocompact)
      have h2 : Tendsto (fun x ↦ Real.pi * (Θ x / Real.pi)) atBot atBot :=
        (h1.congr fun x ↦ by ring).const_mul_atBot Real.pi_pos
      exact h2.congr fun x ↦ by field_simp
  have hzero : ∀ z : ℂ, Eβ z * f z + fstar Eβ z * fstar f z = 0 ↔
      ∃ x ∈ {x : ℝ | ∃ k : ℤ, Θ x = k * Real.pi}, z = (x : ℂ) := by
    intro z
    rw [zero_set_eq_phaseLevel hEβS hf (hEβ0) hf0 hφEβ hφf z]
    simp only [mem_image, phaseLevel, mem_ofPred_eq]
    constructor
    · rintro ⟨x, ⟨k, hk⟩, rfl⟩; exact ⟨x, ⟨k, by simp only [hΘ]; linarith⟩, rfl⟩
    · rintro ⟨x, ⟨k, hk⟩, rfl⟩; exact ⟨x, ⟨k, by simp only [hΘ] at hk; linarith⟩, rfl⟩
  have hsep : IsSeparated {x : ℝ | ∃ k : ℤ, Θ x = k * Real.pi} := by
    obtain ⟨CE, hCE⟩ := HEEqPW.phaseDeriv_mul_sq_le hPW hE hEHB hEPW
    obtain ⟨c, Cc, hc, hcc⟩ := hcomp
    have hEx : ∀ x : ℝ, c ≤ ‖E x‖ := fun x ↦ by simpa using (hcc (x : ℂ) (by simp)).1
    have hpE : ∀ x : ℝ, phaseDeriv E x ≤ max CE 0 / c ^ 2 := fun x ↦ by
      rw [le_div_iff₀ (by positivity)]
      have h0 : 0 ≤ phaseDeriv E x := hEHB.phaseDeriv_nonneg (hE0 x)
      have h1 : c ^ 2 ≤ ‖E x‖ ^ 2 := by gcongr; exact hEx x
      calc phaseDeriv E x * c ^ 2 ≤ phaseDeriv E x * ‖E x‖ ^ 2 := by gcongr
        _ ≤ CE := hCE x
        _ ≤ max CE 0 := le_max_left _ _
    have hΘ' : ∀ x, HasDerivAt Θ (phaseDeriv E x + phaseDeriv f x) x := fun x ↦
      (((hφE' x).sub_const β).add (hφf' x)).sub_const (Real.pi / 2)
    have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
    have hbd : ∀ x, phaseDeriv E x + phaseDeriv f x ≤ max CE 0 / c ^ 2 + Mg + 1 := fun x ↦ by
      have := hpE x; have := (le_abs_self _).trans (hMg x); linarith
    exact isSeparated_levelSet hΘsm (C := max CE 0 / c ^ 2 + Mg + 1)
      (by have : 0 ≤ max CE 0 / c ^ 2 := by positivity
          linarith)
      (fun x y hxy ↦ sub_le_mul_sub_of_hasDerivAt hΘ' hbd hxy)
  have hsamp := theorem1_sufficiency hPW hE hsep hEβHB hf hEβPW hzero
  obtain ⟨δ, hinj, himg, hδ⟩ := exists_perturbation_of_phase hψ hΘsm hΘsurj hlim
  rw [← himg]
  refine IsSampling.of_perturbation hPW hDS hsep hsamp hinj fun ε hε ↦ ?_
  have := (hδ.eventually (Metric.ball_mem_nhds 0 hε))
  obtain ⟨t, ht, hts⟩ := Filter.mem_cocompact.mp this
  obtain ⟨R', hR'⟩ := ht.isBounded.subset_closedBall 0
  refine ⟨R' + 1, fun x _ hx ↦ ?_⟩
  have hxt : x ∉ t := fun h ↦ by
    have := hR' h
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith
  have := hts hxt
  simp only [mem_ofPred_eq, dist_zero_right, Real.norm_eq_abs] at this
  exact this.le

end FF
