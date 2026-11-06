import FourierFrames.Construction
import FourierFrames.Perturbation
import FourierFrames.Theorem1.Sufficiency
import FourierFrames.HB.Comparable

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
  sorry

/-- The integrand of `multU` is integrable for every bounded measurable density (for weights this is
`OCS.integrable_multUIntegrand`; a bounded `g` is `(g + K) - K` with `g + K ≥ 1`). -/
theorem integrable_multU_integrand_of_bdd {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ t, |g t| ≤ M) (z : ℂ) :
    Integrable fun t : ℝ ↦
      (Real.log ‖1 - z / t‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).re) * g t := by
  sorry

theorem multU_add {g h : ℝ → ℝ} (hg : Measurable g) (hh : Measurable h) {M : ℝ}
    (hgM : ∀ t, |g t| ≤ M) (hhM : ∀ t, |h t| ≤ M) (z : ℂ) :
    OCS.multU (fun t ↦ g t + h t) 0 z = OCS.multU g 0 z + OCS.multU h 0 z := by
  sorry

theorem multU_const_mul {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) (c : ℝ)
    (z : ℂ) : OCS.multU (fun t ↦ c * g t) 0 z = c * OCS.multU g 0 z := by
  sorry

/-- The potential of Lebesgue measure: `U_1(z) = π |Im z|`.  (Compute
`∫_{-T}^{T} log|1 - z/t| dt` with the antiderivative of `½ log(u² + y²)` and let `T → ∞`;
the odd term `Re(z/t)` integrates to `0` over `[-T, T] ∖ [-1, 1]`.) -/
theorem multU_one (z : ℂ) : OCS.multU (fun _ ↦ (1 : ℝ)) 0 z = Real.pi * |z.im| := by
  sorry

/-- Growth of potentials of bounded densities. -/
theorem abs_multU_le_of_bdd {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) :
    ∃ K : ℝ, ∀ z : ℂ, |OCS.multU g 0 z| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
  sorry

/-- Potential of a compactly supported bounded density of total mass `0`: bounded up to the linear
term `(∫_{|t| > 1} h(t)/t dt) Re z` coming from the `Re(z/t)` normalisation. -/
theorem multU_compact_sub_linear {h : ℝ → ℝ} (hh : Measurable h) {M R : ℝ}
    (hM : ∀ t, |h t| ≤ M) (hR : ∀ t, R < |t| → h t = 0) (h0 : ∫ t, h t = 0) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |OCS.multU h 0 z - (∫ t, (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (h t / t)) * z.re| ≤ C := by
  sorry

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
  sorry

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
  sorry

/-- **Schwarz reflection** (via Morera on discs and the rectangle theorem for functions continuous
on a closed half-disc): `H` continuous on `Im z ≥ 0`, holomorphic on `Im z > 0`, with `Im H = c`
on `ℝ`, extends to an entire function with `H(z̄) = conj H(z) + 2ic`... precisely
`H^ext(z) = conj (H (conj z)) + 2 i c` for `Im z < 0`. -/
theorem exists_entire_reflection {H : ℂ → ℂ} (hc : ContinuousOn H {z : ℂ | 0 ≤ z.im})
    (hd : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) {c : ℝ} (him : ∀ x : ℝ, (H x).im = c) :
    ∃ Ĥ : ℂ → ℂ, Differentiable ℂ Ĥ ∧ (∀ z : ℂ, 0 ≤ z.im → Ĥ z = H z) ∧
      ∀ z : ℂ, Ĥ (conj z) = conj (Ĥ z) + 2 * Complex.I * c := by
  sorry

/-- An entire function whose real part grows like `|z|^{3/2}` is affine
(Borel–Carathéodory, then Cauchy's estimate for `H''`). -/
theorem entire_affine_of_re_growth {H : ℂ → ℂ} (hH : Differentiable ℂ H) {K : ℝ}
    (hK : ∀ z : ℂ, |(H z).re| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ)) :
    ∃ α β : ℂ, ∀ z : ℂ, H z = α + β * z := by
  sorry

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
  sorry

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
  sorry

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

/-- A continuous function tending to `0` at infinity is bounded. -/
theorem bounded_of_tendsto_cocompact {g : ℝ → ℝ} (hg : Continuous g)
    (h : Tendsto g (cocompact ℝ) (𝓝 0)) : ∃ M : ℝ, ∀ x, |g x| ≤ M := by
  have h1 : {x | g x ∈ Metric.closedBall (0 : ℝ) 1} ∈ cocompact ℝ :=
    h.eventually (Metric.closedBall_mem_nhds 0 one_pos)
  obtain ⟨t, ht, hts⟩ := Filter.mem_cocompact.mp h1
  obtain ⟨C, hC⟩ := ht.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 1, fun x ↦ ?_⟩
  by_cases hx : x ∈ t
  · exact (hC x hx).trans (le_max_left _ _)
  · have := hts hx
    simp only [mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact this.trans (le_max_right _ _)

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
