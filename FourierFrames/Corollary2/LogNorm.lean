import FourierFrames.Corollary2.PotCCont
import FourierFrames.Corollary2.PotCDiff
import FourierFrames.Corollary2.Reflection
import FourierFrames.Corollary2.Affine
import FourierFrames.Corollary2.LogInt

/-!
# M07 -- helper lemmas for `Corollary2.lean`: `log |f| = U_g / pi + b Re z + c`

Instead of a holomorphic logarithm of `f` on the closed half plane we use
`Phi = e^{i phi(0)} f e^{-P}` with `P = potC g / pi`.  It is continuous on `Im >= 0`, holomorphic on
`Im > 0` and real on `R`, so Schwarz reflection (`exists_entire_reflection_aux`) makes it entire and
zero free; `Phi^ = e^G` with `G` entire, `Re G = log |Phi^|` of growth `O(|z|^{3/2})`, hence affine.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF


theorem exists_exp_of_nonvanishing {H : ℂ → ℂ} (hH : Differentiable ℂ H) (h0 : ∀ z, H z ≠ 0) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, H z = Complex.exp (G z) := by
  have hh : Differentiable ℂ (fun z ↦ deriv H z / H z) :=
    hH.deriv.div hH h0
  obtain ⟨G₀, hG₀⟩ := hh.isExactOn_univ
  have hG₀d : Differentiable ℂ G₀ := fun z ↦ (hG₀ z (mem_univ z)).differentiableAt
  have hK : ∀ z, HasDerivAt (fun w ↦ H w * Complex.exp (-G₀ w)) 0 z := by
    intro z
    have h1 : HasDerivAt H (deriv H z) z := (hH z).hasDerivAt
    have h2 : HasDerivAt (fun w ↦ Complex.exp (-G₀ w))
        (Complex.exp (-G₀ z) * (-(deriv H z / H z))) z := by
      have := (hG₀ z (mem_univ z)).neg.cexp
      simpa using this
    have := h1.mul h2
    convert this using 1
    field_simp [h0 z]
    ring
  have hconst : ∀ z, H z * Complex.exp (-G₀ z) = H 0 * Complex.exp (-G₀ 0) := fun z ↦
    is_const_of_deriv_eq_zero (fun w ↦ (hK w).differentiableAt) (fun w ↦ (hK w).deriv) z 0
  have hκ : H 0 * Complex.exp (-G₀ 0) ≠ 0 := mul_ne_zero (h0 0) (Complex.exp_ne_zero _)
  refine ⟨fun z ↦ G₀ z + Complex.log (H 0 * Complex.exp (-G₀ 0)), hG₀d.add_const _, fun z ↦ ?_⟩
  rw [Complex.exp_add, Complex.exp_log hκ, ← hconst z]
  rw [mul_left_comm, ← Complex.exp_add]
  simp


theorem exp_aux (r Z Z0 U : ℝ) :
    Complex.exp (Complex.I * Z0) * ((r : ℂ) * Complex.exp (-(Complex.I * Z))) *
      Complex.exp (-((U : ℂ) - Complex.I * ((Z - Z0 : ℝ) : ℂ))) = ((r * Real.exp (-U) : ℝ) : ℂ) := by
  have h1 : Complex.exp (Complex.I * Z0) * ((r : ℂ) * Complex.exp (-(Complex.I * Z))) *
      Complex.exp (-((U : ℂ) - Complex.I * ((Z - Z0 : ℝ) : ℂ))) =
      (r : ℂ) * Complex.exp (Complex.I * Z0 + (-(Complex.I * Z)) +
        (-((U : ℂ) - Complex.I * ((Z - Z0 : ℝ) : ℂ)))) := by
    rw [Complex.exp_add, Complex.exp_add]; ring
  have h2 : Complex.I * (Z0 : ℂ) + (-(Complex.I * (Z : ℂ))) +
      (-((U : ℂ) - Complex.I * ((Z - Z0 : ℝ) : ℂ))) = ((-U : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, h2, Complex.ofReal_mul, Complex.ofReal_exp]

theorem log_norm_aux {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : ∀ z : ℂ, 0 ≤ z.im → f z ≠ 0) {φ g : ℝ → ℝ} (hφ : IsPhaseFunction f φ)
    (hφ' : ∀ x, HasDerivAt φ (g x) x) (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    (hgrow : ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |Real.log ‖f z‖| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ)) :
    ∃ b c : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.log ‖f z‖ = OCS.multU g 0 z / Real.pi + b * z.re + c := by
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨K₁, hK₁⟩ := hgrow
  obtain ⟨K₂, hK₂⟩ := abs_multU_le_aux hg.measurable hM
  set P : ℂ → ℂ := fun z ↦ potC' g z / (Real.pi : ℂ) with hP
  set Φ : ℂ → ℂ := fun z ↦ Complex.exp (Complex.I * φ 0) * f z * Complex.exp (-P z) with hΦ
  have hPc : ContinuousOn P {z : ℂ | 0 ≤ z.im} := (continuousOn_potC' hg.measurable hM).div_const _
  have hΦc : ContinuousOn Φ {z : ℂ | 0 ≤ z.im} := by
    refine ((continuousOn_const.mul hf.continuous.continuousOn).mul ?_)
    exact Complex.continuous_exp.comp_continuousOn hPc.neg
  have hΦd : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.im} := by
    intro z hz
    have hz' : 0 < z.im := hz
    have hPd : DifferentiableAt ℂ P z := (differentiableAt_potC' hg.measurable hM hz').div_const _
    exact ((differentiableAt_const _).mul (hf z)).mul (hPd.neg.cexp) |>.differentiableWithinAt
  -- reality on the real axis
  have hreal : ∀ x : ℝ, (Φ (x : ℂ)).im = (0 : ℝ) := by
    intro x
    have hre := potC'_re hg.measurable hM (x : ℂ)
    have him := potC'_im_ofReal hg hM hφ' x
    have hp : potC' g (x : ℂ) = ((OCS.multU g 0 (x : ℂ) : ℝ) : ℂ) +
        Complex.I * ((-Real.pi * (φ x - φ 0) : ℝ) : ℂ) := Complex.ext (by simp [hre]) (by simp [him])
    have hPx : P (x : ℂ) = (((OCS.multU g 0 (x : ℂ) / Real.pi : ℝ)) : ℂ) -
        Complex.I * ((φ x - φ 0 : ℝ) : ℂ) := by
      simp only [hP, hp]
      push_cast
      field_simp
      ring
    have hfx := hφ.2 x
    have : Φ (x : ℂ) = ((‖f (x : ℂ)‖ * Real.exp (-(OCS.multU g 0 (x : ℂ) / Real.pi)) : ℝ) : ℂ) := by
      simp only [hΦ]
      rw [hPx]
      conv_lhs => rw [hfx]
      exact exp_aux ‖f (x : ℂ)‖ (φ x) (φ 0) (OCS.multU g 0 (x : ℂ) / Real.pi)
    rw [this]; exact Complex.ofReal_im _
  obtain ⟨Ĥ, hĤd, hĤeq, hĤsym⟩ := exists_entire_reflection_aux hΦc hΦd hreal
  have hsym : ∀ z, Ĥ (conj z) = conj (Ĥ z) := fun z ↦ by
    have := hĤsym z; simpa using this
  have hĤ0 : ∀ z, Ĥ z ≠ 0 := by
    intro z
    by_cases hz : 0 ≤ z.im
    · rw [hĤeq z hz]
      exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (hf0 z hz)) (Complex.exp_ne_zero _)
    · have hz' : 0 ≤ (conj z).im := by simp; linarith [not_le.mp hz]
      have h1 := hsym (conj z)
      rw [Complex.conj_conj] at h1
      rw [h1]
      refine (map_ne_zero (starRingEnd ℂ)).mpr ?_
      rw [hĤeq _ hz']
      exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (hf0 _ hz')) (Complex.exp_ne_zero _)
  have hsymn : ∀ z, ‖Ĥ (conj z)‖ = ‖Ĥ z‖ := fun z ↦ by rw [hsym z]; exact Complex.norm_conj _
  obtain ⟨G, hGd, hGe⟩ := exists_exp_of_nonvanishing hĤd hĤ0
  have hReG : ∀ z, (G z).re = Real.log ‖Ĥ z‖ := fun z ↦ by
    rw [hGe z, Complex.norm_exp, Real.log_exp]
  have hnorm : ∀ z, 0 ≤ z.im → ‖Ĥ z‖ = ‖f z‖ * Real.exp (-(OCS.multU g 0 z / Real.pi)) := by
    intro z hz
    rw [hĤeq z hz]
    simp only [hΦ, norm_mul, Complex.norm_exp]
    have h1 : (Complex.I * (φ 0 : ℂ)).re = 0 := by simp
    have h2 : (-P z).re = -(OCS.multU g 0 z / Real.pi) := by
      simp only [hP, Complex.neg_re, Complex.div_ofReal_re, potC'_re hg.measurable hM z]
    rw [h1, h2]; simp
  have hReGH : ∀ z : ℂ, 0 ≤ z.im → (G z).re = Real.log ‖f z‖ - OCS.multU g 0 z / Real.pi := by
    intro z hz
    have hpos : 0 < ‖f z‖ := norm_pos_iff.mpr (hf0 z hz)
    rw [hReG, hnorm z hz, Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
  have hbound : ∀ z : ℂ, |(G z).re| ≤ (|K₁| + |K₂| / Real.pi) * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
    have hX : ∀ z : ℂ, 0 ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) := fun z ↦ by positivity
    have hup : ∀ z : ℂ, 0 ≤ z.im → |(G z).re| ≤ (|K₁| + |K₂| / Real.pi) * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
      intro z hz
      rw [hReGH z hz]
      calc |Real.log ‖f z‖ - OCS.multU g 0 z / Real.pi|
          ≤ |Real.log ‖f z‖| + |OCS.multU g 0 z / Real.pi| := abs_sub _ _
        _ ≤ K₁ * (1 + ‖z‖) ^ (3 / 2 : ℝ) + K₂ / Real.pi * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
            refine add_le_add (hK₁ z hz) ?_
            rw [abs_div, abs_of_pos hπ, div_eq_mul_inv, div_eq_mul_inv]
            have := hK₂ z
            have : |OCS.multU g 0 z| * Real.pi⁻¹ ≤ K₂ * (1 + ‖z‖) ^ (3 / 2 : ℝ) * Real.pi⁻¹ :=
              mul_le_mul_of_nonneg_right this (by positivity)
            linarith
        _ ≤ _ := by
            have := hX z
            nlinarith [le_abs_self K₁, le_abs_self K₂, abs_nonneg K₁, abs_nonneg K₂,
              div_nonneg (abs_nonneg K₂) hπ.le, show K₂ / Real.pi ≤ |K₂| / Real.pi from
                div_le_div_of_nonneg_right (le_abs_self K₂) hπ.le]
    intro z
    by_cases hz : 0 ≤ z.im
    · exact hup z hz
    · have hz' : 0 ≤ (conj z).im := by simp; linarith [not_le.mp hz]
      have := hup (conj z) hz'
      rw [hReG z, ← hsymn z, ← hReG (conj z)]
      simpa using this
  obtain ⟨α, β, hαβ⟩ := entire_affine_aux hGd hbound
  -- `β` is real
  have hβ : β.im = 0 := by
    by_contra hne
    have hsin : ∀ x : ℝ, Real.sin (G (x : ℂ)).im = 0 := by
      intro x
      have h1 := hGe (x : ℂ)
      rw [hĤeq (x : ℂ) (by simp)] at h1
      have h2 := hreal x
      have h3 : (Complex.exp (G (x : ℂ))).im = 0 := by rw [← h1]; simpa using h2
      rw [Complex.exp_im] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h (Real.exp_pos _).ne'
      · exact h
    set x₁ : ℝ := (Real.pi / 2 - α.im) / β.im with hx₁
    have := hsin x₁
    rw [hαβ] at this
    have e : (α + β * (x₁ : ℂ)).im = Real.pi / 2 := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero]
      rw [hx₁]; field_simp; ring
    rw [e, Real.sin_pi_div_two] at this
    exact one_ne_zero this
  refine ⟨β.re, α.re, fun z hz ↦ ?_⟩
  have h1 := hReGH z hz
  rw [hαβ z] at h1
  simp only [Complex.add_re, Complex.mul_re, hβ] at h1
  linarith




theorem potKernel_neg (z : ℂ) (t : ℝ) : potKernel (-z) t = potKernel z (-t) := by
  unfold potKernel
  have e : (-z) / (t : ℂ) = z / ((-t : ℝ) : ℂ) := by push_cast; rw [neg_div, div_neg]
  rw [e]
  have h : (Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) t = (Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) (-t) := by
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · have : -t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [indicator_of_mem ht, indicator_of_mem this]; rfl
    · have : -t ∉ Icc (-1 : ℝ) 1 := fun h' ↦ ht ⟨by linarith [h'.2], by linarith [h'.1]⟩
      rw [indicator_of_notMem ht, indicator_of_notMem this]
  rw [h]

theorem multU_one_neg (z : ℂ) :
    OCS.multU (fun _ ↦ (1 : ℝ)) 0 (-z) = OCS.multU (fun _ ↦ (1 : ℝ)) 0 z := by
  simp only [multU_eq_integral, mul_one]
  simp_rw [potKernel_neg]
  exact integral_neg_eq_self (fun t ↦ potKernel z t) volume

theorem multU_one_zero : OCS.multU (fun _ ↦ (1 : ℝ)) 0 0 = 0 := by
  simp [multU_eq_integral, potKernel]


theorem multU_one_aux (z : ℂ) : OCS.multU (fun _ ↦ (1 : ℝ)) 0 z = Real.pi * |z.im| := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set f : ℂ → ℂ := fun z ↦ Complex.exp (-(Complex.I * Real.pi * z)) with hf
  have hfd : Differentiable ℂ f := by fun_prop
  have hfn : ∀ z : ℂ, ‖f z‖ = Real.exp (Real.pi * z.im) := fun z ↦ by
    simp only [hf, Complex.norm_exp]
    congr 1; simp
  have hf0 : ∀ z : ℂ, 0 ≤ z.im → f z ≠ 0 := fun z _ ↦ Complex.exp_ne_zero _
  have hφ : IsPhaseFunction f (fun x ↦ Real.pi * x) := by
    refine ⟨by fun_prop, fun x ↦ ?_⟩
    have h1 : ‖f (x : ℂ)‖ = 1 := by rw [hfn]; simp
    rw [h1]
    simp only [hf, Complex.ofReal_one, one_mul]
    congr 1
    push_cast; ring
  have hφ' : ∀ x : ℝ, HasDerivAt (fun x : ℝ ↦ Real.pi * x) Real.pi x := fun x ↦ by
    simpa using (hasDerivAt_id x).const_mul Real.pi
  have hgrow : ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      |Real.log ‖f z‖| ≤ K * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
    refine ⟨Real.pi, fun z _ ↦ ?_⟩
    rw [hfn, Real.log_exp, abs_mul, abs_of_pos hπ]
    have h1 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have h2 : 1 + ‖z‖ ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) :=
      Real.self_le_rpow_of_one_le (by linarith [norm_nonneg z]) (by norm_num)
    nlinarith [norm_nonneg z]
  obtain ⟨b, c, hbc⟩ := log_norm_aux hfd hf0 hφ hφ' (g := fun _ ↦ Real.pi) continuous_const
    (M := Real.pi) (fun _ ↦ by rw [abs_of_pos hπ]) hgrow
  have hscale : ∀ z : ℂ, OCS.multU (fun _ ↦ Real.pi) 0 z = Real.pi * OCS.multU (fun _ ↦ (1 : ℝ)) 0 z := by
    intro z
    simp only [multU_eq_integral, mul_one]
    rw [integral_mul_const, mul_comm]
  have key : ∀ z : ℂ, 0 ≤ z.im → Real.pi * z.im = OCS.multU (fun _ ↦ (1 : ℝ)) 0 z + b * z.re + c := by
    intro z hz
    have := hbc z hz
    rw [hfn, Real.log_exp, hscale z] at this
    rw [this]; field_simp
  set U : ℂ → ℝ := OCS.multU (fun _ ↦ (1 : ℝ)) 0 with hU
  have hUconj : ∀ z, U (conj z) = U z := fun z ↦ OCS.multU_conj _ 0 z
  have z1 : U (-(conj ((1 : ℂ) + Complex.I))) = U ((1 : ℂ) + Complex.I) := by
    rw [hU, multU_one_neg, ← hU, hUconj]
  have k1 := key ((1 : ℂ) + Complex.I) (by simp)
  have k2 := key (-(conj ((1 : ℂ) + Complex.I))) (by simp)
  have k0 := key 0 (by simp)
  have hb : b = 0 := by
    simp only [Complex.neg_re, Complex.conj_re, Complex.add_re, Complex.one_re, Complex.I_re,
      Complex.neg_im, Complex.conj_im, Complex.add_im, Complex.one_im, Complex.I_im] at k1 k2
    rw [z1] at k2
    linarith
  have hc : c = 0 := by
    have : U 0 = 0 := multU_one_zero
    simp only [Complex.zero_re, Complex.zero_im, mul_zero] at k0
    linarith
  have hup : ∀ z : ℂ, 0 ≤ z.im → U z = Real.pi * |z.im| := fun z hz ↦ by
    have := key z hz
    rw [hb, hc, abs_of_nonneg hz] at *
    linarith
  by_cases hz : 0 ≤ z.im
  · exact hup z hz
  · have hz' : 0 ≤ (conj z).im := by simp; linarith [not_le.mp hz]
    have := hup (conj z) hz'
    rw [hUconj] at this
    rw [this]
    simp [abs_neg]


end FF
