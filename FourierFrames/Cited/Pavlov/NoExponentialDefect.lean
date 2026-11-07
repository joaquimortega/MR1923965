import FourierFrames.Cited.Pavlov.Cardinal
import FourierFrames.HB.Comparable
import FourierFrames.HB.H2

/-! # Elimination of an exponential Hardy defect by interpolation uniqueness -/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section
namespace FF.Pavlov

private theorem norm_exp_sin_le_one {a τ b γ : ℝ} (hτ : 0 ≤ τ) (hτa : τ ≤ a)
    {z : ℂ} (hz : 0 ≤ z.im) :
    ‖Complex.exp (I*((a : ℂ)*z+(b : ℂ))) *
      Complex.sin ((τ : ℂ)*(z-(γ : ℂ)))‖ ≤ 1 := by
  let u := I*((a : ℂ)*z+(b : ℂ))
  let v := (τ : ℂ)*(z-(γ : ℂ))
  have hm : ‖Complex.exp (u-v*I)‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    dsimp [u, v]
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, one_mul, mul_one, sub_zero, add_zero,
      Complex.sub_im]
    nlinarith
  have hp : ‖Complex.exp (u+v*I)‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    dsimp [u, v]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, one_mul, mul_one, sub_zero, add_zero,
      Complex.sub_im]
    nlinarith
  have he : Complex.exp u * Complex.sin v =
      (Complex.exp (u-v*I)-Complex.exp (u+v*I))*I/2 := by
    rw [show u-v*I = u+(-v*I) by ring, Complex.exp_add, Complex.exp_add]
    have hs := Complex.two_sin v
    linear_combination (Complex.exp u / 2) * hs
  change ‖Complex.exp u * Complex.sin v‖ ≤ 1
  rw [he, norm_div, norm_mul, Complex.norm_I, mul_one]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_one (by norm_num : (0 : ℝ) < 2)).mpr
  exact (norm_sub_le _ _).trans (by linarith)

private theorem exponential_pi_isHB : IsHB (fun z : ℂ ↦ Complex.exp (-I*Real.pi*z)) := by
  refine ⟨(differentiable_id.const_mul (-I*Real.pi)).cexp, fun z _ ↦ Complex.exp_ne_zero _, ?_⟩
  intro z hz
  rw [Complex.norm_exp, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  nlinarith [Real.pi_pos]

/-- Interpolation uniqueness excludes a positive exponential Hardy defect. -/
theorem no_exponential_defect {Γ : Set ℝ} (hcis : IsCompleteInterpolating Γ)
    {q O : ℂ → ℂ} (hq : Differentiable ℂ q) (hqreal : fstar q = q)
    (hO : IsH2Upper O) {γ a b : ℝ} (hqγ : q (γ : ℂ) ≠ 0)
    (hzeros : ∀ x ∈ Γ, x ≠ γ → q (x : ℂ) = 0)
    (ha : 0 ≤ a)
    (hfactor : ∀ z : ℂ, 0 < z.im →
      Complex.exp (I * Real.pi * z) * q z =
        Complex.exp (I * ((a : ℂ)*z+(b : ℂ))) * O z) : a = 0 := by
  by_contra hne
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
  let τ : ℝ := a/2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτa : τ ≤ a := by dsimp [τ]; linarith
  let f : ℂ → ℂ := fun z ↦ q z * Complex.sin ((τ : ℂ)*(z-(γ : ℂ)))
  have hsin : Differentiable ℂ (fun z : ℂ ↦ Complex.sin ((τ : ℂ)*(z-(γ : ℂ)))) :=
    Complex.differentiable_sin.comp ((differentiable_id.sub_const _).const_mul _)
  have hf : Differentiable ℂ f := hq.mul hsin
  have hreal : fstar f = f := by
    funext z
    have hqz := congrFun hqreal z
    dsimp [fstar, f] at hqz ⊢
    rw [map_mul, ← Complex.sin_conj]
    simp only [map_mul, map_sub, Complex.conj_ofReal, Complex.conj_conj]
    rw [hqz]
  have hhardy : IsH2Upper (fun z ↦ Complex.exp (I*Real.pi*z)*f z) := by
    have hmult := hO.mul_bounded
      (((differentiable_id.const_mul (a : ℂ)).add_const (b : ℂ)).const_mul I |>.cexp |>.mul hsin).differentiableOn
      (fun z hz ↦ norm_exp_sin_le_one hτ.le hτa hz.le)
    apply hmult.congr
    intro z hz
    dsimp [f]
    have hh := hfactor z hz
    linear_combination -(Complex.sin ((τ : ℂ)*(z-(γ : ℂ)))) * hh
  let E : ℂ → ℂ := fun z ↦ Complex.exp (-I*Real.pi*z)
  have hdiv : IsH2Upper (fun z ↦ f z / E z) := by
    apply hhardy.congr
    intro z hz
    dsimp [E]
    rw [div_eq_mul_inv, ← Complex.exp_neg]
    have he : -(-I*Real.pi*z) = I*Real.pi*z := by ring
    rw [he, mul_comm]
  have hmem : MemHE E f := ⟨hf, hdiv, by simpa only [hreal] using hdiv⟩
  have hcomp : ∀ z : ℂ, 0 ≤ z.im →
      (1 : ℝ)*Real.exp (Real.pi*z.im) ≤ ‖E z‖ ∧
      ‖E z‖ ≤ (1 : ℝ)*Real.exp (Real.pi*z.im) := by
    intro z hz
    have he : ‖E z‖ = Real.exp (Real.pi*z.im) := by
      dsimp [E]
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    simp only [he, one_mul, le_refl, and_self]
  have hpw : MemPW f := (memPW_of_memHE exponential_pi_isHB (by norm_num) hcomp hmem).1
  have hzero : ∀ x ∈ Γ, f (x : ℂ) = 0 := by
    intro x hx
    by_cases he : x = γ
    · subst x
      simp [f]
    · simp [f, hzeros x hx he]
  obtain ⟨f₀, hf₀, huniq⟩ := hcis (fun _ ↦ 0) (by simp)
  have heq : f = (fun _ ↦ 0) := (huniq f ⟨hpw, hzero⟩).trans
    (huniq _ ⟨memPW_zero, by simp⟩).symm
  have hsder : HasDerivAt (fun z : ℂ ↦ Complex.sin ((τ : ℂ)*(z-(γ : ℂ)))) (τ : ℂ) (γ : ℂ) := by
    simpa only [Function.comp_def, id_eq, sub_self, mul_zero, Complex.cos_zero, one_mul, mul_one] using (Complex.hasDerivAt_sin ((τ : ℂ)*((γ : ℂ)-(γ : ℂ)))).comp (γ : ℂ)
      (((hasDerivAt_id (γ : ℂ)).sub_const (γ : ℂ)).const_mul (τ : ℂ))
  have hd := ((hq (γ : ℂ)).hasDerivAt.mul hsder).deriv
  change deriv f (γ : ℂ) = _ at hd
  rw [heq] at hd
  simp only [deriv_const, sub_self, mul_zero, Complex.sin_zero, zero_add] at hd
  exact mul_ne_zero hqγ (Complex.ofReal_ne_zero.mpr hτ.ne') hd.symm

end FF.Pavlov
