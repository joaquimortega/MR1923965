import FourierFrames.Defs

/-!
# Polynomial Hermite–Biehler (Lemma H; aux file for `Construction.lean`, M07 §2.4)
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace FF

namespace PolyHB

/-- `s ↦ s / √(s² + y²)` is strictly increasing for `y > 0`. -/
theorem div_sqrt_lt {y u v : ℝ} (hy : 0 < y) (huv : v < u) :
    v / Real.sqrt (v ^ 2 + y ^ 2) < u / Real.sqrt (u ^ 2 + y ^ 2) := by
  have hA : 0 < Real.sqrt (u ^ 2 + y ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hB : 0 < Real.sqrt (v ^ 2 + y ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hA2 : Real.sqrt (u ^ 2 + y ^ 2) ^ 2 = u ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  have hB2 : Real.sqrt (v ^ 2 + y ^ 2) ^ 2 = v ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  rw [div_lt_div_iff₀ hB hA]
  set A := Real.sqrt (u ^ 2 + y ^ 2)
  set B := Real.sqrt (v ^ 2 + y ^ 2)
  -- goal : v * A < u * B
  rcases le_or_gt v 0 with hv | hv
  · rcases le_or_gt 0 u with hu | hu
    · -- v ≤ 0 ≤ u, v < u
      have h1 : 0 ≤ u * B := by positivity
      have h2 : v * A ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hv hA.le
      rcases hu.eq_or_lt with h | h
      · subst h
        have : v < 0 := huv
        nlinarith [mul_pos hA hB]
      · nlinarith [mul_pos h hB]
    · -- v < u < 0 : |u| < |v|
      have hvu : u ^ 2 < v ^ 2 := by nlinarith
      have hq : 0 < -u * B := mul_pos (neg_pos.2 hu) hB
      have hp : 0 < -v * A := mul_pos (by linarith) hA
      have hsq : (-u * B) ^ 2 < (-v * A) ^ 2 := by
        have : (-u * B) ^ 2 = u ^ 2 * (v ^ 2 + y ^ 2) := by rw [mul_pow, hB2]; ring
        have h2 : (-v * A) ^ 2 = v ^ 2 * (u ^ 2 + y ^ 2) := by rw [mul_pow, hA2]; ring
        rw [this, h2]; nlinarith [sq_nonneg y, mul_pos hy hy]
      have := lt_of_pow_lt_pow_left₀ 2 hp.le hsq
      linarith
  · -- 0 < v < u
    have hvu : v ^ 2 < u ^ 2 := by nlinarith
    have hq : 0 < v * A := mul_pos hv hA
    have hp : 0 < u * B := mul_pos (by linarith) hB
    have hsq : (v * A) ^ 2 < (u * B) ^ 2 := by
      have e1 : (v * A) ^ 2 = v ^ 2 * (u ^ 2 + y ^ 2) := by rw [mul_pow, hA2]
      have e2 : (u * B) ^ 2 = u ^ 2 * (v ^ 2 + y ^ 2) := by rw [mul_pow, hB2]
      rw [e1, e2]; nlinarith [mul_pos hy hy]
    exact lt_of_pow_lt_pow_left₀ 2 hp.le hsq

theorem arg_sub_mem {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    0 < arg (z - t) ∧ arg (z - t) < Real.pi := by
  have him : 0 < (z - (t : ℂ)).im := by simpa using hz
  refine ⟨lt_of_le_of_ne (arg_nonneg_iff.2 him.le) fun h ↦ ?_, arg_lt_pi_iff.2 (Or.inr him.ne')⟩
  have := arg_eq_zero_iff.1 h.symm
  linarith [this.2]

theorem arg_sub_strictMono {z : ℂ} (hz : 0 < z.im) {s t : ℝ} (hst : s < t) :
    arg (z - s) < arg (z - t) := by
  have hs : 0 < (z - (s : ℂ)).im := by simpa using hz
  have ht : 0 < (z - (t : ℂ)).im := by simpa using hz
  rw [arg_of_im_pos hs, arg_of_im_pos ht]
  have nrm : ∀ r : ℝ, ‖z - (r : ℂ)‖ = Real.sqrt ((z.re - r) ^ 2 + z.im ^ 2) := by
    intro r
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp; ring
  have rr : ∀ r : ℝ, (z - (r : ℂ)).re = z.re - r := fun r ↦ by simp
  rw [nrm, nrm, rr, rr]
  have hlt := div_sqrt_lt hz (u := z.re - s) (v := z.re - t) (by linarith)
  have b1 : ∀ r : ℝ, (z.re - r) / Real.sqrt ((z.re - r) ^ 2 + z.im ^ 2) ≤ 1 := fun r ↦ by
    have hp : 0 < Real.sqrt ((z.re - r) ^ 2 + z.im ^ 2) := Real.sqrt_pos.2 (by positivity)
    rw [div_le_one hp]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg z.im])
  have b2 : ∀ r : ℝ, -1 ≤ (z.re - r) / Real.sqrt ((z.re - r) ^ 2 + z.im ^ 2) := fun r ↦ by
    have hp : 0 < Real.sqrt ((z.re - r) ^ 2 + z.im ^ 2) := Real.sqrt_pos.2 (by positivity)
    rw [le_div_iff₀ hp]
    have : |z.re - r| ≤ Real.sqrt ((z.re - r) ^ 2 + z.im ^ 2) :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg z.im])
    linarith [neg_abs_le (z.re - r)]
  exact Real.arccos_lt_arccos (b2 _) hlt (b1 _)

/-- Polar form of the quotient of two factors. -/
theorem factor_eq {z : ℂ} (hz : 0 < z.im) (s t : ℝ) :
    (z - t) / (z - s) = ((‖z - t‖ / ‖z - s‖ : ℝ) : ℂ) *
      Complex.exp (((arg (z - t) - arg (z - s) : ℝ) : ℂ) * I) := by
  have hs : z - (s : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hnorm : ((‖z - (s : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, norm_eq_zero]; exact hs
  have e1 := Complex.norm_mul_exp_arg_mul_I (z - t)
  have e2 := Complex.norm_mul_exp_arg_mul_I (z - s)
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, Complex.ofReal_div]
  conv_lhs => rw [← e1, ← e2]
  have : Complex.exp (arg (z - s) * I) ≠ 0 := Complex.exp_ne_zero _
  field_simp

theorem sum_bound {z : ℂ} (hz : 0 < z.im) : ∀ (n : ℕ) (a b : Fin (n + 1) → ℝ),
    (∀ k, a k < b k) → (∀ k : Fin n, b k.castSucc < a k.succ) →
      ∑ k, (arg (z - b k) - arg (z - a k)) ≤ arg (z - b (Fin.last n)) - arg (z - a 0) := by
  intro n
  induction n with
  | zero =>
    intro a b _ _
    simp
  | succ n ih =>
    intro a b hab hba
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun k ↦ a k.castSucc) (fun k ↦ b k.castSucc) (fun k ↦ hab _)
      (fun k ↦ by
        have := hba k.castSucc
        rw [Fin.succ_castSucc] at this
        exact this)
    have h2 := hba (Fin.last n)
    rw [Fin.succ_last] at h2
    have h3 := arg_sub_strictMono hz h2
    simp only [Fin.castSucc_zero] at h1
    linarith

end PolyHB

/-- **Polynomial Hermite–Biehler**. -/
theorem im_prod_div_pos' {n : ℕ} {a b : Fin (n + 1) → ℝ}
    (hab : ∀ k, a k < b k) (hba : ∀ k : Fin n, b k.castSucc < a k.succ) {z : ℂ} (hz : 0 < z.im) :
    0 < (∏ k, ((z - b k) / (z - a k))).im := by
  have hf : ∀ k, (z - b k) / (z - a k) = ((‖z - b k‖ / ‖z - a k‖ : ℝ) : ℂ) *
      Complex.exp (((arg (z - b k) - arg (z - a k) : ℝ) : ℂ) * I) :=
    fun k ↦ PolyHB.factor_eq hz (a k) (b k)
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, ← Complex.ofReal_prod]
  have e : ∑ k, (((arg (z - b k) - arg (z - a k) : ℝ) : ℂ) * I) =
      ((∑ k, (arg (z - b k) - arg (z - a k)) : ℝ) : ℂ) * I := by
    rw [← Finset.sum_mul]; push_cast; rfl
  rw [e, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  set S := ∑ k, (arg (z - b k) - arg (z - a k)) with hS
  have hSpos : 0 < S := Finset.sum_pos (fun k _ ↦ sub_pos.2 (PolyHB.arg_sub_strictMono hz (hab k)))
    Finset.univ_nonempty
  have hSlt : S < Real.pi := by
    have := PolyHB.sum_bound hz n a b hab hba
    have h1 := (PolyHB.arg_sub_mem hz (b (Fin.last n))).2
    have h2 := (PolyHB.arg_sub_mem hz (a 0)).1
    linarith
  refine mul_pos (Finset.prod_pos fun k _ ↦ ?_) (Real.sin_pos_of_pos_of_lt_pi hSpos hSlt)
  have hn : ∀ r : ℝ, 0 < ‖z - (r : ℂ)‖ := fun r ↦ by
    rw [norm_pos_iff]
    intro h; have := congrArg Complex.im h; simp at this; linarith
  exact div_pos (hn _) (hn _)

/-- If `A`, `B` are entire and real-symmetric, `A ≠ 0` on the upper half-plane and `Im (B/A) > 0`
there, then `A - i λ B ∈ \overline{HB}` for `λ > 0`. -/
theorem isHB_of_im_div_pos {A B : ℂ → ℂ} (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (hAc : ∀ z, A (conj z) = conj (A z)) (hBc : ∀ z, B (conj z) = conj (B z))
    (hA0 : ∀ z : ℂ, 0 < z.im → A z ≠ 0) (him : ∀ z : ℂ, 0 < z.im → 0 < (B z / A z).im)
    {lam : ℝ} (hlam : 0 < lam) :
    IsHB (fun z ↦ A z - I * lam * B z) := by
  refine ⟨by fun_prop, fun z hz ↦ ?_, fun z hz ↦ ?_⟩ <;>
  · have ha := hA0 z hz
    have hi := him z hz
    have hnsq : 0 < Complex.normSq (A z) := Complex.normSq_pos.2 ha
    rw [Complex.div_im] at hi
    have hxy : 0 < (B z).im * (A z).re - (B z).re * (A z).im := by
      have : (B z).im * (A z).re / Complex.normSq (A z) - (B z).re * (A z).im /
          Complex.normSq (A z) = ((B z).im * (A z).re - (B z).re * (A z).im) /
            Complex.normSq (A z) := by ring
      rw [this] at hi
      exact (div_pos_iff_of_pos_right hnsq).1 hi
    have hconj : A (conj z) - I * lam * B (conj z) = conj (A z + I * lam * B z) := by
      rw [hAc, hBc]; simp [map_add, map_mul, Complex.conj_ofReal, sub_eq_add_neg]
    have key : Complex.normSq (A z + I * lam * B z) < Complex.normSq (A z - I * lam * B z) := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      nlinarith [mul_pos hlam hxy]
    first
    | (intro h0
       have : Complex.normSq (A z + I * lam * B z) < 0 := by
         have h1 : A z - I * lam * B z = 0 := h0
         rw [h1, Complex.normSq_zero] at key; exact key
       exact absurd this (not_lt.2 (Complex.normSq_nonneg _)))
    | (simp only [hconj, Complex.norm_conj]
       refine le_of_lt ?_
       rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm]
       exact key)

end FF
