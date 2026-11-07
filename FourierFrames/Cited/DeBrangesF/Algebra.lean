import FourierFrames.Defs

/-!
# Algebra for the elementary proof of de Branges' Theorem F

The inverse disk automorphism preserves the closed unit disk. Its linear-fractional
form in the Cauchy transforms F and H yields the final Schur function. The last
identities recover the real part of the original weighted Cauchy transform.
See `blueprint/P4F_Elementary.md` and its independent review `reviews/R11_TheoremF.md`.
-/

open Complex
open scoped ComplexConjugate
namespace FF

lemma schurBack_defect (a b : ℂ) :
    ‖1 + a * b‖ ^ 2 - ‖conj a + b‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

lemma schurBack_den_ne_zero {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) :
    1 + a * b ≠ 0 := by
  have hab : ‖a * b‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg a) hb) ha
  intro h
  have heq : a * b = -1 := by linear_combination h
  rw [heq] at hab
  norm_num at hab

lemma norm_schurBack_le {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) :
    ‖(conj a + b) / (1 + a * b)‖ ≤ 1 := by
  rw [norm_div, div_le_one (norm_pos_iff.mpr (schurBack_den_ne_zero ha hb))]
  have hd := schurBack_defect a b
  have hapos : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hbpos : 0 ≤ 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  have := mul_nonneg hapos hbpos
  nlinarith [norm_nonneg (1 + a * b), norm_nonneg (conj a + b)]

lemma norm_schurBack_lt {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ‖(conj a + b) / (1 + a * b)‖ < 1 := by
  rw [norm_div, div_lt_one (norm_pos_iff.mpr (schurBack_den_ne_zero ha hb.le))]
  have hd := schurBack_defect a b
  have hapos : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hbpos : 0 < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  have := mul_pos hapos hbpos
  nlinarith [norm_nonneg (1 + a * b), norm_nonneg (conj a + b)]

lemma schur_one_sub_mul_ne_zero {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) :
    1 - a * b ≠ 0 := by
  simpa only [norm_neg, mul_neg, ← sub_eq_add_neg] using
    schurBack_den_ne_zero ha (b := -b) (by simpa using hb)

lemma norm_diskBack_lt {a φ : ℂ} (ha : ‖a‖ < 1) (hφ : ‖φ‖ < 1) :
    ‖(a + φ) / (1 + conj a * φ)‖ < 1 := by
  simpa only [Complex.conj_conj] using
    norm_schurBack_lt (a := conj a) (by simpa using ha) hφ

lemma schurBack_quotient (a F H : ℂ) (hF : F ≠ 0) :
    (conj a + H / F) / (1 + a * (H / F)) = (conj a * F + H) / (F + a * H) := by
  field_simp

lemma schurBack_linear_den_ne_zero {a F H : ℂ} (ha : ‖a‖ < 1) (hF : F ≠ 0)
    (hH : ‖H‖ ≤ ‖F‖) : F + a * H ≠ 0 := by
  have hb : ‖H / F‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hF)]
    exact hH
  have hn := schurBack_den_ne_zero ha hb
  intro h
  apply hn
  field_simp
  simpa using h

lemma norm_schurBack_linear_le {a F H : ℂ} (ha : ‖a‖ < 1) (hF : F ≠ 0)
    (hH : ‖H‖ ≤ ‖F‖) : ‖(conj a * F + H) / (F + a * H)‖ ≤ 1 := by
  rw [← schurBack_quotient a F H hF]
  apply norm_schurBack_le ha
  rw [norm_div, div_le_one (norm_pos_iff.mpr hF)]
  exact hH

lemma diskBack_den_ne_zero {a φ : ℂ} (ha : ‖a‖ < 1) (hφ : ‖φ‖ ≤ 1) :
    1 + conj a * φ ≠ 0 :=
  schurBack_den_ne_zero (by simpa using ha) hφ

lemma disk_defect_ne_zero {a : ℂ} (ha : ‖a‖ < 1) :
    (1 : ℂ) - a * conj a ≠ 0 :=
  schur_one_sub_mul_ne_zero ha (by simpa using ha.le)

lemma cayley_schurBack_linear {a φ F H : ℂ} (ha : ‖a‖ < 1) (hφ : ‖φ‖ < 1)
    (hF0 : F ≠ 0) (hH : ‖H‖ ≤ ‖F‖) (hF : F - φ * H = 1) :
    ((1 + a * conj a) * (2 * F - 1) + 2 * conj a * φ * F + 2 * a * H) /
        (1 - a * conj a) =
      (1 + ((a + φ) / (1 + conj a * φ)) * ((conj a * F + H) / (F + a * H))) /
        (1 - ((a + φ) / (1 + conj a * φ)) * ((conj a * F + H) / (F + a * H))) := by
  have hA := schurBack_linear_den_ne_zero ha hF0 hH
  have hD := diskBack_den_ne_zero ha hφ.le
  have hD' : 1 + φ * conj a ≠ 0 := by simpa only [mul_comm] using hD
  have hd := disk_defect_ne_zero ha
  have ht := schur_one_sub_mul_ne_zero (norm_diskBack_lt ha hφ)
    (norm_schurBack_linear_le ha hF0 hH)
  symm
  apply (div_eq_iff ht).mpr
  field_simp [hA, hD, hd]
  have hFeq : F = 1 + φ * H := by linear_combination hF
  rw [hFeq]
  field_simp [hD']
  ring

lemma weighted_cauchy_re (a φ F H J c : ℂ) (d : ℝ) (hJ : J - c = φ * F) :
    (2 * (((1 + (‖a‖ ^ 2 : ℂ)) * F + conj a * J + a * H) / (d : ℂ)) -
      ((1 + (‖a‖ ^ 2 : ℂ)) + conj a * c + a * conj c) / (d : ℂ)).re =
    (((1 + (‖a‖ ^ 2 : ℂ)) * (2 * F - 1) + 2 * conj a * φ * F + 2 * a * H) /
      (d : ℂ)).re := by
  have hJeq : J = c + φ * F := by linear_combination hJ
  rw [hJeq]
  simp [Complex.mul_re, Complex.mul_im, Complex.div_ofReal_re]
  ring

lemma weighted_cauchy_cayley_re {a φ F H J c : ℂ} (ha : ‖a‖ < 1) (hφ : ‖φ‖ < 1)
    (hF0 : F ≠ 0) (hH : ‖H‖ ≤ ‖F‖) (hF : F - φ * H = 1) (hJ : J - c = φ * F) :
    (2 * (((1 + (‖a‖ ^ 2 : ℂ)) * F + conj a * J + a * H) /
        ((1 - ‖a‖ ^ 2 : ℝ) : ℂ)) -
      ((1 + (‖a‖ ^ 2 : ℂ)) + conj a * c + a * conj c) /
        ((1 - ‖a‖ ^ 2 : ℝ) : ℂ)).re =
      ((1 + ((a + φ) / (1 + conj a * φ)) * ((conj a * F + H) / (F + a * H))) /
        (1 - ((a + φ) / (1 + conj a * φ)) * ((conj a * F + H) / (F + a * H)))).re := by
  rw [weighted_cauchy_re a φ F H J c (1 - ‖a‖ ^ 2) hJ]
  have h := congrArg Complex.re (cayley_schurBack_linear ha hφ hF0 hH hF)
  simpa only [Complex.mul_conj', Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using h

end FF
