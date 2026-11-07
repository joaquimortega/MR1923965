import FourierFrames.Cited.Pavlov.Basic

/-!
# Uniform rational-kernel estimates for the conjugate Poisson integral

These estimates are independent of the positive regularization parameter.
-/

namespace FF.Pavlov

/-- A denominator occurring in the conjugate Poisson kernel is positive. -/
theorem poisson_square_denominator_pos {y t : ℝ} (hy : 0 < y) :
    0 < t ^ 2 + y ^ 2 := by positivity

/-- Algebraic form of the difference of two conjugate Poisson fractions. -/
theorem conjugatePoissonFraction_sub {y a b : ℝ} (hy : 0 < y) :
    a / (a ^ 2 + y ^ 2) - b / (b ^ 2 + y ^ 2) =
      (a-b) * (y ^ 2-a*b) / ((a ^ 2+y ^ 2)*(b ^ 2+y ^ 2)) := by
  have ha := ne_of_gt (poisson_square_denominator_pos (t := a) hy)
  have hb := ne_of_gt (poisson_square_denominator_pos (t := b) hy)
  field_simp
  ring

/-- A uniform difference bound for the fractions, away from their center. -/
theorem abs_conjugatePoissonFraction_sub_le {y a b : ℝ}
    (hy : 0 < y) (ha : a ≠ 0) (hb : b ≠ 0) :
    |a / (a ^ 2 + y ^ 2) - b / (b ^ 2 + y ^ 2)| ≤
      |a-b| / (|a| *|b|) := by
  have hda := poisson_square_denominator_pos (t := a) hy
  have hdb := poisson_square_denominator_pos (t := b) hy
  have hab : 0 < |a| *|b| := mul_pos (abs_pos.mpr ha) (abs_pos.mpr hb)
  rw [conjugatePoissonFraction_sub hy, abs_div, abs_mul,
    abs_of_pos (mul_pos hda hdb)]
  have hnum : |y^2-a*b| ≤ y^2 + |a| *|b| := by
    calc
      _ ≤ |y^2| + |a*b| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg (sq_nonneg y), abs_mul]
  have hden : (y^2+|a| *|b|) * (|a| *|b|) ≤
      (a^2+y^2)*(b^2+y^2) := by
    have hs : |a| *|b| ≤ a^2+b^2 := by
      nlinarith [sq_nonneg (|a|-|b|), sq_abs a, sq_abs b]
    have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg y)
    have he : (|a| *|b|)^2 = a^2*b^2 := by rw [mul_pow, sq_abs, sq_abs]
    nlinarith [sq_nonneg (y^2)]
  calc
    |a-b| * |y^2-a*b| / ((a^2+y^2)*(b^2+y^2)) ≤
        |a-b| * (y^2+|a| *|b|) / ((a^2+y^2)*(b^2+y^2)) := by
      gcongr
    _ ≤ |a-b| / (|a| *|b|) := by
      apply (div_le_div_iff₀ (mul_pos hda hdb) hab).mpr
      nlinarith [mul_le_mul_of_nonneg_left hden (abs_nonneg (a-b))]

/-- Uniform decay of a translated kernel difference outside twice the translation. -/
theorem abs_conjugatePoissonFraction_shift_sub_le {y s h : ℝ}
    (hy : 0 < y) (hs : s ≠ 0) (hsep : 2 * |h| ≤ |s|) :
    |(s+h) / ((s+h)^2+y^2) - s / (s^2+y^2)| ≤ 2 * |h| / s^2 := by
  have hspos : 0 < |s| := abs_pos.mpr hs
  have htri : |s| ≤ |s+h| + |h| := by
    simpa only [add_sub_cancel_right] using abs_sub (s+h) h
  have hapos : 0 < |s+h| := by linarith
  have ha : s+h ≠ 0 := abs_pos.mp hapos
  have hb := abs_conjugatePoissonFraction_sub_le hy ha hs
  simp only [add_sub_cancel_left] at hb
  apply hb.trans
  apply (div_le_div_iff₀ (mul_pos hapos hspos) (sq_pos_of_ne_zero hs)).mpr
  have hprod : s^2 ≤ 2 * (|s+h| * |s|) := by
    nlinarith [mul_nonneg hspos.le (show 0 ≤ 2 * |s+h| - |s| by linarith),
      sq_abs s]
  nlinarith [mul_le_mul_of_nonneg_left hprod (abs_nonneg h)]

/-- The preceding uniform decay estimate with the conventional `π` normalization. -/
theorem abs_conjugatePoissonKernel_shift_sub_le {y s h : ℝ}
    (hy : 0 < y) (hs : s ≠ 0) (hsep : 2 * |h| ≤ |s|) :
    |(s+h) / (Real.pi * ((s+h)^2+y^2)) - s / (Real.pi * (s^2+y^2))| ≤
      2 * |h| / (Real.pi * s^2) := by
  have he : (s+h) / (Real.pi * ((s+h)^2+y^2)) -
      s / (Real.pi * (s^2+y^2)) =
      ((s+h) / ((s+h)^2+y^2) - s / (s^2+y^2)) / Real.pi := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, abs_div, abs_of_pos Real.pi_pos]
  have hb := div_le_div_of_nonneg_right
    (abs_conjugatePoissonFraction_shift_sub_le hy hs hsep) Real.pi_pos.le
  convert hb using 1
  ring

end FF.Pavlov
