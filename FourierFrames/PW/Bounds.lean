import FourierFrames.PW.Basic
import OrtegaCerdaSeip.Bernstein.Sinc

/-!
# M01 — Paley–Wiener space toolkit: pointwise and line bounds

See `blueprint/M01_PW.md`, §2.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- Imaginary translate of a transform: `pwFT g (z + i y) = pwFT (g e^{-y·}) z`. -/
theorem pwFT_add_mul_I (g : ℝ → ℂ) (y : ℝ) (z : ℂ) :
    pwFT g (z + y * I) = pwFT (fun t ↦ g t * ((Real.exp (-(y * t)) : ℝ) : ℂ)) z := by
  unfold pwFT
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only
  have : I * (z + (y : ℂ) * I) * (t : ℂ) = I * z * t + ((-(y * t) : ℝ) : ℂ) := by
    push_cast; ring_nf; simp [Complex.I_sq]; ring
  rw [this, Complex.exp_add, ← Complex.ofReal_exp]
  push_cast
  ring

theorem enorm_sq_mul_exp (g : ℝ → ℂ) (y t : ℝ) :
    ‖g t * ((Real.exp (-(y * t)) : ℝ) : ℂ)‖ₑ ^ 2 =
      ENNReal.ofReal (Real.exp (-(2 * y * t))) * ‖g t‖ₑ ^ 2 := by
  have he : ‖((Real.exp (-(y * t)) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (Real.exp (-(y * t))) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [enorm_mul, mul_pow, mul_comm, he,
    ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 3
  push_cast; ring

/-- `g ∈ L²(-π,π)` implies `g e^{-y·} ∈ L²(-π,π)` with `‖g e^{-y·}‖² ≤ e^{2π|y|} ‖g‖²`. -/
theorem memL2pi_mul_exp {g : ℝ → ℂ} (hg : MemL2pi g) (y : ℝ) :
    MemL2pi (fun t ↦ g t * ((Real.exp (-(y * t)) : ℝ) : ℂ)) ∧
      l2piSq (fun t ↦ g t * ((Real.exp (-(y * t)) : ℝ) : ℂ)) ≤
        ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * l2piSq g := by
  have hcont : Continuous (fun t : ℝ ↦ ((Real.exp (-(y * t)) : ℝ) : ℂ)) := by fun_prop
  have hle : l2piSq (fun t ↦ g t * ((Real.exp (-(y * t)) : ℝ) : ℂ)) ≤
        ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * l2piSq g := by
    unfold l2piSq
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
    rw [enorm_sq_mul_exp]
    gcongr
    have h1 : |t| ≤ Real.pi := abs_le.2 ⟨ht.1.le, ht.2⟩
    have : -(2 * y * t) ≤ 2 * Real.pi * |y| := by
      calc -(2 * y * t) ≤ |2 * y * t| := neg_le_abs _
        _ = 2 * |y| * |t| := by rw [abs_mul, abs_mul]; norm_num
        _ ≤ 2 * |y| * Real.pi := by gcongr
        _ = 2 * Real.pi * |y| := by ring
    exact this
  refine ⟨?_, hle⟩
  refine memLp_two_of_lintegral ((MemLp.aestronglyMeasurable hg).mul hcont.aestronglyMeasurable) ?_
  refine lt_of_le_of_lt hle ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 (l2piSq_ne_top hg))

/-- Imaginary translates of `f ∈ PW` are in `PW` (`z ↦ f(z + i y)` corresponds to `g e^{-y t}`),
and `‖f(· + iy)‖² = 2π ∫ |g|² e^{-2yt}`. -/
theorem pw_translate_I (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (y : ℝ) :
    MemPW (fun z ↦ f (z + y * I)) := by
  obtain ⟨g, hg, hfg, -⟩ := exists_pwFT hPW hf
  obtain ⟨hgy, -⟩ := memL2pi_mul_exp hg y
  have hfun : (fun z : ℂ ↦ f (z + y * I)) =
      pwFT (fun t ↦ g t * ((Real.exp (-(y * t)) : ℝ) : ℂ)) := by
    funext z
    rw [hfg, pwFT_add_mul_I]
  rw [hfun]
  exact (memPW_pwFT hPW hgy).1

/-- The exact norm of an imaginary translate: if `f = pwFT g` then
`‖f(· + iy)‖² = 2π ∫ e^{-2yt} |g(t)|² dt`. -/
theorem pwNormSq_translate_I (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (y : ℝ) :
    ∃ g : ℝ → ℂ, MemL2pi g ∧ f = pwFT g ∧
      pwNormSq f = ENNReal.ofReal (2 * Real.pi) * l2piSq g ∧
      pwNormSq (fun z ↦ f (z + y * I)) = ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ t in Set.Ioc (-Real.pi) Real.pi, ENNReal.ofReal (Real.exp (-(2 * y * t))) * ‖g t‖ₑ ^ 2 := by
  obtain ⟨g, hg, hfg, hn⟩ := exists_pwFT hPW hf
  refine ⟨g, hg, hfg, hn, ?_⟩
  obtain ⟨hgy, -⟩ := memL2pi_mul_exp hg y
  have hfun : (fun z : ℂ ↦ f (z + y * I)) =
      pwFT (fun t ↦ g t * ((Real.exp (-(y * t)) : ℝ) : ℂ)) := by
    funext z
    rw [hfg, pwFT_add_mul_I]
  rw [hfun, (memPW_pwFT hPW hgy).2]
  congr 1
  unfold l2piSq
  refine lintegral_congr fun t ↦ ?_
  exact enorm_sq_mul_exp g y t

/-- **Pointwise bound** `|f(z)|² ≤ e^{2π|Im z|} ‖f‖²` (constant exactly `1`). -/
theorem pw_norm_sq_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (z : ℂ) :
    ‖f z‖ ^ 2 ≤ Real.exp (2 * Real.pi * |z.im|) * (pwNormSq f).toReal := by
  obtain ⟨g, hg, hfg, hn⟩ := exists_pwFT hPW hf
  subst hfg
  have h1 := norm_pwFT_le hg z
  have hN : (pwNormSq (pwFT g)).toReal = 2 * Real.pi * (l2piSq g).toReal := by
    rw [hn, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rw [hN]
  have hS : 0 ≤ 2 * Real.pi * (l2piSq g).toReal := by positivity
  calc ‖pwFT g z‖ ^ 2 ≤ (Real.exp (Real.pi * |z.im|) *
        Real.sqrt (2 * Real.pi * (l2piSq g).toReal)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = Real.exp (2 * Real.pi * |z.im|) * (2 * Real.pi * (l2piSq g).toReal) := by
        rw [mul_pow, Real.sq_sqrt hS, ← Real.exp_nat_mul]
        congr 2
        push_cast; ring

theorem ofReal_exp_neg_le {y t : ℝ} (ht : t ∈ Set.Ioc (-Real.pi) Real.pi) :
    ENNReal.ofReal (Real.exp (-(2 * y * t))) ≤ ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h1 : |t| ≤ Real.pi := abs_le.2 ⟨ht.1.le, ht.2⟩
  calc -(2 * y * t) ≤ |2 * y * t| := neg_le_abs _
    _ = 2 * |y| * |t| := by rw [abs_mul, abs_mul]; norm_num
    _ ≤ 2 * |y| * Real.pi := by gcongr
    _ = 2 * Real.pi * |y| := by ring

/-- **Line integrals** `∫ |f(x + iy)|² dx ≤ e^{2π|y|} ‖f‖²`. -/
theorem pw_line_integral_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (y : ℝ) :
    ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * pwNormSq f := by
  obtain ⟨g, hg, hfg, hn, hy⟩ := pwNormSq_translate_I hPW hf y
  have : ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 = pwNormSq (fun z ↦ f (z + y * I)) := rfl
  rw [this, hy, hn]
  calc ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ t in Set.Ioc (-Real.pi) Real.pi, ENNReal.ofReal (Real.exp (-(2 * y * t))) * ‖g t‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ t in Set.Ioc (-Real.pi) Real.pi,
          ENNReal.ofReal (Real.exp (2 * Real.pi * |y|)) * ‖g t‖ₑ ^ 2 := by
        refine mul_le_mul' le_rfl ?_
        refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
        exact mul_le_mul' (ofReal_exp_neg_le ht) le_rfl
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        unfold l2piSq
        ring

theorem enorm_sq_mul_exp_I_pi (w : ℂ) (u : ℂ) :
    ‖w * Complex.exp (I * Real.pi * u)‖ₑ ^ 2 =
      ENNReal.ofReal (Real.exp (-(2 * Real.pi * u.im))) * ‖w‖ₑ ^ 2 := by
  have he : ‖Complex.exp (I * Real.pi * u)‖ₑ = ENNReal.ofReal (Real.exp (-(Real.pi * u.im))) := by
    rw [← ofReal_norm, Complex.norm_exp]
    congr 2
    simp
  rw [enorm_mul, mul_pow, mul_comm, he, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
    ← Real.exp_nat_mul]
  congr 3
  push_cast; ring

/-- The `H²` norm bound, with constant `1`: for `y > 0`,
`∫ |f(x+iy) e^{iπ(x+iy)}|² dx ≤ ‖f‖²_{PW}`. -/
theorem MemPW.lintegral_mul_exp_le (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) {y : ℝ}
    (hy : 0 < y) :
    ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I) * Complex.exp (I * Real.pi * ((x : ℂ) + (y : ℂ) * I))‖ₑ ^ 2
      ≤ pwNormSq f := by
  obtain ⟨g, hg, hfg, hn, hyn⟩ := pwNormSq_translate_I hPW hf y
  have h1 : ∀ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I) * Complex.exp (I * Real.pi * ((x : ℂ) + (y : ℂ) * I))‖ₑ ^ 2
      = ENNReal.ofReal (Real.exp (-(2 * Real.pi * y))) * ‖f ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 := by
    intro x
    rw [enorm_sq_mul_exp_I_pi _ _ ]
    simp
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have : ∫⁻ x : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I)‖ₑ ^ 2 = pwNormSq (fun z ↦ f (z + y * I)) := rfl
  rw [this, hyn, hn, ← mul_assoc, mul_comm (ENNReal.ofReal (Real.exp _)), mul_assoc,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine mul_le_mul' le_rfl ?_
  unfold l2piSq
  refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  have : Real.exp (-(2 * Real.pi * y) + -(2 * y * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [ht.1, hy]
  calc _ ≤ ENNReal.ofReal 1 * ‖g t‖ₑ ^ 2 := mul_le_mul' (ENNReal.ofReal_le_ofReal this) le_rfl
    _ = _ := by simp

/-- `f(z) e^{iπz} ∈ H²(ℂ₊)`. -/
theorem MemPW.isH2Upper_mul_exp (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) :
    IsH2Upper (fun z ↦ f z * Complex.exp (I * Real.pi * z)) := by
  refine ⟨(hf.1.mul (by fun_prop)).differentiableOn, (pwNormSq f).toNNReal, fun y hy ↦ ?_⟩
  rw [ENNReal.coe_toNNReal (pwNormSq_ne_top hf)]
  exact MemPW.lintegral_mul_exp_le hPW hf hy

/-- **Derivative bound on `ℝ`**: `|f'(x)|² ≤ π² e² ‖f‖²` (Cauchy estimate on the circle of radius
`1/π`; the constant is absolute). -/
theorem pw_deriv_bound (hPW : PaleyWienerThm) {f : ℂ → ℂ} (hf : MemPW f) (x : ℝ) :
    ‖deriv f x‖ ^ 2 ≤ (Real.pi * Real.exp 1) ^ 2 * (pwNormSq f).toReal := by
  set N := (pwNormSq f).toReal with hN
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have hR : (0 : ℝ) < 1 / Real.pi := by positivity
  have hb : ‖deriv f (x : ℂ)‖ ≤ (Real.exp 1 * Real.sqrt N) / (1 / Real.pi) := by
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
      (hf.1.diffContOnCl) fun w hw ↦ ?_
    have him : |w.im| ≤ 1 / Real.pi := by
      have h1 : |(w - (x : ℂ)).im| ≤ ‖w - (x : ℂ)‖ := Complex.abs_im_le_norm _
      have h2 : ‖w - (x : ℂ)‖ = 1 / Real.pi := by
        simpa [dist_eq_norm] using hw
      simpa [h2] using h1
    have h3 := pw_norm_sq_le hPW hf w
    have h4 : Real.exp (2 * Real.pi * |w.im|) ≤ Real.exp 2 := by
      refine Real.exp_le_exp.2 ?_
      calc 2 * Real.pi * |w.im| ≤ 2 * Real.pi * (1 / Real.pi) := by gcongr
        _ = 2 := by field_simp
    have h5 : (Real.exp 1 * Real.sqrt N) ^ 2 = Real.exp 2 * N := by
      rw [mul_pow, Real.sq_sqrt hN0, ← Real.exp_nat_mul]; norm_num
    have h6 : ‖f w‖ ^ 2 ≤ (Real.exp 1 * Real.sqrt N) ^ 2 := by
      rw [h5]
      exact h3.trans (mul_le_mul_of_nonneg_right h4 hN0)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h6
  have hb2 : ‖deriv f (x : ℂ)‖ ≤ Real.pi * (Real.exp 1 * Real.sqrt N) := by
    simpa [div_eq_mul_inv, mul_comm] using hb
  calc ‖deriv f (x : ℂ)‖ ^ 2 ≤ (Real.pi * (Real.exp 1 * Real.sqrt N)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb2 2
    _ = (Real.pi * Real.exp 1) ^ 2 * N := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hN0]; ring

/-! ## A fixed function with `g(0) = 1` -/

/-- `((sin (π z / 2)) / (π z / 2))²`. -/
def pwBump (z : ℂ) : ℂ :=
  OCS.csinc (((Real.pi / 2 : ℝ) : ℂ) * z) ^ 2

theorem pwBump_zero : pwBump 0 = 1 := by
  simp [pwBump]

theorem differentiable_pwBump : Differentiable ℂ pwBump :=
  (OCS.differentiable_csinc.comp (differentiable_id.const_mul _)).pow 2

theorem norm_pwBump_sq_le (x : ℝ) : ‖pwBump (x : ℂ)‖ ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  set w : ℂ := (((Real.pi / 2 : ℝ) : ℂ) * (x : ℂ)) with hw
  have hwr : w = (((Real.pi / 2 * x : ℝ)) : ℂ) := by rw [hw]; push_cast; ring
  have hc1 : ‖OCS.csinc w‖ ≤ 1 := by rw [hwr]; exact OCS.norm_csinc_ofReal_le_one _
  have hc0 : 0 ≤ ‖OCS.csinc w‖ := norm_nonneg _
  have hpb : ‖pwBump (x : ℂ)‖ = ‖OCS.csinc w‖ ^ 2 := by
    unfold pwBump; rw [norm_pow]
  rw [hpb]
  by_cases hx : |x| ≤ 1
  · have h1 : (‖OCS.csinc w‖ ^ 2) ^ 2 ≤ 1 := by
      have : ‖OCS.csinc w‖ ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (‖OCS.csinc w‖ ^ 2)]
    have h2 : 1 ≤ 2 * (1 + x ^ 2)⁻¹ := by
      have : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    linarith
  · rw [not_le] at hx
    have hx0 : x ≠ 0 := by intro h; rw [h] at hx; simp at hx; linarith
    have hw0 : w ≠ 0 := by
      rw [hw]
      exact mul_ne_zero (by exact_mod_cast (by positivity : Real.pi / 2 ≠ 0)) (by exact_mod_cast hx0)
    have h1 := OCS.norm_csinc_le_div hw0
    have him : w.im = 0 := by rw [hwr]; simp
    have hnorm : ‖w‖ = Real.pi / 2 * |x| := by
      rw [hwr, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    rw [him, hnorm] at h1
    simp only [abs_zero, Real.exp_zero] at h1
    have h2 : ‖OCS.csinc w‖ ≤ 1 / |x| := by
      refine h1.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_gt_three, abs_pos.2 hx0]
    have h3 : ‖OCS.csinc w‖ ^ 2 ≤ (1 / |x|) ^ 2 := pow_le_pow_left₀ hc0 h2 2
    have h4 : (‖OCS.csinc w‖ ^ 2) ^ 2 ≤ ‖OCS.csinc w‖ ^ 2 := by
      have : ‖OCS.csinc w‖ ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg ‖OCS.csinc w‖]
    have h5 : (1 / |x|) ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [div_pow, sq_abs, one_pow, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 1 < x ^ 2 := by nlinarith [sq_abs x]
      nlinarith
    linarith

theorem memPW_pwBump : MemPW pwBump := by
  refine ⟨differentiable_pwBump, ?_, ?_⟩
  · intro ε hε
    refine ⟨1, fun z ↦ ?_⟩
    have h1 : ‖pwBump z‖ ≤ Real.exp (Real.pi * |z.im|) := by
      have h := OCS.norm_csinc_le_exp_abs_im (((Real.pi / 2 : ℝ) : ℂ) * z)
      have him : (((Real.pi / 2 : ℝ) : ℂ) * z).im = Real.pi / 2 * z.im := by simp
      rw [him, abs_mul, abs_of_pos (by positivity)] at h
      unfold pwBump
      rw [norm_pow]
      calc ‖OCS.csinc (((Real.pi / 2 : ℝ) : ℂ) * z)‖ ^ 2 ≤ (Real.exp (Real.pi / 2 * |z.im|)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc ‖pwBump z‖ ≤ Real.exp (Real.pi * |z.im|) := h1
      _ ≤ 1 * Real.exp ((Real.pi + ε) * ‖z‖) := by
        rw [one_mul]
        refine Real.exp_le_exp.2 ?_
        calc Real.pi * |z.im| ≤ Real.pi * ‖z‖ :=
              mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) Real.pi_pos.le
          _ ≤ (Real.pi + ε) * ‖z‖ := by nlinarith [norm_nonneg z]
  · have hc : Continuous (fun x : ℝ ↦ pwBump (x : ℂ)) :=
      differentiable_pwBump.continuous.comp Complex.continuous_ofReal
    rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 2)
      (hc.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact norm_pwBump_sq_le x

theorem pwNormSq_pwBump_pos : 0 < pwNormSq pwBump := by
  refine pos_iff_ne_zero.2 fun h ↦ ?_
  have := memPW_pwBump.eq_zero_of_pwNormSq_eq_zero h
  have h1 := congrFun this 0
  rw [pwBump_zero] at h1
  simp at h1

theorem exists_memPW_eval_ne_zero : ∃ g : ℂ → ℂ, MemPW g ∧ g 0 = 1 := by
  exact ⟨pwBump, memPW_pwBump, pwBump_zero⟩

/-- A uniform lower bound for point evaluations: for every real `x` there is `f ∈ PW`, namely a
translate of `pwBump`, with `0 < ‖f‖² < ∞` and `c ‖f‖² ≤ |f(x)|²`; the constant is
`c = ‖pwBump‖⁻²` (absolute), `‖pwBump‖² = pwNormSq pwBump`. -/
theorem pw_eval_lower : ∃ c : ℝ≥0, 0 < c ∧ ∀ x : ℝ, ∃ f : ℂ → ℂ, MemPW f ∧
    (c : ℝ≥0∞) * pwNormSq f ≤ ‖f (x : ℂ)‖ₑ ^ 2 ∧ pwNormSq f ≠ 0 ∧ pwNormSq f ≠ ⊤ := by
  set N := pwNormSq pwBump with hN
  have hN0 : N ≠ 0 := pwNormSq_pwBump_pos.ne'
  have hNt : N ≠ ⊤ := pwNormSq_ne_top memPW_pwBump
  have hNn : N.toNNReal ≠ 0 := fun h ↦ by
    rcases (ENNReal.toNNReal_eq_zero_iff _).1 h with h | h
    exacts [hN0 h, hNt h]
  refine ⟨(N.toNNReal)⁻¹, by simpa using pos_iff_ne_zero.2 hNn, fun x ↦ ?_⟩
  refine ⟨fun z ↦ pwBump (z - x), memPW_pwBump.comp_sub_ofReal x, ?_, ?_, ?_⟩
  · rw [pwNormSq_comp_sub_ofReal, ← hN]
    simp only [sub_self, pwBump_zero, enorm_one, one_pow]
    rw [ENNReal.coe_inv hNn, ENNReal.coe_toNNReal hNt]
    exact (ENNReal.inv_mul_cancel hN0 hNt).le
  · rw [pwNormSq_comp_sub_ofReal]; exact hN0
  · rw [pwNormSq_comp_sub_ofReal]; exact hNt

end FF
