import FourierFrames.Theorem2i.Basic
import FourierFrames.Theorem2i.PhaseDecay

/-!
# M08 helper: the product f, phase derivative

See `blueprint/M08_Theorem2i.md`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

/-! ## §3. The function `f` -/

namespace B1

theorem cellLen_pos (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) : 0 < cellLen t n := by
  unfold cellLen
  have := h.mono (Nat.sub_lt hn Nat.one_pos)
  linarith

theorem im_zPt_neg (h : RegData ψ t C M) {n : ℕ} (hn : 1 ≤ n) : (zPt ψ t C n).im < 0 := by
  have h1 := h.im_zPt_le hn
  have h2 := h.cAngle_pos
  have h3 := cellLen_pos h hn
  have : 0 < 2 / Real.pi * (cAngle ψ t C * cellLen t n) := by positivity
  linarith

/-- The enumeration `n ↦ z_{n+1}` of the zero set. -/
def zEquiv (h : RegData ψ t C M) : ℕ ≃ ↥(zSet ψ t C) :=
  Equiv.ofBijective (fun n => ⟨zPt ψ t C (n + 1), n + 1, by omega, rfl⟩)
    ⟨fun a b hab => by
      have := h.zPt_injOn (x₁ := a + 1) (x₂ := b + 1) (by simp) (by simp)
        (congrArg Subtype.val hab)
      omega,
     fun ⟨a, n, hn, hna⟩ => ⟨n - 1, Subtype.ext (by
       simp only; rw [Nat.sub_add_cancel hn]; exact hna)⟩⟩

theorem zEquiv_apply (h : RegData ψ t C M) (n : ℕ) :
    ((zEquiv h n : zSet ψ t C) : ℂ) = zPt ψ t C (n + 1) := rfl

theorem notMem_zSet_of_im_nonneg (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    z ∉ zSet ψ t C := by
  rintro ⟨n, hn, rfl⟩
  have := im_zPt_neg h hn
  linarith

theorem hasSum_log_of_notMem (h : RegData ψ t C M) {z : ℂ} (hz : z ∉ zSet ψ t C) :
    HasSum (fun n : ℕ => Real.log ‖1 - z / zPt ψ t C (n + 1)‖ + z.re * convFac ψ t (n + 1))
      (Real.log ‖fProd ψ t C z‖) := by
  have H := OCS.hasSum_log_norm_canonicalProd h.isGenusOneData hz
  have H2 := (zEquiv h).hasSum_iff.mpr H
  have e : (fun n : ℕ => Real.log ‖1 - z / zPt ψ t C (n + 1)‖ + z.re * convFac ψ t (n + 1)) =
      (fun a : zSet ψ t C => Real.log ‖1 - z / (a : ℂ)‖ + (z * convFun ψ t C a).re) ∘ zEquiv h := by
    funext n
    simp only [Function.comp_apply, zEquiv_apply]
    rw [show convFun ψ t C (zPt ψ t C (n + 1)) = (convFac ψ t (n + 1) : ℂ) from
      h.convFun_zPt (by omega), Complex.re_mul_ofReal]
  rw [e]
  exact H2

end B1

theorem RegData.differentiable_fProd (h : RegData ψ t C M) : Differentiable ℂ (fProd ψ t C) :=
  OCS.differentiable_canonicalProd h.isGenusOneData

theorem RegData.fProd_ne_zero (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    fProd ψ t C z ≠ 0 := by
  unfold fProd
  rw [Ne, OCS.canonicalProd_eq_zero_iff h.isGenusOneData]
  exact B1.notMem_zSet_of_im_nonneg h hz

theorem RegData.hasSum_log_fProd (h : RegData ψ t C M) {z : ℂ} (hz : 0 ≤ z.im) :
    HasSum (fun n : ℕ => Real.log ‖1 - z / zPt ψ t C (n + 1)‖ + z.re * convFac ψ t (n + 1))
      (Real.log ‖fProd ψ t C z‖) :=
  B1.hasSum_log_of_notMem h (B1.notMem_zSet_of_im_nonneg h hz)

theorem RegData.isHB_fProd (h : RegData ψ t C M) : IsHB (fProd ψ t C) := by
  refine ⟨h.differentiable_fProd, fun z hz => h.fProd_ne_zero hz.le, ?_⟩
  intro z hz
  by_cases hc : conj z ∈ zSet ψ t C
  · have : fProd ψ t C (conj z) = 0 := by
      unfold fProd
      exact (OCS.canonicalProd_eq_zero_iff h.isGenusOneData).mpr hc
    rw [this, norm_zero]; exact norm_nonneg _
  · have H1 := h.hasSum_log_fProd hz.le
    have H2 := B1.hasSum_log_of_notMem h hc
    have hle : Real.log ‖fProd ψ t C (conj z)‖ ≤ Real.log ‖fProd ψ t C z‖ := by
      refine hasSum_le (fun n => ?_) H2 H1
      have hn : 1 ≤ n + 1 := by omega
      set a := zPt ψ t C (n + 1) with ha
      have ha0 : a ≠ 0 := by
        intro h0
        have := B1.im_zPt_neg h hn
        rw [← ha, h0] at this; simp at this
      have hay : a.im < 0 := B1.im_zPt_neg h hn
      have hre : (conj z).re = z.re := by simp
      have hne : conj z ≠ a := fun e => hc ⟨n + 1, hn, by rw [← ha]; exact e.symm⟩
      have hpos : 0 < ‖1 - conj z / a‖ := by
        rw [norm_pos_iff, sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq ha0]; exact hne
      have key : ‖1 - conj z / a‖ ≤ ‖1 - z / a‖ := by
        have e1 : ∀ w : ℂ, ‖1 - w / a‖ = ‖a - w‖ / ‖a‖ := fun w => by
          rw [show (1 : ℂ) - w / a = (a - w) / a by field_simp, norm_div]
        rw [e1, e1]
        gcongr
        apply le_of_sq_le_sq _ (norm_nonneg _)
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only [sub_re, sub_im, conj_re, conj_im]
        nlinarith [mul_pos_of_neg_of_neg hay (neg_neg_of_pos hz)]
      have := Real.log_le_log hpos key
      rw [hre]
      linarith
    exact (Real.log_le_log_iff (by
      rcases eq_or_ne (fProd ψ t C (conj z)) 0 with h0 | h0
      · exact absurd h0 (fun h0 => hc (by
          unfold fProd at h0
          exact (OCS.canonicalProd_eq_zero_iff h.isGenusOneData).mp h0))
      · exact norm_pos_iff.mpr h0) (norm_pos_iff.mpr (h.fProd_ne_zero hz.le))).mp hle

namespace B1

theorem logDeriv_factor {a c : ℂ} {x : ℂ} (ha : a ≠ 0) (hx : x ≠ a) :
    logDeriv (OCS.genusOneFactor a c) x = 1 / (x - a) + c := by
  have hA : HasDerivAt (fun z : ℂ ↦ 1 - z / a) (-(1 / a)) x :=
    (hasDerivAt_id' (x := x)).div_const a |>.const_sub 1
  have hB : HasDerivAt (fun z : ℂ ↦ Complex.exp (z * c)) (Complex.exp (x * c) * (1 * c)) x :=
    ((hasDerivAt_id' (x := x)).mul_const c).cexp
  have hD := hA.fun_mul hB
  have hf : OCS.genusOneFactor a c = fun z => (1 - z / a) * Complex.exp (z * c) := rfl
  rw [logDeriv_apply, hf, hD.deriv]
  have h1 : (1 : ℂ) - x / a ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq ha]; exact hx
  have h2 : x - a ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  ring

theorem summable_logDeriv (h : RegData ψ t C M) (x : ℝ) :
    Summable fun a : zSet ψ t C =>
      logDeriv (OCS.genusOneFactor a (convFun ψ t C a)) (x : ℂ) := by
  have hZ := h.isGenusOneData
  have hS : Summable fun a : zSet ψ t C =>
      2 * |x| * ‖(a : ℂ)‖⁻¹ ^ 2 + ‖convFun ψ t C a - (a : ℂ)⁻¹‖ :=
    (hZ.summable_inv_sq.mul_left _).add hZ.summable_sub_inv
  refine hS.of_norm_bounded_eventually ?_
  filter_upwards [hZ.eventually_small (2 * |x|)] with a ⟨ha1, _⟩
  have ha0 : (a : ℂ) ≠ 0 := hZ.ne_zero a.2
  have hapos : 0 < ‖(a : ℂ)‖ := norm_pos_iff.mpr ha0
  have h2x : 2 * |x| ≤ ‖(a : ℂ)‖ := by
    rwa [mul_inv_le_iff₀ hapos, one_mul] at ha1
  have hxa : (x : ℂ) ≠ a := by
    intro e
    have := B1.notMem_zSet_of_im_nonneg h (z := (x : ℂ)) (by simp)
    exact this (e ▸ a.2)
  rw [logDeriv_factor ha0 hxa]
  have hid : 1 / ((x : ℂ) - a) + convFun ψ t C a =
      (x : ℂ) / (a * (x - a)) + (convFun ψ t C a - (a : ℂ)⁻¹) := by
    have : (x : ℂ) - a ≠ 0 := sub_ne_zero.mpr hxa
    field_simp
    ring
  rw [hid]
  have hxa' : ‖(a : ℂ)‖ / 2 ≤ ‖(x : ℂ) - a‖ := by
    have := norm_sub_norm_le (a : ℂ) (x : ℂ)
    rw [norm_sub_rev] at this
    rw [Complex.norm_real, Real.norm_eq_abs] at *
    linarith
  refine (norm_add_le _ _).trans ?_
  have hxn : ‖(x : ℂ) / (a * (x - a))‖ ≤ 2 * |x| * ‖(a : ℂ)‖⁻¹ ^ 2 := by
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hxpos : 0 < ‖(x : ℂ) - a‖ := by linarith
    rw [div_le_iff₀ (by positivity)]
    have : ‖(a : ℂ)‖ * (‖(a : ℂ)‖ / 2) ≤ ‖(a : ℂ)‖ * ‖(x : ℂ) - a‖ :=
      mul_le_mul_of_nonneg_left hxa' hapos.le
    have e : 2 * |x| * ‖(a : ℂ)‖⁻¹ ^ 2 * (‖(a : ℂ)‖ * ‖(x : ℂ) - a‖) =
        2 * |x| * (‖(a : ℂ)‖ * ‖(x : ℂ) - a‖) / ‖(a : ℂ)‖ ^ 2 := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [abs_nonneg x]
  linarith

end B1

/-- `φ_f'(x) = ∑ |Im z_n| / |x - z_n|²`. -/
theorem RegData.hasSum_phaseDeriv_fProd (h : RegData ψ t C M) (x : ℝ) :
    HasSum (fun n : ℕ => -(zPt ψ t C (n + 1)).im / ‖(x : ℂ) - zPt ψ t C (n + 1)‖ ^ 2)
      (phaseDeriv (fProd ψ t C) x) := by
  have hZ := h.isGenusOneData
  have hxZ : (x : ℂ) ∉ zSet ψ t C := B1.notMem_zSet_of_im_nonneg h (by simp)
  have hxa : ∀ a : zSet ψ t C, (x : ℂ) ≠ a := fun a e => hxZ (e ▸ a.2)
  have hL := logDeriv_tprod_eq_tsum (s := Set.univ) isOpen_univ (Set.mem_univ (x : ℂ))
    (f := fun (a : zSet ψ t C) z => OCS.genusOneFactor a (convFun ψ t C a) z)
    (fun a => by
      rw [Ne, OCS.genusOneFactor_eq_zero_iff (hZ.ne_zero a.2)]; exact hxa a)
    (fun a => ((OCS.differentiable_genusOneFactor _ _).differentiableOn))
    (B1.summable_logDeriv h x)
    ⟨_, OCS.hasProdLocallyUniformlyOn_canonicalProd hZ⟩
    (by
      have := h.fProd_ne_zero (z := (x : ℂ)) (by simp)
      exact this)
  have hf : (fun z => ∏' a : zSet ψ t C, OCS.genusOneFactor a (convFun ψ t C a) z) =
      fProd ψ t C := rfl
  rw [hf] at hL
  have hpd : phaseDeriv (fProd ψ t C) x = -(∑' a : zSet ψ t C,
      logDeriv (OCS.genusOneFactor a (convFun ψ t C a)) (x : ℂ)).im := by
    rw [← hL, logDeriv_apply]; rfl
  rw [hpd]
  have H := (Complex.hasSum_im (B1.summable_logDeriv h x).hasSum).neg
  have H2 := (B1.zEquiv h).hasSum_iff.mpr H
  convert H2 using 1
  funext n
  simp only [Function.comp_apply, B1.zEquiv_apply]
  have hn : 1 ≤ n + 1 := by omega
  have ha0 : zPt ψ t C (n + 1) ≠ 0 := hZ.ne_zero (B1.zEquiv h n).2
  rw [B1.logDeriv_factor ha0 (hxa (B1.zEquiv h n)), show convFun ψ t C (zPt ψ t C (n + 1)) =
    (convFac ψ t (n + 1) : ℂ) from h.convFun_zPt hn]
  rw [Complex.add_im, Complex.ofReal_im, add_zero, one_div, Complex.inv_im, Complex.sub_im,
    Complex.ofReal_im, Complex.sq_norm]
  simp only [zero_sub, neg_neg, neg_div]

theorem RegData.tendsto_phaseDeriv_fProd (h : RegData ψ t C M) :
    Tendsto (phaseDeriv (fProd ψ t C)) (cocompact ℝ) (𝓝 0) := by
  exact h.tendsto_phaseDeriv_of_hasSum (g := phaseDeriv (fProd ψ t C)) (fun x => h.hasSum_phaseDeriv_fProd x)


end FF
