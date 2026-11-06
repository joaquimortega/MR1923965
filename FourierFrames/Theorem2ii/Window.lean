import FourierFrames.Defs

/-!
# M09 helper: the window lemma

The only place where `x ψ'(x) → 0` is used in Theorem 2 (ii).
-/

open MeasureTheory Metric Set Complex Filter Topology

noncomputable section

namespace FF

namespace T2ii

lemma tendsto_atTop_of_h0 {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0) :
    Tendsto ψ atTop atTop := by
  rcases hψ.2.2.1 with h | h
  · exact h
  · exfalso
    have : ∀ᶠ x in atBot, ψ x ≤ -1 := h.eventually (eventually_le_atBot (-1))
    obtain ⟨b, hb⟩ := eventually_atBot.1 this
    have := hb (min b 0) (min_le_left _ _)
    rw [h0 _ (min_le_right _ _)] at this
    norm_num at this

/-- Slow growth: `x ψ'(x) ≤ ε` on `[R, ∞)` gives `ψ x - ψ x₀ ≤ ε log (x/x₀)`. -/
lemma psi_sub_le {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {ε R : ℝ} (hR : 0 < R)
    (hε : ∀ x, R ≤ x → x * deriv ψ x ≤ ε) {x₀ x : ℝ} (hx₀ : R ≤ x₀) (hx : x₀ ≤ x) :
    ψ x - ψ x₀ ≤ ε * (Real.log x - Real.log x₀) := by
  have hd : Differentiable ℝ ψ := hψ.1.differentiable one_ne_zero
  have hmono : MonotoneOn (fun y ↦ ε * Real.log y - ψ y) (Ici R) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici R) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ hd.continuous.continuousOn
      exact continuousOn_const.mul (Real.continuousOn_log.mono (fun y hy ↦ by
        simp only [mem_Ici] at hy; simp only [mem_compl_iff, mem_singleton_iff]; linarith [hy]))
    · rw [interior_Ici]
      intro y hy
      have : 0 < y := lt_trans hR hy
      refine DifferentiableAt.differentiableWithinAt ?_
      exact ((Real.differentiableAt_log this.ne').const_mul _).sub (hd y)
    · rw [interior_Ici]
      intro y hy
      have hy0 : 0 < y := lt_trans hR hy
      have h1 : HasDerivAt (fun y ↦ ε * Real.log y - ψ y) (ε * y⁻¹ - deriv ψ y) y :=
        ((Real.hasDerivAt_log hy0.ne').const_mul ε).sub (hd y).hasDerivAt
      rw [h1.deriv]
      have := hε y (le_of_lt hy)
      have h2 : deriv ψ y ≤ ε / y := by rw [le_div_iff₀ hy0]; linarith
      rw [← div_eq_mul_inv]; linarith
  have := hmono (mem_Ici.2 hx₀) (mem_Ici.2 (hx₀.trans hx)) hx
  simp only at this
  linarith

theorem exists_window {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hsmall : Tendsto (fun x ↦ x * deriv ψ x) atTop (𝓝 0)) {η s : ℝ} (hη : 0 < η) (hs : 0 < s)
    (A₀ : ℝ) :
    ∃ a₁ a₂ : ℝ, A₀ ≤ a₁ ∧ 8 ≤ a₁ ∧ 16 * a₁ ≤ a₂ ∧ s ≤ Real.log (a₂ / (4 * a₁)) ∧
      ∀ l ∈ LambdaPsi ψ, l ∈ Icc (2 * a₁ + 3) (a₂ - 3) → ∃ k : ℤ, |l - (k + 1 / 2)| ≤ η := by
  have hcont : Continuous ψ := hψ.1.continuous
  have hmono : Monotone ψ := hψ.2.1
  have hinf := tendsto_atTop_of_h0 hψ h0
  set s' : ℝ := max (s + 1) 3 with hs'
  have hs'3 : 3 ≤ s' := le_max_right _ _
  have hs'pos : 0 < s' := by linarith
  have hs's : s + 1 ≤ s' := le_max_left _ _
  set ε : ℝ := η / s' with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 (hsmall.eventually (eventually_le_nhds hεpos))
  set R : ℝ := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRε : ∀ x, R ≤ x → x * deriv ψ x ≤ ε := fun x hx ↦
    hR₀ x ((le_max_left _ _).trans hx)
  set R' : ℝ := max R (max 19 (2 * A₀ + 3)) with hR'
  have hR'R : R ≤ R' := le_max_left _ _
  have hR'19 : 19 ≤ R' := (le_max_left _ _).trans (le_max_right _ _)
  have hR'A : 2 * A₀ + 3 ≤ R' := (le_max_right _ _).trans (le_max_right _ _)
  -- integer `n`
  set n : ℤ := ⌈ψ R'⌉ with hn
  have hn1 : ψ R' ≤ n + 1 / 2 := by
    have := Int.le_ceil (ψ R'); linarith
  obtain ⟨b, hb⟩ := eventually_atTop.1 (hinf.eventually (eventually_ge_atTop ((n : ℝ) + 1 / 2)))
  have hb' := hb (max b R') (le_max_left _ _)
  obtain ⟨x₀, hx₀mem, hx₀⟩ := intermediate_value_Icc (le_max_right b R')
    hcont.continuousOn ⟨hn1, hb'⟩
  have hx₀R' : R' ≤ x₀ := hx₀mem.1
  have hx₀19 : 19 ≤ x₀ := hR'19.trans hx₀R'
  have hx₀pos : 0 < x₀ := by linarith
  have hx₀R : R ≤ x₀ := hR'R.trans hx₀R'
  have hexp3 : (8 : ℝ) ≤ Real.exp s' := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    have : Real.exp 3 ≤ Real.exp s' := Real.exp_le_exp.2 hs'3
    have h8 : (8 : ℝ) ≤ Real.exp 1 ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) h1 3]
    linarith
  refine ⟨(x₀ - 3) / 2, x₀ * Real.exp s' + 3, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · nlinarith
  · have hpos : 0 < 4 * ((x₀ - 3) / 2) := by linarith
    have : Real.exp s' / 2 ≤ (x₀ * Real.exp s' + 3) / (4 * ((x₀ - 3) / 2)) := by
      rw [le_div_iff₀ hpos]
      nlinarith [Real.exp_pos s']
    have h2 := Real.log_le_log (by positivity) this
    rw [Real.log_div (Real.exp_pos s').ne' (by norm_num), Real.log_exp] at h2
    have := Real.log_two_lt_d9
    linarith
  · rintro l ⟨k, hk⟩ ⟨hl1, hl2⟩
    have hl1' : x₀ ≤ l := by linarith
    have hl2' : l ≤ x₀ * Real.exp s' := by linarith
    refine ⟨k - n - 1, ?_⟩
    have hlpos : 0 < l := by linarith
    have hup : ψ l - ψ x₀ ≤ ε * (Real.log l - Real.log x₀) :=
      psi_sub_le hψ (by linarith) hRε hx₀R hl1'
    have hlog : Real.log l - Real.log x₀ ≤ s' := by
      rw [← Real.log_div hlpos.ne' hx₀pos.ne']
      calc Real.log (l / x₀) ≤ Real.log (Real.exp s') := by
            apply Real.log_le_log (by positivity)
            rw [div_le_iff₀ hx₀pos]; linarith
        _ = s' := Real.log_exp _
    have hηle : ε * (Real.log l - Real.log x₀) ≤ η := by
      calc ε * (Real.log l - Real.log x₀) ≤ ε * s' := by gcongr
        _ = η := by rw [hε]; field_simp
    have hlow : ψ x₀ ≤ ψ l := hmono hl1'
    have : l - (((k - n - 1 : ℤ) : ℝ) + 1 / 2) = ψ x₀ - ψ l := by
      push_cast
      have : l + ψ l = k := hk
      linarith
    rw [this, abs_le]
    constructor <;> linarith
end T2ii

end FF
