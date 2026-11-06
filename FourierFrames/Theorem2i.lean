
import FourierFrames.Theorem2i.Estimates

/-!
# M08 — Theorem 2 (i)

See `blueprint/M08_Theorem2i.md`.  Construction of the canonical product `f` with zeros
`z_n = r_n e^{-i c d_n / r_n}` (one zero per cell `(t_{n-1}, t_n]` of `ψ`-mass `1`) such that
`|U_ψ - log|f|| ≲ 1` on `Im z ≥ 0`, and application of Corollary 2.

**Warning (see the blueprint, "Issues in the source", §A).**  The estimate of the cells at
distance `≲ d_n` from `z` needs the local density bound `ψ' ≲ 1/d_n` on `[t_{n-1}, t_n]`
(`DensBound`), which is *not* implied by the hypotheses of `theorem2_i`.  All lemmas below that
need it carry `hK : DensBound ψ t K`.  `theorem2_i_of_regular` is the provable statement;
`theorem2_i` (identical to `comparator/statements.lean`) has no honest proof from the paper's
argument unless `DensBound` can be derived or added to the hypotheses.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

variable {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ}

/-! ## §6. Theorem 2 (i) -/

/-- The data of `IsLogRegularPartitionWithDensity`: a partition with `RegData` and `DensBound`. -/
theorem RegData.of_isLogRegularPartitionWithDensity {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ)
    (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0) (hreg : IsLogRegularPartitionWithDensity ψ) :
    ∃ (t : ℕ → ℝ) (C M K : ℝ), RegData ψ t C M ∧ DensBound ψ t K := by
  obtain ⟨t, t0, hm, hpsi, ⟨C, hC⟩, ⟨M, hM⟩, K, hK⟩ := hreg
  refine ⟨t, max C 1, M, K, ⟨hψ, h0, le_max_right _ _, t0, hm, hpsi, ?_, hM⟩, hK⟩
  intro n hn
  obtain ⟨h1, h2⟩ := hC n hn
  have d1 : 0 < t n - t (n - 1) := sub_pos.2 (hm (by omega))
  have d2 : 0 < t (n + 1) - t n := sub_pos.2 (hm (by omega))
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) d1.le),
    h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) d2.le)⟩

/-- The provable version of Theorem 2 (i), with the extra local regularity `DensBound`
(`RegData` is produced from the hypotheses of `theorem2_i` by `RegData.of_isLogRegularPartition`). -/
theorem theorem2_i_of_regular (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} {t : ℕ → ℝ} {C M K : ℝ} (h : RegData ψ t C M) (hK : DensBound ψ t K) :
    IsSampling (LambdaPsi ψ) := by
  obtain ⟨B, hB⟩ := h.exists_approx hK
  refine corollary2 hPW hE hDS h.adm h.isHB_fProd h.tendsto_phaseDeriv_fProd ⟨B, fun z hz => ?_⟩
  have hne := h.fProd_ne_zero hz
  have hpos : 0 < ‖fProd ψ t C z‖ := norm_pos_iff.2 hne
  obtain ⟨hb1, hb2⟩ := abs_le.1 (hB z hz)
  constructor
  · calc Real.exp (UPsi ψ z - B) ≤ Real.exp (Real.log ‖fProd ψ t C z‖) :=
          Real.exp_le_exp.2 (by linarith)
      _ = ‖fProd ψ t C z‖ := Real.exp_log hpos
  · calc ‖fProd ψ t C z‖ = Real.exp (Real.log ‖fProd ψ t C z‖) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (UPsi ψ z + B) := Real.exp_le_exp.2 (by linarith)

/-- An eventually nonincreasing `ψ'` gives the local density bound: on `[t_{n-1}, t_n]`,
`ψ' ≤ ψ'(t_{n-1}) ≤ 1/d_{n-1} ≤ C/d_n` for the cells beyond `X` (the previous cell has mass `1`
and `ψ' ≥ ψ'(t_{n-1})` on it), and `ψ'` is bounded on the finitely many cells before `X`. -/
theorem RegData.densBound_of_antitoneOn (h : RegData ψ t C M)
    (hmono : ∃ X : ℝ, AntitoneOn (deriv ψ) (Set.Ici X)) : ∃ K : ℝ, DensBound ψ t K := by
  obtain ⟨X, hX⟩ := hmono
  have hcont : Continuous (deriv ψ) := h.adm.1.continuous_deriv le_rfl
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h.tendsto_t.eventually_ge_atTop X)
  have hT0 : 0 ≤ t (N + 1) := by
    have := h.mono.monotone (Nat.zero_le (N + 1)); rwa [h.t0] at this
  obtain ⟨B0, hB0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t (N + 1))).exists_bound_of_continuousOn
    hcont.continuousOn
  have hB0' : ∀ s ∈ Icc (0 : ℝ) (t (N + 1)), deriv ψ s ≤ max B0 0 :=
    fun s hs => by
      have := hB0 s hs
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  refine ⟨max C (max B0 0 * t (N + 1)), fun n hn s hs => ?_⟩
  have hd : 0 < cellLen t n := sub_pos.2 (h.mono (by omega))
  rw [le_div_iff₀ hd]
  by_cases hnN : n ≤ N + 1
  · -- finitely many early cells
    have htn : t n ≤ t (N + 1) := h.mono.monotone hnN
    have ht0 : 0 ≤ t (n - 1) := by
      have := h.mono.monotone (Nat.zero_le (n - 1)); rwa [h.t0] at this
    have hs' : s ∈ Icc (0 : ℝ) (t (N + 1)) := ⟨ht0.trans hs.1, hs.2.trans htn⟩
    have hdn : cellLen t n ≤ t (N + 1) := by
      unfold cellLen; linarith
    calc deriv ψ s * cellLen t n ≤ max B0 0 * t (N + 1) :=
          mul_le_mul (hB0' s hs') hdn hd.le (le_max_right _ _)
      _ ≤ _ := le_max_right _ _
  · push Not at hnN
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hs
    have hm1 : 1 ≤ m := by omega
    have hXm : X ≤ t (m - 1) := hN _ (by omega)
    have hdm : 0 < cellLen t m := sub_pos.2 (h.mono (by omega))
    -- ψ' s ≤ ψ' (t m)
    have h1 : deriv ψ s ≤ deriv ψ (t m) :=
      hX (show X ≤ t m from hXm.trans (h.mono.monotone (by omega))) (show X ≤ s from
        (hXm.trans (h.mono.monotone (by omega))).trans hs.1) hs.1
    -- ψ' (t m) ≤ ψ' u on the cell m
    have h2 : ∀ u ∈ cell t m, deriv ψ (t m) ≤ deriv ψ u := fun u hu =>
      hX (show X ≤ u from hXm.trans hu.1.le) (show X ≤ t m from hXm.trans
        (h.mono.monotone (by omega))) hu.2
    have hint : deriv ψ (t m) * cellLen t m ≤ 1 := by
      have hc := h.integral_cell hm1
      have hI : IntegrableOn (deriv ψ) (cell t m) :=
        (hcont.continuousOn.integrableOn_Icc (a := t (m - 1)) (b := t m)).mono_set
          Ioc_subset_Icc_self
      have : ∫ u in cell t m, deriv ψ (t m) ≤ ∫ u in cell t m, deriv ψ u :=
        setIntegral_mono_on (integrableOn_const (by simp [cell])) hI measurableSet_Ioc h2
      rw [hc, setIntegral_const] at this
      have hpos : 0 ≤ t m - t (m - 1) := (sub_pos.2 (h.mono (show m - 1 < m by omega))).le
      simpa [cell, cellLen, Real.volume_Ioc, smul_eq_mul, mul_comm, max_eq_left hpos] using this
    have hratio := (h.ratio m hm1).1
    have hdeq : t (m + 1) - t m = cellLen t (m + 1) := by simp [cellLen]
    have hnn : 0 ≤ deriv ψ (t m) := by
      exact h.adm.2.1.deriv_nonneg
    rw [hdeq] at hratio
    calc deriv ψ s * cellLen t (m + 1) ≤ deriv ψ (t m) * cellLen t (m + 1) :=
          mul_le_mul_of_nonneg_right h1 hd.le
      _ ≤ deriv ψ (t m) * (C * cellLen t m) := mul_le_mul_of_nonneg_left hratio hnn
      _ = C * (deriv ψ (t m) * cellLen t m) := by ring
      _ ≤ C * 1 := by
          have hC0 : 0 ≤ C := by linarith [h.one_le]
          exact mul_le_mul_of_nonneg_left hint hC0
      _ ≤ _ := by rw [mul_one]; exact le_max_left _ _

/-- **Theorem 2 (i)**, in the form its proof gives (p. 802): if `ψ = 0` on `(-∞, 0]` and `ψ` induces
a logarithmically regular partition on whose cells `ψ' ≲ 1/d_n`, then `Λ(ψ)` is sampling for `PW`.
The hypothesis `ψ'(x) = 1/O(x)` of the printed statement is not needed (NOTEBOOK N-22, N-26). -/
theorem theorem2_i_of_densityBound (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hreg : IsLogRegularPartitionWithDensity ψ) :
    IsSampling (LambdaPsi ψ) := by
  obtain ⟨t, C, M, K, h, hK⟩ := RegData.of_isLogRegularPartitionWithDensity hψ h0 hreg
  exact theorem2_i_of_regular hPW hE hDS h hK

/-- **Theorem 2 (i)** (p. 801), identical to `comparator/statements.lean`.  The paper's argument
needs `DensBound`, which follows from `hmono` (NOTEBOOK N-22). -/
theorem theorem2_i (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x → c / x ≤ deriv ψ x)
    (hreg : IsLogRegularPartition ψ) (hmono : ∃ X : ℝ, AntitoneOn (deriv ψ) (Set.Ici X)) :
    IsSampling (LambdaPsi ψ) := by
  obtain ⟨t, C, M, h⟩ := RegData.of_isLogRegularPartition hψ h0 hreg
  obtain ⟨K, hK⟩ := h.densBound_of_antitoneOn hmono
  exact theorem2_i_of_regular hPW hE hDS h hK

end FF
