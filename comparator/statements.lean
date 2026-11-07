/-- **The Paley–Wiener reduction** (p. 790): `{e^{iλx}}_{λ ∈ Λ}` is a Fourier frame if and only if
`Λ` is sampling for `PW`. -/
theorem isFourierFrame_iff_isSampling (hPW : PaleyWienerThm) (Λ : Set ℝ) :
    IsFourierFrame Λ ↔ IsSampling Λ := by
  sorry

/-- **The "evident fact"** (p. 799): if `E ∈ \overline{HB}` and `|E(z)| ≃ e^{π Im z}` for
`Im z ≥ 0`, then `H(E) = PW`. -/
theorem heEqPW_of_comparable (hPW : PaleyWienerThm) {E : ℂ → ℂ} (hE : IsHB E)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) :
    HEEqPW E := by
  sorry

/-- **Theorem 1** (p. 795), necessity: a separated sampling sequence is the zero set of
`EF + E^*F^*` with `E, F ∈ \overline{HB}` and `H(E) = PW`. -/
theorem theorem1_necessity (hPW : PaleyWienerThm) (hC : TheoremC) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry

/-- **Theorem 1** (p. 795), sufficiency. -/
theorem theorem1_sufficiency (hPW : PaleyWienerThm) (hE : TheoremE)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) {E F : ℂ → ℂ} (hEHB : IsHB E) (hFHB : IsHB F)
    (hEPW : HEEqPW E) (hzero : ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ)) :
    IsSampling Λ := by
  sorry

/-- **Theorem 1** (p. 795): a separated sequence `Λ` is sampling for `PW` if and only if there are
`E, F ∈ \overline{HB}` with `H(E) = PW` such that `Λ` is the zero set of `EF + E^*F^*`. -/
theorem theorem1 (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) :
    IsSampling Λ ↔ ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry

/-- **Remark** (p. 797): a separated complete interpolating sequence is the zero set of `E + E^*`
for some `E ∈ \overline{HB}` with `H(E) = PW`. -/
theorem completeInterpolating_zero_set (hPW : PaleyWienerThm) (hC : TheoremC) (hD : TheoremD)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hcis : IsCompleteInterpolating Λ) :
    ∃ E : ℂ → ℂ, IsHB E ∧ HEEqPW E ∧ ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry

/-- **Corollary 1** (p. 798): a separated sampling sequence is "everywhere denser" than some
complete interpolating sequence `Γ = {γ_k}`: every `[γ_k, γ_{k+1})` contains a point of `Λ`. -/
theorem corollary1 (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ IsCompleteInterpolating (Set.range γ) ∧
      ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1) := by
  sorry

/-- **Claim** (p. 798): Landau's inequality (Theorem B) follows from the John–Nirenberg theorem,
Pavlov's theorem (Theorem A) and Theorem 1: for a separated sampling sequence `Λ`,
`n_Λ(b) - n_Λ(a) ≥ b - a - A log⁺(b - a) - B`. -/
theorem landau_inequality (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE)
    (hF : TheoremF) (hA : PavlovBMO) (hJN : JohnNirenberg)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ A B : ℝ, ∀ a b : ℝ, a < b →
      ENNReal.ofReal (b - a - A * Real.posLog (b - a) - B) ≤ ((Λ ∩ Ioc a b).encard : ℝ≥0∞) := by
  sorry

/-- **The example of p. 798**: `{k + log⁺|k|}` is a complete interpolating sequence. -/
theorem logExample_isCompleteInterpolating (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsCompleteInterpolating logExample := by
  sorry

/-- **The example of p. 798**: `n_Λ(R) = R - log R + O(1)` and `-n_Λ(-R) = R + log R + O(1)` for
`Λ = {k + log⁺|k|}`. -/
theorem logExample_count : ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
    |((logExample ∩ Ioc 0 R).ncard : ℝ) - (R - Real.log R)| ≤ C ∧
      |((logExample ∩ Ioc (-R) 0).ncard : ℝ) - (R + Real.log R)| ≤ C := by
  sorry

/-- **Landau's inequality is best possible** (p. 798): `{k + log⁺|k|}` is a separated sampling
sequence for which no coefficient `A < 1` of the logarithmic term works. -/
theorem landau_sharp (hPW : PaleyWienerThm) (hE : TheoremE) :
    IsSeparated logExample ∧ IsSampling logExample ∧
      ∀ A : ℝ, A < 1 → ¬ ∃ B : ℝ, ∀ a b : ℝ, a < b →
        ENNReal.ofReal (b - a - A * Real.posLog (b - a) - B) ≤
          ((logExample ∩ Ioc a b).encard : ℝ≥0∞) := by
  sorry

/-- **Corollary 2** (p. 800): `Λ(ψ)` is sampling for `PW` if there is `f ∈ \overline{HB}` with
`φ_f'(x) → 0` as `|x| → ∞` and `|U_ψ(z) - log|f(z)|| ≲ 1` for `Im z ≥ 0`. -/
theorem corollary2 (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {f : ℂ → ℂ} (hf : IsHB f)
    (hφ : Tendsto (phaseDeriv f) (cocompact ℝ) (𝓝 0))
    (happ : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.exp (UPsi ψ z - C) ≤ ‖f z‖ ∧ ‖f z‖ ≤ Real.exp (UPsi ψ z + C)) :
    IsSampling (LambdaPsi ψ) := by
  sorry

/-- **Theorem 2 (i)** (p. 801): if `ψ = 0` on `(-∞, 0]` and `ψ` induces a logarithmically regular
partition, then `Λ(ψ)` is sampling for `PW`.  The printed hypothesis `ψ'(x) = 1/O(x)`
(`ψ'(x) ≥ c/x` for large `x`) is not needed by the proof and is not assumed (NOTEBOOK N-26, I-03).
The proof needs `ψ` to be "sufficiently regular" (p. 790; "the smoothness of `ψ` ensures",
p. 802), which the statement does not say: we assume `ψ'` eventually nonincreasing
(NOTEBOOK N-22). -/
theorem theorem2_i (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hreg : IsLogRegularPartition ψ) (hmono : ∃ X : ℝ, AntitoneOn (deriv ψ) (Set.Ici X)) :
    IsSampling (LambdaPsi ψ) := by
  sorry

/-- **Theorem 2 (i)**, in the form its proof gives (p. 802): if `ψ = 0` on `(-∞, 0]` and `ψ` induces
a logarithmically regular partition on whose cells `ψ' ≲ 1/d_n`, then `Λ(ψ)` is sampling for `PW`.
The hypothesis `ψ'(x) = 1/O(x)` of the printed statement is not needed (NOTEBOOK N-22, N-26). -/
theorem theorem2_i_of_densityBound (hPW : PaleyWienerThm) (hE : TheoremE) (hDS : DSPerturbation)
    {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hreg : IsLogRegularPartitionWithDensity ψ) :
    IsSampling (LambdaPsi ψ) := by
  sorry

/-- **Theorem 2 (ii)** (p. 801): if `ψ = 0` on `(-∞, 0]` and `ψ'(x) = o(1/x)`, then `Λ(ψ)` is not
sampling for `PW`.  The proof uses no cited theorem, so the statement has no `PaleyWienerThm`
hypothesis: it is unconditional (NOTEBOOK I-03). -/
theorem theorem2_ii {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ)
    (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hsmall : Tendsto (fun x ↦ x * deriv ψ x) atTop (𝓝 0)) :
    ¬ IsSampling (LambdaPsi ψ) := by
  sorry

/-! ## Phase 2: the cited results that are proved, and the main results with them discharged -/

/-- **The Paley–Wiener theorem** (phase 2). -/
theorem paleyWiener_holds : PaleyWienerThm := by
  sorry

/-- **The John–Nirenberg inequality** (phase 2). -/
theorem johnNirenberg_holds : JohnNirenberg := by
  sorry

/-- **de Branges' Theorem C** (phase 2). -/
theorem theoremC_holds : TheoremC := by
  sorry

/-- **de Branges' Theorem D** (phase 2). -/
theorem theoremD_holds : TheoremD := by
  sorry

/-- **de Branges' Theorem E** (phase 2). -/
theorem theoremE_holds : TheoremE := by
  sorry

/-- **Lemma III of Duffin–Schaeffer**, unconditionally. -/
theorem dsPerturbation_holds : DSPerturbation := by
  sorry

/-- **Fourier frames ⟺ sampling** (p. 790), unconditionally. -/
theorem isFourierFrame_iff_isSampling_unconditional (Λ : Set ℝ) :
    IsFourierFrame Λ ↔ IsSampling Λ := by
  sorry

/-- **The "evident fact"** (p. 799), unconditionally. -/
theorem heEqPW_of_comparable_unconditional {E : ℂ → ℂ} (hE : IsHB E)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.im →
      c * Real.exp (Real.pi * z.im) ≤ ‖E z‖ ∧ ‖E z‖ ≤ C * Real.exp (Real.pi * z.im)) :
    HEEqPW E := by
  sorry

/-- **Theorem 1, sufficiency**, unconditionally. -/
theorem theorem1_sufficiency_unconditional {Λ : Set ℝ} (hΛ : IsSeparated Λ) {E F : ℂ → ℂ}
    (hEHB : IsHB E) (hFHB : IsHB F) (hEPW : HEEqPW E)
    (hzero : ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ)) :
    IsSampling Λ := by
  sorry

/-- **Theorem 1, necessity**, from de Branges' Theorems C and F alone. -/
theorem theorem1_necessity_of_theoremCF (hC : TheoremC) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry

/-- **Theorem 1**, from de Branges' Theorems C and F alone. -/
theorem theorem1_of_theoremCF (hC : TheoremC) (hF : TheoremF) {Λ : Set ℝ} (hΛ : IsSeparated Λ) :
    IsSampling Λ ↔ ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry

/-- **Remark p. 797**, from de Branges' Theorem C alone. -/
theorem completeInterpolating_zero_set_of_theoremC (hC : TheoremC)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hcis : IsCompleteInterpolating Λ) :
    ∃ E : ℂ → ℂ, IsHB E ∧ HEEqPW E ∧ ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry

/-- **Corollary 1**, from de Branges' Theorems C and F alone. -/
theorem corollary1_of_theoremCF (hC : TheoremC) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ IsCompleteInterpolating (Set.range γ) ∧
      ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1) := by
  sorry

/-- **Landau's inequality** (the Claim of §4), from de Branges' Theorems C and F and Pavlov's
Theorem A alone. -/
theorem landau_inequality_of_theoremCF_pavlov (hC : TheoremC) (hF : TheoremF) (hA : PavlovBMO)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ A B : ℝ, ∀ a b : ℝ, a < b →
      ENNReal.ofReal (b - a - A * Real.posLog (b - a) - B) ≤ ((Λ ∩ Ioc a b).encard : ℝ≥0∞) := by
  sorry

/-- **The example of p. 798** is a complete interpolating sequence, unconditionally. -/
theorem logExample_isCompleteInterpolating_unconditional :
    IsCompleteInterpolating logExample := by
  sorry

/-- **Landau's inequality is best possible**, unconditionally. -/
theorem landau_sharp_unconditional :
    IsSeparated logExample ∧ IsSampling logExample ∧
      ∀ A : ℝ, A < 1 → ¬ ∃ B : ℝ, ∀ a b : ℝ, a < b →
        ENNReal.ofReal (b - a - A * Real.posLog (b - a) - B) ≤
          ((logExample ∩ Ioc a b).encard : ℝ≥0∞) := by
  sorry

/-- **Corollary 2**, unconditionally. -/
theorem corollary2_unconditional {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) {f : ℂ → ℂ} (hf : IsHB f)
    (hφ : Tendsto (phaseDeriv f) (cocompact ℝ) (𝓝 0))
    (happ : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im →
      Real.exp (UPsi ψ z - C) ≤ ‖f z‖ ∧ ‖f z‖ ≤ Real.exp (UPsi ψ z + C)) :
    IsSampling (LambdaPsi ψ) := by
  sorry

/-- **Theorem 2 (i)** (with `ψ'` eventually nonincreasing), unconditionally. -/
theorem theorem2_i_unconditional {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ)
    (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0) (hreg : IsLogRegularPartition ψ)
    (hmono : ∃ X : ℝ, AntitoneOn (deriv ψ) (Set.Ici X)) :
    IsSampling (LambdaPsi ψ) := by
  sorry

/-- **Theorem 2 (i)** (with the cell density bound), unconditionally. -/
theorem theorem2_i_of_densityBound_unconditional {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ)
    (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0) (hreg : IsLogRegularPartitionWithDensity ψ) :
    IsSampling (LambdaPsi ψ) := by
  sorry

/-- **Theorem 1, necessity**, from de Branges' Theorem F alone. -/
theorem theorem1_necessity_of_theoremF (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry

/-- **Theorem 1**, from de Branges' Theorem F alone. -/
theorem theorem1_of_theoremF (hF : TheoremF) {Λ : Set ℝ} (hΛ : IsSeparated Λ) :
    IsSampling Λ ↔ ∃ E F : ℂ → ℂ, IsHB E ∧ IsHB F ∧ HEEqPW E ∧
      ∀ z : ℂ, E z * F z + fstar E z * fstar F z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry

/-- **Remark p. 797**, unconditionally. -/
theorem completeInterpolating_zero_set_unconditional
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hcis : IsCompleteInterpolating Λ) :
    ∃ E : ℂ → ℂ, IsHB E ∧ HEEqPW E ∧ ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  sorry

/-- **Corollary 1**, from de Branges' Theorem F alone. -/
theorem corollary1_of_theoremF (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ IsCompleteInterpolating (Set.range γ) ∧
      ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1) := by
  sorry

/-- **Landau's inequality**, from de Branges' Theorem F and Pavlov's Theorem A alone. -/
theorem landau_inequality_of_theoremF_pavlov (hF : TheoremF) (hA : PavlovBMO)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ A B : ℝ, ∀ a b : ℝ, a < b →
      ENNReal.ofReal (b - a - A * Real.posLog (b - a) - B) ≤ ((Λ ∩ Ioc a b).encard : ℝ≥0∞) := by
  sorry
