import FourierFrames.Theorem1.Necessity
import FourierFrames.Theorem1.Sufficiency
import FourierFrames.Corollary1.Rotate
import FourierFrames.Corollary1.Kernel
import FourierFrames.Corollary1.ClosedGraph

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace FF

open Suff

/-!
# M04 — Corollary 1 and the remark of p. 797

See `blueprint/M04_Sufficiency.md`.
-/

/-! ## Enumerating a level set by `ℤ` -/

/-- A continuous increasing bijection `φ` of `ℝ` has level sets `{φ ∈ α + πℤ}` enumerated
increasingly by `ℤ`. -/
theorem exists_levelSet_enum {φ : ℝ → ℝ} (hm : StrictMono φ) (hs : Function.Surjective φ)
    (α : ℝ) : ∃ γ : ℤ → ℝ, StrictMono γ ∧ Set.range γ = phaseLevel φ α := by
  classical
  let e : ℝ ≃o ℝ := hm.orderIsoOfSurjective φ hs
  refine ⟨fun k ↦ e.symm (α + k * Real.pi), ?_, ?_⟩
  · intro j k hjk
    apply e.symm.strictMono
    have := Real.pi_pos
    have : (j : ℝ) < k := by exact_mod_cast hjk
    nlinarith
  · ext x
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      have : φ (e.symm (α + k * Real.pi)) = α + k * Real.pi := e.apply_symm_apply _
      exact this
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply e.injective
      rw [e.apply_symm_apply]
      exact hk.symm

/-- A half-open interval `[u, v)` with `v - u ≥ π` meets every coset `c + πℤ`. -/
theorem exists_mem_Ico_add_int_mul_pi (c u v : ℝ) (h : u + Real.pi ≤ v) :
    ∃ j : ℤ, u ≤ c + j * Real.pi ∧ c + j * Real.pi < v := by
  have hπ := Real.pi_pos
  refine ⟨⌈(u - c) / Real.pi⌉, ?_, ?_⟩
  · have := Int.le_ceil ((u - c) / Real.pi)
    rw [div_le_iff₀ hπ] at this
    linarith
  · have := Int.ceil_lt_add_one ((u - c) / Real.pi)
    have h2 : (⌈(u - c) / Real.pi⌉ : ℝ) * Real.pi < ((u - c) / Real.pi + 1) * Real.pi :=
      mul_lt_mul_of_pos_right this hπ
    have h3 : ((u - c) / Real.pi + 1) * Real.pi = u - c + Real.pi := by field_simp
    linarith

/-! ## Corollary 1 (p. 798) -/

/-- **Corollary 1**, strong form: the complete interpolating sequence `Γ` can be taken
separated (needed by Pavlov's theorem in the Claim). -/
theorem corollary1_strong (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE)
    (hF : TheoremF) {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ IsSeparated (Set.range γ) ∧
      IsCompleteInterpolating (Set.range γ) ∧ ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1) := by
  obtain ⟨E, F, hEHB, hFHB, hEPW, hzero⟩ := theorem1_necessity hPW hC hF hΛ hs
  have hstrict : IsStrictHB E := HEEqPW.isStrictHB hEHB hEPW
  have hE0 : ∀ x : ℝ, E x ≠ 0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  obtain ⟨G, hGHB, hG0, hGΛ⟩ := exists_noRealZero_hb hFHB hzero
  obtain ⟨φE, hφE, hφE'⟩ := exists_isPhaseFunction hEHB.1 hE0
  obtain ⟨φG, hφG, hφG'⟩ := exists_isPhaseFunction hGHB.1 hG0
  have hφEm : StrictMono φE :=
    strictMono_of_hasDerivAt_pos hφE' (fun x ↦ hstrict.phaseDeriv_pos (hE0 x))
  have hGnn : ∀ x, 0 ≤ phaseDeriv G x := fun x ↦ hGHB.phaseDeriv_nonneg (hG0 x)
  have hφGm : Monotone φG := monotone_of_hasDerivAt_nonneg hφG' hGnn
  obtain ⟨α, hα⟩ := exists_not_exceptional hstrict
  obtain ⟨hT, hB⟩ := HEEqPW.phase_tendsto hPW hE hEHB hEPW hφE hφE'
  have hφEs : Function.Surjective φE := hφE.1.surjective hT hB
  obtain ⟨γ, hγm, hγr⟩ := exists_levelSet_enum hφEm hφEs α
  have hαe : ¬ Exceptional E α := hα
  have hsepΓ := HEEqPW.levelSet_separated hPW hE hEHB hEPW hφE hαe
  have hcisΓ := HEEqPW.levelSet_cis hE hEHB hEPW hφE hαe
  refine ⟨γ, hγm, by rw [hγr]; exact hsepΓ, by rw [hγr]; exact hcisΓ, fun k ↦ ?_⟩
  -- interlacing
  have hmem : ∀ k, φE (γ k) ∈ {y | ∃ n : ℤ, y = α + n * Real.pi} := by
    intro k
    have : γ k ∈ phaseLevel φE α := hγr ▸ ⟨k, rfl⟩
    obtain ⟨n, hn⟩ := this
    exact ⟨n, hn⟩
  obtain ⟨n, hn⟩ := hmem k
  obtain ⟨n', hn'⟩ := hmem (k + 1)
  have hlt : φE (γ k) < φE (γ (k + 1)) := hφEm (hγm (by omega))
  have hnn : n < n' := by
    rw [hn, hn'] at hlt
    have : (n : ℝ) < n' := by nlinarith [Real.pi_pos]
    exact_mod_cast this
  have hdiff : φE (γ k) + Real.pi ≤ φE (γ (k + 1)) := by
    rw [hn, hn']
    have : (n : ℝ) + 1 ≤ n' := by exact_mod_cast hnn
    nlinarith [Real.pi_pos]
  set ψ : ℝ → ℝ := fun x ↦ φE x + φG x with hψ
  have hψc : Continuous ψ := hφE.1.add hφG.1
  have hψ1 : ψ (γ k) + Real.pi ≤ ψ (γ (k + 1)) := by
    have := hφGm (hγm.monotone (show k ≤ k + 1 by omega))
    simp only [hψ]; linarith
  obtain ⟨j, hj1, hj2⟩ := exists_mem_Ico_add_int_mul_pi (Real.pi / 2) _ _ hψ1
  have hivt := intermediate_value_Icc (hγm.monotone (show k ≤ k + 1 by omega)) hψc.continuousOn
  obtain ⟨x, hx, hxψ⟩ := hivt ⟨hj1, hj2.le⟩
  have hxlt : x < γ (k + 1) := by
    rcases lt_or_eq_of_le hx.2 with h | h
    · exact h
    · rw [h] at hxψ; linarith
  refine ⟨x, ?_, hx.1, hxlt⟩
  have hxm : (x : ℂ) ∈ Complex.ofReal '' phaseLevel (fun t ↦ φE t + φG t) (Real.pi / 2) :=
    ⟨x, ⟨j, hxψ⟩, rfl⟩
  have h2 := (zero_set_eq_phaseLevel hstrict hGHB hE0 hG0 hφE hφG (x : ℂ)).mpr hxm
  obtain ⟨y, hy, hxy⟩ := hGΛ _ h2
  have : x = y := by exact_mod_cast hxy
  rwa [this]

/-- **Corollary 1** (p. 798): a separated sampling sequence is "everywhere denser" than some
complete interpolating sequence `Γ = {γ_k}`: every `[γ_k, γ_{k+1})` contains a point of `Λ`. -/
theorem corollary1 (hPW : PaleyWienerThm) (hC : TheoremC) (hE : TheoremE) (hF : TheoremF)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hs : IsSampling Λ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ IsCompleteInterpolating (Set.range γ) ∧
      ∀ k : ℤ, ∃ x ∈ Λ, γ k ≤ x ∧ x < γ (k + 1) := by
  obtain ⟨γ, h1, -, h3, h4⟩ := corollary1_strong hPW hC hE hF hΛ hs
  exact ⟨γ, h1, h3, h4⟩

/-! ## The remark of p. 797 -/

/-- A complete interpolating sequence is a sampling sequence (bounded inverse of the sampling map
`PW → ℓ²(Λ)`, open mapping theorem). -/
theorem isSampling_of_isCompleteInterpolating (hPW : PaleyWienerThm) {Λ : Set ℝ}
    (hΛ : IsSeparated Λ) (hcis : IsCompleteInterpolating Λ) : IsSampling Λ :=
  CG.isSampling_aux hPW hΛ hcis

theorem HEEqPW.rotate {E : ℂ → ℂ} (h : HEEqPW E) (θ : ℝ) :
    HEEqPW (fun z ↦ Complex.exp (I * θ) * E z) :=
  HEEqPW.rotate_aux h θ

/-- The zero set of `E + E^*` for `E` strict without real zeros. -/
theorem zero_set_single {E : ℂ → ℂ} (hE : IsStrictHB E) (hE0 : ∀ x : ℝ, E x ≠ 0)
    {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) (z : ℂ) :
    E z + fstar E z = 0 ↔ ∃ x ∈ phaseLevel φ (Real.pi / 2), z = (x : ℂ) := by
  have h1 : IsPhaseFunction (fun _ : ℂ ↦ (1 : ℂ)) (fun _ ↦ (0 : ℝ)) :=
    ⟨continuous_const, fun x ↦ by simp⟩
  have := zero_set_eq_phaseLevel hE isHB_one hE0 (fun x ↦ one_ne_zero) hφ h1 z
  simp only [fstar, map_one, mul_one] at this
  show E z + conj (E (conj z)) = 0 ↔ _
  rw [this]
  simp only [add_zero, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

/-- Formula (1) of p. 793 on the real axis: `K_E(x, y) = |E(x)E(y)| sin(φ(y) - φ(x)) /
(π (y - x))` for real `x ≠ y`. -/
theorem deBrangesKernel_real {E : ℂ → ℂ} {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) {x y : ℝ}
    (hxy : x ≠ y) :
    deBrangesKernel E x y =
      ((‖E x‖ * ‖E y‖ * Real.sin (φ y - φ x) / (Real.pi * (y - x)) : ℝ) : ℂ) := by
  have hne : (y : ℂ) ≠ conj (x : ℂ) := by
    rw [Complex.conj_ofReal]; exact_mod_cast hxy.symm
  unfold deBrangesKernel
  simp only [hne, ↓reduceIte]
  have hx := hφ.2 x
  have hy := hφ.2 y
  simp only [fstar_apply, Complex.conj_ofReal, Complex.conj_conj]
  have hs : ((Real.sin (φ y - φ x) : ℝ) : ℂ) =
      (Complex.exp (-((φ y : ℂ) - φ x) * I) - Complex.exp (((φ y : ℂ) - φ x) * I)) * I / 2 := by
    rw [Complex.ofReal_sin]; push_cast; exact Complex.sin.eq_1 _
  have hyne : (y : ℂ) - x ≠ 0 := by
    intro h; exact hxy (by exact_mod_cast (sub_eq_zero.mp h).symm)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul]
  rw [hs]
  conv_lhs => rw [hx, hy]
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_I]
  push_cast
  field_simp
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 3 <;> ring_nf

/-- The kernels at the points of a complete interpolating sequence are orthogonal:
`K_E(a, b) = 0` for `a ≠ b` in `Λ` (Theorem D, Cauchy–Schwarz and the norm identity). -/
theorem kernel_orthogonal (hPW : PaleyWienerThm) (hD : TheoremD) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {Λ : Set ℝ} (hΛ : IsSeparated Λ)
    (hcis : IsCompleteInterpolating Λ)
    (hnorm : ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Λ f)
    {a b : ℝ} (ha : a ∈ Λ) (hb : b ∈ Λ) (hab : a ≠ b) : deBrangesKernel E a b = 0 :=
  kernel_orthogonal_aux hPW hD hEHB hEPW hΛ hcis hnorm ha hb hab

/-- Completeness: a complete interpolating `Λ` is a full level set of the phase. -/
theorem levelSet_eq_of_cis (hPW : PaleyWienerThm) (hD : TheoremD) {E : ℂ → ℂ}
    (hEHB : IsHB E) (hEPW : HEEqPW E) {Λ : Set ℝ} (hΛ : IsSeparated Λ)
    (hcis : IsCompleteInterpolating Λ)
    (hnorm : ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Λ f)
    {φ : ℝ → ℝ} (hφ : IsPhaseFunction E φ) : ∃ β : ℝ, Λ = phaseLevel φ β := by
  have hπ := Real.pi_pos
  have hstrict := HEEqPW.isStrictHB hEHB hEPW
  have hE0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  obtain ⟨g, hgPW, hg0⟩ := exists_memPW_eval_ne_zero
  -- `Λ` is nonempty
  have hne : Λ.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    obtain ⟨f, -, hfu⟩ := hcis (fun _ ↦ 0) (by simp [hemp])
    have h1 := hfu g ⟨hgPW, by simp [hemp]⟩
    have h2 := hfu (fun _ ↦ 0) ⟨memPW_zero, by simp [hemp]⟩
    have := congrFun (h1.trans h2.symm) 0
    simp [hg0] at this
  obtain ⟨a₀, ha₀⟩ := hne
  -- every point of `Λ` lies on the level set of `φ(a₀)`
  have hsub : ∀ b ∈ Λ, b ∈ phaseLevel φ (φ a₀) := by
    intro b hb
    by_cases hba : b = a₀
    · exact ⟨0, by simp [hba]⟩
    · have h0 := kernel_orthogonal hPW hD hEHB hEPW hΛ hcis hnorm ha₀ hb (Ne.symm hba)
      rw [deBrangesKernel_real hφ (Ne.symm hba)] at h0
      have h1 : ‖E a₀‖ * ‖E b‖ * Real.sin (φ b - φ a₀) / (Real.pi * (b - a₀)) = 0 := by
        exact_mod_cast h0
      have hna : 0 < ‖E a₀‖ := norm_pos_iff.mpr (hE0 a₀)
      have hnb : 0 < ‖E b‖ := norm_pos_iff.mpr (hE0 b)
      have hba' : b - a₀ ≠ 0 := sub_ne_zero.mpr hba
      have h2 : Real.sin (φ b - φ a₀) = 0 := by
        rw [div_eq_zero_iff] at h1
        rcases h1 with h1 | h1
        · rcases mul_eq_zero.mp h1 with h1 | h1
          · exact absurd h1 (mul_pos hna hnb).ne'
          · exact h1
        · exact absurd h1 (mul_ne_zero hπ.ne' hba')
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h2
      exact ⟨n, by linarith⟩
  refine ⟨φ a₀, Set.Subset.antisymm hsub ?_⟩
  intro x hx
  by_contra hxΛ
  obtain ⟨hKHE, hrep⟩ := hD E hstrict hE0 (x : ℂ)
  set K : ℂ → ℂ := deBrangesKernel E (x : ℂ) with hKdef
  have hKPW : MemPW K := (hEPW.1 K).mp hKHE
  have hK0 : ∀ b ∈ Λ, K b = 0 := by
    intro b hb
    have hxb : x ≠ b := fun h ↦ hxΛ (h ▸ hb)
    simp only [hKdef]
    rw [deBrangesKernel_real hφ hxb]
    obtain ⟨n, hn⟩ := hsub b hb
    obtain ⟨m, hm⟩ := hx
    have : Real.sin (φ b - φ x) = 0 := by
      rw [Real.sin_eq_zero_iff]
      exact ⟨n - m, by push_cast; linarith⟩
    rw [this]; simp
  have hKz : K = fun _ ↦ 0 := by
    obtain ⟨f, -, hfu⟩ := hcis (fun _ ↦ 0) (by simp)
    have h1 := hfu K ⟨hKPW, fun b hb ↦ hK0 b hb⟩
    have h2 := hfu (fun _ ↦ 0) ⟨memPW_zero, fun b hb ↦ rfl⟩
    exact h1.trans h2.symm
  have hgx : MemPW (fun z ↦ g (z - x)) := hgPW.comp_sub_ofReal x
  have h1 := hrep _ ((hEPW.1 _).mpr hgx)
  have h2 : ∫ t : ℝ, g ((t : ℂ) - x) * conj (deBrangesKernel E (x : ℂ) t) /
      ((‖E t‖ ^ 2 : ℝ) : ℂ) = 0 := by
    have : ∀ t : ℝ, deBrangesKernel E (x : ℂ) t = 0 := fun t ↦ congrFun hKz t
    simp [this]
  rw [h2] at h1
  simp [hg0] at h1

/-- **Remark** (p. 797): a separated complete interpolating sequence is the zero set of `E + E^*`
for some `E ∈ \overline{HB}` with `H(E) = PW`. -/
theorem completeInterpolating_zero_set (hPW : PaleyWienerThm) (hC : TheoremC) (hD : TheoremD)
    {Λ : Set ℝ} (hΛ : IsSeparated Λ) (hcis : IsCompleteInterpolating Λ) :
    ∃ E : ℂ → ℂ, IsHB E ∧ HEEqPW E ∧ ∀ z : ℂ, E z + fstar E z = 0 ↔ ∃ x ∈ Λ, z = (x : ℂ) := by
  have hs := isSampling_of_isCompleteInterpolating hPW hΛ hcis
  obtain ⟨E₀, hEHB, hEPW, -, hnorm⟩ := exists_E hPW hC hs
  have hE0 : ∀ x : ℝ, E₀ x ≠ 0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  obtain ⟨φ, hφ, -⟩ := exists_isPhaseFunction hEHB.1 hE0
  obtain ⟨β, hβ⟩ := levelSet_eq_of_cis hPW hD hEHB hEPW hΛ hcis hnorm hφ
  set θ : ℝ := β - Real.pi / 2 with hθ
  have hEHB' := hEHB.rotate θ
  have hEPW' := hEPW.rotate θ
  have hstrict := HEEqPW.isStrictHB hEHB' hEPW'
  have hE0' := HEEqPW.ne_zero_ofReal hEHB' hEPW'
  refine ⟨_, hEHB', hEPW', fun z ↦ ?_⟩
  rw [zero_set_single hstrict hE0' (hφ.rotate θ) z]
  have : phaseLevel (fun x ↦ φ x - θ) (Real.pi / 2) = Λ := by
    rw [hβ]
    ext x
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, by simp only [hθ] at hk; linarith⟩
    · rintro ⟨k, hk⟩; exact ⟨k, by simp only [hθ]; linarith⟩
  rw [this]

end FF
