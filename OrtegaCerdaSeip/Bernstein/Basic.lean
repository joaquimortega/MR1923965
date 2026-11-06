import OrtegaCerdaSeip.Defs

/-!
# M02 (Bernstein) — Exponential type and the algebra of `𝓑_τ`

See `blueprint/M02_Bernstein.md`, §1.1–§1.2.

Elementary closure properties of `IsExpTypeLE τ` (exponential type `≤ τ`) and of
`MemBernstein τ` (the Bernstein space `𝓑_τ`, p. 401) that do not need the Phragmén–Lindelöf
principle: sums, scalar multiples, products (`𝓑_σ · 𝓑_τ ⊆ 𝓑_{σ+τ}`), finite products,
monotonicity in `τ`, real translations, reflection `z ↦ -z`, multiplication by `e^{icz}`.
Complex translations (which need Phragmén–Lindelöf for the bound on `ℝ`) are in
`Bernstein/PhragmenLindelof.lean`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

variable {f g : ℂ → ℂ} {σ τ : ℝ}

/-! ### Exponential type -/

/-- A global bound `|f(z)| ≤ C e^{τ|z|}` gives exponential type `≤ τ`. -/
theorem IsExpTypeLE.of_bound {C : ℝ} (h : ∀ z, ‖f z‖ ≤ C * Real.exp (τ * ‖z‖)) :
    IsExpTypeLE τ f := by
  have hC : 0 ≤ C := by
    have := h 0
    simp only [norm_zero, mul_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  intro ε hε
  refine ⟨C, fun z ↦ (h z).trans ?_⟩
  gcongr
  linarith

/-- The constants in `IsExpTypeLE` can be taken nonnegative (they are automatically so). -/
theorem IsExpTypeLE.exists_nonneg (hf : IsExpTypeLE τ f) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ z, ‖f z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖) := by
  obtain ⟨C, hC⟩ := hf ε hε
  exact ⟨max C 0, le_max_right _ _, fun z ↦ (hC z).trans (by gcongr; exact le_max_left _ _)⟩

theorem IsExpTypeLE.mono (hf : IsExpTypeLE σ f) (h : σ ≤ τ) : IsExpTypeLE τ f := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := hf.exists_nonneg hε
  exact ⟨C, fun z ↦ (hC z).trans (by gcongr)⟩

theorem isExpTypeLE_const (c : ℂ) : IsExpTypeLE 0 (fun _ ↦ c) := by
  intro ε hε
  exact ⟨‖c‖, fun z ↦ le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (by positivity))⟩

theorem IsExpTypeLE.add (hf : IsExpTypeLE τ f) (hg : IsExpTypeLE τ g) :
    IsExpTypeLE τ (f + g) := by
  intro ε hε
  obtain ⟨C₁, h1⟩ := hf ε hε
  obtain ⟨C₂, h2⟩ := hg ε hε
  exact ⟨C₁ + C₂, fun z ↦ (norm_add_le (f z) (g z)).trans
    (by rw [add_mul]; exact add_le_add (h1 z) (h2 z))⟩

theorem IsExpTypeLE.neg (hf : IsExpTypeLE τ f) : IsExpTypeLE τ (-f) := by
  intro ε hε
  obtain ⟨C, hC⟩ := hf ε hε
  exact ⟨C, fun z ↦ by simpa using hC z⟩

theorem IsExpTypeLE.sub (hf : IsExpTypeLE τ f) (hg : IsExpTypeLE τ g) :
    IsExpTypeLE τ (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem IsExpTypeLE.const_mul (hf : IsExpTypeLE τ f) (c : ℂ) :
    IsExpTypeLE τ (fun z ↦ c * f z) := by
  intro ε hε
  obtain ⟨C, hC⟩ := hf ε hε
  refine ⟨‖c‖ * C, fun z ↦ ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC z) (norm_nonneg _)

/-- Types add under products. -/
theorem IsExpTypeLE.mul (hf : IsExpTypeLE σ f) (hg : IsExpTypeLE τ g) :
    IsExpTypeLE (σ + τ) (f * g) := by
  intro ε hε
  obtain ⟨C₁, hC₁, h1⟩ := hf.exists_nonneg (half_pos hε)
  obtain ⟨C₂, hC₂, h2⟩ := hg.exists_nonneg (half_pos hε)
  refine ⟨C₁ * C₂, fun z ↦ ?_⟩
  calc ‖(f * g) z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ (C₁ * Real.exp ((σ + ε / 2) * ‖z‖)) * (C₂ * Real.exp ((τ + ε / 2) * ‖z‖)) :=
        mul_le_mul (h1 z) (h2 z) (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * Real.exp ((σ + τ + ε) * ‖z‖) := by
        rw [show (σ + τ + ε) * ‖z‖ = (σ + ε / 2) * ‖z‖ + (τ + ε / 2) * ‖z‖ by ring,
          Real.exp_add]
        ring

/-- Types add under finite products. -/
theorem IsExpTypeLE.prod {ι : Type*} (s : Finset ι) {t : ι → ℝ} {F : ι → ℂ → ℂ}
    (h : ∀ i ∈ s, IsExpTypeLE (t i) (F i)) :
    IsExpTypeLE (∑ i ∈ s, t i) (fun z ↦ ∏ i ∈ s, F i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isExpTypeLE_const (1 : ℂ)
  | insert i s hi ih =>
    have h1 := h i (Finset.mem_insert_self _ _)
    have h2 := ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi]
    convert h1.mul h2 using 1
    funext z
    simp [Finset.prod_insert hi]

/-- Translation by any complex number preserves the type. -/
theorem IsExpTypeLE.comp_sub (hf : IsExpTypeLE τ f) (c : ℂ) :
    IsExpTypeLE τ (fun z ↦ f (z - c)) := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := hf.exists_nonneg hε
  refine ⟨C * Real.exp (|τ + ε| * ‖c‖), fun z ↦ (hC (z - c)).trans ?_⟩
  rw [mul_assoc, ← Real.exp_add]
  gcongr
  rcases le_or_gt 0 (τ + ε) with h | h
  · rw [abs_of_nonneg h]
    nlinarith [norm_sub_le z c]
  · rw [abs_of_neg h]
    nlinarith [norm_sub_norm_le z c]

/-- Dilation `z ↦ a z` multiplies the type by `|a|`. -/
theorem IsExpTypeLE.comp_const_mul (hf : IsExpTypeLE τ f) (a : ℂ) :
    IsExpTypeLE (‖a‖ * τ) (fun z ↦ f (a * z)) := by
  by_cases ha : a = 0
  · subst ha
    simpa using isExpTypeLE_const (f 0)
  · intro ε hε
    have ha' : 0 < ‖a‖ := norm_pos_iff.2 ha
    obtain ⟨C, hC0, hC⟩ := hf.exists_nonneg (div_pos hε ha')
    refine ⟨C, fun z ↦ (hC (a * z)).trans (le_of_eq ?_)⟩
    congr 2
    rw [norm_mul]
    field_simp

/-- Reflection `z ↦ -z` preserves the type. -/
theorem IsExpTypeLE.comp_neg (hf : IsExpTypeLE τ f) : IsExpTypeLE τ (fun z ↦ f (-z)) := by
  simpa using hf.comp_const_mul (-1)

/-- `e^{cz}` has type `|c|`. -/
theorem isExpTypeLE_cexp_mul (c : ℂ) : IsExpTypeLE ‖c‖ (fun z ↦ Complex.exp (c * z)) := by
  refine IsExpTypeLE.of_bound (C := 1) fun z ↦ ?_
  rw [Complex.norm_exp, one_mul]
  gcongr
  calc (c * z).re ≤ ‖c * z‖ := Complex.re_le_norm _
    _ = ‖c‖ * ‖z‖ := norm_mul _ _

/-! ### The Bernstein space -/

theorem MemBernstein.exists_bound (hf : MemBernstein τ f) :
    ∃ M, 0 ≤ M ∧ ∀ x : ℝ, ‖f x‖ ≤ M :=
  let ⟨M, hM⟩ := hf.2.2
  ⟨max M 0, le_max_right _ _, fun x ↦ (hM x).trans (le_max_left _ _)⟩

theorem MemBernstein.mono (hf : MemBernstein σ f) (h : σ ≤ τ) : MemBernstein τ f := by
  exact ⟨hf.1, hf.2.1.mono h, hf.2.2⟩

theorem memBernstein_const (c : ℂ) (hτ : 0 ≤ τ) : MemBernstein τ (fun _ ↦ c) := by
  exact ⟨differentiable_const _, (isExpTypeLE_const c).mono hτ, ⟨‖c‖, fun _ ↦ le_rfl⟩⟩

theorem MemBernstein.add (hf : MemBernstein τ f) (hg : MemBernstein τ g) :
    MemBernstein τ (f + g) := by
  obtain ⟨M₁, h1⟩ := hf.2.2
  obtain ⟨M₂, h2⟩ := hg.2.2
  exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    ⟨M₁ + M₂, fun x ↦ (norm_add_le (f x) (g x)).trans (add_le_add (h1 x) (h2 x))⟩⟩

theorem MemBernstein.neg (hf : MemBernstein τ f) : MemBernstein τ (-f) := by
  obtain ⟨M, h⟩ := hf.2.2
  exact ⟨hf.1.neg, hf.2.1.neg, ⟨M, fun x ↦ by simpa using h x⟩⟩

theorem MemBernstein.sub (hf : MemBernstein τ f) (hg : MemBernstein τ g) :
    MemBernstein τ (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem MemBernstein.const_mul (hf : MemBernstein τ f) (c : ℂ) :
    MemBernstein τ (fun z ↦ c * f z) := by
  obtain ⟨M, h⟩ := hf.2.2
  refine ⟨hf.1.const_mul c, hf.2.1.const_mul c, ⟨‖c‖ * M, fun x ↦ ?_⟩⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h x) (norm_nonneg _)

/-- `𝓑_σ · 𝓑_τ ⊆ 𝓑_{σ+τ}`. -/
theorem MemBernstein.mul (hf : MemBernstein σ f) (hg : MemBernstein τ g) :
    MemBernstein (σ + τ) (f * g) := by
  obtain ⟨M₁, hM₁, h1⟩ := hf.exists_bound
  obtain ⟨M₂, -, h2⟩ := hg.exists_bound
  refine ⟨hf.1.mul hg.1, hf.2.1.mul hg.2.1, ⟨M₁ * M₂, fun x ↦ ?_⟩⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (h1 x) (h2 x) (norm_nonneg _) hM₁

theorem MemBernstein.prod {ι : Type*} (s : Finset ι) {t : ι → ℝ} {F : ι → ℂ → ℂ}
    (h : ∀ i ∈ s, MemBernstein (t i) (F i)) :
    MemBernstein (∑ i ∈ s, t i) (fun z ↦ ∏ i ∈ s, F i z) := by
  have hb : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ (i ∈ s → ∀ x : ℝ, ‖F i x‖ ≤ M) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨M, hM0, hM⟩ := (h i hi).exists_bound
      exact ⟨M, hM0, fun _ ↦ hM⟩
    · exact ⟨0, le_rfl, fun h' ↦ absurd h' hi⟩
  choose M hM0 hM using hb
  refine ⟨Differentiable.fun_finsetProd fun i hi ↦ (h i hi).1,
    IsExpTypeLE.prod s fun i hi ↦ (h i hi).2.1, ⟨∏ i ∈ s, M i, fun x ↦ ?_⟩⟩
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _) fun i hi ↦ hM i hi x

/-- Real translations `T_a f = f(· - a)` act on `𝓑_τ` (isometrically, p. 413). -/
theorem MemBernstein.comp_sub_ofReal (hf : MemBernstein τ f) (a : ℝ) :
    MemBernstein τ (fun z ↦ f (z - a)) := by
  obtain ⟨M, h⟩ := hf.2.2
  exact ⟨hf.1.comp (differentiable_id.sub_const _), hf.2.1.comp_sub a,
    ⟨M, fun x ↦ by simpa using h (x - a)⟩⟩

theorem norm_comp_sub_ofReal_le {M : ℝ} (hM : ∀ x : ℝ, ‖f x‖ ≤ M) (a x : ℝ) :
    ‖f ((x : ℂ) - a)‖ ≤ M := by
  simpa using hM (x - a)

/-- Reflection `z ↦ -z`. -/
theorem MemBernstein.comp_neg (hf : MemBernstein τ f) : MemBernstein τ (fun z ↦ f (-z)) := by
  obtain ⟨M, h⟩ := hf.2.2
  exact ⟨hf.1.comp differentiable_neg, hf.2.1.comp_neg, ⟨M, fun x ↦ by simpa using h (-x)⟩⟩

/-- Multiplication by the unimodular-on-`ℝ` factor `e^{icz}`, `c ∈ ℝ`. -/
theorem MemBernstein.mul_cexp (hf : MemBernstein τ f) (c : ℝ) :
    MemBernstein (τ + |c|) (fun z ↦ f z * Complex.exp (I * c * z)) := by
  have h1 : MemBernstein |c| (fun z ↦ Complex.exp (I * c * z)) := by
    refine ⟨by fun_prop, by simpa using isExpTypeLE_cexp_mul (I * c), ⟨1, fun x ↦ ?_⟩⟩
    rw [Complex.norm_exp]
    simp
  exact hf.mul h1

end OCS
