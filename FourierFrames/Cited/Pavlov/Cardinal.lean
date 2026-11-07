import FourierFrames.Corollary1
import FourierFrames.Cited.PaleyWiener
import FourierFrames.Cited.DeBrangesFC
import FourierFrames.Cited.DeBrangesDE

/-!
# Cardinal functions for a complete interpolating sequence

The sampling norm identifies the sequence with a phase level of a de Branges
space. Its real entire generator gives normalized removable quotients in PW.
See `blueprint/P5_Cardinal.md`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section
namespace FF.Pavlov

/-- The removable cardinal quotient, including its value at the central node. -/
def cardinal (G : ℂ → ℂ) (γ : ℝ) (z : ℂ) : ℂ :=
  dslope G (γ : ℂ) z / deriv G (γ : ℂ)

/-- A real generator obtained by retaining the exact sampling norm in Theorem C. -/
structure GeneratingData (Γ : Set ℝ) where
  E : ℂ → ℂ
  strictHB : IsStrictHB E
  eqPW : HEEqPW E
  sample_norm : ∀ f : ℂ → ℂ, MemPW f → heNormSq E f = sampleSum Γ f
  G : ℂ → ℂ
  G_eq : G = fun z ↦ E z + fstar E z
  entire : Differentiable ℂ G
  real : fstar G = G
  zeros : ∀ z : ℂ, G z = 0 ↔ ∃ x ∈ Γ, z = (x : ℂ)

/-- Rotation to a full phase level preserves the exact sampling norm. -/
theorem exists_generatingData {Γ : Set ℝ} (hΓ : IsSeparated Γ)
    (hcis : IsCompleteInterpolating Γ) : Nonempty (GeneratingData Γ) := by
  have hs := isSampling_of_isCompleteInterpolating paleyWiener_holds hΓ hcis
  obtain ⟨E₀, hEHB, hEPW, -, hnorm⟩ := exists_E paleyWiener_holds theoremC_holds hs
  have hE0 := HEEqPW.ne_zero_ofReal hEHB hEPW
  obtain ⟨φ, hφ, -⟩ := exists_isPhaseFunction hEHB.1 hE0
  obtain ⟨β, hβ⟩ := levelSet_eq_of_cis paleyWiener_holds theoremD_holds
    hEHB hEPW hΓ hcis hnorm hφ
  let θ : ℝ := β - Real.pi / 2
  let E : ℂ → ℂ := fun z ↦ Complex.exp (I * θ) * E₀ z
  have hHB : IsHB E := hEHB.rotate θ
  have hPW : HEEqPW E := hEPW.rotate θ
  have hstrict := HEEqPW.isStrictHB hHB hPW
  have hEreal := HEEqPW.ne_zero_ofReal hHB hPW
  have hlevel : phaseLevel (fun x ↦ φ x - θ) (Real.pi / 2) = Γ := by
    rw [hβ]
    ext x
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by dsimp [θ] at hk; linarith⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by dsimp [θ]; linarith⟩
  refine ⟨⟨E, hstrict, hPW, ?_, (fun z ↦ E z + fstar E z), rfl,
    hHB.1.add (FF.Differentiable.fstar hHB.1), ?_, ?_⟩⟩
  · intro f hf
    have hc : ‖Complex.exp (I * θ)‖ = 1 := by
      rw [mul_comm]
      exact Complex.norm_exp_ofReal_mul_I θ
    exact (heNormSq_unit_mul hc E₀ f).trans (hnorm f hf)
  · ext z
    simp only [fstar, map_add, Complex.conj_conj]
    ring
  · intro z
    rw [zero_set_single hstrict hEreal (hφ.rotate θ), hlevel]

variable {Γ : Set ℝ}

/-- The coefficient in the kernel formula at a generator zero. -/
def kernelCoeff (d : GeneratingData Γ) (γ : ℝ) : ℂ :=
  I / (2 * Real.pi) * conj (d.E γ)

theorem GeneratingData.zero (d : GeneratingData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    d.G (γ : ℂ) = 0 := (d.zeros _).mpr ⟨γ, hγ, rfl⟩

theorem GeneratingData.kernel_eq_dslope (d : GeneratingData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    deBrangesKernel d.E (γ : ℂ) =
      fun z ↦ kernelCoeff d γ * dslope d.G (γ : ℂ) z := by
  have hGγ := d.zero hγ
  have he : fstar d.E (γ : ℂ) = -d.E γ := by
    rw [d.G_eq] at hGγ
    linear_combination hGγ
  have hs : Differentiable ℂ (dslope d.G (γ : ℂ)) := by
    exact differentiableOn_univ.mp ((Complex.differentiableOn_dslope Filter.univ_mem).mpr
      d.entire.differentiableOn)
  apply FF.Differentiable.eq_of_eqOn_upper
    (differentiable_deBrangesKernel d.strictHB.1.1 _) (hs.const_mul _)
  intro z hz
  have hne : z ≠ (γ : ℂ) := by
    intro h
    simp [h] at hz
  rw [deBrangesKernel_of_ne d.E (by simpa using hne), dslope_of_ne _ hne,
    slope_def_field, hGγ, sub_zero]
  simp only [kernelNum, he, map_neg, Complex.conj_ofReal, kernelCoeff, d.G_eq]
  field_simp
  ring

/-- Every zero of the generator is simple. -/
theorem GeneratingData.simple (d : GeneratingData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    deriv d.G (γ : ℂ) ≠ 0 := by
  have hk := congrFun (d.kernel_eq_dslope hγ) (γ : ℂ)
  rw [dslope_same] at hk
  have h0 := HEEqPW.ne_zero_ofReal d.strictHB.1 d.eqPW γ
  have hp : 0 < phaseDeriv d.E γ * ‖d.E γ‖ ^ 2 / Real.pi :=
    div_pos (mul_pos (d.strictHB.phaseDeriv_pos h0)
      (sq_pos_of_pos (norm_pos_iff.mpr h0))) Real.pi_pos
  intro h
  rw [h, mul_zero, deBrangesKernel_diag_real] at hk
  have := congrArg Complex.re hk
  simp only [Complex.ofReal_re, Complex.zero_re] at this
  linarith

theorem kernelCoeff_ne_zero (d : GeneratingData Γ) (γ : ℝ) : kernelCoeff d γ ≠ 0 := by
  unfold kernelCoeff
  apply mul_ne_zero
  · exact div_ne_zero I_ne_zero (mul_ne_zero (by norm_num)
      (ofReal_ne_zero.mpr Real.pi_ne_zero))
  · exact (map_ne_zero _).mpr (HEEqPW.ne_zero_ofReal d.strictHB.1 d.eqPW γ)

theorem GeneratingData.cardinal_eq_kernel (d : GeneratingData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    cardinal d.G γ = fun z ↦ (kernelCoeff d γ)⁻¹ / deriv d.G (γ : ℂ) *
      deBrangesKernel d.E (γ : ℂ) z := by
  funext z
  rw [d.kernel_eq_dslope hγ]
  dsimp only [cardinal]
  field_simp [kernelCoeff_ne_zero d γ]

theorem GeneratingData.cardinal_mem (d : GeneratingData Γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    MemPW (cardinal d.G γ) := by
  rw [d.cardinal_eq_kernel hγ]
  exact ((d.eqPW.1 _).mp (memHE_deBrangesKernel d.strictHB.1
    (HEEqPW.ne_zero_ofReal d.strictHB.1 d.eqPW) _)).const_mul _

theorem GeneratingData.cardinal_values (d : GeneratingData Γ) {γ t : ℝ}
    (hγ : γ ∈ Γ) (ht : t ∈ Γ) :
    cardinal d.G γ (t : ℂ) = if t = γ then 1 else 0 := by
  classical
  by_cases he : t = γ
  · subst t
    simp [cardinal, dslope_same, d.simple hγ]
  · have hec : (t : ℂ) ≠ γ := by exact_mod_cast he
    simp [cardinal, dslope_of_ne _ hec, slope_def_field, d.zero hγ, d.zero ht, he]

theorem GeneratingData.sampleSum_cardinal (d : GeneratingData Γ) {γ : ℝ}
    (hγ : γ ∈ Γ) : sampleSum Γ (cardinal d.G γ) = 1 := by
  classical
  unfold sampleSum
  rw [tsum_eq_single (⟨γ, hγ⟩ : Γ)]
  · simp [d.cardinal_values hγ hγ]
  · intro t ht
    have hne : (t : ℝ) ≠ γ := fun h ↦ ht (Subtype.ext h)
    simp [d.cardinal_values hγ t.2, hne]

/-- The cardinal functions have a uniform squared PW norm. -/
theorem GeneratingData.uniform_cardinal_norm (d : GeneratingData Γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ ∈ Γ, (pwNormSq (cardinal d.G γ)).toReal ≤ C := by
  obtain ⟨c, C, hc, hbd⟩ := d.eqPW.2
  have hc' : 0 < (c : ℝ) := hc
  refine ⟨1 / c, by positivity, ?_⟩
  intro γ hγ
  have h := (hbd _ (d.cardinal_mem hγ)).1
  rw [d.sample_norm _ (d.cardinal_mem hγ), d.sampleSum_cardinal hγ] at h
  have hr := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) h
  rw [ENNReal.toReal_mul] at hr
  simp only [ENNReal.coe_toReal, ENNReal.toReal_one] at hr
  exact (le_div_iff₀ hc').mpr (by simpa only [mul_comm] using hr)

/-- A real generator together with its PW cardinal functions and uniform norm. -/
structure CardinalData (Γ : Set ℝ) extends GeneratingData Γ where
  normBound : ℝ
  normBound_pos : 0 < normBound
  cardinal_norm : ∀ γ ∈ Γ, (pwNormSq (cardinal G γ)).toReal ≤ normBound

theorem exists_cardinalData {Γ : Set ℝ} (hΓ : IsSeparated Γ)
    (hcis : IsCompleteInterpolating Γ) : Nonempty (CardinalData Γ) := by
  obtain ⟨d⟩ := exists_generatingData hΓ hcis
  obtain ⟨C, hC, hbd⟩ := d.uniform_cardinal_norm
  exact ⟨⟨d, C, hC, hbd⟩⟩

/-- Multiplying by the removed linear factor recovers the generator everywhere. -/
theorem GeneratingData.cardinal_mul_sub (d : GeneratingData Γ) {γ : ℝ}
    (hγ : γ ∈ Γ) (z : ℂ) :
    deriv d.G (γ : ℂ) * (z-(γ : ℂ)) * cardinal d.G γ z = d.G z := by
  have hs := sub_smul_dslope d.G (γ : ℂ) z
  rw [d.zero hγ, sub_zero, smul_eq_mul] at hs
  dsimp only [cardinal]
  field_simp [d.simple hγ]
  linear_combination hs

theorem GeneratingData.cardinal_zero_iff (d : GeneratingData Γ) {γ : ℝ}
    (hγ : γ ∈ Γ) (z : ℂ) :
    cardinal d.G γ z = 0 ↔ ∃ t ∈ Γ, t ≠ γ ∧ z = (t : ℂ) := by
  constructor
  · intro h
    have hg : d.G z = 0 := by rw [← d.cardinal_mul_sub hγ z, h, mul_zero]
    obtain ⟨t, ht, rfl⟩ := (d.zeros z).mp hg
    refine ⟨t, ht, ?_, rfl⟩
    intro he
    subst t
    simp [d.cardinal_values hγ hγ] at h
  · rintro ⟨t, ht, hne, rfl⟩
    simp [d.cardinal_values hγ ht, hne]

/-- A finite linear combination of cardinal functions remains in PW. -/
theorem GeneratingData.cardinal_synthesis_mem (d : GeneratingData Γ)
    (s : Finset Γ) (a : Γ → ℂ) :
    MemPW (fun z ↦ ∑ γ ∈ s, a γ * cardinal d.G (γ : ℝ) z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using memPW_zero
  | @insert γ s hγ ih =>
    convert ((d.cardinal_mem γ.2).const_mul (a γ)).add ih using 1
    funext z
    simp only [Finset.sum_insert hγ, Pi.add_apply]

/-- The sample values of a finite cardinal sum are its coefficients. -/
theorem GeneratingData.cardinal_synthesis_value (d : GeneratingData Γ)
    (s : Finset Γ) (a : Γ → ℂ) (t : Γ) :
    (∑ γ ∈ s, a γ * cardinal d.G (γ : ℝ) (t : ℂ)) = if t ∈ s then a t else 0 := by
  classical
  have h (γ : Γ) : cardinal d.G (γ : ℝ) (t : ℂ) = if t = γ then 1 else 0 := by
    rw [d.cardinal_values γ.2 t.2]
    simp only [Subtype.ext_iff]
  simp only [h]
  simp

/-- Sampling computes the squared norm of finite cardinal sums exactly. -/
theorem GeneratingData.sampleSum_cardinal_synthesis (d : GeneratingData Γ)
    (s : Finset Γ) (a : Γ → ℂ) :
    sampleSum Γ (fun z ↦ ∑ γ ∈ s, a γ * cardinal d.G (γ : ℝ) z) =
      ∑ γ ∈ s, ‖a γ‖ₑ ^ 2 := by
  classical
  unfold sampleSum
  simp only [d.cardinal_synthesis_value]
  rw [tsum_eq_sum (s := s)]
  · exact Finset.sum_congr rfl (fun γ hγ ↦ by simp [hγ])
  · intro γ hγ
    simp [hγ]

/-- Sampling bounds give uniform synthesis bounds without an abstract basis type. -/
theorem GeneratingData.cardinal_synthesis_bound (d : GeneratingData Γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset Γ) (a : Γ → ℂ),
      (pwNormSq (fun z ↦ ∑ γ ∈ s, a γ * cardinal d.G (γ : ℝ) z)).toReal ≤
        C * ∑ γ ∈ s, ‖a γ‖ ^ 2 := by
  obtain ⟨c, C, hc, hbd⟩ := d.eqPW.2
  have hc' : 0 < (c : ℝ) := hc
  refine ⟨1 / c, by positivity, ?_⟩
  intro s a
  have h := (hbd _ (d.cardinal_synthesis_mem s a)).1
  rw [d.sample_norm _ (d.cardinal_synthesis_mem s a), d.sampleSum_cardinal_synthesis] at h
  have hfin : (∑ γ ∈ s, ‖a γ‖ₑ ^ 2) ≠ (⊤ : ℝ≥0∞) := by simp
  have hr := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul] at hr
  simp only [ENNReal.coe_toReal] at hr
  have hsum : (∑ γ ∈ s, ‖a γ‖ₑ ^ 2).toReal = ∑ γ ∈ s, ‖a γ‖ ^ 2 := by
    rw [ENNReal.toReal_sum (fun _ _ ↦ by simp)]
    simp only [ENNReal.toReal_pow, ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
  rw [hsum] at hr
  apply (mul_le_mul_iff_right₀ hc').mp
  calc
    (c : ℝ) * (pwNormSq (fun z ↦ ∑ γ ∈ s, a γ * cardinal d.G (γ : ℝ) z)).toReal
        ≤ ∑ γ ∈ s, ‖a γ‖ ^ 2 := hr
    _ = (c : ℝ) * (1 / c * ∑ γ ∈ s, ‖a γ‖ ^ 2) := by field_simp


/-- Separation and a sampling lower bound rule out arbitrarily large holes. -/
theorem sampling_relatively_dense {Γ : Set ℝ} (hΓ : IsSeparated Γ) (hs : IsSampling Γ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, ∃ γ ∈ Γ, |γ-t| < R := by
  obtain ⟨δ, hδ, hsep⟩ := hΓ
  obtain ⟨A, B, hA, hsample⟩ := hs
  let ε : ℝ≥0∞ := (A : ℝ≥0∞) * pwNormSq pwBump
  have hε : ε ≠ 0 := mul_ne_zero (by exact_mod_cast hA.ne') pwNormSq_pwBump_pos.ne'
  have hεfin : ε ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top (pwNormSq_ne_top memPW_pwBump)
  obtain ⟨R, hR⟩ := Suff.translate_tail paleyWiener_holds hδ memPW_pwBump
    (ENNReal.half_pos hε).ne'
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t
  by_contra hn
  push Not at hn
  have htail := hR Γ t hsep (fun γ hγ ↦ (le_max_left R 1).trans (hn γ hγ))
  have hlo := (hsample (fun z ↦ pwBump (z-t)) (memPW_pwBump.comp_sub_ofReal t)).1
  rw [pwNormSq_comp_sub_ofReal] at hlo
  have hhalf : ε / 2 < ε := ENNReal.half_lt_self hε hεfin
  exact (not_lt_of_ge (hlo.trans htail)) hhalf

/-- An increasing integer enumeration with uniformly bounded positive gaps. -/
structure Grid (Γ : Set ℝ) where
  point : ℤ → ℝ
  strictMono : StrictMono point
  range_eq : Set.range point = Γ
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_le_upper : lower ≤ upper
  gap_lower : ∀ k, lower ≤ point (k+1) - point k
  gap_upper : ∀ k, point (k+1) - point k ≤ upper

/-- Closed Voronoi cells; neighboring cells share just their endpoint. -/
def cell {Γ : Set ℝ} (g : Grid Γ) (k : ℤ) : Set ℝ :=
  Icc ((g.point (k-1) + g.point k)/2) ((g.point k + g.point (k+1))/2)

/-- The generator's phase gives an integer enumeration of its full zero set. -/
theorem GeneratingData.exists_enum (d : GeneratingData Γ) :
    ∃ γ : ℤ → ℝ, StrictMono γ ∧ Set.range γ = Γ := by
  have h0 := HEEqPW.ne_zero_ofReal d.strictHB.1 d.eqPW
  obtain ⟨φ, hφ, hφ'⟩ := exists_isPhaseFunction d.strictHB.1.1 h0
  have hm := hφ.strictMono_of_isStrictHB d.strictHB h0
  obtain ⟨ht, hb⟩ := HEEqPW.phase_tendsto paleyWiener_holds theoremE_holds
    d.strictHB.1 d.eqPW hφ hφ'
  obtain ⟨γ, hγ, hrange⟩ := exists_levelSet_enum hm (hφ.1.surjective ht hb) (Real.pi/2)
  refine ⟨γ, hγ, hrange.trans ?_⟩
  ext x
  have hz := zero_set_single d.strictHB h0 hφ (x : ℂ)
  rw [← congrFun d.G_eq (x : ℂ), d.zeros] at hz
  simpa [Complex.ofReal_inj, eq_comm] using hz.symm

/-- An empty gap between consecutive enumerated nodes is controlled by relative density. -/
theorem gap_le_of_relatively_dense {γ : ℤ → ℝ} (hγ : StrictMono γ)
    {R : ℝ} (hR : ∀ t : ℝ, ∃ k : ℤ, |γ k-t| < R) (k : ℤ) :
    γ (k+1)-γ k ≤ 2*R := by
  obtain ⟨j, hj⟩ := hR ((γ k+γ (k+1))/2)
  rcases le_or_gt j k with h | h
  · have he := hγ.monotone h
    have ha := (abs_lt.mp hj).1
    linarith
  · have he := hγ.monotone (show k+1 ≤ j by omega)
    have ha := (abs_lt.mp hj).2
    linarith

/-- Complete interpolation supplies a bounded-gap integer grid. -/
theorem exists_grid {Γ : Set ℝ} (hΓ : IsSeparated Γ)
    (hcis : IsCompleteInterpolating Γ) : Nonempty (Grid Γ) := by
  obtain ⟨d⟩ := exists_generatingData hΓ hcis
  obtain ⟨γ, hm, hr⟩ := d.exists_enum
  obtain ⟨R, hR, hdense⟩ := sampling_relatively_dense hΓ
    (isSampling_of_isCompleteInterpolating paleyWiener_holds hΓ hcis)
  obtain ⟨δ, hδ, hsep⟩ := hΓ
  have hg : ∀ k, γ k ∈ Γ := fun k ↦ hr ▸ mem_range_self k
  refine ⟨⟨γ, hm, hr, δ, max δ (2*R), hδ, le_max_left _ _, ?_, ?_⟩⟩
  · intro k
    have hk := hm (show k < k+1 by omega)
    have h := hsep (γ (k+1)) (hg _) (γ k) (hg _) (ne_of_gt hk)
    rwa [abs_of_pos (sub_pos.mpr hk)] at h
  · intro k
    refine (gap_le_of_relatively_dense hm ?_ k).trans (le_max_right _ _)
    intro t
    obtain ⟨x, hx, hxt⟩ := hdense t
    obtain ⟨j, rfl⟩ := hr.symm ▸ hx
    exact ⟨j, hxt⟩

theorem Grid.point_mem (g : Grid Γ) (k : ℤ) : g.point k ∈ Γ :=
  g.range_eq.subset (mem_range_self k)

theorem Grid.upper_pos (g : Grid Γ) : 0 < g.upper :=
  g.lower_pos.trans_le g.lower_le_upper

theorem Grid.point_mem_cell (g : Grid Γ) (k : ℤ) : g.point k ∈ cell g k := by
  have hp := g.strictMono (show k-1 < k by omega)
  have hn := g.strictMono (show k < k+1 by omega)
  constructor <;> linarith

/-- Voronoi cell lengths are bounded between the grid's gap constants. -/
theorem Grid.cell_length_bounds (g : Grid Γ) (k : ℤ) :
    g.lower ≤ (g.point k + g.point (k+1))/2 - (g.point (k-1)+g.point k)/2 ∧
    (g.point k + g.point (k+1))/2 - (g.point (k-1)+g.point k)/2 ≤ g.upper := by
  have hpL := g.gap_lower (k-1)
  have hpU := g.gap_upper (k-1)
  have hnL := g.gap_lower k
  have hnU := g.gap_upper k
  have hk : k-1+1 = k := by omega
  rw [hk] at hpL hpU
  constructor <;> linarith

theorem Grid.abs_sub_center_le (g : Grid Γ) {k : ℤ} {x : ℝ} (hx : x ∈ cell g k) :
    |x-g.point k| ≤ g.upper/2 := by
  have hp := g.gap_upper (k-1)
  have hn := g.gap_upper k
  have hk : k-1+1 = k := by omega
  rw [hk] at hp
  obtain ⟨hxl, hxr⟩ := hx
  apply abs_le.mpr
  constructor <;> linarith

/-- Other nodes stay a fixed distance from an entire closed Voronoi cell. -/
theorem Grid.other_node_distance (g : Grid Γ) {k : ℤ} {x : ℝ}
    (hx : x ∈ cell g k) {j : ℤ} (hj : j ≠ k) : g.lower/2 ≤ |x-g.point j| := by
  obtain ⟨hxl, hxr⟩ := hx
  rcases lt_or_gt_of_ne hj with hj | hj
  · have he := g.strictMono.monotone (show j ≤ k-1 by omega)
    have hp := g.gap_lower (k-1)
    have hk : k-1+1 = k := by omega
    rw [hk] at hp
    calc g.lower/2 ≤ x-g.point j := by linarith
      _ ≤ |x-g.point j| := le_abs_self _
  · have he := g.strictMono.monotone (show k+1 ≤ j by omega)
    have hn := g.gap_lower k
    calc g.lower/2 ≤ -(x-g.point j) := by linarith
      _ ≤ |x-g.point j| := neg_le_abs _

/-- Removing the lower linear growth leaves a monotone function of the index. -/
theorem Grid.monotone_sub_lower (g : Grid Γ) :
    Monotone (fun k : ℤ ↦ g.point k-g.lower*(k : ℝ)) := by
  apply monotone_int_of_le_succ
  intro k
  have h := g.gap_lower k
  push_cast
  linarith

theorem Grid.exists_above (g : Grid Γ) (x : ℝ) : ∃ k : ℤ, x < g.point k := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((x-g.point 0)/g.lower)
  have hn' : x-g.point 0 < (n : ℝ)*g.lower := (div_lt_iff₀ g.lower_pos).mp hn
  have h := g.monotone_sub_lower (show (0 : ℤ) ≤ n by positivity)
  simp only [Int.cast_zero, mul_zero, sub_zero, Int.cast_natCast] at h
  exact ⟨n, by nlinarith⟩

theorem Grid.exists_below (g : Grid Γ) (x : ℝ) : ∃ k : ℤ, g.point k < x := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((g.point 0-x)/g.lower)
  have hn' : g.point 0-x < (n : ℝ)*g.lower := (div_lt_iff₀ g.lower_pos).mp hn
  have h := g.monotone_sub_lower (show -(n : ℤ) ≤ 0 by omega)
  simp only [Int.cast_zero, mul_zero, sub_zero, Int.cast_neg, Int.cast_natCast] at h
  exact ⟨-(n : ℤ), by nlinarith⟩

theorem Grid.exists_between (g : Grid Γ) (x : ℝ) :
    ∃ k : ℤ, g.point k ≤ x ∧ x < g.point (k+1) := by
  obtain ⟨a, ha⟩ := g.exists_below x
  obtain ⟨b, hb⟩ := g.exists_above x
  have hbd : ∃ b : ℤ, ∀ k : ℤ, g.point k ≤ x → k ≤ b := by
    refine ⟨b, fun k hk ↦ ?_⟩
    exact (g.strictMono.le_iff_le).mp (hk.trans hb.le)
  obtain ⟨k, hk, hmax⟩ := Int.exists_greatest_of_bdd hbd ⟨a, ha.le⟩
  refine ⟨k, hk, ?_⟩
  by_contra hn
  have he := hmax (k+1) (not_lt.mp hn)
  omega

/-- The closed Voronoi cells cover the whole real line. -/
theorem Grid.exists_cell (g : Grid Γ) (x : ℝ) : ∃ k : ℤ, x ∈ cell g k := by
  obtain ⟨k, hkl, hkr⟩ := g.exists_between x
  by_cases hm : x ≤ (g.point k+g.point (k+1))/2
  · refine ⟨k, ?_, hm⟩
    have hp := g.strictMono (show k-1 < k by omega)
    linarith
  · refine ⟨k+1, ?_, ?_⟩
    · have he : k+1-1 = k := by omega
      simp only [he]
      linarith
    · have hn := g.strictMono (show k+1 < k+1+1 by omega)
      linarith

end FF.Pavlov
