import OrtegaCerdaSeip.Lemma3.Main

/-!
# Locally uniform limits (aux file for `Construction.lean`, M07 §2.4)
-/

open MeasureTheory Metric Set Complex Filter Topology

noncomputable section

namespace FF

namespace Limits

theorem tendstoLU_comp_filter {ι κ α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ι → α → β} {f : α → β} {p : Filter ι} {q : Filter κ}
    (h : TendstoLocallyUniformly F f p) {g : κ → ι} (hg : Tendsto g q p) :
    TendstoLocallyUniformly (fun k ↦ F (g k)) f q := by
  intro u hu x
  obtain ⟨t, ht, H⟩ := h u hu x
  exact ⟨t, ht, hg.eventually H⟩

/-- If `G_i · Q → G · Q` locally uniformly, with `Q = ∏_{j ∈ s} (z - a_j)`, `G_i`, `G` entire,
then `G_i → G` locally uniformly (maximum modulus principle on a large circle). -/
theorem tendstoLU_of_mul_prod {ι κ : Type*} {p : Filter ι} {G : ι → ℂ → ℂ} {G₀ : ℂ → ℂ}
    (hG : ∀ i, Differentiable ℂ (G i)) (hG₀ : Differentiable ℂ G₀) (s : Finset κ) (a : κ → ℂ)
    (h : TendstoLocallyUniformly (fun i z ↦ G i z * ∏ j ∈ s, (z - a j))
      (fun z ↦ G₀ z * ∏ j ∈ s, (z - a j)) p) :
    TendstoLocallyUniformly G G₀ p := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  set ρ : ℝ := max r 0 + 1 + ∑ j ∈ s, ‖a j‖ with hρ
  have hρpos : 0 < ρ := by
    have : 0 ≤ ∑ j ∈ s, ‖a j‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    have := le_max_right r 0
    rw [hρ]; linarith
  have hρ1 : ∀ j ∈ s, 1 ≤ ρ - ‖a j‖ := by
    intro j hj
    have h1 : ‖a j‖ ≤ ∑ j ∈ s, ‖a j‖ :=
      Finset.single_le_sum (f := fun j ↦ ‖a j‖) (fun j _ ↦ norm_nonneg _) hj
    have := le_max_right r 0
    rw [hρ]; linarith
  have hQ : ∀ z : ℂ, ‖z‖ = ρ → 1 ≤ ‖∏ j ∈ s, (z - a j)‖ := by
    intro z hz
    rw [norm_prod]
    exact Finset.one_le_prod₀ (fun j hj ↦ by
      have := norm_sub_norm_le z (a j)
      have := hρ1 j hj
      linarith)
  have hKρ : K ⊆ closedBall 0 ρ := fun x hx ↦ by
    have := hr hx
    have h2 := le_max_left r 0
    have h3 : 0 ≤ ∑ j ∈ s, ‖a j‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    rw [mem_closedBall] at this ⊢
    rw [hρ]; linarith
  have hcpt := (tendstoLocallyUniformly_iff_forall_isCompact.1 h) (closedBall 0 ρ)
    (isCompact_closedBall 0 ρ)
  rw [Metric.tendstoUniformlyOn_iff] at hcpt ⊢
  intro ε hε
  filter_upwards [hcpt (ε / 2) (half_pos hε)] with i hi
  intro x hx
  have hmax : ∀ z ∈ closure (ball (0 : ℂ) ρ), ‖G i z - G₀ z‖ ≤ ε / 2 := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (f := fun z ↦ G i z - G₀ z)
      (U := ball (0 : ℂ) ρ) Metric.isBounded_ball ?_ (fun z hz ↦ ?_) hz
    · exact ((hG i).sub hG₀).diffContOnCl
    · rw [frontier_ball _ hρpos.ne'] at hz
      have hz' : ‖z‖ = ρ := by simpa using hz
      have h1 := hi z (by rw [mem_closedBall, dist_zero_right]; exact hz'.le)
      rw [dist_eq_norm] at h1
      have h2 : ‖(G₀ z * ∏ j ∈ s, (z - a j)) - (G i z * ∏ j ∈ s, (z - a j))‖ =
          ‖G i z - G₀ z‖ * ‖∏ j ∈ s, (z - a j)‖ := by
        rw [← sub_mul, norm_mul, norm_sub_rev]
      have h3 := hQ z hz'
      rw [h2] at h1
      nlinarith [norm_nonneg (G i z - G₀ z)]
  have hxcl : x ∈ closure (ball (0 : ℂ) ρ) := by
    rw [closure_ball _ hρpos.ne']
    exact hKρ hx
  have := hmax x hxcl
  rw [dist_eq_norm, norm_sub_rev]
  linarith

theorem tendstoLU_congr_eventually {ι α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F G : ι → α → β} {f : α → β} {p : Filter ι} (h : TendstoLocallyUniformly F f p)
    (hE : ∀ᶠ i in p, F i = G i) : TendstoLocallyUniformly G f p := by
  intro u hu x
  obtain ⟨t, ht, H⟩ := h u hu x
  exact ⟨t, ht, (H.and hE).mono fun i hi y hy ↦ hi.2 ▸ hi.1 y hy⟩

/-- Multiplication by a fixed continuous function preserves locally uniform convergence. -/
theorem tendstoLU_const_mul {ι : Type*} {p : Filter ι} {e : ℂ → ℂ} (he : Continuous e)
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (h : TendstoLocallyUniformly F f p) (hf : Continuous f) :
    TendstoLocallyUniformly (fun i z ↦ e z * F i z) (fun z ↦ e z * f z) p := by
  have h0 : TendstoLocallyUniformly (fun (_ : ι) ↦ e) e p := fun u hu x ↦
    ⟨univ, univ_mem, Eventually.of_forall fun _ y _ ↦ refl_mem_uniformity hu⟩
  exact h0.mul₀ h he hf

variable {m : ℝ → ℝ} {a b : ℝ}

/-- The symmetric partial products of the canonical product of `Γ` converge locally uniformly. -/
theorem tendstoLU_partial_prod (hw : OCS.IsMultWeight m a b) :
    TendstoLocallyUniformly
      (fun (R : ℕ) (z : ℂ) ↦ ∏ j ∈ Finset.Icc (-(R : ℤ)) R,
        OCS.genusOneFactor (OCS.multBary m j : ℂ) ((OCS.multBary m j : ℂ)⁻¹) z)
      (OCS.canonicalProd (OCS.multGammaC m) (fun w ↦ w⁻¹)) atTop := by
  have h := OCS.hasProdLocallyUniformlyOn_canonicalProd (OCS.isGenusOneData_multGammaC hw)
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn_univ] at h
  let g : ℕ → Finset (OCS.multGammaC m) := fun R ↦
    (Finset.Icc (-(R : ℤ)) R).map (OCS.multGammaEquiv hw).toEmbedding
  have hg : Tendsto g atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun R S hRS ↦ ?_) (fun x ↦ ?_)
    · exact Finset.map_subset_map.2 (Finset.Icc_subset_Icc (by omega) (by exact_mod_cast hRS))
    · refine ⟨((OCS.multGammaEquiv hw).symm x).natAbs, ?_⟩
      simp only [g, Finset.mem_map_equiv, Finset.mem_Icc]
      omega
  have := tendstoLU_comp_filter h hg
  refine this.congr ?_
  intro R z
  simp only [g, Finset.prod_map, Equiv.coe_toEmbedding, OCS.multGammaEquiv_apply]

end Limits

end FF
