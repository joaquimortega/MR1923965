import OrtegaCerdaSeip.Bernstein.PhragmenLindelof

/-!
# M02 (Bernstein) — Normal families in `𝓑_τ`

See `blueprint/M02_Bernstein.md`, §1.9.

A family `F i ∈ 𝓑_τ` with `|F i| ≤ M` on `ℝ` satisfies `|F i z| ≤ M e^{τ|Im z|}` (Phragmén–Lindelöf),
so it is locally bounded; by Montel's theorem it has locally uniform limits along ultrafilters,
cluster points along any filter, and convergent subsequences.  Every such limit is in `𝓑_τ` with
`|f| ≤ M` on `ℝ`.  This is the normal-family argument of p. 410 (passage from finite to infinite
interpolation, M14).

**Provenance.** `exists_tendstoLocallyUniformlyOn_of_ultrafilter` and
`exists_holomorphic_clusterPt` are a copy of `BOC.exists_holomorphic_clusterPt`
(`BerndtssonOrtegaCerda/Uniform/Canonical.lean` of the companion project `../MR1340337`, commit
`d745f9b`, same author, Apache-2.0), split in two: the first lemma is the first half of that proof
(the ultrafilter limit is locally uniform), the second is the original statement.  Namespace
`BOC` → `OCS`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-- **Montel, ultrafilter form** (from the proof of `BOC.exists_holomorphic_clusterPt`): a family
of holomorphic functions on `U` bounded by a continuous function converges locally uniformly on
`U` along any ultrafilter, to a holomorphic function with the same bound. -/
theorem exists_tendstoLocallyUniformlyOn_of_ultrafilter {ι : Type*} (𝒰 : Ultrafilter ι)
    {U : Set ℂ} (hU : IsOpen U) {F : ι → ℂ → ℂ} (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    {M : ℂ → ℝ} (hM : ContinuousOn M U) (hFM : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ M z) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H U ∧ (∀ z ∈ U, ‖H z‖ ≤ M z) ∧
      TendstoLocallyUniformlyOn F H (𝒰 : Filter ι) U := by
  classical
  -- pointwise limits along the ultrafilter
  have hlim : ∀ z ∈ U, ∃ x : ℂ, ‖x‖ ≤ M z ∧ Tendsto (fun i ↦ F i z) (𝒰 : Filter ι) (𝓝 x) := by
    intro z hz
    obtain ⟨x, hx, hle⟩ := (isCompact_closedBall (0 : ℂ) (M z)).ultrafilter_le_nhds'
      (Ultrafilter.map (fun i ↦ F i z) 𝒰)
      (Ultrafilter.mem_map.2 (Filter.univ_mem' fun i ↦ by
        simpa [mem_closedBall_zero_iff] using hFM i z hz))
    exact ⟨x, by simpa [mem_closedBall_zero_iff] using hx, hle⟩
  choose! H hHM hHt using hlim
  -- `F i → H` locally uniformly along `𝒰`
  have hTLU : TendstoLocallyUniformlyOn F H (𝒰 : Filter ι) U := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x hx
    obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x hx
    set r := R / 3 with hrdef
    have hr : 0 < r := by positivity
    have hcl : closedBall x (2 * r) ⊆ U :=
      (closedBall_subset_ball (by rw [hrdef]; linarith)).trans hRU
    have hbr : ball x r ⊆ U := (ball_subset_ball (by rw [hrdef]; linarith)).trans hRU
    obtain ⟨C, hC⟩ := (isCompact_closedBall x (2 * r)).exists_bound_of_continuousOn (hM.mono hcl)
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x (mem_closedBall_self (by positivity)))
    -- Cauchy estimate for the derivatives on `ball x r`
    have hderiv : ∀ i, ∀ y ∈ ball x r, ‖deriv (F i) y‖ ≤ C / r := by
      intro i y hy
      have hsub : closedBall y r ⊆ closedBall x (2 * r) := by
        intro w hw
        rw [mem_closedBall] at hw ⊢
        rw [mem_ball] at hy
        linarith [dist_triangle w y x]
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
        ((hF i).diffContOnCl_ball (hsub.trans hcl)) (fun w hw ↦ ?_)
      have hw' : w ∈ closedBall x (2 * r) := hsub (sphere_subset_closedBall hw)
      have h1 := hC w hw'
      rw [Real.norm_eq_abs] at h1
      exact (hFM i w (hcl hw')).trans ((le_abs_self _).trans h1)
    -- uniform Lipschitz bounds on `ball x r`
    have hlipF : ∀ i, ∀ y ∈ ball x r, ∀ y' ∈ ball x r, ‖F i y - F i y'‖ ≤ C / r * ‖y - y'‖ := by
      intro i y hy y' hy'
      exact (convex_ball x r).norm_image_sub_le_of_norm_deriv_le
        (fun z hz ↦ (hF i).differentiableAt (hU.mem_nhds (hbr hz))) (hderiv i) hy' hy
    have hlipH : ∀ y ∈ ball x r, ∀ y' ∈ ball x r, ‖H y - H y'‖ ≤ C / r * ‖y - y'‖ := by
      intro y hy y' hy'
      have ht := ((hHt y (hbr hy)).sub (hHt y' (hbr hy'))).norm
      exact le_of_tendsto ht (Filter.Eventually.of_forall fun i ↦ hlipF i y hy y' hy')
    -- a finite `δ`-net of `closedBall x (r / 2)`
    set δ := ε * r / (3 * (C + 1)) with hδdef
    have hδ : 0 < δ := by positivity
    have hCδ : C / r * δ ≤ ε / 3 := by
      have e : C / r * δ = ε / 3 * (C / (C + 1)) := by
        rw [hδdef]; field_simp
      rw [e]
      exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
    obtain ⟨T, hTs, hTf, hcover⟩ :=
      finite_cover_balls_of_compact (isCompact_closedBall x (r / 2)) hδ
    have hTr : ∀ y ∈ T, y ∈ ball x r := fun y hy ↦
      closedBall_subset_ball (by linarith) (hTs hy)
    have hev : ∀ᶠ i in (𝒰 : Filter ι), ∀ y ∈ T, dist (H y) (F i y) < ε / 3 := by
      rw [hTf.eventually_all]
      intro y hy
      filter_upwards [Metric.tendsto_nhds.1 (hHt y (hbr (hTr y hy))) (ε / 3) (by positivity)]
        with i hi
      rwa [dist_comm]
    refine ⟨ball x (r / 2), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (by positivity)), ?_⟩
    filter_upwards [hev] with i hi y hy
    obtain ⟨y₀, hy₀T, hyy₀⟩ : ∃ y₀ ∈ T, y ∈ ball y₀ δ := by
      simpa using hcover (ball_subset_closedBall hy)
    have hyr : y ∈ ball x r := ball_subset_ball (by linarith) hy
    have hy₀r := hTr y₀ hy₀T
    have hd : ‖y - y₀‖ < δ := by rw [← dist_eq_norm]; exact hyy₀
    have hd' : ‖y₀ - y‖ < δ := by rw [norm_sub_rev]; exact hd
    have hCr : 0 ≤ C / r := by positivity
    have e1 : dist (H y) (H y₀) ≤ ε / 3 := by
      rw [dist_eq_norm]
      calc ‖H y - H y₀‖ ≤ C / r * ‖y - y₀‖ := hlipH y hyr y₀ hy₀r
        _ ≤ C / r * δ := by gcongr
        _ ≤ ε / 3 := hCδ
    have e3 : dist (F i y₀) (F i y) ≤ ε / 3 := by
      rw [dist_eq_norm]
      calc ‖F i y₀ - F i y‖ ≤ C / r * ‖y₀ - y‖ := hlipF i y₀ hy₀r y hyr
        _ ≤ C / r * δ := by gcongr
        _ ≤ ε / 3 := hCδ
    have e2 := hi y₀ hy₀T
    calc dist (H y) (F i y) ≤ dist (H y) (H y₀) + dist (H y₀) (F i y₀) + dist (F i y₀) (F i y) :=
          dist_triangle4 _ _ _ _
      _ < ε := by linarith
  exact ⟨H, hTLU.differentiableOn (Filter.Eventually.of_forall hF) hU, hHM, hTLU⟩

/-- **Normal families** (Montel; copy of `BOC.exists_holomorphic_clusterPt`): a family of
holomorphic functions on `U` bounded by a continuous function has, along any non-trivial filter, a
holomorphic cluster point (pointwise), with the same bound. -/
theorem exists_holomorphic_clusterPt {ι : Type*} {l : Filter ι} [l.NeBot] {U : Set ℂ}
    (hU : IsOpen U) {F : ι → ℂ → ℂ} (hF : ∀ i, DifferentiableOn ℂ (F i) U) {M : ℂ → ℝ}
    (hM : ContinuousOn M U) (hFM : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ M z) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H U ∧ (∀ z ∈ U, ‖H z‖ ≤ M z) ∧
      ∀ z ∈ U, ∀ ε > 0, ∃ᶠ i in l, ‖F i z - H z‖ < ε := by
  obtain ⟨𝒰, h𝒰⟩ := Ultrafilter.exists_le l
  obtain ⟨H, hHd, hHM, hTLU⟩ := exists_tendstoLocallyUniformlyOn_of_ultrafilter 𝒰 hU hF hM hFM
  refine ⟨H, hHd, hHM, fun z hz ε hε ↦ ?_⟩
  -- a limit along `𝒰 ≤ l` is a cluster value along `l`
  have h1 : ∀ᶠ i in (𝒰 : Filter ι), ‖F i z - H z‖ < ε := by
    filter_upwards [Metric.tendsto_nhds.1 (hTLU.tendsto_at hz) ε hε] with i hi
    rwa [dist_eq_norm] at hi
  exact h1.frequently.filter_mono h𝒰

/-! ### Normal families in `𝓑_τ` -/

variable {τ : ℝ}

/-- A pointwise limit of a family in `𝓑_τ` bounded by `M` on `ℝ`, if entire, is in `𝓑_τ` and
bounded by `M` on `ℝ`. -/
theorem MemBernstein.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ}
    {f : ℂ → ℂ} (hτ : 0 ≤ τ) (hF : ∀ i, MemBernstein τ (F i)) {M : ℝ}
    (hM : ∀ i, ∀ x : ℝ, ‖F i x‖ ≤ M) (hd : Differentiable ℂ f)
    (hlim : ∀ z, Tendsto (fun i ↦ F i z) l (𝓝 (f z))) :
    MemBernstein τ f ∧ ∀ x : ℝ, ‖f x‖ ≤ M := by
  have hb : ∀ z, ‖f z‖ ≤ M * Real.exp (τ * |z.im|) := fun z ↦
    le_of_tendsto (hlim z).norm (Eventually.of_forall fun i ↦ (hF i).norm_le hτ (hM i) z)
  exact ⟨memBernstein_of_norm_le hd hτ hb, fun x ↦ by simpa using hb x⟩

/-- **Normal families in `𝓑_τ`, ultrafilter form.** -/
theorem MemBernstein.exists_tendstoLocallyUniformly {ι : Type*} (𝒰 : Ultrafilter ι)
    {F : ι → ℂ → ℂ} (hτ : 0 ≤ τ) (hF : ∀ i, MemBernstein τ (F i)) {M : ℝ}
    (hM : ∀ i, ∀ x : ℝ, ‖F i x‖ ≤ M) :
    ∃ f, MemBernstein τ f ∧ (∀ x : ℝ, ‖f x‖ ≤ M) ∧
      TendstoLocallyUniformly F f (𝒰 : Filter ι) := by
  have hc : Continuous fun z : ℂ ↦ M * Real.exp (τ * |z.im|) := by fun_prop
  obtain ⟨H, hHd, hHM, hT⟩ := exists_tendstoLocallyUniformlyOn_of_ultrafilter 𝒰 isOpen_univ
    (fun i ↦ (hF i).1.differentiableOn) hc.continuousOn
    (fun i z _ ↦ (hF i).norm_le hτ (hM i) z)
  have hb : ∀ z, ‖H z‖ ≤ M * Real.exp (τ * |z.im|) := fun z ↦ hHM z (mem_univ z)
  exact ⟨H, memBernstein_of_norm_le (differentiableOn_univ.1 hHd) hτ hb,
    fun x ↦ by simpa using hb x, tendstoLocallyUniformlyOn_univ.1 hT⟩

/-- **Normal families in `𝓑_τ`, cluster-point form** (along any non-trivial filter; e.g.
`atTop : Filter (Finset Λ)` for the passage from finite to infinite interpolation). -/
theorem MemBernstein.exists_clusterPt {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ}
    (hτ : 0 ≤ τ) (hF : ∀ i, MemBernstein τ (F i)) {M : ℝ} (hM : ∀ i, ∀ x : ℝ, ‖F i x‖ ≤ M) :
    ∃ f, MemBernstein τ f ∧ (∀ x : ℝ, ‖f x‖ ≤ M) ∧
      ∀ z, ∀ ε > 0, ∃ᶠ i in l, ‖F i z - f z‖ < ε := by
  obtain ⟨𝒰, h𝒰⟩ := Ultrafilter.exists_le l
  obtain ⟨f, hf, hfM, hT⟩ := MemBernstein.exists_tendstoLocallyUniformly 𝒰 hτ hF hM
  refine ⟨f, hf, hfM, fun z ε hε ↦ ?_⟩
  have h1 : ∀ᶠ i in (𝒰 : Filter ι), ‖F i z - f z‖ < ε := by
    filter_upwards [Metric.tendsto_nhds.1
      ((tendstoLocallyUniformlyOn_univ.2 hT).tendsto_at (mem_univ z)) ε hε] with i hi
    rwa [dist_eq_norm] at hi
  exact h1.frequently.filter_mono h𝒰

/-- **Normal families in `𝓑_τ`, subsequence form.** -/
theorem MemBernstein.exists_subseq_tendstoLocallyUniformly {F : ℕ → ℂ → ℂ} (hτ : 0 ≤ τ)
    (hF : ∀ n, MemBernstein τ (F n)) {M : ℝ} (hM : ∀ n, ∀ x : ℝ, ‖F n x‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f, MemBernstein τ f ∧ (∀ x : ℝ, ‖f x‖ ≤ M) ∧
      TendstoLocallyUniformly (fun n ↦ F (φ n)) f atTop := by
  -- a free ultrafilter `𝒰 ≥ atTop` and the compact-open topology on `C(ℂ, ℂ)`, which is first
  -- countable (`ℂ` is locally compact and σ-compact)
  obtain ⟨𝒰, h𝒰⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  obtain ⟨f, hf, hfM, hT⟩ := MemBernstein.exists_tendstoLocallyUniformly 𝒰 hτ hF hM
  let u : ℕ → C(ℂ, ℂ) := fun n ↦ ⟨F n, (hF n).1.continuous⟩
  let f' : C(ℂ, ℂ) := ⟨f, hf.1.continuous⟩
  have hu : Tendsto u (𝒰 : Filter ℕ) (𝓝 f') :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.2 hT
  have hcl : MapClusterPt f' atTop u := (ClusterPt.of_le_nhds hu).mono (map_mono h𝒰)
  obtain ⟨ψ, hψ, hψt⟩ := hcl.tendsto_subseq
  exact ⟨ψ, hψ, f, hf, hfM, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 hψt⟩

end OCS
