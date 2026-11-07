import FourierFrames.Cited.Pavlov.BoundaryPhaseCount
import TauCeti.Analysis.Complex.BranchLogRoot

/-!
# Boundary argument of a real entire generator

Local logarithms give a constant boundary argument on every zero-free interval.
A simple real zero gives a downward jump by π from left to right. See
`blueprint/P5_BoundaryPhase.md`.
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped ENNReal NNReal ComplexConjugate

noncomputable section
namespace FF.Pavlov

private lemma isOpen_UHP : IsOpen UHP :=
  isOpen_lt continuous_const Complex.continuous_im

theorem GeneratingData.exists_upper_log {Γ : Set ℝ} (d : GeneratingData Γ) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L UHP ∧
      ∀ z ∈ UHP, Complex.exp (L z) = d.G z := by
  have hsc : IsSimplyConnected UHP := by
    let : ContractibleSpace UHP := (convex_halfSpace_im_gt 0).contractibleSpace
      ⟨I, by simp⟩
    exact SimplyConnectedSpace.ofContractible _
  apply TauCeti.exists_differentiableOn_eqOn_exp_comp hsc isOpen_UHP
    d.entire.differentiableOn
  rintro ⟨z, hz, hzero⟩
  obtain ⟨x, _, he⟩ := (d.zeros z).mp hzero
  simp [he, UHP] at hz

private lemma exists_const_of_exp_const {V : Set ℂ} (ho : IsOpen V)
    (hc : IsPreconnected V) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F V)
    {C : ℂ} (he : ∀ z ∈ V, Complex.exp (F z) = C) :
    ∃ D : ℂ, ∀ z ∈ V, F z = D := by
  apply ho.exists_is_const_of_deriv_eq_zero hc hF
  intro z hz
  have hd := (hF.differentiableAt (ho.mem_nhds hz)).hasDerivAt.cexp
  have hloc : (fun _ : ℂ ↦ C) =ᶠ[𝓝 z] fun w ↦ Complex.exp (F w) := by
    filter_upwards [ho.mem_nhds hz] with w hw
    exact (he w hw).symm
  have hm := (hd.congr_of_eventuallyEq hloc).unique (hasDerivAt_const z C)
  exact (mul_eq_zero.mp hm).resolve_left (Complex.exp_ne_zero _)

private lemma GeneratingData.im_real {Γ : Set ℝ} (d : GeneratingData Γ) (x : ℝ) :
    (d.G (x : ℂ)).im = 0 := by
  have h := congrArg Complex.im (congrFun d.real (x : ℂ))
  simp only [fstar, Complex.conj_ofReal, Complex.conj_im] at h
  linarith

private lemma local_log_data {A : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hreal : ∀ t : ℝ, (A t).im = 0) {x : ℝ} (hx : A x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ ball (x : ℂ) r, A z / A x ∈ Complex.slitPlane) ∧
      (∀ t : ℝ, |t-x| < r → (Complex.log (A t / A x)).im = 0) := by
  have hslit : ∀ᶠ z in 𝓝 (x : ℂ), A z / A x ∈ Complex.slitPlane := by
    apply ((hA (x : ℂ)).continuousAt.div_const (A x)).preimage_mem_nhds
    simpa only [div_self hx] using Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hslit
  refine ⟨r, hr, fun z hz ↦ hball (mem_ball.mp hz), ?_⟩
  intro t ht
  have hmem : A (t : ℂ) / A (x : ℂ) ∈ Complex.slitPlane := hball (by simpa only [dist_eq_norm, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using ht)
  have him : (A t / A x).im = 0 := by
    simp only [Complex.div_im, hreal, zero_mul, mul_zero, sub_zero, zero_div]
  rw [Complex.log_im, Complex.arg_eq_zero_iff]
  refine ⟨?_, him⟩
  rcases Complex.mem_slitPlane_iff.mp hmem with hpos | hnonzero
  · exact hpos.le
  · exact (hnonzero him).elim

private lemma local_log_representation {A L : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hreal : ∀ t : ℝ, (A t).im = 0) {x : ℝ} (hx : A x ≠ 0)
    (hL : DifferentiableOn ℂ L UHP)
    (hexp : ∀ z ∈ UHP, Complex.exp (L z) = A z) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℂ,
      (∀ z ∈ ball (x : ℂ) r, A z / A x ∈ Complex.slitPlane) ∧
      (∀ t : ℝ, |t-x| < r → (Complex.log (A t / A x)).im = 0) ∧
      ∀ z ∈ ball (x : ℂ) r ∩ UHP, L z = Complex.log (A z / A x) + C := by
  obtain ⟨r, hr, hs, him⟩ := local_log_data hA hreal hx
  let V := ball (x : ℂ) r ∩ UHP
  have ho : IsOpen V := isOpen_ball.inter isOpen_UHP
  have hc : IsPreconnected V := ((convex_ball (x : ℂ) r).inter
    (convex_halfSpace_im_gt 0)).isPreconnected
  have hb : DifferentiableOn ℂ (fun z ↦ Complex.log (A z / A x)) (ball (x : ℂ) r) := by
    intro z hz
    exact (((hA z).div_const (A x)).clog (hs z hz)).differentiableWithinAt
  have hE : ∀ z ∈ V, Complex.exp ((L - fun w ↦ Complex.log (A w / A x)) z) = A x := by
    intro z hz
    change Complex.exp (L z - Complex.log (A z / A x)) = _
    rw [Complex.exp_sub, hexp z hz.2,
      Complex.exp_log (Complex.slitPlane_ne_zero (hs z hz.1))]
    have hAz : A z ≠ 0 := by rw [← hexp z hz.2]; exact Complex.exp_ne_zero _
    field_simp
  obtain ⟨C, hC⟩ := exists_const_of_exp_const ho hc
    ((hL.mono inter_subset_right).sub (hb.mono inter_subset_left)) hE
  refine ⟨r, hr, C, hs, him, ?_⟩
  intro z hz
  have h : L z - Complex.log (A z / A x) = C := hC z hz
  simpa only [add_comm] using sub_eq_iff_eq_add.mp h

private lemma vertical_tendsto (t : ℝ) :
    Tendsto (fun y : ℝ ↦ (t : ℂ)+(y : ℂ)*I) (𝓝[>] 0) (𝓝 (t : ℂ)) := by
  convert ((continuous_const.add (Complex.continuous_ofReal.mul_const I)).tendsto (0 : ℝ)).mono_left
    nhdsWithin_le_nhds using 1
  simp

private lemma local_boundary_limit {A L : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hreal : ∀ t : ℝ, (A t).im = 0) {x : ℝ} (hx : A x ≠ 0)
    (hL : DifferentiableOn ℂ L UHP)
    (hexp : ∀ z ∈ UHP, Complex.exp (L z) = A z) :
    ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ, ∀ t : ℝ, |t-x| < r →
      Tendsto (fun y : ℝ ↦ (L ((t:ℂ)+(y:ℂ)*I)).im) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨r, hr, C, hs, him, hrep⟩ := local_log_representation hA hreal hx hL hexp
  refine ⟨r, hr, C.im, ?_⟩
  intro t ht
  have htb : (t : ℂ) ∈ ball (x : ℂ) r := by
    simpa only [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using ht
  have hb : ContinuousAt (fun z ↦ Complex.log (A z / A x)) (t : ℂ) :=
    ((hA (t : ℂ)).continuousAt.div_const _).clog (hs _ htb)
  have hlim := Complex.continuous_im.tendsto _ |>.comp
    ((hb.tendsto.comp (vertical_tendsto t)).add_const C)
  have heq : (fun y : ℝ ↦ (Complex.log (A ((t:ℂ)+(y:ℂ)*I) / A x) + C).im)
      =ᶠ[𝓝[>] 0] (fun y : ℝ ↦ (L ((t:ℂ)+(y:ℂ)*I)).im) := by
    filter_upwards [(vertical_tendsto t).eventually (isOpen_ball.mem_nhds htb),
      self_mem_nhdsWithin] with y hyb hy
    exact (congrArg Complex.im (hrep _ ⟨hyb, by simpa [UHP] using hy⟩)).symm
  simpa only [Complex.add_im, him t ht, zero_add] using hlim.congr' heq

private lemma GeneratingData.ne_zero_of_not_mem {Γ : Set ℝ} (d : GeneratingData Γ)
    {x : ℝ} (hx : x ∉ Γ) : d.G (x : ℂ) ≠ 0 := by
  intro h
  obtain ⟨t, ht, he⟩ := (d.zeros _).mp h
  have hxt : x = t := Complex.ofReal_injective he
  exact hx (hxt ▸ ht)

private lemma boundary_value_eq_on_gap {Γ : Set ℝ} (d : GeneratingData Γ) (g : Grid Γ)
    {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L UHP)
    (hexp : ∀ z ∈ UHP, Complex.exp (L z) = d.G z) (β : ℝ → ℝ)
    (hβ : ∀ x : ℝ, x ∉ Γ →
      Tendsto (fun y : ℝ ↦ (L ((x:ℂ)+(y:ℂ)*I)).im) (𝓝[>] 0) (𝓝 (β x)))
    {k : ℤ} {x y : ℝ} (hx : x ∈ Ioo (g.point k) (g.point (k+1)))
    (hy : y ∈ Ioo (g.point k) (g.point (k+1))) : β x = β y := by
  let J := Ioo (g.point k) (g.point (k+1))
  have hlc : IsLocallyConstant (fun t : J ↦ β t) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    obtain ⟨r, hr, c, hc⟩ := local_boundary_limit d.entire d.im_real
      (d.ne_zero_of_not_mem (g.not_mem_of_mem_gap t.property)) hL hexp
    have hec : β t = c := tendsto_nhds_unique (hβ t (g.not_mem_of_mem_gap t.property))
      (hc t (by simpa using hr))
    have hn : {s : J | |(s : ℝ)-(t : ℝ)| < r} ∈ 𝓝 t := by
      apply (isOpen_lt (show Continuous (fun s : J ↦ |(s : ℝ)-(t : ℝ)|) from
        (continuous_subtype_val.sub continuous_const).abs) continuous_const).mem_nhds
      simpa using hr
    filter_upwards [hn] with s hs
    exact (tendsto_nhds_unique (hβ s (g.not_mem_of_mem_gap s.property)) (hc s hs)).trans hec.symm
  let : PreconnectedSpace J := Subtype.preconnectedSpace isPreconnected_Ioo
  exact hlc.apply_eq_of_isPreconnected isPreconnected_univ
    (x := (⟨x, hx⟩ : J)) (y := (⟨y, hy⟩ : J)) (mem_univ _) (mem_univ _)

private lemma GeneratingData.dslope_im_real {Γ : Set ℝ} (d : GeneratingData Γ)
    (γ t : ℝ) : (dslope d.G (γ : ℂ) (t : ℂ)).im = 0 := by
  by_cases ht : t = γ
  · subst t
    rw [dslope_same]
    have h := congrArg (fun f : ℂ → ℂ ↦ deriv f (γ : ℂ)) d.real
    rw [deriv_fstar_ofReal] at h
    have hi := congrArg Complex.im h
    simp only [Complex.conj_im] at hi
    linarith
  · rw [dslope_of_ne _ (by exact_mod_cast ht), slope_def_field]
    simp only [Complex.div_im, Complex.sub_im, d.im_real, Complex.ofReal_im,
      sub_self, mul_zero, zero_mul, zero_div]

private lemma vertical_log_im_limit (s : ℝ) (hs : s ≠ 0) :
    Tendsto (fun y : ℝ ↦ (Complex.log ((s:ℂ)+(y:ℂ)*I)).im)
      (𝓝[>] 0) (𝓝 (if 0 < s then 0 else Real.pi)) := by
  simp only [Complex.log_im]
  rcases hs.lt_or_gt with hneg | hpos
  · rw [ite_eq_right hneg.not_gt]
    apply (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
      (z := (s : ℂ)) (by simpa using hneg) (by simp)).comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨vertical_tendsto s, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa using hy.le
  · rw [ite_eq_left hpos]
    have hc : ContinuousAt Complex.arg (s : ℂ) :=
      Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hpos)))
    convert hc.tendsto.comp (vertical_tendsto s) using 1 <;>
      simp only [Function.comp_def, Complex.arg_ofReal_of_nonneg hpos.le]

private lemma local_boundary_jump {Γ : Set ℝ} (d : GeneratingData Γ)
    {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L UHP)
    (hexp : ∀ z ∈ UHP, Complex.exp (L z) = d.G z)
    {γ : ℝ} (hγ : γ ∈ Γ) :
    ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ, ∀ t : ℝ, |t-γ| < r → t ≠ γ →
      Tendsto (fun y : ℝ ↦ (L ((t:ℂ)+(y:ℂ)*I)).im)
        (𝓝[>] 0) (𝓝 (c + if γ < t then 0 else Real.pi)) := by
  let B := dslope d.G (γ : ℂ)
  have hB : Differentiable ℂ B := differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope Filter.univ_mem).mpr d.entire.differentiableOn)
  have hB0 : B (γ : ℂ) ≠ 0 := by simpa only [B, dslope_same] using d.simple hγ
  let M : ℂ → ℂ := fun z ↦ L z - Complex.log (z-(γ:ℂ))
  have hsub (z : ℂ) (hz : z ∈ UHP) : z-(γ:ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, UHP] using ne_of_gt hz
  have hM : DifferentiableOn ℂ M UHP := hL.sub fun z hz ↦
    ((differentiableAt_id.sub_const (γ:ℂ)).clog (hsub z hz)).differentiableWithinAt
  have heM : ∀ z ∈ UHP, Complex.exp (M z) = B z := by
    intro z hz
    have hne : z ≠ (γ : ℂ) := sub_ne_zero.mp (Complex.slitPlane_ne_zero (hsub z hz))
    dsimp [M, B]
    rw [Complex.exp_sub, hexp z hz, Complex.exp_log (sub_ne_zero.mpr hne),
      dslope_of_ne _ hne, slope_def_field, d.zero hγ, sub_zero]
  obtain ⟨r, hr, c, hc⟩ := local_boundary_limit hB (d.dslope_im_real γ) hB0 hM heM
  refine ⟨r, hr, c, ?_⟩
  intro t ht htg
  have hl := (hc t ht).add (vertical_log_im_limit (t-γ) (sub_ne_zero.mpr htg))
  have he (y : ℝ) : (M ((t:ℂ)+(y:ℂ)*I)).im +
      (Complex.log (((t-γ:ℝ):ℂ)+(y:ℂ)*I)).im = (L ((t:ℂ)+(y:ℂ)*I)).im := by
    have harg : ((t-γ:ℝ):ℂ)+(y:ℂ)*I = (t:ℂ)+(y:ℂ)*I-(γ:ℂ) := by push_cast; ring
    rw [harg]
    simp only [M, Complex.sub_im, sub_add_cancel]
  simpa only [he, sub_pos] using hl

private lemma boundary_value_gap_jump {Γ : Set ℝ} (d : GeneratingData Γ) (g : Grid Γ)
    {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L UHP)
    (hexp : ∀ z ∈ UHP, Complex.exp (L z) = d.G z) (β : ℝ → ℝ)
    (hβ : ∀ x : ℝ, x ∉ Γ →
      Tendsto (fun y : ℝ ↦ (L ((x:ℂ)+(y:ℂ)*I)).im) (𝓝[>] 0) (𝓝 (β x)))
    (k : ℤ) : β (gapMid g (k+1)) = β (gapMid g k) - Real.pi := by
  obtain ⟨r, hr, c, hc⟩ := local_boundary_jump d hL hexp (g.point_mem (k+1))
  let δ : ℝ := min r (min (g.point (k+1)-g.point k)
    (g.point ((k+1)+1)-g.point (k+1))) / 2
  have hleft : 0 < g.point (k+1)-g.point k := sub_pos.mpr (g.strictMono (by omega))
  have hright : 0 < g.point ((k+1)+1)-g.point (k+1) := sub_pos.mpr (g.strictMono (by omega))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ < r := by
    have := min_le_left r (min (g.point (k+1)-g.point k)
      (g.point ((k+1)+1)-g.point (k+1)))
    dsimp [δ]
    linarith
  have hδl : δ < g.point (k+1)-g.point k := by
    have := (min_le_right r _).trans (min_le_left (g.point (k+1)-g.point k)
      (g.point ((k+1)+1)-g.point (k+1)))
    dsimp [δ]
    linarith
  have hδrr : δ < g.point ((k+1)+1)-g.point (k+1) := by
    have := (min_le_right r _).trans (min_le_right (g.point (k+1)-g.point k)
      (g.point ((k+1)+1)-g.point (k+1)))
    dsimp [δ]
    linarith
  let l := g.point (k+1)-δ
  let v := g.point (k+1)+δ
  have hl : l ∈ Ioo (g.point k) (g.point (k+1)) := by dsimp [l]; constructor <;> linarith
  have hv : v ∈ Ioo (g.point (k+1)) (g.point ((k+1)+1)) := by dsimp [v]; constructor <;> linarith
  have hln : l ≠ g.point (k+1) := hl.2.ne
  have hvn : v ≠ g.point (k+1) := hv.1.ne'
  have hlr : |l-g.point (k+1)| < r := by
    dsimp [l]
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ]
    exact hδr
  have hvr : |v-g.point (k+1)| < r := by
    dsimp [v]
    rw [add_sub_cancel_left, abs_of_pos hδ]
    exact hδr
  have hbl : β l = c + Real.pi := by
    have h := tendsto_nhds_unique (hβ l (g.not_mem_of_mem_gap hl)) (hc l hlr hln)
    simpa only [ite_eq_right hl.2.not_gt] using h
  have hbv : β v = c := by
    have h := tendsto_nhds_unique (hβ v (g.not_mem_of_mem_gap hv)) (hc v hvr hvn)
    simpa only [ite_eq_left hv.1, add_zero] using h
  rw [← boundary_value_eq_on_gap d g hL hexp β hβ hv (g.gapMid_mem (k+1)),
    ← boundary_value_eq_on_gap d g hL hexp β hβ hl (g.gapMid_mem k), hbl, hbv]
  ring

theorem GeneratingData.boundary_phase {Γ : Set ℝ}
    (hΓ : IsSeparated Γ) (d : GeneratingData Γ) (g : Grid Γ)
    {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L UHP)
    (hexp : ∀ z ∈ UHP, Complex.exp (L z) = d.G z) :
    ∃ c : ℝ, ∀ x : ℝ, x ∉ Γ →
      Tendsto (fun y : ℝ ↦ (L ((x:ℂ)+(y:ℂ)*I)).im)
        (𝓝[>] 0) (𝓝 (-Real.pi * countFn Γ x + c)) := by
  have hvalues : ∀ x : ℝ, ∃ b : ℝ, x ∉ Γ →
      Tendsto (fun y : ℝ ↦ (L ((x:ℂ)+(y:ℂ)*I)).im) (𝓝[>] 0) (𝓝 b) := by
    intro x
    by_cases hx : x ∈ Γ
    · exact ⟨0, fun h ↦ (h hx).elim⟩
    · obtain ⟨r, hr, b, hb⟩ := local_boundary_limit d.entire d.im_real
        (d.ne_zero_of_not_mem hx) hL hexp
      exact ⟨b, fun _ ↦ hb x (by simpa using hr)⟩
  choose β hβ using hvalues
  obtain ⟨c, hc⟩ := g.exists_countFn_constant_of_pi_jump hΓ
    (fun k ↦ β (gapMid g k)) (boundary_value_gap_jump d g hL hexp β hβ)
  refine ⟨c, ?_⟩
  intro x hx
  obtain ⟨k, hk⟩ := g.exists_open_gap hx
  have he := boundary_value_eq_on_gap d g hL hexp β hβ hk (g.gapMid_mem k)
  have hn := g.countFn_eq_of_mem_gap hΓ hk
  simpa only [he, hc k, hn] using hβ x hx

end FF.Pavlov
