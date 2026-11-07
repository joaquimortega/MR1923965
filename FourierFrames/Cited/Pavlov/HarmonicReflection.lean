import FourierFrames.Cited.DeBrangesDE.EntireHerglotz
import FourierFrames.Cited.DeBrangesFC
import TauCeti.Analysis.PDE.PoissonIntegral.Ball
import TauCeti.Analysis.InnerProductSpace.Laplacian.Comparison

open Set Complex InnerProductSpace Metric Topology
open scoped ComplexConjugate

noncomputable section

namespace FF.Pavlov

/-- The odd reflection of upper-half-plane data across the real axis. -/
def oddReflection (r : ℂ → ℝ) (z : ℂ) : ℝ :=
  if 0 ≤ z.im then r z else -r (conj z)

private lemma eq_of_im_zero {z : ℂ} (hz : z.im = 0) : z = (z.re : ℂ) := by
  apply Complex.ext <;> simp [hz]

private lemma boundary_zero {r : ℂ → ℝ} (hzero : ∀ x : ℝ, r x = 0)
    {z : ℂ} (hz : z.im = 0) : r z = 0 := by rw [eq_of_im_zero hz]; exact hzero _

private lemma oddReflection_conj {r : ℂ → ℝ} (hzero : ∀ x : ℝ, r x = 0) (z : ℂ) :
    oddReflection r (conj z) = -oddReflection r z := by
  by_cases hz : z.im = 0
  · simp [oddReflection, hz, boundary_zero hzero hz, conj_eq_iff_im.mpr hz]
  · by_cases hpos : 0 < z.im
    · simp [oddReflection, hpos.le, not_le.mpr hpos]
    · have hneg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hz
      simp [oddReflection, hneg.le, not_le.mpr hneg]

private lemma continuous_oddReflection {r : ℂ → ℝ}
    (hcont : ContinuousOn r {z : ℂ | 0 ≤ z.im})
    (hzero : ∀ x : ℝ, r x = 0) : Continuous (oddReflection r) := by
  have hc : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const continuous_im
  have hlow : ContinuousOn (fun z ↦ -r (conj z)) {z : ℂ | z.im ≤ 0} :=
    (hcont.comp continuous_conj.continuousOn (fun z hz ↦ by simpa only [mem_ofPred_eq, conj_im, neg_nonneg] using hz)).neg
  apply continuous_if
  · intro z hz
    have hz0 : z.im = 0 := by simpa using hz
    simp [boundary_zero hzero hz0, conj_eq_iff_im.mpr hz0]
  · simpa [hc.closure_eq] using hcont
  · have heq : closure {z : ℂ | ¬0 ≤ z.im} = {z : ℂ | z.im ≤ 0} := by
      simp only [not_le]
      simp only [closure_setOfPred_im_lt]
    simpa only [heq] using hlow

private lemma harmonicAt_neg_conj {h : ℂ → ℝ} {z : ℂ}
    (hh : HarmonicAt h (conj z)) : HarmonicAt (fun w ↦ -h (conj w)) z :=
  ((TauCeti.harmonicAt_comp_linearIsometryEquiv_right_iff conjLIE).mpr hh).neg

private lemma dirichlet_odd {r h : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hzero : ∀ x : ℝ, r x = 0)
    (hh : HarmonicOnNhd h (ball 0 R))
    (hhc : ContinuousOn h (closedBall 0 R))
    (hbd : EqOn h (oddReflection r) (sphere 0 R)) :
    ∀ z ∈ closedBall 0 R, h (conj z) = -h z := by
  have hconj : ContinuousOn (fun z ↦ -h (conj z)) (closedBall 0 R) :=
    (hhc.comp continuous_conj.continuousOn (fun z hz ↦ by simpa using hz)).neg
  have hconjh : HarmonicOnNhd (fun z ↦ -h (conj z)) (ball 0 R) :=
    fun z hz ↦ harmonicAt_neg_conj (hh _ (by simpa using hz))
  have heq := TauCeti.eqOn_of_harmonicOnNhd_of_eqOn_frontier (isCompact_closedBall (0 : ℂ) R)
    hhc hconj (hh.mono (by simp [interior_closedBall _ hR.ne'])) (hconjh.mono (by simp [interior_closedBall _ hR.ne'])) (fun z hz ↦ ?_)
  · intro z hz
    have := heq hz
    linarith
  · have hzs : z ∈ sphere 0 R := by simpa [frontier_closedBall _ hR.ne'] using hz
    rw [hbd hzs, hbd (by simpa using hzs), oddReflection_conj hzero, neg_neg]

private lemma dirichlet_eq_upper {r h : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hr : HarmonicOnNhd r FF.UHP)
    (hcont : ContinuousOn r {z : ℂ | 0 ≤ z.im})
    (hzero : ∀ x : ℝ, r x = 0)
    (hh : HarmonicOnNhd h (ball 0 R))
    (hhc : ContinuousOn h (closedBall 0 R))
    (hbd : EqOn h (oddReflection r) (sphere 0 R)) :
    EqOn h r (closedBall 0 R ∩ {z : ℂ | 0 ≤ z.im}) := by
  have hcl : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const continuous_im
  have hint : interior (closedBall (0 : ℂ) R ∩ {z : ℂ | 0 ≤ z.im}) =
      ball 0 R ∩ FF.UHP := by
    rw [interior_inter, interior_closedBall _ hR.ne', interior_setOfPred_le_im]
    rfl
  have hodd := dirichlet_odd hR hzero hh hhc hbd
  apply TauCeti.eqOn_of_harmonicOnNhd_of_eqOn_frontier
    ((isCompact_closedBall (0 : ℂ) R).inter_right hcl)
    (hhc.mono inter_subset_left) (hcont.mono inter_subset_right)
    (hh.mono (by rw [hint]; exact inter_subset_left))
    (hr.mono (by rw [hint]; exact inter_subset_right))
  intro z hz
  have hzK := ((isClosed_closedBall.inter hcl).closure_eq ▸ frontier_subset_closure) hz
  rcases frontier_inter_subset (closedBall (0 : ℂ) R) {z : ℂ | 0 ≤ z.im} hz with hz | hz
  · have hzs : z ∈ sphere 0 R := by simpa only [frontier_closedBall _ hR.ne'] using hz.1
    rw [hbd hzs, oddReflection, ite_eq_left (show 0 ≤ z.im from hzK.2)]
  · have hz0 : z.im = 0 := by simpa using hz.2
    have hhzero : h z = 0 := by
      have := hodd z hzK.1
      rw [conj_eq_iff_im.mpr hz0] at this
      linarith
    rw [hhzero, boundary_zero hzero hz0]

/-- Continuous harmonic data that vanish on the real axis admit odd harmonic reflection. -/
theorem harmonicOnNhd_oddReflection {r : ℂ → ℝ}
    (hr : HarmonicOnNhd r FF.UHP)
    (hcont : ContinuousOn r {z : ℂ | 0 ≤ z.im})
    (hzero : ∀ x : ℝ, r x = 0) : HarmonicOnNhd (oddReflection r) univ := by
  intro z _
  let R := ‖z‖+1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨h, hh, hhc, hbd⟩ :=
    TauCeti.exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere
      ((continuous_oddReflection hcont hzero).continuousOn :
        ContinuousOn (oddReflection r) (sphere (0 : ℂ) R))
  have hodd := dirichlet_odd hR hzero hh hhc hbd
  have hu := dirichlet_eq_upper hR hr hcont hzero hh hhc hbd
  have heq : EqOn (oddReflection r) h (ball 0 R) := by
    intro w hw
    have hwc := ball_subset_closedBall hw
    by_cases hwi : 0 ≤ w.im
    · rw [oddReflection, ite_eq_left hwi, hu ⟨hwc,hwi⟩]
    · have hcw : conj w ∈ closedBall 0 R ∩ {z : ℂ | 0 ≤ z.im} := by
        refine ⟨by simpa using hwc, ?_⟩
        simpa only [mem_ofPred_eq, conj_im, neg_nonneg] using (le_of_not_ge hwi)
      rw [oddReflection, ite_eq_right hwi, ← hu hcw, hodd w hwc, neg_neg]
  have hz : z ∈ ball (0 : ℂ) R := by simp [R]
  exact (harmonicAt_congr_nhds (Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) heq)).mpr
    (hh z hz)

/-- A nonnegative harmonic function on the upper half-plane, continuous and zero on
its finite boundary, is a nonnegative multiple of the imaginary coordinate. -/
theorem nonneg_harmonic_zero_boundary_eq_mul_im
    {r : ℂ → ℝ}
    (hr : HarmonicOnNhd r FF.UHP)
    (hcont : ContinuousOn r {z : ℂ | 0 ≤ z.im})
    (hzero : ∀ x : ℝ, r x = 0)
    (hpos : ∀ z ∈ FF.UHP, 0 ≤ r z) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ z ∈ FF.UHP, r z = a*z.im := by
  have hR := harmonicOnNhd_oddReflection hr hcont hzero
  obtain ⟨H, hH, hRe⟩ := hR.exists_analyticOnNhd_univ_re_eq
  have hHd : Differentiable ℂ H := fun z ↦ (hH z (mem_univ z)).differentiableAt
  let F : ℂ → ℂ := fun z ↦ I * H z
  have hFd : Differentiable ℂ F := hHd.const_mul I
  have hFi : ∀ z, (F z).im = oddReflection r z := by
    intro z
    have := congrFun hRe z
    simpa [F] using this
  let P : ℂ → ℂ := fun z ↦ (F z + FF.fstar F z)/2
  have hPd : Differentiable ℂ P := (hFd.add (FF.Differentiable.fstar hFd)).div_const 2
  have hPi : ∀ z, (P z).im = oddReflection r z := by
    intro z
    simp only [P, Complex.div_ofNat_im, add_im, FF.fstar, conj_im, hFi,
      oddReflection_conj hzero]
    ring
  have hPreal : ∀ z, P (conj z) = conj (P z) := by
    intro z
    simp [P, FF.fstar, map_add, map_ofNat, add_comm]
  have hPpos : ∀ z : ℂ, 0 < z.im → 0 ≤ (P z).im := by
    intro z hz
    rw [hPi, oddReflection, ite_eq_left hz.le]
    exact hpos z hz
  obtain ⟨a, b, ha, hab⟩ := FF.entire_pick_linear hPd hPreal hPpos
  refine ⟨a, ha, ?_⟩
  intro z hz
  have hi := congrArg Complex.im (hab z)
  simpa [hPi, oddReflection, (show 0 ≤ z.im from hz.le)] using hi

end FF.Pavlov
