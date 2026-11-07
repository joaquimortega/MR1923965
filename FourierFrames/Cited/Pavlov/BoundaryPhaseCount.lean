import FourierFrames.Cited.Pavlov.Cardinal
import FourierFrames.Landau

/-!
# Counting the gaps of a separated grid

A boundary argument that drops by π at every node equals the prescribed
counting staircase, up to its additive constant.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace FF.Pavlov
variable {Γ : Set ℝ}

/-- A fixed reference point in each open gap. -/
def gapMid (g : Grid Γ) (k : ℤ) : ℝ := (g.point k+g.point (k+1))/2

theorem Grid.gapMid_mem (g : Grid Γ) (k : ℤ) :
    gapMid g k ∈ Ioo (g.point k) (g.point (k+1)) := by
  have h := g.strictMono (show k < k+1 by omega)
  constructor <;> dsimp [gapMid] <;> linarith

/-- An open gap contains no grid node. -/
theorem Grid.not_mem_of_mem_gap (g : Grid Γ) {k : ℤ} {x : ℝ}
    (hx : x ∈ Ioo (g.point k) (g.point (k+1))) : x ∉ Γ := by
  intro hn
  obtain ⟨j, rfl⟩ := g.range_eq.symm.subset hn
  have hkj := g.strictMono.lt_iff_lt.mp hx.1
  have hjk := g.strictMono.lt_iff_lt.mp hx.2
  omega

/-- Every real point outside the grid lies in an open gap. -/
theorem Grid.exists_open_gap (g : Grid Γ) {x : ℝ} (hx : x ∉ Γ) :
    ∃ k : ℤ, x ∈ Ioo (g.point k) (g.point (k+1)) := by
  obtain ⟨k, hkl, hkr⟩ := g.exists_between x
  refine ⟨k, lt_of_le_of_ne hkl ?_, hkr⟩
  intro he
  exact hx (he ▸ g.point_mem k)

private theorem finite_inter_Ioc_of_separated (hΓ : IsSeparated Γ) (a b : ℝ) :
    (Γ ∩ Ioc a b).Finite := by
  refine (hΓ.finite_inter_Icc (|a|+|b|)).subset ?_
  intro x hx
  exact ⟨hx.1, by linarith [hx.2.1, neg_abs_le a, abs_nonneg b],
    by linarith [hx.2.2, le_abs_self b, abs_nonneg a]⟩

/-- The prescribed counting function is constant on each open gap. -/
theorem Grid.countFn_eq_on_gap (g : Grid Γ) (hΓ : IsSeparated Γ) {k : ℤ} {x y : ℝ}
    (hx : x ∈ Ioo (g.point k) (g.point (k+1)))
    (hy : y ∈ Ioo (g.point k) (g.point (k+1))) : countFn Γ x = countFn Γ y := by
  have hzero {a b : ℝ} (ha : a ∈ Ioo (g.point k) (g.point (k+1)))
      (hb : b ∈ Ioo (g.point k) (g.point (k+1))) : Γ ∩ Ioc a b = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact g.not_mem_of_mem_gap (k := k) ⟨ha.1.trans ht.2.1, ht.2.2.trans_lt hb.2⟩ ht.1
  rcases le_total x y with h | h
  · have he := FF.countFn_sub (finite_inter_Ioc_of_separated hΓ) h
    rw [hzero hx hy] at he
    simp only [Set.ncard_empty, Nat.cast_zero] at he
    linarith
  · have he := FF.countFn_sub (finite_inter_Ioc_of_separated hΓ) h
    rw [hzero hy hx] at he
    simp only [Set.ncard_empty, Nat.cast_zero] at he
    linarith

theorem Grid.countFn_eq_of_mem_gap (g : Grid Γ) (hΓ : IsSeparated Γ) {k : ℤ} {x : ℝ}
    (hx : x ∈ Ioo (g.point k) (g.point (k+1))) : countFn Γ x = countFn Γ (gapMid g k) :=
  g.countFn_eq_on_gap hΓ hx (g.gapMid_mem k)

/-- Between successive gap midpoints there is exactly one node. -/
theorem Grid.nodes_between_gapMids (g : Grid Γ) (k : ℤ) :
    Γ ∩ Ioc (gapMid g k) (gapMid g (k+1)) = {g.point (k+1)} := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, rfl⟩ := g.range_eq.symm.subset hx.1
    have hleft : g.point k < g.point j := (g.gapMid_mem k).1.trans hx.2.1
    have hright : g.point j < g.point (k+1+1) := hx.2.2.trans_lt (g.gapMid_mem (k+1)).2
    have hj : j = k+1 := by
      have := g.strictMono.lt_iff_lt.mp hleft
      have := g.strictMono.lt_iff_lt.mp hright
      omega
    simp [hj]
  · intro hx
    have he : x = g.point (k+1) := mem_singleton_iff.mp hx
    subst x
    exact ⟨g.point_mem _, (g.gapMid_mem k).2, (g.gapMid_mem (k+1)).1.le⟩

/-- The counting staircase rises by one between successive gap midpoints. -/
theorem Grid.countFn_gapMid_succ_sub (g : Grid Γ) (hΓ : IsSeparated Γ) (k : ℤ) :
    countFn Γ (gapMid g (k+1))-countFn Γ (gapMid g k) = 1 := by
  have hmid : gapMid g k ≤ gapMid g (k+1) :=
    ((g.gapMid_mem k).2.trans (g.gapMid_mem (k+1)).1).le
  rw [FF.countFn_sub (finite_inter_Ioc_of_separated hΓ) hmid, g.nodes_between_gapMids]
  simp

/-- A sequence with downward π jumps differs from the counting staircase by a constant. -/
theorem Grid.exists_countFn_constant_of_pi_jump (g : Grid Γ) (hΓ : IsSeparated Γ)
    (β : ℤ → ℝ) (hβ : ∀ k : ℤ, β (k+1) = β k-Real.pi) :
    ∃ c : ℝ, ∀ k : ℤ, β k = -Real.pi * countFn Γ (gapMid g k)+c := by
  let f : ℤ → ℝ := fun k ↦ β k+Real.pi*countFn Γ (gapMid g k)
  have hs : ∀ k : ℤ, f (k+1) = f k := by
    intro k
    have hcount := g.countFn_gapMid_succ_sub hΓ k
    dsimp only [f]
    rw [hβ]
    linear_combination Real.pi*hcount
  have hm : Monotone f := monotone_int_of_le_succ (fun k ↦ (hs k).ge)
  have hn : Monotone (fun k ↦ -f k) := monotone_int_of_le_succ (fun k ↦ by rw [hs])
  refine ⟨f 0, fun k ↦ ?_⟩
  have he : f k = f 0 := by
    rcases le_total (0 : ℤ) k with h | h
    · linarith [hm h, hn h]
    · linarith [hm h, hn h]
  dsimp only [f] at he ⊢
  linarith

end FF.Pavlov
