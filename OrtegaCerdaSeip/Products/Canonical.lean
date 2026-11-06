import OrtegaCerdaSeip.Defs

/-!
# M06 (Products) — genus-one canonical products

See `blueprint/M06_Products.md`, §1.1–§1.4.

For a set `Z ⊆ ℂ ∖ {0}` with `∑_{a ∈ Z} |a|⁻² < ∞` and convergence factors `c : ℂ → ℂ` with
`∑_{a ∈ Z} |c a − 1/a| < ∞` we define
`P_{Z,c}(z) = ∏_{a ∈ Z} (1 − z/a) e^{z c_a}` (an unconditional `tprod` over the subtype `↥Z`).
This covers the Weierstrass product `c_a = 1/a` (Lemma 3, p. 406) and the paper's
`F_A(z) = ∏ (1 − z/λ) e^{z Re(1/λ)}` (p. 407), for which `∑ |Re(1/λ) − 1/λ| = ∑ |Im λ|/|λ|²`.

Main results: `P` is entire (`differentiable_canonicalProd`), locally uniformly convergent
(`hasProdLocallyUniformlyOn_canonicalProd`), vanishes exactly on `Z` (`canonicalProd_eq_zero_iff`)
with simple zeros (`hasDerivAt_canonicalProd_of_mem`), `log|P| = ∑ (log|1 − z/a| + Re(z c_a))` off
`Z` (`hasSum_log_norm_canonicalProd`); change of convergence factors
(`canonicalProd_congr_factor`), unions (`canonicalProd_union`), conjugation symmetry
(`canonicalProd_conj`), and an explicit logarithm off the "rays" of `Z`
(`canonicalLog`, `exp_canonicalLog`, `differentiableOn_canonicalLog`).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-! ## Definitions -/

/-- The genus-one factor `(1 − z/a) e^{z c}`. -/
def genusOneFactor (a c z : ℂ) : ℂ :=
  (1 - z / a) * Complex.exp (z * c)

/-- The data of a genus-one canonical product: `0 ∉ Z`, `∑_{a ∈ Z} |a|⁻² < ∞` and
`∑_{a ∈ Z} |c_a − a⁻¹| < ∞`.  (`Z` is then countable and locally finite.) -/
structure IsGenusOneData (Z : Set ℂ) (c : ℂ → ℂ) : Prop where
  zero_notMem : (0 : ℂ) ∉ Z
  summable_inv_sq : Summable fun a : Z ↦ ‖(a : ℂ)‖⁻¹ ^ 2
  summable_sub_inv : Summable fun a : Z ↦ ‖c a - (a : ℂ)⁻¹‖

/-- The canonical product `P_{Z,c}(z) = ∏_{a ∈ Z} (1 − z/a) e^{z c_a}`. -/
def canonicalProd (Z : Set ℂ) (c : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∏' a : Z, genusOneFactor a (c a) z

/-- An explicit logarithm of `P_{Z,c}`: `∑_{a ∈ Z} (Log(1 − z/a) + z c_a)` (principal `Log`).
It is a logarithm of `P` wherever every `1 − z/a` lies in the slit plane. -/
def canonicalLog (Z : Set ℂ) (c : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' a : Z, (Complex.log (1 - z / a) + z * c a)

/-! ## Elementary facts about a single factor -/

theorem genusOneFactor_eq_zero_iff {a c z : ℂ} (ha : a ≠ 0) :
    genusOneFactor a c z = 0 ↔ z = a := by
  rw [genusOneFactor, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), sub_eq_zero, eq_comm,
    div_eq_one_iff_eq ha]

theorem differentiable_genusOneFactor (a c : ℂ) : Differentiable ℂ (genusOneFactor a c) := by
  unfold genusOneFactor; fun_prop

/-- Lemma 1.2 (pointwise form): with `w = z/a` and `e = z(c − a⁻¹)`, if `|w| ≤ 1` and `|e| ≤ 1`
then `|(1 − w)e^{zc} − 1| ≤ 9|w|² + 2|e|`. -/
theorem norm_genusOneFactor_sub_one_le {a c z : ℂ} (hw : ‖z / a‖ ≤ 1)
    (hd : ‖z * (c - a⁻¹)‖ ≤ 1) :
    ‖genusOneFactor a c z - 1‖ ≤ 9 * ‖z / a‖ ^ 2 + 2 * ‖z * (c - a⁻¹)‖ := by
  set w := z / a with hw_def
  set e := z * (c - a⁻¹) with he_def
  have hzc : z * c = w + e := by simp only [w, e, div_eq_mul_inv]; ring
  have hid : genusOneFactor a c z - 1
      = ((exp w - 1 - w) - w * (exp w - 1)) * exp e + (exp e - 1) := by
    rw [genusOneFactor, hzc, Complex.exp_add, ← hw_def]; ring
  have h1 : ‖exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hw
  have h2 : ‖exp w - 1‖ ≤ 2 * ‖w‖ := Complex.norm_exp_sub_one_le hw
  have h3 : ‖exp e - 1‖ ≤ 2 * ‖e‖ := Complex.norm_exp_sub_one_le hd
  have h4 : ‖exp e‖ ≤ 3 := by
    refine (Complex.norm_exp_le_exp_norm e).trans ((Real.exp_le_exp.mpr hd).trans ?_)
    have := Real.exp_one_lt_d9
    norm_num at this ⊢; linarith
  rw [hid]
  calc _ ≤ ‖(exp w - 1 - w) - w * (exp w - 1)‖ * ‖exp e‖ + ‖exp e - 1‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ (‖w‖ ^ 2 + ‖w‖ * (2 * ‖w‖)) * 3 + 2 * ‖e‖ := by
        gcongr
        exact (norm_sub_le _ _).trans (by rw [norm_mul]; gcongr)
    _ = 9 * ‖w‖ ^ 2 + 2 * ‖e‖ := by ring

/-- `|Log(1 − w) + w| ≤ |w|²` for `|w| ≤ 1/2`. -/
theorem norm_log_one_sub_add_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (1 - w) + w‖ ≤ ‖w‖ ^ 2 := by
  have := Complex.norm_log_one_add_sub_self_le (z := -w) (by rw [norm_neg]; linarith)
  rw [norm_neg, sub_neg_eq_add, ← sub_eq_add_neg] at this
  refine this.trans ?_
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]; linarith
  calc ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ ‖w‖ ^ 2 * 2 / 2 := by gcongr
    _ = _ := by ring

/-- Summability over a union of two sets, for nonnegative terms. -/
theorem summable_subtype_union {Z W : Set ℂ} {g : ℂ → ℝ} (hg : ∀ x, 0 ≤ g x)
    (hZ : Summable fun a : Z ↦ g a) (hW : Summable fun a : W ↦ g a) :
    Summable fun a : ↥(Z ∪ W) ↦ g a := by
  have hZ' := (summable_subtype_iff_indicator (s := Z) (f := g)).mp hZ
  have hW' := (summable_subtype_iff_indicator (s := W) (f := g)).mp hW
  refine (summable_subtype_iff_indicator (s := Z ∪ W) (f := g)).mpr ?_
  refine (hZ'.add hW').of_nonneg_of_le (fun x ↦ indicator_nonneg (fun x _ ↦ hg x) x) fun x ↦ ?_
  by_cases hx : x ∈ Z <;> by_cases hx' : x ∈ W <;> simp [indicator, hx, hx', hg]

/-! ## The hypotheses -/

theorem IsGenusOneData.ne_zero {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) {a : ℂ}
    (ha : a ∈ Z) : a ≠ 0 :=
  fun h0 ↦ h.zero_notMem (h0 ▸ ha)

theorem IsGenusOneData.mono {Z W : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) (hW : W ⊆ Z) :
    IsGenusOneData W c := by
  refine ⟨fun h0 ↦ h.zero_notMem (hW h0), ?_, ?_⟩
  · have := h.summable_inv_sq.comp_injective (Set.inclusion_injective hW)
    exact this
  · have := h.summable_sub_inv.comp_injective (Set.inclusion_injective hW)
    exact this

/-- `Z ∪ W` carries genus-one data if `Z` and `W` do. -/
theorem IsGenusOneData.union {Z W : Set ℂ} {c : ℂ → ℂ} (hZ : IsGenusOneData Z c)
    (hW : IsGenusOneData W c) : IsGenusOneData (Z ∪ W) c :=
  ⟨fun h0 ↦ h0.elim hZ.zero_notMem hW.zero_notMem,
    summable_subtype_union (g := fun a ↦ ‖a‖⁻¹ ^ 2) (fun _ ↦ by positivity)
      hZ.summable_inv_sq hW.summable_inv_sq,
    summable_subtype_union (g := fun a ↦ ‖c a - a⁻¹‖) (fun _ ↦ norm_nonneg _)
      hZ.summable_sub_inv hW.summable_sub_inv⟩

/-- Changing the convergence factors by a summable amount. -/
theorem IsGenusOneData.of_summable_sub {Z : Set ℂ} {c c' : ℂ → ℂ} (h : IsGenusOneData Z c)
    (hc : Summable fun a : Z ↦ ‖c' a - c a‖) : IsGenusOneData Z c' := by
  refine ⟨h.zero_notMem, h.summable_inv_sq, ?_⟩
  refine (hc.add h.summable_sub_inv).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun a ↦ ?_
  calc ‖c' a - (a : ℂ)⁻¹‖ = ‖(c' a - c a) + (c a - (a : ℂ)⁻¹)‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _

/-- A set carrying genus-one data has finitely many points in every ball. -/
theorem IsGenusOneData.finite_inter_ball {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c)
    (R : ℝ) : (Z ∩ ball (0 : ℂ) R).Finite := by
  rcases le_or_gt R 0 with hR | hR
  · simp [ball_eq_empty.mpr hR]
  have hev : ∀ᶠ a : Z in cofinite, ‖(a : ℂ)‖⁻¹ ^ 2 < (R ^ 2)⁻¹ :=
    h.summable_inv_sq.tendsto_cofinite_zero.eventually (gt_mem_nhds (by positivity))
  rw [Filter.eventually_cofinite] at hev
  refine (hev.image Subtype.val).subset ?_
  rintro x ⟨hxZ, hxR⟩
  refine ⟨⟨x, hxZ⟩, ?_, rfl⟩
  rw [mem_ball_zero_iff] at hxR
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr (h.ne_zero hxZ)
  simp only [mem_ofPred_eq, not_lt]
  rw [← inv_pow]
  gcongr

theorem IsGenusOneData.countable {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) :
    Z.Countable := by
  have : Z = ⋃ n : ℕ, Z ∩ ball (0 : ℂ) n := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_ball_zero_iff]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      exact ⟨n, hx, hn⟩
    · rintro ⟨n, hx, _⟩
      exact hx
  rw [this]
  exact countable_iUnion fun n ↦ (h.finite_inter_ball n).countable

/-! ## The uniform factor estimate (Lemma 1.2) -/

/-- The summable majorant of `|f_a − 1|` (and of the logarithmic terms) on `closedBall 0 R`. -/
def genusOneBound (Z : Set ℂ) (c : ℂ → ℂ) (R : ℝ) (a : Z) : ℝ :=
  9 * R ^ 2 * ‖(a : ℂ)‖⁻¹ ^ 2 + 2 * R * ‖c a - (a : ℂ)⁻¹‖

theorem IsGenusOneData.summable_genusOneBound {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c)
    (R : ℝ) : Summable (genusOneBound Z c R) :=
  (h.summable_inv_sq.mul_left _).add (h.summable_sub_inv.mul_left _)

theorem IsGenusOneData.eventually_small {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c)
    (R : ℝ) : ∀ᶠ a : Z in cofinite, R * ‖(a : ℂ)‖⁻¹ ≤ 1 ∧ R * ‖c a - (a : ℂ)⁻¹‖ ≤ 1 := by
  have h1 := ((h.summable_inv_sq.mul_left (R ^ 2)).tendsto_cofinite_zero).eventually_le_const
    one_pos
  have h2 := ((h.summable_sub_inv.mul_left R).tendsto_cofinite_zero).eventually_le_const one_pos
  filter_upwards [h1, h2] with a ha1 ha2
  refine ⟨?_, ha2⟩
  have : (R * ‖(a : ℂ)‖⁻¹) ^ 2 ≤ 1 := by rw [mul_pow]; exact ha1
  nlinarith

/-- Lemma 1.2: for all but finitely many `a ∈ Z`, `|f_a(z) − 1| ≤ u_a` on `closedBall 0 R`. -/
theorem IsGenusOneData.eventually_norm_sub_one_le {Z : Set ℂ} {c : ℂ → ℂ}
    (h : IsGenusOneData Z c) (R : ℝ) :
    ∀ᶠ a : Z in cofinite, ∀ z ∈ closedBall (0 : ℂ) R,
      ‖genusOneFactor a (c a) z - 1‖ ≤ genusOneBound Z c R a := by
  filter_upwards [h.eventually_small R] with a ⟨ha1, ha2⟩ z hz
  rw [mem_closedBall_zero_iff] at hz
  have hw : ‖z / a‖ ≤ R * ‖(a : ℂ)‖⁻¹ := by rw [norm_div, div_eq_mul_inv]; gcongr
  have he : ‖z * (c a - (a : ℂ)⁻¹)‖ ≤ R * ‖c a - (a : ℂ)⁻¹‖ := by rw [norm_mul]; gcongr
  refine (norm_genusOneFactor_sub_one_le (hw.trans ha1) (he.trans ha2)).trans ?_
  have : ‖z / a‖ ^ 2 ≤ R ^ 2 * ‖(a : ℂ)‖⁻¹ ^ 2 := by rw [← mul_pow]; gcongr
  unfold genusOneBound
  linarith

/-- The logarithmic analogue of Lemma 1.2 (Lemma 1.11(1)). -/
theorem IsGenusOneData.eventually_norm_log_le {Z : Set ℂ} {c : ℂ → ℂ}
    (h : IsGenusOneData Z c) (R : ℝ) :
    ∀ᶠ a : Z in cofinite, ∀ z ∈ closedBall (0 : ℂ) R,
      ‖Complex.log (1 - z / a) + z * c a‖ ≤ genusOneBound Z c R a := by
  filter_upwards [h.eventually_small (2 * R)] with a ⟨ha1, _⟩ z hz
  rw [mem_closedBall_zero_iff] at hz
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have hw : ‖z / a‖ ≤ R * ‖(a : ℂ)‖⁻¹ := by rw [norm_div, div_eq_mul_inv]; gcongr
  have he : ‖z * (c a - (a : ℂ)⁻¹)‖ ≤ R * ‖c a - (a : ℂ)⁻¹‖ := by rw [norm_mul]; gcongr
  have hid : Complex.log (1 - z / a) + z * c a
      = (Complex.log (1 - z / a) + z / a) + z * (c a - (a : ℂ)⁻¹) := by
    rw [div_eq_mul_inv]; ring
  have hlog := norm_log_one_sub_add_le (w := z / a) (by linarith)
  have : ‖z / a‖ ^ 2 ≤ R ^ 2 * ‖(a : ℂ)‖⁻¹ ^ 2 := by rw [← mul_pow]; gcongr
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  unfold genusOneBound
  have : 0 ≤ R ^ 2 * ‖(a : ℂ)‖⁻¹ ^ 2 := by positivity
  have : 0 ≤ R * ‖c a - (a : ℂ)⁻¹‖ := by positivity
  linarith

theorem IsGenusOneData.summable_norm_sub_one {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c)
    (z : ℂ) : Summable fun a : Z ↦ ‖genusOneFactor a (c a) z - 1‖ :=
  (h.summable_genusOneBound ‖z‖).of_norm_bounded_eventually (by
    filter_upwards [h.eventually_norm_sub_one_le ‖z‖] with a ha
    rw [norm_norm]
    exact ha z (by simp))

theorem IsGenusOneData.summable_log {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) (z : ℂ) :
    Summable fun a : Z ↦ Complex.log (1 - z / a) + z * c a :=
  (h.summable_genusOneBound ‖z‖).of_norm_bounded_eventually (by
    filter_upwards [h.eventually_norm_log_le ‖z‖] with a ha
    exact ha z (by simp))

/-- `exp (canonicalLog Z c z) = P_{Z,c}(z)` for every `z ∉ Z`. -/
theorem exp_canonicalLog_of_notMem {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) {z : ℂ}
    (hz : z ∉ Z) : Complex.exp (canonicalLog Z c z) = canonicalProd Z c z := by
  have hE := (h.summable_log z).hasSum.cexp
  have hfac : ∀ a : Z, (Complex.exp ∘ fun a : Z ↦ Complex.log (1 - z / a) + z * c a) a
      = genusOneFactor a (c a) z := by
    intro a
    have h1 : (1 : ℂ) - z / a ≠ 0 := by
      rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq (h.ne_zero a.2)]
      exact fun e ↦ hz (e ▸ a.2)
    simp only [Function.comp_apply, Complex.exp_add, Complex.exp_log h1, genusOneFactor]
  rw [funext hfac] at hE
  exact hE.tprod_eq.symm

/-! ## Convergence, holomorphy, zeros -/

/-- The product converges locally uniformly on `ℂ`. -/
theorem hasProdLocallyUniformlyOn_canonicalProd {Z : Set ℂ} {c : ℂ → ℂ}
    (h : IsGenusOneData Z c) :
    HasProdLocallyUniformlyOn (fun (a : Z) (z : ℂ) ↦ genusOneFactor a (c a) z)
      (canonicalProd Z c) univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have := Summable.hasProdUniformlyOn_one_add hK (h.summable_genusOneBound R)
    (f := fun (a : Z) z ↦ genusOneFactor a (c a) z - 1)
    (by filter_upwards [h.eventually_norm_sub_one_le R] with a ha z hz using ha z (hR hz))
    (fun a ↦ ((differentiable_genusOneFactor _ _).continuous.sub continuous_const).continuousOn)
  simp only [add_sub_cancel] at this
  exact this

theorem multipliable_genusOneFactor {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) (z : ℂ) :
    Multipliable fun a : Z ↦ genusOneFactor a (c a) z := by
  simpa using multipliable_one_add_of_summable (h.summable_norm_sub_one z)

/-- `P_{Z,c}` is entire. -/
theorem differentiable_canonicalProd {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) :
    Differentiable ℂ (canonicalProd Z c) := by
  rw [← differentiableOn_univ]
  refine (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    (hasProdLocallyUniformlyOn_canonicalProd h)).differentiableOn ?_ isOpen_univ
  exact Eventually.of_forall fun t ↦ DifferentiableOn.fun_finsetProd
    fun a _ ↦ (differentiable_genusOneFactor _ _).differentiableOn

/-- The zero set of `P_{Z,c}` is exactly `Z`. -/
theorem canonicalProd_eq_zero_iff {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) {z : ℂ} :
    canonicalProd Z c z = 0 ↔ z ∈ Z := by
  constructor
  · intro h0
    by_contra hz
    have hne : ∀ a : Z, 1 + (genusOneFactor a (c a) z - 1) ≠ 0 := fun a ↦ by
      rw [add_sub_cancel, Ne, genusOneFactor_eq_zero_iff (h.ne_zero a.2)]
      exact fun e ↦ hz (e ▸ a.2)
    have := tprod_one_add_ne_zero_of_summable hne (h.summable_norm_sub_one z)
    simp only [add_sub_cancel] at this
    exact this h0
  · intro hz
    exact tprod_of_exists_eq_zero
      ⟨⟨z, hz⟩, (genusOneFactor_eq_zero_iff (h.ne_zero hz)).mpr rfl⟩

/-- Splitting off one factor. -/
theorem canonicalProd_eq_mul {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) {a : ℂ}
    (ha : a ∈ Z) (z : ℂ) :
    canonicalProd Z c z = genusOneFactor a (c a) z * canonicalProd (Z \ {a}) c z := by
  have hZ : Z = {a} ∪ (Z \ {a}) := (Set.union_sdiff_cancel (singleton_subset_iff.mpr ha)).symm
  have hm1 : Multipliable ((fun b ↦ genusOneFactor b (c b) z) ∘ (↑) : ({a} : Set ℂ) → ℂ) :=
    Multipliable.of_finite
  have hm2 := multipliable_genusOneFactor (h.mono (sdiff_subset (t := {a}))) z
  unfold canonicalProd
  conv_lhs => rw [hZ]
  rw [Multipliable.tprod_union_disjoint disjoint_sdiff_right hm1 hm2,
    tprod_singleton a (fun b ↦ genusOneFactor b (c b) z)]

/-- The zeros are simple: `P'(a) = −a⁻¹ e^{a c_a} P_{Z∖{a}}(a) ≠ 0`. -/
theorem hasDerivAt_canonicalProd_of_mem {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) {a : ℂ}
    (ha : a ∈ Z) :
    HasDerivAt (canonicalProd Z c) (-a⁻¹ * Complex.exp (a * c a) * canonicalProd (Z \ {a}) c a)
      a := by
  have hfun : canonicalProd Z c = fun z ↦ genusOneFactor a (c a) z * canonicalProd (Z \ {a}) c z :=
    funext (canonicalProd_eq_mul h ha)
  have ha0 := h.ne_zero ha
  have h1 : HasDerivAt (genusOneFactor a (c a)) (-a⁻¹ * Complex.exp (a * c a)) a := by
    have hA : HasDerivAt (fun z : ℂ ↦ 1 - z / a) (-(1 / a)) a :=
      (hasDerivAt_id' (x := a)).div_const a |>.const_sub 1
    have hB : HasDerivAt (fun z : ℂ ↦ Complex.exp (z * c a)) (Complex.exp (a * c a) * (1 * c a))
      a := ((hasDerivAt_id' (x := a)).mul_const (c a)).cexp
    convert hA.fun_mul hB using 1
    · rfl
    · rw [div_self ha0]
      ring
  have h2 := (differentiable_canonicalProd (h.mono (sdiff_subset (t := {a}))) a).hasDerivAt
  rw [hfun]
  convert h1.mul h2 using 1
  rw [(genusOneFactor_eq_zero_iff ha0).mpr rfl]
  ring

theorem deriv_canonicalProd_ne_zero {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) {a : ℂ}
    (ha : a ∈ Z) : deriv (canonicalProd Z c) a ≠ 0 := by
  rw [(hasDerivAt_canonicalProd_of_mem h ha).deriv]
  have hP : canonicalProd (Z \ {a}) c a ≠ 0 := by
    rw [Ne, canonicalProd_eq_zero_iff (h.mono (sdiff_subset (t := {a})))]
    simp
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (h.ne_zero ha)))
    (Complex.exp_ne_zero _)) hP

/-- `log|P(z)| = ∑_{a ∈ Z} (log|1 − z/a| + Re(z c_a))` for `z ∉ Z`. -/
theorem hasSum_log_norm_canonicalProd {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) {z : ℂ}
    (hz : z ∉ Z) :
    HasSum (fun a : Z ↦ Real.log ‖1 - z / a‖ + (z * c a).re)
      (Real.log ‖canonicalProd Z c z‖) := by
  rw [← exp_canonicalLog_of_notMem h hz, Complex.norm_exp, Real.log_exp]
  unfold canonicalLog
  have := Complex.hasSum_re (h.summable_log z).hasSum
  simpa only [add_re, Complex.log_re] using this

/-! ## Algebraic manipulations -/

/-- The involution `a ↦ ā` of a conjugation-symmetric set. -/
def conjEquivOfSymm {Z : Set ℂ} (hZ : ∀ a ∈ Z, conj a ∈ Z) : Z ≃ Z where
  toFun a := ⟨conj (a : ℂ), hZ a a.2⟩
  invFun a := ⟨conj (a : ℂ), hZ a a.2⟩
  left_inv _ := Subtype.ext (Complex.conj_conj _)
  right_inv _ := Subtype.ext (Complex.conj_conj _)

@[simp]
theorem conjEquivOfSymm_apply {Z : Set ℂ} (hZ : ∀ a ∈ Z, conj a ∈ Z) (a : Z) :
    ((conjEquivOfSymm hZ a : Z) : ℂ) = conj (a : ℂ) :=
  rfl

/-- Changing the convergence factors multiplies `P` by `e^{z ∑ (c'_a − c_a)}`. -/
theorem canonicalProd_congr_factor {Z : Set ℂ} {c c' : ℂ → ℂ} (h : IsGenusOneData Z c)
    (h' : IsGenusOneData Z c') (z : ℂ) :
    canonicalProd Z c' z = Complex.exp (z * ∑' a : Z, (c' a - c a)) * canonicalProd Z c z := by
  have hs : Summable fun a : Z ↦ c' a - c a := by
    refine Summable.of_norm_bounded (h'.summable_sub_inv.add h.summable_sub_inv) fun a ↦ ?_
    calc ‖c' a - c a‖ = ‖(c' a - (a : ℂ)⁻¹) - (c a - (a : ℂ)⁻¹)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  have hE : HasProd (fun a : Z ↦ Complex.exp (z * (c' a - c a)))
      (Complex.exp (z * ∑' a : Z, (c' a - c a))) :=
    (hs.hasSum.mul_left z).cexp
  have hfac : ∀ a : Z, genusOneFactor a (c' a) z
      = Complex.exp (z * (c' a - c a)) * genusOneFactor a (c a) z := by
    intro a
    simp only [genusOneFactor]
    rw [mul_left_comm, ← Complex.exp_add]
    ring_nf
  unfold canonicalProd
  rw [tprod_congr hfac, Multipliable.tprod_mul hE.multipliable (multipliable_genusOneFactor h z),
    hE.tprod_eq]

/-- The product over a disjoint union is the product of the products. -/
theorem canonicalProd_union {Z W : Set ℂ} {c : ℂ → ℂ} (hZ : IsGenusOneData Z c)
    (hW : IsGenusOneData W c) (hd : Disjoint Z W) (z : ℂ) :
    canonicalProd (Z ∪ W) c z = canonicalProd Z c z * canonicalProd W c z := by
  unfold canonicalProd
  exact Multipliable.tprod_union_disjoint (f := fun b ↦ genusOneFactor b (c b) z) hd
    (multipliable_genusOneFactor hZ z) (multipliable_genusOneFactor hW z)

/-- Conjugation symmetry: `P(z̄) = conj P(z)` if `Z` and `c` are symmetric.  For `Z ⊆ ℝ` and real
`c` (Lemma 3) the hypotheses are trivial. -/
theorem canonicalProd_conj {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c)
    (hZ : ∀ a ∈ Z, conj a ∈ Z) (hc : ∀ a ∈ Z, c (conj a) = conj (c a)) (z : ℂ) :
    canonicalProd Z c (conj z) = conj (canonicalProd Z c z) := by
  let e : Z ≃ Z := conjEquivOfSymm hZ
  unfold canonicalProd
  rw [(multipliable_genusOneFactor h z).map_tprod (starRingEnd ℂ) Complex.continuous_conj]
  conv_rhs => rw [← e.tprod_eq]
  refine tprod_congr fun a ↦ ?_
  simp only [e, conjEquivOfSymm_apply, genusOneFactor, hc a a.2, map_mul, map_sub, map_one,
    map_div₀, Complex.conj_conj, ← Complex.exp_conj]

/-- Multiplication by `e^{αz+β}` adds `Re(αz+β)` to `log|·|`. -/
theorem log_norm_exp_mul (α β z w : ℂ) (hw : w ≠ 0) :
    Real.log ‖Complex.exp (α * z + β) * w‖ = (α * z + β).re + Real.log ‖w‖ := by
  rw [norm_mul, Complex.norm_exp, Real.log_mul (Real.exp_pos _).ne' (norm_ne_zero_iff.mpr hw),
    Real.log_exp]

/-! ## An explicit logarithm off the rays -/

/-- The partial sums of `canonicalLog` converge locally uniformly on `ℂ` (with the principal
`Log`, whatever the position of `z`). -/
theorem tendstoLocallyUniformlyOn_canonicalLog {Z : Set ℂ} {c : ℂ → ℂ}
    (h : IsGenusOneData Z c) :
    TendstoLocallyUniformlyOn
      (fun (t : Finset Z) z ↦ ∑ a ∈ t, (Complex.log (1 - z / a) + z * c a))
      (canonicalLog Z c) atTop univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  exact (tendstoUniformlyOn_tsum_of_cofinite_eventually (h.summable_genusOneBound R)
    (h.eventually_norm_log_le R)).mono hR

/-- If `a ∈ ℝ` and `z ∉ ℝ`, then `1 − z/a` lies in the slit plane (also for `a = 0`, where
`z/0 = 0`). -/
theorem one_sub_div_mem_slitPlane {a z : ℂ} (ha : a.im = 0) (hz : z.im ≠ 0) :
    1 - z / a ∈ slitPlane := by
  by_cases ha0 : a = 0
  · simp [ha0, one_mem_slitPlane]
  · have hre : a = (a.re : ℂ) := Complex.ext rfl (by simp [ha])
    have hre0 : a.re ≠ 0 := fun h0 ↦ ha0 (by rw [hre, h0]; simp)
    rw [mem_slitPlane_iff]
    right
    rw [hre, sub_im, one_im, div_ofReal_im]
    simp [hz, hre0]

/-- The series defining `canonicalLog` converges locally uniformly on any open set where all
`1 − z/a` lie in the slit plane, and its sum is holomorphic there. -/
theorem differentiableOn_canonicalLog {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hslit : ∀ z ∈ Ω, ∀ a ∈ Z, 1 - z / a ∈ slitPlane) :
    DifferentiableOn ℂ (canonicalLog Z c) Ω := by
  refine ((tendstoLocallyUniformlyOn_canonicalLog h).mono (subset_univ Ω)).differentiableOn
    (Eventually.of_forall fun t ↦ ?_) hΩ
  refine DifferentiableOn.fun_sum fun a _ z hz ↦ ?_
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.add ?_ (by fun_prop)
  exact (DifferentiableAt.clog (by fun_prop) (hslit z hz a a.2))

theorem hasSum_canonicalLog {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) (z : ℂ) :
    HasSum (fun a : Z ↦ Complex.log (1 - z / a) + z * c a) (canonicalLog Z c z) :=
  (h.summable_log z).hasSum

/-- `exp (canonicalLog Z c z) = P_{Z,c}(z)` whenever every `1 − z/a` lies in the slit plane. -/
theorem exp_canonicalLog {Z : Set ℂ} {c : ℂ → ℂ} (h : IsGenusOneData Z c) {z : ℂ}
    (hslit : ∀ a ∈ Z, 1 - z / a ∈ slitPlane) :
    Complex.exp (canonicalLog Z c z) = canonicalProd Z c z := by
  refine exp_canonicalLog_of_notMem h fun hz ↦ ?_
  have := hslit z hz
  rw [div_self (h.ne_zero hz), sub_self] at this
  exact zero_notMem_slitPlane this

/-- Conjugation symmetry of the explicit logarithm. -/
theorem canonicalLog_conj {Z : Set ℂ} {c : ℂ → ℂ} (hZ : ∀ a ∈ Z, conj a ∈ Z)
    (hc : ∀ a ∈ Z, c (conj a) = conj (c a)) {z : ℂ} (hslit : ∀ a ∈ Z, 1 - z / a ∈ slitPlane) :
    canonicalLog Z c (conj z) = conj (canonicalLog Z c z) := by
  -- no summability hypothesis is needed: `conj` commutes with `tsum` unconditionally
  -- (`Complex.conj_tsum`)
  let e : Z ≃ Z := conjEquivOfSymm hZ
  unfold canonicalLog
  rw [Complex.conj_tsum]
  conv_rhs => rw [← e.tsum_eq]
  refine tsum_congr fun a ↦ ?_
  have hca := hc a a.2
  have harg : (1 - z / conj (a : ℂ)).arg ≠ Real.pi :=
    (mem_slitPlane_iff_arg.mp (hslit (conj (a : ℂ)) (hZ a a.2))).1
  simp only [e, conjEquivOfSymm_apply, map_add, map_mul, hca, Complex.conj_conj]
  rw [← Complex.log_conj _ harg]
  simp only [map_sub, map_one, map_div₀, Complex.conj_conj]

end OCS
