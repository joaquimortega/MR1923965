import OrtegaCerdaSeip.Defs

/-!
# M07 (Lemma 3) — the partition, the barycentres and the Peano kernel

See `blueprint/M07_Lemma3.md`, §1.1–§1.4.  Paper, p. 406.

For a weight `m` with `0 < a ≤ m ≤ b`:
* `multPrim m x = ∫_0^x m` is a strictly increasing bijection `ℝ → ℝ`;
* `multPt m j = x_j` with `∫_0^{x_j} m = j` (`x_0 = 0`), so `∫_{I_j} m = 1`, `1/b ≤ |I_j| ≤ 1/a`;
* `multBary m j = γ_j = ∫_{I_j} t m(t) dt`, at distance `≥ a/(2b²)` from both endpoints of `I_j`;
* `multGamma m = Γ = {γ_j : j ∈ ℤ}`: separated (`|γ_j − γ_k| ≥ a/b²`), `0 ∉ Γ`;
* `multPeanoLoc m j` is the paper's `H` on `I_j`:
  `H(x) = (x − γ_j)⁺ − ∫_{x_j}^x (x − t) m(t) dt`, `H(x_j) = H(x_{j+1}) = 0`, `|H| ≤ |I_j|/2`;
  `multPeanoH m` is the global `H` (`= ∫_0^x h`, `h = ∫_0^x dμ`, `μ = ∑ δ_{γ_j} − m dt`);
* the Peano-kernel identity (paper's (4) before summation):
  `g(γ_j) − ∫_{I_j} g m = ∫_{I_j} H g''` (`multErr_eq_integral_peano`).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-- The hypotheses of Lemma 3 on the weight: `m` measurable and `0 < a ≤ m ≤ b`. -/
structure IsMultWeight (m : ℝ → ℝ) (a b : ℝ) : Prop where
  measurable : Measurable m
  pos : 0 < a
  le : ∀ t, a ≤ m t
  ge : ∀ t, m t ≤ b

/-- `M(x) = ∫_0^x m`. -/
def multPrim (m : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, m t

/-- The partition points `x_j = M⁻¹(j)`. -/
def multPt (m : ℝ → ℝ) (j : ℤ) : ℝ :=
  sInf {x : ℝ | (j : ℝ) ≤ multPrim m x}

/-- The index of the interval containing `x`: `j(x) = ⌊M(x)⌋`, so `x ∈ I_{j(x)}`. -/
def multIdx (m : ℝ → ℝ) (x : ℝ) : ℤ :=
  ⌊multPrim m x⌋

/-- The barycentre `γ_j = ∫_{I_j} t m(t) dt`. -/
def multBary (m : ℝ → ℝ) (j : ℤ) : ℝ :=
  ∫ t in multPt m j..multPt m (j + 1), t * m t

/-- The zero set `Γ = {γ_j : j ∈ ℤ}`. -/
def multGamma (m : ℝ → ℝ) : Set ℝ :=
  range (multBary m)

/-- The Peano kernel on `I_j`: `H_j(x) = (x − γ_j)⁺ − ∫_{x_j}^x (x − t) m(t) dt`. -/
def multPeanoLoc (m : ℝ → ℝ) (j : ℤ) (x : ℝ) : ℝ :=
  max (x - multBary m j) 0 - ∫ t in multPt m j..x, (x - t) * m t

/-- The global Peano kernel `H(x) = H_{j(x)}(x)`, the paper's `H = ∫_0^x h`. -/
def multPeanoH (m : ℝ → ℝ) (x : ℝ) : ℝ :=
  multPeanoLoc m (multIdx m x) x

/-- The local error functional `E_j(g) = g(γ_j) − ∫_{I_j} g m`; the paper's
`∫_{I_j} g dμ` with `μ = ∑ δ_{γ_j} − m dt`. -/
def multErr (m : ℝ → ℝ) (g : ℝ → ℝ) (j : ℤ) : ℝ :=
  g (multBary m j) - ∫ t in multPt m j..multPt m (j + 1), g t * m t

/-! ## The primitive `M` -/

theorem IsMultWeight.le_b {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) : a ≤ b :=
  (hw.le 0).trans (hw.ge 0)

theorem IsMultWeight.nonneg {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (t : ℝ) :
    0 ≤ m t :=
  hw.pos.le.trans (hw.le t)

theorem IsMultWeight.b_pos {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) : 0 < b :=
  hw.pos.trans_le hw.le_b

theorem IsMultWeight.norm_le {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (t : ℝ) :
    ‖m t‖ ≤ b := by
  rw [Real.norm_eq_abs, abs_of_nonneg (hw.nonneg t)]; exact hw.ge t

theorem IsMultWeight.intervalIntegrable {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b)
    (x y : ℝ) : IntervalIntegrable m volume x y := by
  have : IntervalIntegrable (fun _ ↦ b) volume x y := intervalIntegrable_const
  refine this.mono_fun hw.measurable.aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
  rw [Real.norm_eq_abs b, abs_of_nonneg (by linarith [hw.le t, hw.pos, hw.ge t])]
  exact hw.norm_le t

/-- A bounded measurable factor preserves interval integrability. -/
theorem IsMultWeight.intervalIntegrable_mul {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b)
    {g : ℝ → ℝ} {x y : ℝ} (hg : IntervalIntegrable g volume x y) :
    IntervalIntegrable (fun t ↦ g t * m t) volume x y :=
  ⟨hg.1.mul_bdd hw.measurable.aestronglyMeasurable (ae_of_all _ hw.norm_le),
    hg.2.mul_bdd hw.measurable.aestronglyMeasurable (ae_of_all _ hw.norm_le)⟩

theorem multPrim_zero (m : ℝ → ℝ) : multPrim m 0 = 0 :=
  intervalIntegral.integral_same

theorem multPrim_sub_eq {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (x y : ℝ) :
    multPrim m y - multPrim m x = ∫ t in x..y, m t := by
  unfold multPrim
  rw [intervalIntegral.integral_interval_sub_left (hw.intervalIntegrable _ _)
    (hw.intervalIntegrable _ _)]

theorem multPrim_sub_bounds {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {x y : ℝ}
    (hxy : x ≤ y) :
    a * (y - x) ≤ multPrim m y - multPrim m x ∧ multPrim m y - multPrim m x ≤ b * (y - x) := by
  rw [multPrim_sub_eq hw]
  constructor
  · have := intervalIntegral.integral_mono_on hxy intervalIntegrable_const
      (hw.intervalIntegrable x y) (fun t _ ↦ hw.le t)
    simpa [mul_comm] using this
  · have := intervalIntegral.integral_mono_on hxy (hw.intervalIntegrable x y)
      intervalIntegrable_const (fun t _ ↦ hw.ge t)
    simpa [mul_comm] using this

theorem continuous_multPrim {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    Continuous (multPrim m) :=
  intervalIntegral.continuous_primitive (fun x y ↦ hw.intervalIntegrable x y) 0

theorem strictMono_multPrim {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    StrictMono (multPrim m) := by
  intro x y hxy
  have := (multPrim_sub_bounds hw hxy.le).1
  nlinarith [hw.pos, mul_pos hw.pos (sub_pos.mpr hxy)]

/-! ## The partition -/

theorem surjective_multPrim {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    Function.Surjective (multPrim m) := by
  refine (continuous_multPrim hw).surjective ?_ ?_
  · refine tendsto_atTop_mono' atTop ?_ (tendsto_id.const_mul_atTop hw.pos)
    filter_upwards [eventually_ge_atTop 0] with x hx
    have := (multPrim_sub_bounds hw hx).1
    rw [multPrim_zero, sub_zero, sub_zero] at this
    exact this
  · refine tendsto_atBot_mono' atBot ?_ (tendsto_id.const_mul_atBot hw.pos)
    filter_upwards [eventually_le_atBot 0] with x hx
    have := (multPrim_sub_bounds hw hx).1
    rw [multPrim_zero] at this
    simp only [id]
    linarith

theorem multPt_eq_of {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {j : ℤ} {x : ℝ}
    (hx : multPrim m x = j) : multPt m j = x := by
  unfold multPt
  have : {y : ℝ | (j : ℝ) ≤ multPrim m y} = Ici x := by
    ext y
    show (j : ℝ) ≤ multPrim m y ↔ x ≤ y
    rw [← hx]
    exact (strictMono_multPrim hw).le_iff_le
  rw [this, csInf_Ici]

theorem multPrim_multPt {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) :
    multPrim m (multPt m j) = j := by
  obtain ⟨x, hx⟩ := surjective_multPrim hw j
  rw [multPt_eq_of hw hx, hx]

theorem multPt_zero {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) : multPt m 0 = 0 :=
  multPt_eq_of hw (by rw [multPrim_zero]; simp)

theorem strictMono_multPt {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    StrictMono (multPt m) := by
  intro j k hjk
  rw [← (strictMono_multPrim hw).lt_iff_lt, multPrim_multPt hw, multPrim_multPt hw]
  exact_mod_cast hjk

/-- `∫_{I_j} m = 1`. -/
theorem integral_multPt {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) :
    ∫ t in multPt m j..multPt m (j + 1), m t = 1 := by
  rw [← multPrim_sub_eq hw, multPrim_multPt hw, multPrim_multPt hw]
  push_cast; ring

/-- `1/b ≤ |I_j| ≤ 1/a`. -/
theorem multPt_succ_sub_bounds {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) :
    1 / b ≤ multPt m (j + 1) - multPt m j ∧ multPt m (j + 1) - multPt m j ≤ 1 / a := by
  have h := multPrim_sub_bounds hw (strictMono_multPt hw (lt_add_one j)).le
  rw [multPrim_multPt hw, multPrim_multPt hw] at h
  push_cast at h
  have hb := hw.b_pos
  have ha := hw.pos
  constructor
  · rw [div_le_iff₀ hb]; linarith
  · rw [le_div_iff₀ ha]; linarith

/-- `|x_j| ≥ |j|/b`. -/
theorem abs_multPt_ge {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) :
    |(j : ℝ)| / b ≤ |multPt m j| := by
  have hb := hw.b_pos
  rw [div_le_iff₀ hb]
  have hM := multPrim_multPt hw j
  rcases le_total 0 (multPt m j) with h | h
  · have := multPrim_sub_bounds hw h
    rw [multPrim_zero, hM] at this
    rw [abs_of_nonneg h, abs_le]
    constructor <;> nlinarith [hw.pos]
  · have := multPrim_sub_bounds hw h
    rw [multPrim_zero, hM] at this
    rw [abs_of_nonpos h, abs_le]
    constructor <;> nlinarith [hw.pos]

/-- `x ∈ I_{j(x)} = [x_{j(x)}, x_{j(x)+1})`. -/
theorem multIdx_mem {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (x : ℝ) :
    multPt m (multIdx m x) ≤ x ∧ x < multPt m (multIdx m x + 1) := by
  have h1 := Int.floor_le (multPrim m x)
  have h2 := Int.lt_floor_add_one (multPrim m x)
  unfold multIdx
  constructor
  · rw [← (strictMono_multPrim hw).le_iff_le, multPrim_multPt hw]; exact h1
  · rw [← (strictMono_multPrim hw).lt_iff_lt, multPrim_multPt hw]; push_cast; exact h2

theorem multIdx_eq_iff {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {x : ℝ} {j : ℤ} :
    multIdx m x = j ↔ x ∈ Ico (multPt m j) (multPt m (j + 1)) := by
  constructor
  · rintro rfl; exact multIdx_mem hw x
  · rintro ⟨h1, h2⟩
    unfold multIdx
    rw [Int.floor_eq_iff]
    constructor
    · rw [← multPrim_multPt hw j]; exact (strictMono_multPrim hw).monotone h1
    · have := (strictMono_multPrim hw) h2
      rw [multPrim_multPt hw] at this
      push_cast at this
      exact this

/-! ## The barycentres -/

theorem multBary_sub_multPt {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) :
    multBary m j - multPt m j =
      ∫ t in multPt m j..multPt m (j + 1), (t - multPt m j) * m t := by
  have h1 : IntervalIntegrable (fun t ↦ t * m t) volume (multPt m j) (multPt m (j + 1)) :=
    hw.intervalIntegrable_mul (continuous_id.intervalIntegrable _ _)
  have h2 : IntervalIntegrable (fun t ↦ multPt m j * m t) volume (multPt m j)
      (multPt m (j + 1)) := (hw.intervalIntegrable _ _).const_mul _
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
    integral_multPt hw, mul_one]
  rfl

theorem multPt_sub_multBary {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) :
    multPt m (j + 1) - multBary m j =
      ∫ t in multPt m j..multPt m (j + 1), (multPt m (j + 1) - t) * m t := by
  have h1 : IntervalIntegrable (fun t ↦ t * m t) volume (multPt m j) (multPt m (j + 1)) :=
    hw.intervalIntegrable_mul (continuous_id.intervalIntegrable _ _)
  have h2 : IntervalIntegrable (fun t ↦ multPt m (j + 1) * m t) volume (multPt m j)
      (multPt m (j + 1)) := (hw.intervalIntegrable _ _).const_mul _
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub h2 h1, intervalIntegral.integral_const_mul,
    integral_multPt hw, mul_one]
  rfl

/-- `γ_j` is at distance `≥ a/(2b²)` from both endpoints of `I_j`. -/
theorem multBary_mem {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) :
    multPt m j + a / (2 * b ^ 2) ≤ multBary m j ∧
      multBary m j + a / (2 * b ^ 2) ≤ multPt m (j + 1) := by
  set x₀ := multPt m j
  set x₁ := multPt m (j + 1)
  have hL := (multPt_succ_sub_bounds hw j).1
  have hb := hw.b_pos
  have ha := hw.pos
  have hlow : a / (2 * b ^ 2) ≤ a * (x₁ - x₀) ^ 2 / 2 := by
    have h1 : (1 / b) ^ 2 ≤ (x₁ - x₀) ^ 2 := pow_le_pow_left₀ (by positivity) hL 2
    have h2 : a / (2 * b ^ 2) = a * (1 / b) ^ 2 / 2 := by field_simp
    rw [h2]; gcongr
  have hx : x₀ ≤ x₁ := (strictMono_multPt hw (lt_add_one j)).le
  have hc : IntervalIntegrable (fun t : ℝ ↦ t) volume x₀ x₁ := continuous_id.intervalIntegrable _ _
  constructor
  · have e := multBary_sub_multPt hw j
    have : ∫ t in x₀..x₁, (t - x₀) * a ≤ ∫ t in x₀..x₁, (t - x₀) * m t :=
      intervalIntegral.integral_mono_on hx ((hc.sub intervalIntegrable_const).mul_const _)
        (hw.intervalIntegrable_mul (hc.sub intervalIntegrable_const))
        (fun t ht ↦ mul_le_mul_of_nonneg_left (hw.le t) (sub_nonneg.mpr ht.1))
    have hv : ∫ t in x₀..x₁, (t - x₀) * a = a * (x₁ - x₀) ^ 2 / 2 := by
      simp [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub, integral_id]
      ring
    linarith
  · have e := multPt_sub_multBary hw j
    have : ∫ t in x₀..x₁, (x₁ - t) * a ≤ ∫ t in x₀..x₁, (x₁ - t) * m t :=
      intervalIntegral.integral_mono_on hx ((intervalIntegrable_const.sub hc).mul_const _)
        (hw.intervalIntegrable_mul (intervalIntegrable_const.sub hc))
        (fun t ht ↦ mul_le_mul_of_nonneg_left (hw.le t) (sub_nonneg.mpr ht.2))
    have hv : ∫ t in x₀..x₁, (x₁ - t) * a = a * (x₁ - x₀) ^ 2 / 2 := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub (f := fun _ ↦ x₁)
        (g := fun x ↦ x) intervalIntegrable_const hc]
      simp [integral_id]
      ring
    linarith

/-- `γ_k − γ_j ≥ a/b²` for `j < k`. -/
theorem multBary_sub_ge {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {j k : ℤ} (hjk : j < k) :
    a / b ^ 2 ≤ multBary m k - multBary m j := by
  have h1 := (multBary_mem hw j).2
  have h2 := (multBary_mem hw k).1
  have h3 : multPt m (j + 1) ≤ multPt m k := (strictMono_multPt hw).monotone (by omega)
  have : a / b ^ 2 = a / (2 * b ^ 2) + a / (2 * b ^ 2) := by ring
  linarith

theorem strictMono_multBary {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    StrictMono (multBary m) := by
  intro j k hjk
  have := multBary_sub_ge hw hjk
  have : 0 < a / b ^ 2 := div_pos hw.pos (pow_pos hw.b_pos 2)
  linarith

/-- `0 ∉ Γ` (`0 = x_0` is an endpoint, `γ_j` is interior). -/
theorem zero_notMem_multGamma {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    (0 : ℝ) ∉ multGamma m := by
  rintro ⟨j, hj⟩
  have hc : 0 < a / (2 * b ^ 2) := div_pos hw.pos (by positivity [hw.b_pos])
  have h0 := multPt_zero hw
  rcases le_or_gt 0 j with h | h
  · have h1 := (multBary_mem hw j).1
    have h2 : multPt m 0 ≤ multPt m j := (strictMono_multPt hw).monotone h
    linarith
  · have h1 := (multBary_mem hw j).2
    have h2 : multPt m (j + 1) ≤ multPt m 0 := (strictMono_multPt hw).monotone (by omega)
    linarith

/-- `Γ` is separated (for the paper's `σ`). -/
theorem isSeparated_multGamma {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    IsSeparated ((fun t : ℝ ↦ (t : ℂ)) '' multGamma m) := by
  set c := a / b ^ 2 with hc_def
  have hc : 0 < c := div_pos hw.pos (pow_pos hw.b_pos 2)
  refine ⟨c / (1 + c), by positivity, ?_⟩
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩ _ ⟨_, ⟨k, rfl⟩, rfl⟩ hne
  have hjk : j ≠ k := by rintro rfl; exact hne rfl
  have hd : c ≤ |multBary m j - multBary m k| := by
    rcases lt_or_gt_of_ne hjk with h | h
    · rw [abs_sub_comm, abs_of_pos (by linarith [multBary_sub_ge hw h])]
      exact multBary_sub_ge hw h
    · rw [abs_of_pos (by linarith [multBary_sub_ge hw h])]
      exact multBary_sub_ge hw h
  unfold sigmaDist
  rw [Complex.conj_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `∑_j γ_j⁻² < ∞`. -/
theorem summable_multBary_inv_sq {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    Summable fun j : ℤ ↦ (multBary m j)⁻¹ ^ 2 := by
  have hb := hw.b_pos
  have hbound : ∀ j : ℤ, (|(j : ℝ)| - 1) / b ≤ |multBary m j| := by
    intro j
    rcases le_or_gt 0 j with h | h
    · have h1 := (multBary_mem hw j).1
      have h2 := abs_multPt_ge hw j
      have h3 : multPt m 0 ≤ multPt m j := (strictMono_multPt hw).monotone h
      rw [multPt_zero hw] at h3
      have hc : 0 < a / (2 * b ^ 2) := div_pos hw.pos (by positivity)
      rw [abs_of_nonneg h3] at h2
      rw [abs_of_pos (a := multBary m j) (by linarith)]
      have : (|(j : ℝ)| - 1) / b ≤ |(j : ℝ)| / b := by gcongr; linarith
      linarith
    · have h1 := (multBary_mem hw j).2
      have h2 := abs_multPt_ge hw (j + 1)
      have h3 : multPt m (j + 1) ≤ multPt m 0 := (strictMono_multPt hw).monotone (by omega)
      rw [multPt_zero hw] at h3
      have hc : 0 < a / (2 * b ^ 2) := div_pos hw.pos (by positivity)
      rw [abs_of_nonpos h3] at h2
      rw [abs_of_neg (a := multBary m j) (by linarith)]
      have hj : |((j + 1 : ℤ) : ℝ)| = |(j : ℝ)| - 1 := by
        have : (j : ℝ) + 1 ≤ 0 := by exact_mod_cast (show j + 1 ≤ 0 by omega)
        push_cast
        rw [abs_of_nonpos this, abs_of_neg (by linarith)]
        ring
      rw [hj] at h2
      linarith
  refine Summable.of_norm_bounded_eventually (g := fun j : ℤ ↦ 4 * b ^ 2 * (1 / (j : ℝ) ^ 2))
    ((Real.summable_one_div_int_pow.mpr one_lt_two).mul_left _) ?_
  have hfin : {j : ℤ | ¬ 2 ≤ |j|}.Finite := by
    refine (Set.finite_Icc (-1 : ℤ) 1).subset fun j hj ↦ ?_
    simp only [Set.mem_ofPred_eq, not_le] at hj
    rw [abs_lt] at hj
    exact ⟨by omega, by omega⟩
  filter_upwards [hfin.compl_mem_cofinite] with j hj
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hj
  have hj' : (2 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast hj
  have h1 := hbound j
  have hpos : 0 < (|(j : ℝ)| - 1) / b := div_pos (by linarith) hb
  have h2 : |(j : ℝ)| / (2 * b) ≤ (|(j : ℝ)| - 1) / b := by
    rw [div_le_div_iff₀ (by positivity) hb]; nlinarith
  have h3 : |(j : ℝ)| / (2 * b) ≤ |multBary m j| := h2.trans h1
  have hjpos : 0 < |(j : ℝ)| / (2 * b) := by positivity
  rw [norm_pow, norm_inv, Real.norm_eq_abs, inv_pow]
  calc (|multBary m j| ^ 2)⁻¹ ≤ ((|(j : ℝ)| / (2 * b)) ^ 2)⁻¹ := by
        gcongr
    _ = 4 * b ^ 2 * (1 / (j : ℝ) ^ 2) := by
        rw [div_pow, ← sq_abs (j : ℝ)]
        field_simp
        ring

theorem norm_sub_ofReal_le_of_abs_le {z : ℂ} {s t : ℝ} (h : |z.re - s| ≤ |z.re - t|) :
    ‖z - s‖ ≤ ‖z - t‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
  have := sq_le_sq.mpr h
  nlinarith

/-- The nearest points of `Γ` to `z` with `Re z ∈ I_k` are among `γ_{k−1}, γ_k, γ_{k+1}`:
every `γ_j` with `|j − k| ≥ 2` is farther than one of them. -/
theorem norm_sub_multBary_far {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (z : ℂ) {j : ℤ}
    (hj : 2 ≤ |j - multIdx m z.re|) :
    (‖z - multBary m (multIdx m z.re + 1)‖ ≤ ‖z - multBary m j‖ ∧ multIdx m z.re < j) ∨
      (‖z - multBary m (multIdx m z.re - 1)‖ ≤ ‖z - multBary m j‖ ∧ j < multIdx m z.re) := by
  set k := multIdx m z.re
  have hk := multIdx_mem hw z.re
  have hmono := (strictMono_multPt hw).monotone
  rcases le_or_gt k j with h | h
  · left
    have hj : k + 2 ≤ j := by rw [abs_of_nonneg (by omega)] at hj; omega
    refine ⟨norm_sub_ofReal_le_of_abs_le ?_, by omega⟩
    have h1 := multBary_mem hw (k + 1)
    have h2 := multBary_mem hw j
    have h3 : multPt m (k + 1 + 1) ≤ multPt m j := hmono (by omega)
    have hc : 0 < a / (2 * b ^ 2) := div_pos hw.pos (by positivity [hw.b_pos])
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    linarith
  · right
    have hj : j + 2 ≤ k := by rw [abs_of_neg (by omega)] at hj; omega
    refine ⟨norm_sub_ofReal_le_of_abs_le ?_, h⟩
    have h1 := multBary_mem hw (k - 1)
    have h2 := multBary_mem hw j
    have h3 : multPt m (j + 1) ≤ multPt m (k - 1) := hmono (by omega)
    have h4 : multPt m (k - 1 + 1) ≤ multPt m k := hmono (by omega)
    have hc : 0 < a / (2 * b ^ 2) := div_pos hw.pos (by positivity [hw.b_pos])
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith

/-! ## The Peano kernel -/

theorem multPt_lt_succ {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) :
    multPt m j < multPt m (j + 1) :=
  strictMono_multPt hw (lt_add_one j)

theorem IsMultWeight.intervalIntegrable_id_mul {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b)
    (u v : ℝ) : IntervalIntegrable (fun t ↦ t * m t) volume u v :=
  hw.intervalIntegrable_mul (g := fun t ↦ t) (continuous_id.intervalIntegrable u v)

theorem integral_const_sub_mul {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (x u v : ℝ) :
    ∫ t in u..v, (x - t) * m t = x * (∫ t in u..v, m t) - ∫ t in u..v, t * m t := by
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub ((hw.intervalIntegrable _ _).const_mul x)
    (hw.intervalIntegrable_id_mul _ _), intervalIntegral.integral_const_mul]

theorem integral_sub_const_mul {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (x u v : ℝ) :
    ∫ t in u..v, (t - x) * m t = (∫ t in u..v, t * m t) - x * ∫ t in u..v, m t := by
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (hw.intervalIntegrable_id_mul _ _)
    ((hw.intervalIntegrable _ _).const_mul x), intervalIntegral.integral_const_mul]

theorem continuous_multPeanoLoc {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) :
    Continuous (multPeanoLoc m j) := by
  have h1 : Continuous fun x ↦ ∫ t in multPt m j..x, m t :=
    intervalIntegral.continuous_primitive (fun u v ↦ hw.intervalIntegrable u v) _
  have h2 : Continuous fun x ↦ ∫ t in multPt m j..x, t * m t :=
    intervalIntegral.continuous_primitive (fun u v ↦ hw.intervalIntegrable_id_mul u v) _
  have : multPeanoLoc m j = fun x ↦ max (x - multBary m j) 0 -
      (x * (∫ t in multPt m j..x, m t) - ∫ t in multPt m j..x, t * m t) := by
    funext x; rw [multPeanoLoc, integral_const_sub_mul hw]
  rw [this]
  exact ((continuous_id.sub continuous_const).max continuous_const).sub
    ((continuous_id.mul h1).sub h2)

/-- The second closed form: `H_j(x) = (γ_j − x)⁺ − ∫_x^{x_{j+1}} (t − x) m(t) dt`. -/
theorem multPeanoLoc_eq_right {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) (x : ℝ) :
    multPeanoLoc m j x =
      max (multBary m j - x) 0 - ∫ t in x..multPt m (j + 1), (t - x) * m t := by
  have hA := integral_const_sub_mul hw x (multPt m j) x
  have hB := integral_sub_const_mul hw x x (multPt m (j + 1))
  have h1 : (∫ t in multPt m j..x, m t) + ∫ t in x..multPt m (j + 1), m t = 1 := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hw.intervalIntegrable _ _)
      (hw.intervalIntegrable _ _), integral_multPt hw]
  have h2 : (∫ t in multPt m j..x, t * m t) + ∫ t in x..multPt m (j + 1), t * m t =
      multBary m j := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hw.intervalIntegrable_id_mul _ _)
      (hw.intervalIntegrable_id_mul _ _)]
    rfl
  rw [multPeanoLoc, hA, hB]
  have h3 : max (x - multBary m j) 0 - (x - multBary m j) = max (multBary m j - x) 0 := by
    rcases le_total x (multBary m j) with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have h4 : x * (∫ t in multPt m j..x, m t) - ∫ t in multPt m j..x, t * m t =
      (x - multBary m j) +
        ((∫ t in x..multPt m (j + 1), t * m t) - x * ∫ t in x..multPt m (j + 1), m t) := by
    linear_combination x * h1 - h2
  rw [h4, ← h3]; ring

theorem integral_multPt_left_le_one {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ)
    {x : ℝ} (hx : x ∈ Icc (multPt m j) (multPt m (j + 1))) :
    0 ≤ ∫ t in multPt m j..x, m t ∧ ∫ t in multPt m j..x, m t ≤ 1 ∧
      0 ≤ ∫ t in x..multPt m (j + 1), m t ∧ ∫ t in x..multPt m (j + 1), m t ≤ 1 := by
  have h1 : (∫ t in multPt m j..x, m t) + ∫ t in x..multPt m (j + 1), m t = 1 := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hw.intervalIntegrable _ _)
      (hw.intervalIntegrable _ _), integral_multPt hw]
  have h2 : 0 ≤ ∫ t in multPt m j..x, m t :=
    intervalIntegral.integral_nonneg hx.1 fun t _ ↦ hw.nonneg t
  have h3 : 0 ≤ ∫ t in x..multPt m (j + 1), m t :=
    intervalIntegral.integral_nonneg hx.2 fun t _ ↦ hw.nonneg t
  exact ⟨h2, by linarith, h3, by linarith⟩

/-- Two-sided bounds: `−(x − x_j) ≤ H_j(x) ≤ 0` and `−(x_{j+1} − x) ≤ H_j(x)` on `Ī_j`. -/
theorem multPeanoLoc_bounds {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) {x : ℝ}
    (hx : x ∈ Icc (multPt m j) (multPt m (j + 1))) :
    multPeanoLoc m j x ≤ 0 ∧ -(x - multPt m j) ≤ multPeanoLoc m j x ∧
      -(multPt m (j + 1) - x) ≤ multPeanoLoc m j x := by
  obtain ⟨hm1, hm2, hm3, hm4⟩ := integral_multPt_left_le_one hw j hx
  set A := ∫ t in multPt m j..x, (x - t) * m t with hA_def
  set B := ∫ t in x..multPt m (j + 1), (t - x) * m t with hB_def
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg hx.1
    fun t ht ↦ mul_nonneg (by linarith [ht.2]) (hw.nonneg t)
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg hx.2
    fun t ht ↦ mul_nonneg (by linarith [ht.1]) (hw.nonneg t)
  have hA1 : A ≤ x - multPt m j := by
    have : A ≤ ∫ t in multPt m j..x, (x - multPt m j) * m t :=
      intervalIntegral.integral_mono_on hx.1
        (hw.intervalIntegrable_mul ((continuous_const.sub continuous_id).intervalIntegrable _ _))
        ((hw.intervalIntegrable _ _).const_mul _)
        fun t ht ↦ mul_le_mul_of_nonneg_right (by linarith [ht.1]) (hw.nonneg t)
    rw [intervalIntegral.integral_const_mul] at this
    nlinarith [hx.1]
  have hB1 : B ≤ multPt m (j + 1) - x := by
    have : B ≤ ∫ t in x..multPt m (j + 1), (multPt m (j + 1) - x) * m t :=
      intervalIntegral.integral_mono_on hx.2
        (hw.intervalIntegrable_mul ((continuous_id.sub continuous_const).intervalIntegrable _ _))
        ((hw.intervalIntegrable _ _).const_mul _)
        fun t ht ↦ mul_le_mul_of_nonneg_right (by linarith [ht.2]) (hw.nonneg t)
    rw [intervalIntegral.integral_const_mul] at this
    nlinarith [hx.2]
  have eA : multPeanoLoc m j x = max (x - multBary m j) 0 - A := rfl
  have eB : multPeanoLoc m j x = max (multBary m j - x) 0 - B := multPeanoLoc_eq_right hw j x
  refine ⟨?_, ?_, ?_⟩
  · rcases le_total x (multBary m j) with h | h
    · rw [eA, max_eq_right (by linarith)]; linarith
    · rw [eB, max_eq_right (by linarith)]; linarith
  · rw [eA]; linarith [le_max_right (x - multBary m j) 0]
  · rw [eB]; linarith [le_max_right (multBary m j - x) 0]

/-- `H(x_j) = 0` on `I_j` (trivial) and `H(x_{j+1}) = 0` (the choice of `γ_j`). -/
theorem multPeanoLoc_endpoints {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) :
    multPeanoLoc m j (multPt m j) = 0 ∧ multPeanoLoc m j (multPt m (j + 1)) = 0 := by
  constructor
  · have := (multBary_mem hw j).1
    have hc : 0 < a / (2 * b ^ 2) := div_pos hw.pos (by positivity [hw.b_pos])
    rw [multPeanoLoc, intervalIntegral.integral_same, max_eq_right (by linarith)]
    simp
  · have := (multBary_mem hw j).2
    have hc : 0 < a / (2 * b ^ 2) := div_pos hw.pos (by positivity [hw.b_pos])
    rw [multPeanoLoc_eq_right hw, intervalIntegral.integral_same, max_eq_right (by linarith)]
    simp

/-- `|H| ≤ min(x − x_j, x_{j+1} − x) ≤ |I_j|/2 ≤ 1/(2a)` on `I_j`. -/
theorem abs_multPeanoLoc_le {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ) {x : ℝ}
    (hx : x ∈ Icc (multPt m j) (multPt m (j + 1))) : |multPeanoLoc m j x| ≤ 1 / (2 * a) := by
  obtain ⟨h1, h2, h3⟩ := multPeanoLoc_bounds hw j hx
  have hL := (multPt_succ_sub_bounds hw j).2
  rw [abs_of_nonpos h1]
  have : 1 / (2 * a) = (1 / a) / 2 := by ring
  rw [this]
  linarith

theorem abs_multPeanoH_le {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (x : ℝ) :
    |multPeanoH m x| ≤ 1 / (2 * a) := by
  have h := multIdx_mem hw x
  exact abs_multPeanoLoc_le hw _ ⟨h.1, h.2.le⟩

theorem measurable_multPeanoH {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) :
    Measurable (multPeanoH m) := by
  have h1 : Measurable fun p : ℝ × ℤ ↦ multPeanoLoc m p.2 p.1 :=
    measurable_from_prod_countable_left fun j ↦ (continuous_multPeanoLoc hw j).measurable
  have h2 : Measurable (multIdx m) := (continuous_multPrim hw).measurable.floor
  exact h1.comp (measurable_id.prodMk h2)

/-- On `I_j` the global and the local kernels agree. -/
theorem multPeanoH_eq {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) {j : ℤ} {x : ℝ}
    (hx : x ∈ Icc (multPt m j) (multPt m (j + 1))) : multPeanoH m x = multPeanoLoc m j x := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · have hidx : multIdx m x = j + 1 := by
      rw [multIdx_eq_iff hw, h]
      exact ⟨le_rfl, strictMono_multPt hw (lt_add_one _)⟩
    rw [multPeanoH, hidx, h, (multPeanoLoc_endpoints hw j).2, (multPeanoLoc_endpoints hw (j + 1)).1]
  · have hidx : multIdx m x = j := (multIdx_eq_iff hw).2 ⟨hx.1, h⟩
    rw [multPeanoH, hidx]

/-- Taylor's formula with integral remainder at the right endpoint:
`∫_s^ξ (t − s) g''(t) dt = (ξ − s) g'(ξ) − g(ξ) + g(s)`. -/
theorem taylor_integral_right {g g' g'' : ℝ → ℝ} {x₀ ξ s : ℝ} (hs : s ∈ Icc x₀ ξ)
    (hg : ∀ t ∈ Icc x₀ ξ, HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Icc x₀ ξ, HasDerivAt g' (g'' t) t)
    (hg'' : IntervalIntegrable g'' volume x₀ ξ) :
    ∫ t in s..ξ, (t - s) * g'' t = (ξ - s) * g' ξ - g ξ + g s := by
  have hsub : uIcc s ξ ⊆ Icc x₀ ξ := by
    rw [uIcc_of_le hs.2]; exact Icc_subset_Icc hs.1 le_rfl
  have hsub' : uIcc s ξ ⊆ uIcc x₀ ξ := by
    rw [uIcc_of_le (hs.1.trans hs.2)]; exact hsub
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := s) (b := ξ)
    (u := fun t ↦ t - s) (u' := fun _ ↦ 1) (v := g') (v' := g'')
    (fun t _ ↦ (hasDerivAt_id t).sub_const s) (fun t ht ↦ hg' t (hsub ht))
    intervalIntegrable_const (hg''.mono_set hsub')
  have hcont : ContinuousOn g' (uIcc s ξ) :=
    fun t ht ↦ (hg' t (hsub ht)).continuousAt.continuousWithinAt
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := s) (b := ξ)
    (fun t ht ↦ hg t (hsub ht)) hcont.intervalIntegrable
  simp only [one_mul, sub_self, zero_mul, sub_zero] at h1
  rw [h1, h2]
  ring

/-- Fubini on the triangle `{x₀ ≤ s ≤ t ≤ ξ}`. -/
theorem integral_triangle_swap {m g'' : ℝ → ℝ} {x₀ ξ c : ℝ} (hx : x₀ ≤ ξ) (hm : Measurable m)
    (hmb : ∀ t, ‖m t‖ ≤ c) (hg'' : IntervalIntegrable g'' volume x₀ ξ) :
    ∫ t in x₀..ξ, (∫ s in x₀..t, (t - s) * m s) * g'' t =
      ∫ s in x₀..ξ, m s * ∫ t in s..ξ, (t - s) * g'' t := by
  set K : ℝ → ℝ → ℝ := fun t s ↦ if s ≤ t then (t - s) * m s * g'' t else 0 with hK
  set I := Ioc x₀ ξ
  have hI : MeasurableSet I := measurableSet_Ioc
  have hL : ∀ t ∈ I, (∫ s in x₀..t, (t - s) * m s) * g'' t = ∫ s in I, K t s := by
    intro t ht
    have : (fun s ↦ K t s) = (Iic t).indicator (fun s ↦ (t - s) * m s * g'' t) := by
      funext s; simp only [hK, indicator_apply, mem_Iic]
    have hset : I ∩ Iic t = Ioc x₀ t := by
      ext s; simp only [I, mem_inter_iff, mem_Ioc, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans ht.2⟩, h2⟩
    rw [this, setIntegral_indicator measurableSet_Iic, hset, intervalIntegral.integral_of_le ht.1.le,
      ← integral_mul_const]
  have hR : ∀ s ∈ I, m s * ∫ t in s..ξ, (t - s) * g'' t = ∫ t in I, K t s := by
    intro s hs
    have : (fun t ↦ K t s) = (Ici s).indicator (fun t ↦ m s * ((t - s) * g'' t)) := by
      funext t; simp only [hK, indicator_apply, mem_Ici]; split_ifs <;> ring
    rw [this, setIntegral_indicator measurableSet_Ici, intervalIntegral.integral_of_le hs.2,
      ← integral_const_mul]
    have : I ∩ Ici s = Icc s ξ := by
      ext t; simp only [I, mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hs.1.trans_le h1, h2⟩, h1⟩
    rw [this, integral_Icc_eq_integral_Ioc]
  rw [intervalIntegral.integral_of_le hx, intervalIntegral.integral_of_le hx,
    setIntegral_congr_fun hI hL, setIntegral_congr_fun hI hR]
  refine integral_integral_swap ?_
  have hprod : (volume.restrict I).prod (volume.restrict I) =
      (volume : Measure (ℝ × ℝ)).restrict (I ×ˢ I) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hg_ae : AEStronglyMeasurable g'' (volume.restrict I) := hg''.1.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (Function.uncurry K) ((volume.restrict I).prod (volume.restrict I)) := by
    have h1 : Measurable fun p : ℝ × ℝ ↦ if p.2 ≤ p.1 then (p.1 - p.2) * m p.2 else 0 :=
      Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        ((measurable_fst.sub measurable_snd).mul (hm.comp measurable_snd)) measurable_const
    have h2 := h1.aestronglyMeasurable.mul (hg_ae.comp_fst (ν := volume.restrict I))
    refine h2.congr (ae_of_all _ fun p ↦ ?_)
    simp only [Function.uncurry, hK, Pi.mul_apply]
    split_ifs <;> simp
  have hbound : Integrable (fun p : ℝ × ℝ ↦ (ξ - x₀) * c * ‖g'' p.1‖)
      ((volume.restrict I).prod (volume.restrict I)) := by
    have := (hg''.1.norm.const_mul ((ξ - x₀) * c)).mul_prod
      (integrableOn_const (μ := volume) (s := I) (C := (1 : ℝ)) (by simp [I]))
    simpa using this
  refine hbound.mono' hmeas ?_
  rw [hprod]
  filter_upwards [ae_restrict_mem (hI.prod hI)] with p hp
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
  simp only [Function.uncurry, hK]
  split_ifs with h
  · rw [norm_mul, norm_mul, Real.norm_eq_abs (p.1 - p.2), abs_of_nonneg (sub_nonneg.mpr h)]
    have hc : 0 ≤ c := (norm_nonneg _).trans (hmb 0)
    have h5 : p.1 - p.2 ≤ ξ - x₀ := by linarith
    have h6 := hmb p.2
    have h7 : 0 ≤ ‖g'' p.1‖ := norm_nonneg _
    have h8 : (p.1 - p.2) * ‖m p.2‖ ≤ (ξ - x₀) * c :=
      mul_le_mul h5 h6 (norm_nonneg _) (by linarith)
    exact mul_le_mul_of_nonneg_right h8 h7
  · simp only [norm_zero]
    have := (norm_nonneg _).trans (hmb 0)
    positivity

/-- **The Peano-kernel identity** (the paper's (4) on one interval, "integrating by parts
twice"): `E_j(g) = g(γ_j) − ∫_{I_j} g m = ∫_{I_j} H g''` for `g ∈ C²` near `I_j`. -/
theorem multErr_eq_integral_peano {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ)
    {g g' g'' : ℝ → ℝ}
    (hg : ∀ t ∈ Icc (multPt m j) (multPt m (j + 1)), HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Icc (multPt m j) (multPt m (j + 1)), HasDerivAt g' (g'' t) t)
    (hg'' : IntervalIntegrable g'' volume (multPt m j) (multPt m (j + 1))) :
    multErr m g j = ∫ t in multPt m j..multPt m (j + 1), multPeanoLoc m j t * g'' t := by
  set x₀ := multPt m j
  set ξ := multPt m (j + 1)
  set γ := multBary m j
  have hx : x₀ ≤ ξ := (multPt_lt_succ hw j).le
  have hγ := multBary_mem hw j
  have hc : 0 < a / (2 * b ^ 2) := div_pos hw.pos (by positivity [hw.b_pos])
  have hγ1 : x₀ ≤ γ := by linarith [hγ.1]
  have hγ2 : γ ≤ ξ := by linarith [hγ.2]
  have hsub1 : uIcc x₀ γ ⊆ uIcc x₀ ξ := by
    rw [uIcc_of_le hγ1, uIcc_of_le hx]; exact Icc_subset_Icc le_rfl hγ2
  have hsub2 : uIcc γ ξ ⊆ uIcc x₀ ξ := by
    rw [uIcc_of_le hγ2, uIcc_of_le hx]; exact Icc_subset_Icc hγ1 le_rfl
  -- the two pieces of `H_j`
  set A : ℝ → ℝ := fun x ↦ ∫ t in x₀..x, (x - t) * m t with hA
  have hAcont : Continuous A := by
    have h1 : Continuous fun x ↦ ∫ t in x₀..x, m t :=
      intervalIntegral.continuous_primitive (fun u v ↦ hw.intervalIntegrable u v) _
    have h2 : Continuous fun x ↦ ∫ t in x₀..x, t * m t :=
      intervalIntegral.continuous_primitive (fun u v ↦ hw.intervalIntegrable_id_mul u v) _
    have : A = fun x ↦ x * (∫ t in x₀..x, m t) - ∫ t in x₀..x, t * m t := by
      funext x; exact integral_const_sub_mul hw x x₀ x
    rw [this]; exact (continuous_id.mul h1).sub h2
  have hmaxc : Continuous fun t : ℝ ↦ max (t - γ) 0 :=
    (continuous_id.sub continuous_const).max continuous_const
  have i1 : IntervalIntegrable (fun t ↦ max (t - γ) 0 * g'' t) volume x₀ ξ :=
    hg''.continuousOn_mul hmaxc.continuousOn
  have i2 : IntervalIntegrable (fun t ↦ A t * g'' t) volume x₀ ξ :=
    hg''.continuousOn_mul hAcont.continuousOn
  have hsplit : (∫ t in x₀..ξ, multPeanoLoc m j t * g'' t) =
      (∫ t in x₀..ξ, max (t - γ) 0 * g'' t) - ∫ t in x₀..ξ, A t * g'' t := by
    rw [← intervalIntegral.integral_sub i1 i2]
    congr 1; funext t; simp only [multPeanoLoc, hA]; ring
  -- the first piece: Taylor at `γ`
  have hfirst : (∫ t in x₀..ξ, max (t - γ) 0 * g'' t) = (ξ - γ) * g' ξ - g ξ + g γ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (i1.mono_set hsub1)
      (i1.mono_set hsub2)]
    have e1 : (∫ t in x₀..γ, max (t - γ) 0 * g'' t) = 0 := by
      rw [← intervalIntegral.integral_zero (a := x₀) (b := γ) (μ := volume)]
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [uIcc_of_le hγ1] at ht
      simp [max_eq_right (sub_nonpos.mpr ht.2)]
    have e2 : (∫ t in γ..ξ, max (t - γ) 0 * g'' t) = ∫ t in γ..ξ, (t - γ) * g'' t := by
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [uIcc_of_le hγ2] at ht
      simp [max_eq_left (sub_nonneg.mpr ht.1)]
    rw [e1, e2, zero_add, taylor_integral_right ⟨hγ1, hγ2⟩ hg hg' hg'']
  -- the second piece: Fubini on the triangle, then Taylor at every `s`
  have hsecond : (∫ t in x₀..ξ, A t * g'' t) =
      g' ξ * (ξ - γ) - g ξ + ∫ t in x₀..ξ, g t * m t := by
    rw [integral_triangle_swap hx hw.measurable hw.norm_le hg'']
    have hgc : ContinuousOn g (uIcc x₀ ξ) := by
      rw [uIcc_of_le hx]
      exact fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt
    have e : ∀ s ∈ uIcc x₀ ξ, m s * ∫ t in s..ξ, (t - s) * g'' t =
        g' ξ * ((ξ - s) * m s) - g ξ * m s + g s * m s := by
      intro s hs
      rw [uIcc_of_le hx] at hs
      rw [taylor_integral_right hs hg hg' hg'']; ring
    rw [intervalIntegral.integral_congr e]
    have j1 : IntervalIntegrable (fun s ↦ g' ξ * ((ξ - s) * m s)) volume x₀ ξ :=
      (hw.intervalIntegrable_mul ((continuous_const.sub continuous_id).intervalIntegrable _ _)).const_mul _
    have j2 : IntervalIntegrable (fun s ↦ g ξ * m s) volume x₀ ξ :=
      (hw.intervalIntegrable _ _).const_mul _
    have j3 : IntervalIntegrable (fun s ↦ g s * m s) volume x₀ ξ :=
      hw.intervalIntegrable_mul hgc.intervalIntegrable
    rw [intervalIntegral.integral_add (j1.sub j2) j3, intervalIntegral.integral_sub j1 j2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      ← multPt_sub_multBary hw j, integral_multPt hw]
    ring
  rw [hsplit, hfirst, hsecond, multErr]
  ring

/-- The Peano bound: `|E_j(g)| ≤ (1/(2a)) ∫_{I_j} |g''|`. -/
theorem abs_multErr_le {m : ℝ → ℝ} {a b : ℝ} (hw : IsMultWeight m a b) (j : ℤ)
    {g g' g'' : ℝ → ℝ}
    (hg : ∀ t ∈ Icc (multPt m j) (multPt m (j + 1)), HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Icc (multPt m j) (multPt m (j + 1)), HasDerivAt g' (g'' t) t)
    (hg'' : IntervalIntegrable g'' volume (multPt m j) (multPt m (j + 1))) :
    |multErr m g j| ≤ 1 / (2 * a) * ∫ t in multPt m j..multPt m (j + 1), |g'' t| := by
  have hx : multPt m j ≤ multPt m (j + 1) := (multPt_lt_succ hw j).le
  rw [multErr_eq_integral_peano hw j hg hg' hg'']
  have hint : IntervalIntegrable (fun t ↦ multPeanoLoc m j t * g'' t) volume
      (multPt m j) (multPt m (j + 1)) :=
    hg''.continuousOn_mul (continuous_multPeanoLoc hw j).continuousOn
  refine (intervalIntegral.abs_integral_le_integral_abs hx).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hx hint.abs (hg''.abs.const_mul _) fun t ht ↦ ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_multPeanoLoc_le hw j ht) (abs_nonneg _)

end OCS
