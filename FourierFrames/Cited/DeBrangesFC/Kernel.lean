import FourierFrames.Cited.DeBrangesFC.Space

/-!
# P4, Part C: the reproducing kernel of `H` and the function `E` (C.1–C.8)

See `blueprint/P4_DeBrangesFC.md`, §1.4–1.5.  From the axioms (H1)–(H3): kernel vectors by Riesz,
`‖k ζ‖ > 0` by iterating (H1), Hermitian symmetry, (H3) as a conjugate-linear isometric
involution, (H1) as a unitary map giving the identity (★), and the explicit
`E = √π (z + i) K(i, z)/√K(i, i)` with `ι (k w) = K_E(w, ·)` and `E` strict.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace FF

section PartC

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The data and axioms (H1)–(H3) of Theorem C, bundled (exactly the hypotheses of `TheoremC`). -/
structure DBAxioms (ι : H →ₗ[ℂ] (ℂ → ℂ)) : Prop where
  inj : Function.Injective ι
  entire : ∀ h : H, Differentiable ℂ (ι h)
  h1 : ∀ h : H, ∀ ζ : ℂ, ζ.im ≠ 0 → ι h ζ = 0 →
      ∃ g : H, ‖g‖ = ‖h‖ ∧ ∀ z : ℂ, z ≠ ζ → ι g z = ι h z * (z - conj ζ) / (z - ζ)
  h2 : ∀ ζ : ℂ, ζ.im ≠ 0 → Continuous fun h : H ↦ ι h ζ
  h3 : ∀ h : H, ∃ g : H, ‖g‖ = ‖h‖ ∧ ι g = fstar (ι h)
  nontrivial : ∃ h : H, h ≠ 0

/-- `k ζ` is the reproducing kernel vector at the nonreal point `ζ`:
`(ι h)(ζ) = ⟪k ζ, h⟫`; the kernel function is `K(w, z) = ι (k w) z`. -/
def IsKernelFamily (ι : H →ₗ[ℂ] (ℂ → ℂ)) (k : ℂ → H) : Prop :=
  ∀ ζ : ℂ, ζ.im ≠ 0 → ∀ h : H, ι h ζ = ⟪k ζ, h⟫_ℂ

/-- The Hermite–Biehler function built from the kernel (de Branges' recipe, ζ₀ = i):
`E(z) = √π (z + i) K(i, z) / √K(i, i)`. -/
def kernelE (ι : H →ₗ[ℂ] (ℂ → ℂ)) (k : ℂ → H) (z : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * (z + I) * ι (k I) z / (Real.sqrt (ι (k I) I).re : ℂ)

variable {ι : H →ₗ[ℂ] (ℂ → ℂ)}

/-- An element whose function vanishes on `ℂ₊` is `0`. -/
theorem DBAxioms.eq_zero_of_upper (hax : DBAxioms ι) {h : H}
    (h0 : ∀ z : ℂ, 0 < z.im → ι h z = 0) : h = 0 := by
  have h1 := eq_of_eqOn_upper (hax.entire h) (differentiable_const 0) h0
  apply hax.inj
  rw [h1, map_zero]
  rfl

/-- Two elements whose functions agree off a finite set are equal. -/
theorem DBAxioms.eq_of_eq_off_finite (hax : DBAxioms ι) {g g' : H} {s : Set ℂ} (hs : s.Finite)
    (h : ∀ z, z ∉ s → ι g z = ι g' z) : g = g' :=
  hax.inj (FF.eq_of_eq_off_finite (hax.entire g) (hax.entire g') hs h)

/-! ### C.1–C.4 The reproducing kernel of `H` -/

/-- C.1 Existence of kernels (Riesz representation, `InnerProductSpace.toDual`). -/
theorem exists_kernel [CompleteSpace H] (hax : DBAxioms ι) : ∃ k : ℂ → H, IsKernelFamily ι k := by
  classical
  let Λ : ∀ ζ : ℂ, ζ.im ≠ 0 → (H →L[ℂ] ℂ) := fun ζ hζ ↦
    { toFun := fun h ↦ ι h ζ
      map_add' := fun x y ↦ by simp
      map_smul' := fun c x ↦ by simp
      cont := hax.h2 ζ hζ }
  refine ⟨fun ζ ↦ if hζ : ζ.im ≠ 0 then (InnerProductSpace.toDual ℂ H).symm (Λ ζ hζ) else 0, ?_⟩
  intro ζ hζ h
  simp only [ne_eq, hζ, not_false_eq_true, ↓reduceDIte, InnerProductSpace.toDual_symm_apply]
  rfl

/-- `K(ζ, ζ) = ‖k ζ‖²`. -/
theorem kernel_diag {k : ℂ → H} (hk : IsKernelFamily ι k) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    ι (k ζ) ζ = ((‖k ζ‖ ^ 2 : ℝ) : ℂ) := by
  rw [hk ζ hζ, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- C.2 `K(ζ,ζ) = ‖k ζ‖² > 0` for nonreal `ζ` (iterate (H1): the zero order at `ζ` would drop). -/
theorem kernel_norm_pos (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) {ζ : ℂ}
    (hζ : ζ.im ≠ 0) : 0 < ‖k ζ‖ := by
  by_contra hneg
  have hk0 : k ζ = 0 := norm_le_zero_iff.mp (not_lt.mp hneg)
  have hvan : ∀ h : H, ι h ζ = 0 := fun h ↦ by rw [hk ζ hζ, hk0, inner_zero_left]
  have hclaim : ∀ n : ℕ, ∀ h : H, analyticOrderAt (ι h) ζ ≠ n := by
    intro n
    induction n with
    | zero =>
      intro h hn
      rcases analyticOrderAt_eq_zero.mp hn with h1 | h1
      · exact h1 ((hax.entire h).analyticAt ζ)
      · exact h1 (hvan h)
    | succ n ih =>
      intro h hn
      obtain ⟨g, -, hg⟩ := hax.h1 h ζ hζ (hvan h)
      exact ih g (analyticOrderAt_eq_of_mul_div (hax.entire h) (hax.entire g) hζ hn hg)
  obtain ⟨h, hne⟩ := hax.nontrivial
  have hιne : ι h ≠ 0 := fun h0 ↦ hne (hax.inj (by rw [h0, map_zero]))
  have htop : analyticOrderAt (ι h) ζ ≠ ⊤ := fun ht ↦ hιne
    ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ζ
      fun z ↦ (hax.entire h).analyticAt z).mp ht)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  exact hclaim n h hn.symm

theorem kernel_diag_ne_zero (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) {ζ : ℂ}
    (hζ : ζ.im ≠ 0) : ι (k ζ) ζ ≠ 0 := by
  rw [kernel_diag hk hζ, Complex.ofReal_ne_zero]
  exact pow_ne_zero 2 (kernel_norm_pos hax hk hζ).ne'

/-- C.3 Hermitian symmetry `K(w,z) = conj K(z,w)` for nonreal `w, z`. -/
theorem kernel_symm {k : ℂ → H} (hk : IsKernelFamily ι k) {w z : ℂ} (hw : w.im ≠ 0)
    (hz : z.im ≠ 0) : ι (k w) z = conj (ι (k z) w) := by
  rw [hk z hz, hk w hw, inner_conj_symm]

/-- C.4 (H3) as a conjugate-linear isometric involution `S`, `ι (S h) = (ι h)^*`. -/
theorem exists_conjMap (hax : DBAxioms ι) :
    ∃ S : H → H, (∀ h : H, ι (S h) = fstar (ι h)) ∧ (∀ x y : H, ⟪S x, S y⟫_ℂ = ⟪y, x⟫_ℂ) ∧
      ∀ h : H, S (S h) = h := by
  choose S hSn hS using hax.h3
  have hadd : ∀ x y, S (x + y) = S x + S y := fun x y ↦ hax.inj (by
    rw [hS, map_add, map_add, hS, hS]
    funext z
    simp [fstar])
  have hsub : ∀ x y, S (x - y) = S x - S y := fun x y ↦ hax.inj (by
    rw [hS, map_sub, map_sub, hS, hS]
    funext z
    simp [fstar])
  have hsmul : ∀ (c : ℂ) x, S (c • x) = conj c • S x := fun c x ↦ hax.inj (by
    rw [hS, map_smul, map_smul, hS]
    funext z
    simp [fstar])
  have hSS : ∀ h, S (S h) = h := fun h ↦ hax.inj (by rw [hS, hS, fstar_fstar])
  refine ⟨S, hS, ?_, hSS⟩
  intro x y
  have h1 : ‖S x + S y‖ = ‖y + x‖ := by rw [← hadd, hSn, add_comm]
  have h2 : ‖S x - S y‖ = ‖y - x‖ := by rw [← hsub, hSn, norm_sub_rev]
  have h3 : ‖S x - I • S y‖ = ‖y - I • x‖ := by
    have e1 : S x - I • S y = S (x + I • y) := by
      rw [hadd, hsmul, Complex.conj_I, neg_smul, sub_eq_add_neg]
    have e2 : y - I • x = (-I) • (x + I • y) := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
      abel
    rw [e1, hSn, e2, norm_smul]
    simp
  have h4 : ‖S x + I • S y‖ = ‖y + I • x‖ := by
    have e1 : S x + I • S y = S (x - I • y) := by
      rw [hsub, hsmul, Complex.conj_I, neg_smul, sub_neg_eq_add]
    have e2 : y + I • x = I • (x - I • y) := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add, add_comm]
    rw [e1, hSn, e2, norm_smul]
    simp
  rw [inner_eq_sum_norm_sq_div_four (S x), inner_eq_sum_norm_sq_div_four y x]
  simp only [RCLike.I_to_complex]
  rw [h1, h2, h3, h4]

/-- C.4 `K(w,·)^* = K(w̄,·)`. -/
theorem kernel_fstar (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) {w : ℂ}
    (hw : w.im ≠ 0) : fstar (ι (k w)) = ι (k (conj w)) := by
  obtain ⟨S, hS, hSinner, hSS⟩ := exists_conjMap hax
  have hw' : (conj w).im ≠ 0 := by simpa using hw
  have hSk : S (k w) = k (conj w) := by
    refine ext_inner_right ℂ fun v ↦ ?_
    calc ⟪S (k w), v⟫_ℂ = ⟪S (k w), S (S v)⟫_ℂ := by rw [hSS]
      _ = ⟪S v, k w⟫_ℂ := hSinner _ _
      _ = conj ⟪k w, S v⟫_ℂ := (inner_conj_symm _ _).symm
      _ = conj (ι (S v) w) := by rw [hk w hw]
      _ = ι v (conj w) := by rw [hS]; simp [fstar]
      _ = ⟪k (conj w), v⟫_ℂ := hk _ hw' v
  rw [← hS, hSk]

/-! ### C.5–C.8 The identity from (H1) and the function `E` -/

/-- C.5 (H1) as a unitary map `T : {f(ζ) = 0} → {f(ζ̄) = 0}`, `T f = f (z - ζ̄)/(z - ζ)`. -/
theorem exists_mulMap (hax : DBAxioms ι) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    ∃ T : H → H,
      (∀ f : H, ι f ζ = 0 → ∀ z : ℂ, z ≠ ζ → ι (T f) z = ι f z * (z - conj ζ) / (z - ζ)) ∧
      (∀ f f' : H, ι f ζ = 0 → ι f' ζ = 0 → ⟪T f, T f'⟫_ℂ = ⟪f, f'⟫_ℂ) ∧
      ∀ g : H, ι g (conj ζ) = 0 → ∃ f : H, ι f ζ = 0 ∧ T f = g := by
  classical
  let T : H → H := fun f ↦ if h : ι f ζ = 0 then (hax.h1 f ζ hζ h).choose else 0
  have hTf : ∀ f, ι f ζ = 0 → ‖T f‖ = ‖f‖ ∧
      ∀ z, z ≠ ζ → ι (T f) z = ι f z * (z - conj ζ) / (z - ζ) := by
    intro f hf
    simp only [T, hf, ↓reduceDIte]
    exact (hax.h1 f ζ hζ hf).choose_spec
  let Hζ : Submodule ℂ H := LinearMap.ker ((LinearMap.proj ζ).comp ι)
  have hmem : ∀ f, f ∈ Hζ ↔ ι f ζ = 0 := fun f ↦ by simp [Hζ]
  have hT : ∀ f : Hζ, ‖T f‖ = ‖(f : H)‖ ∧
      ∀ z, z ≠ ζ → ι (T f) z = ι f z * (z - conj ζ) / (z - ζ) := fun f ↦
    hTf f ((hmem f).mp f.2)
  let Tl : Hζ →ₗᵢ[ℂ] H :=
    { toFun := fun f ↦ T f
      map_add' := fun f f' ↦ hax.eq_of_eq_off_finite (Set.finite_singleton ζ) fun z hz ↦ by
        rw [(hT (f + f')).2 z hz, map_add, Pi.add_apply, (hT f).2 z hz, (hT f').2 z hz]
        simp only [Submodule.coe_add, map_add, Pi.add_apply]
        ring
      map_smul' := fun c f ↦ hax.eq_of_eq_off_finite (Set.finite_singleton ζ) fun z hz ↦ by
        rw [(hT (c • f)).2 z hz, RingHom.id_apply, map_smul, Pi.smul_apply, (hT f).2 z hz]
        simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul]
        ring
      norm_map' := fun f ↦ (hT f).1 }
  refine ⟨T, fun f hf ↦ (hTf f hf).2, fun f f' hf hf' ↦ ?_, ?_⟩
  · exact Tl.inner_map_map ⟨f, (hmem f).mpr hf⟩ ⟨f', (hmem f').mpr hf'⟩
  · intro g hg
    have hζ' : (conj ζ).im ≠ 0 := by simpa using hζ
    obtain ⟨g', -, hg'⟩ := hax.h1 g (conj ζ) hζ' hg
    have hne : ζ ≠ conj ζ := fun h ↦ sub_conj_ne_zero hζ (by rw [← h, sub_self])
    have hg'ζ : ι g' ζ = 0 := by
      rw [hg' ζ hne, Complex.conj_conj, sub_self, mul_zero, zero_div]
    refine ⟨g', hg'ζ, hax.eq_of_eq_off_finite (s := {ζ, conj ζ}) (Set.toFinite _) ?_⟩
    intro z hz
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
    rw [(hTf g' hg'ζ).2 z hz.1, hg' z hz.2, Complex.conj_conj]
    have h1 : z - ζ ≠ 0 := sub_ne_zero.mpr hz.1
    have h2 : z - conj ζ ≠ 0 := sub_ne_zero.mpr hz.2
    field_simp

/-- C.5 The identity (★): `T` maps the kernel of `{f(ζ)=0}` at `w` to a multiple of the kernel
of `{f(ζ̄)=0}` at `w` (multiplied form, valid for all `z`). -/
theorem kernel_identity (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) {ζ w z : ℂ}
    (hζ : ζ.im ≠ 0) (hw : w.im ≠ 0) :
    (z - conj ζ) * (conj w - ζ) *
        (ι (k w) z - ι (k ζ) z * ι (k w) ζ / ι (k ζ) ζ) =
      (z - ζ) * (conj w - conj ζ) *
        (ι (k w) z - ι (k (conj ζ)) z * ι (k w) (conj ζ) / ι (k (conj ζ)) (conj ζ)) := by
  have hζ' : (conj ζ).im ≠ 0 := by simpa using hζ
  set a := ι (k ζ) ζ with ha
  set b := ι (k (conj ζ)) (conj ζ) with hb
  have ha0 : a ≠ 0 := kernel_diag_ne_zero hax hk hζ
  have hb0 : b ≠ 0 := kernel_diag_ne_zero hax hk hζ'
  set p : H := k w - (ι (k w) ζ / a) • k ζ with hp
  set q : H := k w - (ι (k w) (conj ζ) / b) • k (conj ζ) with hq
  have hpz : ∀ u, ι p u = ι (k w) u - ι (k ζ) u * ι (k w) ζ / a := fun u ↦ by
    simp only [hp, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hqz : ∀ u, ι q u = ι (k w) u - ι (k (conj ζ)) u * ι (k w) (conj ζ) / b := fun u ↦ by
    simp only [hq, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hpζ : ι p ζ = 0 := by rw [hpz]; field_simp; ring
  have hqζ : ι q (conj ζ) = 0 := by rw [hqz]; field_simp; ring
  have hpf : ∀ f : H, ι f ζ = 0 → ⟪p, f⟫_ℂ = ι f w := fun f hf ↦ by
    rw [hp, inner_sub_left, inner_smul_left, ← hk w hw, ← hk ζ hζ, hf, mul_zero, sub_zero]
  have hqg : ∀ g : H, ι g (conj ζ) = 0 → ⟪q, g⟫_ℂ = ι g w := fun g hg ↦ by
    rw [hq, inner_sub_left, inner_smul_left, ← hk w hw, ← hk (conj ζ) hζ', hg, mul_zero,
      sub_zero]
  rw [← hpz, ← hqz]
  by_cases hwζ : w = ζ
  · have hp0 : ∀ u, ι p u = 0 := fun u ↦ by
      rw [hpz, hwζ]
      field_simp
      ring
    rw [hp0, hwζ, sub_self]
    ring
  obtain ⟨T, hT1, hT2, hT3⟩ := exists_mulMap hax hζ
  have hne : conj ζ ≠ ζ := fun h ↦ sub_conj_ne_zero hζ (by rw [h, sub_self])
  set c₀ : ℂ := (w - conj ζ) / (w - ζ) with hc₀
  have hwζ' : w - ζ ≠ 0 := sub_ne_zero.mpr hwζ
  have hTp : ι (T p) (conj ζ) = 0 := by
    rw [hT1 p hpζ _ hne, sub_self, mul_zero, zero_div]
  set d : H := q - conj c₀ • T p with hd
  have hdζ : ι d (conj ζ) = 0 := by
    simp only [hd, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hqζ, hTp,
      mul_zero, sub_zero]
  have horth : ∀ g : H, ι g (conj ζ) = 0 → ⟪d, g⟫_ℂ = 0 := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := hT3 g hg
    rw [hd, inner_sub_left, inner_smul_left, Complex.conj_conj, hqg _ hg, hT2 p f hpζ hf,
      hpf f hf, hT1 f hf w hwζ, hc₀]
    ring
  have hd0 : d = 0 := inner_self_eq_zero.mp (horth d hdζ)
  have hqT : q = conj c₀ • T p := sub_eq_zero.mp hd0
  by_cases hzζ : z = ζ
  · rw [hzζ, hpζ, sub_self]
    ring
  have hz' : z - ζ ≠ 0 := sub_ne_zero.mpr hzζ
  have hw' : conj w - conj ζ ≠ 0 := by
    rw [← map_sub]
    exact (map_ne_zero _).mpr hwζ'
  have hcc : conj c₀ = (conj w - ζ) / (conj w - conj ζ) := by
    rw [hc₀, map_div₀, map_sub, map_sub, Complex.conj_conj]
  rw [hqT, map_smul, Pi.smul_apply, smul_eq_mul, hT1 p hpζ z hzζ, hcc]
  generalize ι p z = X
  field_simp

/-- C.6 `kernelE` is entire. -/
theorem differentiable_kernelE (hax : DBAxioms ι) (k : ℂ → H) :
    Differentiable ℂ (kernelE ι k) := by
  have h := hax.entire (k I)
  unfold kernelE
  fun_prop

/-- `kernelE` with the normalisation `√K(i,i) = ‖k i‖`. -/
theorem kernelE_eq {k : ℂ → H} (hk : IsKernelFamily ι k) (z : ℂ) :
    kernelE ι k z = ((Real.sqrt Real.pi / ‖k I‖ : ℝ) : ℂ) * ((z + I) * ι (k I) z) := by
  unfold kernelE
  rw [kernel_diag hk (by simp : I.im ≠ 0), Complex.ofReal_re, Real.sqrt_sq (norm_nonneg _)]
  push_cast
  ring

/-- C.6 `E^*(z) = √π (z - i) K(-i, z) / √K(i, i)`. -/
theorem fstar_kernelE (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) :
    fstar (kernelE ι k) =
      fun z ↦ (Real.sqrt Real.pi : ℂ) * (z - I) * ι (k (-I)) z / (Real.sqrt (ι (k I) I).re : ℂ) := by
  funext z
  have hK := congrFun (kernel_fstar hax hk (w := I) (by simp)) z
  rw [Complex.conj_I] at hK
  simp only [fstar] at hK ⊢
  unfold kernelE
  rw [← hK]
  simp only [map_div₀, map_mul, map_add, Complex.conj_ofReal, Complex.conj_conj, Complex.conj_I]
  ring

theorem fstar_kernelE_eq (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) (z : ℂ) :
    fstar (kernelE ι k) z = ((Real.sqrt Real.pi / ‖k I‖ : ℝ) : ℂ) * ((z - I) * ι (k (-I)) z) := by
  rw [fstar_kernelE hax hk, kernel_diag hk (by simp : I.im ≠ 0), Complex.ofReal_re,
    Real.sqrt_sq (norm_nonneg _)]
  push_cast
  ring

/-- `K(-i, -i) = K(i, i)`. -/
theorem kernel_diag_neg_I (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) :
    ι (k (-I)) (-I) = ι (k I) I := by
  have hK := congrFun (kernel_fstar hax hk (w := I) (by simp)) (-I)
  rw [Complex.conj_I] at hK
  rw [← hK, kernel_diag hk (by simp : I.im ≠ 0)]
  simp [fstar, kernel_diag hk (by simp : I.im ≠ 0)]

/-- C.7 Formula (1), multiplied form, all `z`: `K(w,z) π (z - w̄) = (i/2) kernelNum E w z`. -/
theorem kernel_mul_eq (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) {w : ℂ}
    (hw : w.im ≠ 0) (z : ℂ) :
    ι (k w) z * (Real.pi * (z - conj w)) = I / 2 * kernelNum (kernelE ι k) w z := by
  have hI : I.im ≠ 0 := by simp
  have hmI : (-I).im ≠ 0 := by simp
  set a := ι (k I) I with ha
  have hc : ((Real.sqrt Real.pi / ‖k I‖ : ℝ) : ℂ) ^ 2 = Real.pi / a := by
    rw [ha, kernel_diag hk hI]
    have hr : (Real.sqrt Real.pi / ‖k I‖) ^ 2 = Real.pi / ‖k I‖ ^ 2 := by
      rw [div_pow, Real.sq_sqrt Real.pi_pos.le]
    exact_mod_cast hr
  have hID := kernel_identity hax hk hI hw (z := z)
  simp only [Complex.conj_I] at hID
  rw [kernel_diag_neg_I hax hk, ← ha] at hID
  have hs1 := kernel_symm hk hw hI
  have hs2 := kernel_symm hk hw hmI
  unfold kernelNum
  rw [kernelE_eq hk z, kernelE_eq hk w, fstar_kernelE_eq hax hk z, fstar_kernelE_eq hax hk w]
  simp only [map_mul, map_add, map_sub, Complex.conj_ofReal, Complex.conj_I]
  rw [← hs1, ← hs2]
  set c := ((Real.sqrt Real.pi / ‖k I‖ : ℝ) : ℂ)
  linear_combination (I * Real.pi / 2) * hID - (I / 2) * ((z + I) * (conj w + -I) *
    (ι (k I) z * ι (k w) I) - (z - I) * (conj w - -I) * (ι (k (-I)) z * ι (k w) (-I))) * hc +
    ι (k w) z * Real.pi * (z - conj w) * Complex.I_sq

/-- C.7 The kernel of `H` is the de Branges kernel of `E = kernelE ι k` (as functions). -/
theorem kernel_eq_deBrangesKernel (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k)
    {w : ℂ} (hw : w.im ≠ 0) : ι (k w) = deBrangesKernel (kernelE ι k) w := by
  refine FF.eq_of_eq_off_finite (hax.entire _)
    (differentiable_deBrangesKernel (differentiable_kernelE hax k) w)
    (Set.finite_singleton (conj w)) fun z hz ↦ ?_
  have hne : (Real.pi : ℂ) * (z - conj w) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (sub_ne_zero.mpr hz)
  apply mul_right_cancel₀ hne
  rw [kernel_mul_eq hax hk hw z, deBrangesKernel_mul]

/-- C.8 `E` is in the strict Hermite–Biehler class: `|E^*(w)| < |E(w)|` on `ℂ₊`, from
`K(w,w) = (|E(w)|² - |E(w̄)|²)/(4π Im w) > 0`. -/
theorem isStrictHB_kernelE (hax : DBAxioms ι) {k : ℂ → H} (hk : IsKernelFamily ι k) :
    IsStrictHB (kernelE ι k) := by
  have hstrict : ∀ z : ℂ, 0 < z.im → ‖kernelE ι k (conj z)‖ < ‖kernelE ι k z‖ := by
    intro z hz
    have h1 := kernel_diag hk hz.ne'
    rw [kernel_eq_deBrangesKernel hax hk hz.ne', deBrangesKernel_diag _ hz.ne'] at h1
    have h2 := Complex.ofReal_injective h1
    have hpos : 0 < ‖k z‖ ^ 2 := pow_pos (kernel_norm_pos hax hk hz.ne') 2
    rw [← h2] at hpos
    have h4 : 0 < ‖kernelE ι k z‖ ^ 2 - ‖kernelE ι k (conj z)‖ ^ 2 :=
      (div_pos_iff_of_pos_right (by positivity)).mp hpos
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by linarith)
  refine ⟨⟨differentiable_kernelE hax k, fun z hz h0 ↦ ?_, fun z hz ↦ (hstrict z hz).le⟩,
    hstrict⟩
  have := hstrict z hz
  rw [h0, norm_zero] at this
  exact (norm_nonneg _).not_gt this

end PartC

end FF
