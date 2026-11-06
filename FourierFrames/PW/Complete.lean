import FourierFrames.PW.Bounds
import OrtegaCerdaSeip.Bernstein.NormalFamily

/-!
# M01 — Completeness and normal-family compactness of `PW`

See `blueprint/M01_PW.md`, §4.  Both results use only the pointwise bound `pw_norm_sq_le`
(hence `hPW`) and Fatou's lemma.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- Uniform pointwise bound `‖F z‖ ≤ √M e^{π|Im z|}` from a norm bound. -/
theorem norm_le_of_pwNormSq_le (hPW : PaleyWienerThm) {F : ℂ → ℂ} (hF : MemPW F) {M : ℝ≥0∞}
    (hM' : M ≠ ⊤) (hM : pwNormSq F ≤ M) (z : ℂ) :
    ‖F z‖ ≤ Real.sqrt M.toReal * Real.exp (Real.pi * |z.im|) := by
  have h1 := pw_norm_sq_le hPW hF z
  have h2 : (pwNormSq F).toReal ≤ M.toReal := ENNReal.toReal_mono hM' hM
  have h3 : ‖F z‖ ^ 2 ≤ (Real.sqrt M.toReal * Real.exp (Real.pi * |z.im|)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg, ← Real.exp_nat_mul]
    refine h1.trans ?_
    have : (2 : ℕ) * (Real.pi * |z.im|) = 2 * Real.pi * |z.im| := by push_cast; ring
    rw [this, mul_comm]
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le |>.trans_eq (by ring)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3

/-- **Completeness.** An `L²(ℝ)`-Cauchy sequence in `PW` converges in `L²` and locally uniformly
to some `g ∈ PW`. -/
theorem pw_complete (hPW : PaleyWienerThm) {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemPW (f n))
    (hc : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      pwNormSq (fun z ↦ f m z - f n z) < ε) :
    ∃ g : ℂ → ℂ, MemPW g ∧ TendstoLocallyUniformly f g atTop ∧
      Tendsto (fun n ↦ pwNormSq (fun z ↦ f n z - g z)) atTop (nhds 0) := by
  -- Step 1: uniform Cauchy on compact sets
  have hcomp : ∀ m n : ℕ, ∀ z : ℂ, ‖f m z - f n z‖ ^ 2 ≤
      Real.exp (2 * Real.pi * |z.im|) * (pwNormSq (fun z ↦ f m z - f n z)).toReal :=
    fun m n z ↦ pw_norm_sq_le hPW ((hf m).sub (hf n)) z
  have hUC : ∀ K : Set ℂ, IsCompact K → UniformCauchySeqOn f atTop K := by
    intro K hK
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨ρ₀, hρ₀⟩ := hK.isBounded.exists_norm_le
    set ρ : ℝ := max ρ₀ 0 with hρdef
    have hρ : ∀ z ∈ K, ‖z‖ ≤ ρ := fun z hz ↦ (hρ₀ z hz).trans (le_max_left _ _)
    have hρ0 : 0 ≤ ρ := le_max_right _ _
    have hδ : 0 < ε ^ 2 * Real.exp (-(2 * Real.pi * ρ)) := by positivity
    obtain ⟨N, hN⟩ := hc (ENNReal.ofReal (ε ^ 2 * Real.exp (-(2 * Real.pi * ρ))))
      (by simpa using hδ)
    refine ⟨N, fun m hm n hn z hz ↦ ?_⟩
    have h1 := hN m hm n hn
    have h2 : (pwNormSq (fun z ↦ f m z - f n z)).toReal < ε ^ 2 * Real.exp (-(2 * Real.pi * ρ)) := by
      have := ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal hδ.le] at this
    have h3 : |z.im| ≤ ρ := (Complex.abs_im_le_norm z).trans (hρ z hz)
    have h4 : Real.exp (2 * Real.pi * |z.im|) ≤ Real.exp (2 * Real.pi * ρ) :=
      Real.exp_le_exp.2 (by gcongr)
    have h5 : ‖f m z - f n z‖ ^ 2 < ε ^ 2 := by
      calc ‖f m z - f n z‖ ^ 2 ≤ Real.exp (2 * Real.pi * |z.im|) *
            (pwNormSq (fun z ↦ f m z - f n z)).toReal := hcomp m n z
        _ ≤ Real.exp (2 * Real.pi * ρ) * (pwNormSq (fun z ↦ f m z - f n z)).toReal :=
            mul_le_mul_of_nonneg_right h4 ENNReal.toReal_nonneg
        _ < Real.exp (2 * Real.pi * ρ) * (ε ^ 2 * Real.exp (-(2 * Real.pi * ρ))) :=
            mul_lt_mul_of_pos_left h2 (Real.exp_pos _)
        _ = ε ^ 2 := by
            rw [mul_comm, mul_assoc, ← Real.exp_add]; simp
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h5
  -- Step 2: the limit
  have hcs : ∀ z : ℂ, ∃ x : ℂ, Tendsto (fun n ↦ f n z) atTop (nhds x) := fun z ↦
    cauchySeq_tendsto_of_complete ((hUC {z} isCompact_singleton).cauchySeq (Set.mem_singleton z))
  choose g hg using hcs
  have hTLU : TendstoLocallyUniformly f g atTop := by
    rw [← tendstoLocallyUniformlyOn_univ]
    refine (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).2 fun K _ hK ↦ ?_
    exact (hUC K hK).tendstoUniformlyOn_of_tendsto fun x _ ↦ hg x
  have hgd : Differentiable ℂ g := by
    have := (tendstoLocallyUniformlyOn_univ.2 hTLU).differentiableOn
      (Filter.Eventually.of_forall fun n ↦ (hf n).1.differentiableOn) isOpen_univ
    exact differentiableOn_univ.1 this
  -- Step 3: Fatou
  have hmain : ∀ ε : ℝ≥0∞, ε ≠ 0 → ε ≠ ⊤ → ∃ N : ℕ, ∀ n ≥ N,
      MemPW (fun z ↦ g z - f n z) ∧ pwNormSq (fun z ↦ g z - f n z) ≤ ε := by
    intro ε hε hεt
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have hF : ∀ k : ℕ, MemPW (fun z ↦ f (k + N) z - f n z) := fun k ↦ (hf (k + N)).sub (hf n)
    have hM : ∀ k : ℕ, pwNormSq (fun z ↦ f (k + N) z - f n z) ≤ ε := fun k ↦
      (hN (k + N) (Nat.le_add_left N k) n hn).le
    obtain ⟨hmem, hle⟩ := memPW_of_tendsto (l := atTop) (F := fun k z ↦ f (k + N) z - f n z)
      (f := fun z ↦ g z - f n z) hF (K := Real.sqrt ε.toReal)
      (fun k z ↦ norm_le_of_pwNormSq_le hPW (hF k) hεt (hM k) z)
      (hgd.sub (hf n).1)
      (fun z ↦ ((hg z).comp (tendsto_add_atTop_nat N)).sub_const _) hεt hM
    exact ⟨hmem, hle.trans (liminf_le_of_frequently_le' (Filter.Eventually.of_forall hM).frequently)⟩
  have hgmem : MemPW g := by
    obtain ⟨N, hN⟩ := hmain 1 one_ne_zero ENNReal.one_ne_top
    have := (hf N).add (hN N le_rfl).1
    convert this using 1
    ext z; simp
  refine ⟨g, hgmem, hTLU, ?_⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Filter.Eventually.of_forall fun n ↦ by rw [hεt]; exact le_top
  · obtain ⟨N, hN⟩ := hmain ε hε.ne' hεt
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have := (hN n hn).2
    unfold pwNormSq at this ⊢
    simpa [enorm_sub_rev] using this

/-- **Normal families.** A norm-bounded sequence in `PW` has a subsequence converging locally
uniformly to some `g ∈ PW`, and `‖g‖² ≤ liminf ‖f_n‖²` (even `≤ lim ‖f_{φ n}‖²` along the
subsequence, which may be chosen to realise the `liminf`). -/
theorem pw_normal_family (hPW : PaleyWienerThm) {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemPW (f n))
    {M : ℝ} (hM : ∀ n, pwNormSq (f n) ≤ ENNReal.ofReal M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, MemPW g ∧
      TendstoLocallyUniformly (fun n ↦ f (φ n)) g atTop ∧
      pwNormSq g ≤ liminf (fun n ↦ pwNormSq (f n)) atTop := by
  set ℓ : ℝ≥0∞ := liminf (fun n ↦ pwNormSq (f n)) atTop with hℓ
  have hℓM : ℓ ≤ ENNReal.ofReal M :=
    liminf_le_of_frequently_le' (Filter.Eventually.of_forall hM).frequently
  have hℓt : ℓ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hℓM
  -- a subsequence realising the liminf
  have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop, pwNormSq (f n) < ℓ + ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    intro k
    refine Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) ?_
    exact ENNReal.lt_add_right hℓt (by simp; positivity)
  obtain ⟨ψ, hψ, hψk⟩ := Filter.extraction_forall_of_frequently hfreq
  -- Montel for the subsequence
  have hbd : ∀ n z, ‖f (ψ n) z‖ ≤ Real.sqrt (ENNReal.ofReal M).toReal * Real.exp (Real.pi * |z.im|) :=
    fun n z ↦ norm_le_of_pwNormSq_le hPW (hf (ψ n)) ENNReal.ofReal_ne_top (hM (ψ n)) z
  have hc : Continuous fun z : ℂ ↦ Real.sqrt (ENNReal.ofReal M).toReal * Real.exp (Real.pi * |z.im|) := by
    fun_prop
  obtain ⟨𝒰, h𝒰⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  obtain ⟨H, hHd, -, hT⟩ := OCS.exists_tendstoLocallyUniformlyOn_of_ultrafilter 𝒰 isOpen_univ
    (F := fun n ↦ f (ψ n)) (fun n ↦ (hf (ψ n)).1.differentiableOn) hc.continuousOn
    (fun n z _ ↦ hbd n z)
  have hHd' : Differentiable ℂ H := differentiableOn_univ.1 hHd
  let u : ℕ → C(ℂ, ℂ) := fun n ↦ ⟨f (ψ n), (hf (ψ n)).1.continuous⟩
  let H' : C(ℂ, ℂ) := ⟨H, hHd'.continuous⟩
  have hu : Tendsto u (𝒰 : Filter ℕ) (nhds H') :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.2 (tendstoLocallyUniformlyOn_univ.1 hT)
  have hcl : MapClusterPt H' atTop u := (ClusterPt.of_le_nhds hu).mono (map_mono h𝒰)
  obtain ⟨φ, hφ, hφt⟩ := hcl.tendsto_subseq
  have hTLU : TendstoLocallyUniformly (fun n ↦ f (ψ (φ n))) H atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 hφt
  have hlim : ∀ z, Tendsto (fun n ↦ f (ψ (φ n)) z) atTop (nhds (H z)) := fun z ↦
    (tendstoLocallyUniformlyOn_univ.2 hTLU).tendsto_at (Set.mem_univ z)
  obtain ⟨hHmem, hHle⟩ := memPW_of_tendsto (l := atTop) (F := fun n ↦ f (ψ (φ n))) (f := H)
    (fun n ↦ hf _) (K := Real.sqrt (ENNReal.ofReal M).toReal) (fun n z ↦ hbd (φ n) z) hHd' hlim
    ENNReal.ofReal_ne_top (fun n ↦ hM _)
  refine ⟨fun n ↦ ψ (φ n), hψ.comp hφ, H, hHmem, hTLU, hHle.trans ?_⟩
  -- the liminf along the subsequence is at most `ℓ`
  have hv : Tendsto (fun k : ℕ ↦ ℓ + ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (nhds ℓ) := by
    have h1 : Tendsto (fun k : ℕ ↦ ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (nhds 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    simpa using (tendsto_const_nhds (x := ℓ)).add h1
  rw [← hv.liminf_eq]
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun k ↦ ?_)
  refine (hψk (φ k)).le.trans ?_
  gcongr
  have : k ≤ φ k := hφ.id_le k
  have : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast this
  linarith

end FF
