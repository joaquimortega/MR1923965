import FourierFrames.Defs
import FourierFrames.Lemma3Uniform
import FourierFrames.Theorem2ii.Window

/-!
# M09 — Theorem 2 (ii)

See `blueprint/M09_Theorem2ii.md`.  The printed proof (pp. 804–805) is broken (see the section
"Issues in the source" of the blueprint); the proof below is a reconstruction.

Idea.  `Λ(ψ) ∩ (-∞, 0] = ℤ_{≤ 0}`.  If `x ψ'(x) → 0`, then for every `η > 0` and `s > 0` there is
a window `[x₀, x₀ e^s]` far out on which `ψ` stays within `η` of a half integer `n + 1/2`, i.e.
`Λ(ψ)` is within `η` of `ℤ + 1/2` there.  Take the [OS99] Lemma 3 function `F` of the density
`m = 1 + μ`, `μ` = two negative ramps of mass `-1/2` each, on `[a₁, 2a₁]` and `[a₂, 2a₂]`, where
`x₀ ≈ 2 a₁`, `x₀ e^s ≈ a₂`.  Its zeros are `ℤ` on the left, `ℤ + 1/2` between the ramps, and
`ℤ` again after the second ramp, and `|f|² ≃ min(1, a₁/|x|) min(1, a₂/|x|) dist(x, zeros)²`.
Hence `‖f‖² ≳ a₁ log(a₂/a₁)` while `∑_{Λ(ψ)} |f|² ≲ a₁ (1 + η² log(a₂/a₁))`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-! ## The test density and the test function -/

/-- The perturbation `μ = m - 1`: two uniform negative ramps, each of total mass `-1/2`,
on `[a₁, 2a₁]` and `[a₂, 2a₂]`. -/
def rampMu (a₁ a₂ : ℝ) (t : ℝ) : ℝ :=
  -((1 / 2) / a₁) * (Icc a₁ (2 * a₁)).indicator 1 t -
    ((1 / 2) / a₂) * (Icc a₂ (2 * a₂)).indicator 1 t

/-- The density `m = 1 + μ` fed to [OS99] Lemma 3. -/
def dens (a₁ a₂ : ℝ) (t : ℝ) : ℝ :=
  1 + rampMu a₁ a₂ t

/-- The envelope `min(1, a₁/|x|) · min(1, a₂/|x|)`, written without division by `0`. -/
def env (a₁ a₂ x : ℝ) : ℝ :=
  a₁ / max a₁ |x| * (a₂ / max a₂ |x|)

/-- The real potential `W(z) = ∫ μ(t) log|1 - z/t| dt`. -/
def potW (a₁ a₂ : ℝ) (z : ℂ) : ℝ :=
  ∫ t : ℝ, rampMu a₁ a₂ t * Real.log ‖1 - z / t‖

/-- The linear coefficient `κ = ∫ μ(t)/t dt` (`μ` is supported in `[a₁, ∞) ⊂ [1, ∞)`). -/
def kappaMu (a₁ a₂ : ℝ) : ℝ :=
  ∫ t : ℝ, rampMu a₁ a₂ t / t

/-- `G(z) = F(z) e^{-κ z}`, `F = multF (dens a₁ a₂) 0`: the function whose modulus on `ℝ` is
`≃ e^{W} dist(·, Γ)`. -/
def gFun (a₁ a₂ : ℝ) (z : ℂ) : ℂ :=
  OCS.multF (dens a₁ a₂) 0 z * Complex.exp (-(kappaMu a₁ a₂ : ℂ) * z)

/-- The test function `f(z) = G(z + 1/2)`: zeros `ℤ` on the left, `ℤ + 1/2` between the ramps. -/
def testFn (a₁ a₂ : ℝ) (z : ℂ) : ℂ :=
  gFun a₁ a₂ (z + 1 / 2)

/-! ## Part A: the density, and the potential `U` -/

/-- `m = 1 + μ` is a multiplier weight with `a = 1/2`, `b = 1`
(needs `1 ≤ a₁` and disjoint ramps `2 a₁ < a₂`). -/
theorem dens_isMultWeight {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    OCS.IsMultWeight (dens a₁ a₂) (1 / 2) 1 := by
  sorry

/-- `U_1(x) = 0` for real `x`: `∫ [log|1 - x/t| + (1 - χ_{[-1,1]}(t)) x/t] dt = 0`. -/
theorem multUIntegrand_one_real (x : ℝ) :
    ∫ t : ℝ, OCS.multUIntegrand (fun _ ↦ (1 : ℝ)) (x : ℂ) t = 0 := by
  sorry

/-- `U_1(z) = π |Im z|`. -/
theorem multUIntegrand_one (z : ℂ) :
    ∫ t : ℝ, OCS.multUIntegrand (fun _ ↦ (1 : ℝ)) z t = Real.pi * |z.im| := by
  sorry

/-- `U_m(z) = π|Im z| + W(z) + κ Re z` for `m = dens a₁ a₂`. -/
theorem multU_dens {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (z : ℂ) :
    OCS.multU (dens a₁ a₂) 0 z = Real.pi * |z.im| + potW a₁ a₂ z + kappaMu a₁ a₂ * z.re := by
  sorry

/-- **Ramp potential.**  For `a ≥ 1` and real `x`,
`|(1/a) ∫_a^{2a} log|1 - x/t| dt - log max(1, |x|/a)| ≤ 4`. -/
theorem rampPot_estimate {a : ℝ} (ha : 1 ≤ a) (x : ℝ) :
    |(1 / a) * ∫ t in a..2 * a, Real.log ‖1 - (x : ℂ) / t‖ - Real.log (max 1 (|x| / a))| ≤ 4 := by
  sorry

/-- **Envelope.**  `|W(x) - (1/2) log env(x)| ≤ 4` for real `x` (needs `1 ≤ a₁`, `2 a₁ < a₂`). -/
theorem potW_estimate {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (x : ℝ) :
    |potW a₁ a₂ (x : ℂ) - Real.log (env a₁ a₂ x) / 2| ≤ 4 := by
  sorry

/-- A one-sided bound on `W` for complex `z`, enough for exponential type: since `μ ≤ 0`,
`W(z) = ∫ |μ| (log t - log|t - z|) ≤ log(2 a₂) + 1` for every `z`. -/
theorem potW_le_complex {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) (z : ℂ) :
    potW a₁ a₂ z ≤ Real.log (2 * a₂) + 1 := by
  sorry

/-! ## Part B: the zeros of `F` -/

/-- `∫_0^x m = x - 1/2` for `2 a₁ ≤ x ≤ a₂`. -/
theorem multPrim_dens_stretch {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) {x : ℝ}
    (hx : x ∈ Icc (2 * a₁) a₂) : OCS.multPrim (dens a₁ a₂) x = x - 1 / 2 := by
  sorry

/-- Left zeros: for `1 ≤ a₁`, `j ≤ 0`, the barycentre `γ_j = j + 1/2` (the interval `I_j = [j, j+1]`
lies in `{m = 1}`), so `testFn` vanishes at every integer `j ≤ 0`. -/
theorem testFn_eq_zero_of_nonpos {a₁ a₂ : ℝ} (h₁ : 2 ≤ a₁) (h₂ : 2 * a₁ < a₂) (j : ℤ)
    (hj : j ≤ 0) : testFn a₁ a₂ (j : ℂ) = 0 := by
  sorry

/-- Stretch zeros: `Γ ∩ [2a₁ + 1, a₂ - 1] = ℤ + 1` (the zeros of `G`), so for the argument `x` of
the test function, `x ∈ [2a₁ + 3, a₂ - 3]`, `dist(x + 1/2, Γ) = dist(x, ℤ + 1/2)`. -/
theorem infDist_dens_stretch {a₁ a₂ : ℝ} (h₁ : 2 ≤ a₁) (h₂ : 2 * a₁ < a₂) {x : ℝ}
    (hx : x ∈ Icc (2 * a₁ + 3) (a₂ - 3)) :
    infDist (((x + 1 / 2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂)) =
      |x - 1 / 2 - round (x - 1 / 2)| := by
  sorry

/-- For every weight and real `y`, `dist(y, Γ) ≤ 1/a`. -/
theorem infDist_multGammaC_le {m : ℝ → ℝ} {a b : ℝ} (hw : OCS.IsMultWeight m a b) (y : ℝ) :
    infDist (y : ℂ) (OCS.multGammaC m) ≤ 1 / a := by
  sorry

/-! ## Part C: `testFn ∈ PW` and its size on `ℝ` -/

/-- **Two-sided estimate on `ℝ`** with absolute constants `0 < c ≤ C`:
`c √env(x + 1/2) · dist(x + 1/2, Γ) ≤ |f(x)| ≤ C √env(x + 1/2) · dist(x + 1/2, Γ)`
(uniform in `a₁, a₂` with `1 ≤ a₁`, `2 a₁ < a₂`). -/
theorem testFn_norm_real :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a₁ a₂ : ℝ, 1 ≤ a₁ → 2 * a₁ < a₂ → ∀ x : ℝ,
      c * Real.sqrt (env a₁ a₂ (x + 1 / 2)) *
          infDist (((x + 1 / 2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂)) ≤ ‖testFn a₁ a₂ x‖ ∧
      ‖testFn a₁ a₂ x‖ ≤ C * Real.sqrt (env a₁ a₂ (x + 1 / 2)) *
          infDist (((x + 1 / 2 : ℝ)) : ℂ) (OCS.multGammaC (dens a₁ a₂)) := by
  sorry

/-- `testFn` is entire. -/
theorem differentiable_testFn {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    Differentiable ℂ (testFn a₁ a₂) := by
  sorry

/-- `testFn` has exponential type `≤ π`: `|f(z)| ≤ C e^{π |Im z|}`. -/
theorem isExpTypeLE_testFn {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    IsExpTypeLE Real.pi (testFn a₁ a₂) := by
  sorry

/-- `∫ env < ∞` and `testFn ∈ L²(ℝ)`. -/
theorem memLp_testFn {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    MemLp (fun x : ℝ ↦ testFn a₁ a₂ x) 2 := by
  sorry

theorem memPW_testFn {a₁ a₂ : ℝ} (h₁ : 1 ≤ a₁) (h₂ : 2 * a₁ < a₂) :
    MemPW (testFn a₁ a₂) :=
  ⟨differentiable_testFn h₁ h₂, isExpTypeLE_testFn h₁ h₂, memLp_testFn h₁ h₂⟩

/-! ## Part D: norm lower bound and sampling upper bound -/

/-- **Mass.**  `‖f‖² ≥ c a₁ log(a₂/(4 a₁))` for an absolute `c > 0`. -/
theorem pwNormSq_testFn_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ a₁ a₂ : ℝ, 8 ≤ a₁ → 16 * a₁ ≤ a₂ →
      ENNReal.ofReal (c * a₁ * Real.log (a₂ / (4 * a₁))) ≤ pwNormSq (testFn a₁ a₂) := by
  sorry

/-- **Sampling sum.**  For admissible `ψ` vanishing on `(-∞, 0]`, there is `C` (depending on
`sup |ψ'|` only) such that, if `Λ(ψ)` is `η`-close to `ℤ + 1/2` on `[2a₁ + 3, a₂ - 3]`, then
`∑_{λ ∈ Λ(ψ)} |f(λ)|² ≤ C a₁ (1 + η² log(a₂/a₁))`. -/
theorem sampleSum_testFn_le {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ a₁ a₂ η : ℝ, 8 ≤ a₁ → 16 * a₁ ≤ a₂ → 0 ≤ η →
      (∀ l ∈ LambdaPsi ψ, l ∈ Icc (2 * a₁ + 3) (a₂ - 3) → ∃ k : ℤ, |l - (k + 1 / 2)| ≤ η) →
      sampleSum (LambdaPsi ψ) (testFn a₁ a₂) ≤
        ENNReal.ofReal (C * a₁ * (1 + η ^ 2 * Real.log (a₂ / a₁))) := by
  sorry

/-! ## Part E: the choice of the window -/

/-- **The window** (this is where `x ψ'(x) → 0` is used): for every `η > 0`, `s > 0`, `A₀`, there
are `a₁ ≥ A₀`, `a₂` with `16 a₁ ≤ a₂`, `log(a₂/(4a₁)) ≥ s`, such that `Λ(ψ)` is `η`-close to
`ℤ + 1/2` on `[2a₁ + 3, a₂ - 3]`. -/
theorem exists_window {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ) (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hsmall : Tendsto (fun x ↦ x * deriv ψ x) atTop (𝓝 0)) {η s : ℝ} (hη : 0 < η) (hs : 0 < s)
    (A₀ : ℝ) :
    ∃ a₁ a₂ : ℝ, A₀ ≤ a₁ ∧ 8 ≤ a₁ ∧ 16 * a₁ ≤ a₂ ∧ s ≤ Real.log (a₂ / (4 * a₁)) ∧
      ∀ l ∈ LambdaPsi ψ, l ∈ Icc (2 * a₁ + 3) (a₂ - 3) → ∃ k : ℤ, |l - (k + 1 / 2)| ≤ η :=
  T2ii.exists_window hψ h0 hsmall hη hs A₀

/-! ## Main theorem -/

/-- **Theorem 2 (ii)** (p. 801): if `ψ = 0` on `(-∞, 0]` and `ψ'(x) = o(1/x)`, then `Λ(ψ)` is not
sampling for `PW`. -/
theorem theorem2_ii (hPW : PaleyWienerThm) {ψ : ℝ → ℝ} (hψ : IsAdmissiblePsi ψ)
    (h0 : ∀ x : ℝ, x ≤ 0 → ψ x = 0)
    (hsmall : Tendsto (fun x ↦ x * deriv ψ x) atTop (𝓝 0)) :
    ¬ IsSampling (LambdaPsi ψ) := by
  sorry

end FF
