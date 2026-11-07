# P5: elementary BMO algebra, limits, and logarithmic A₂ weights

This module is groundwork for Pavlov's theorem. It proves elementary facts about
the existing definitions `FF.intervalMean`, `FF.meanOsc`, and `FF.MemBMO`; it
neither assumes nor proves a Hilbert-transform or interpolation theorem.
The proposed implementation is `FourierFrames/Cited/Pavlov/BMO.lean`.
The interfaces below are implemented in that file. Proof placeholders occur
only in this Markdown listing. `FourierFrames/Defs.lean` remains unchanged.

## Definitions and dependency boundary

The project uses Lebesgue measure on `ℝ`, oriented interval integrals, and

```lean
intervalMean h a b = (b - a)⁻¹ * ∫ t in a..b, h t
meanOsc h a b = (b - a)⁻¹ * ∫ t in a..b, |h t - intervalMean h a b|
MemBMO h = LocallyIntegrable h ∧
  ∃ M : ℝ, ∀ a b : ℝ, a < b → meanOsc h a b ≤ M
```

All quantitative estimates below assume `a < b`. Thus interval integrals can be
rewritten as integrals over `Ioc a b`, and multiplication by `(b-a)⁻¹` preserves
inequalities. Local integrability is always established before using any
linearity, monotonicity, or limit identity for a real-valued Bochner integral.

The file imports the elementary Fatou helper, whose sole import is `Defs`:

```lean
import FourierFrames.Cited.Pavlov.Fatou

open MeasureTheory Set Filter Topology
noncomputable section
namespace FF.Pavlov
```

Mathlib supplies local integrability algebra, compact-interval integrability,
real logarithm inequalities, Fatou's lemma, and dominated convergence. The
existing `FourierFrames/Cited/JohnNirenberg.lean` contains the closely related
helper `FF.abs_intervalMean_sub_le`; its argument can be adapted here without
importing John–Nirenberg's stopping-time implementation. `FourierFrames/Landau`
consumes `MemBMO` and John–Nirenberg but is not a dependency of this file.
In particular the dependency graph cannot become circular through Pavlov.

## 1. Interval estimates and arbitrary comparison constants

The central estimate compares oscillation around the actual mean with
oscillation around any real constant. Write `L=b-a>0`. Linearity gives

```
h_I - c = L⁻¹ integral_I (h-c),
|h_I-c| ≤ L⁻¹ integral_I |h-c|.
```

The triangle inequality then gives `meanOsc h a b ≤ 2 L⁻¹ integral_I |h-c|`.
This is the bridge used both for logarithms and for Fatou limits with moving
comparison constants. The factor two is intentional.

```lean
theorem intervalMean_sub_const_eq {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) (c : ℝ) :
    intervalMean h a b - c =
      (b - a)⁻¹ * ∫ t in a..b, (h t - c) := by sorry

theorem abs_intervalMean_sub_const_le {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) (c : ℝ) :
    |intervalMean h a b - c| ≤
      (b - a)⁻¹ * ∫ t in a..b, |h t - c| := by sorry

theorem meanOsc_le_twice_comparison {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) (c : ℝ) :
    meanOsc h a b ≤ 2 * ((b - a)⁻¹ * ∫ t in a..b, |h t - c|) := by sorry

theorem meanOsc_nonneg {h : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    0 ≤ meanOsc h a b := by sorry

theorem memBMO_of_comparison {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {M : ℝ} (hM : ∀ a b : ℝ, a < b →
      ∃ c : ℝ, (b - a)⁻¹ * ∫ t in a..b, |h t - c| ≤ M) :
    MemBMO h := by sorry
```

`meanOsc_nonneg` needs no integrability hypothesis: the integrand is nonnegative
and totalized Bochner integration still preserves that fact. The later upper
bounds do need integrability, and include it explicitly.

## 2. Algebra and bounded perturbations

For locally integrable functions, means are linear. Translation by a constant
cancels from the centered integrand; scalar multiplication multiplies the mean
oscillation by the absolute value of the scalar. The triangle inequality gives
subadditivity. These yield closure of `MemBMO` under constants, real scalar
multiplication, addition, subtraction, and negation.

```lean
theorem meanOsc_const (c : ℝ) {a b : ℝ} (hab : a < b) :
    meanOsc (fun _ : ℝ ↦ c) a b = 0 := by sorry

theorem meanOsc_add_const {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    (c : ℝ) {a b : ℝ} (hab : a < b) :
    meanOsc (fun t ↦ h t + c) a b = meanOsc h a b := by sorry

theorem meanOsc_const_mul (h : ℝ → ℝ) (c a b : ℝ) :
    meanOsc (fun t ↦ c * h t) a b = |c| * meanOsc h a b := by sorry

theorem meanOsc_add_le {f g : ℝ → ℝ}
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    {a b : ℝ} (hab : a < b) :
    meanOsc (fun t ↦ f t + g t) a b ≤ meanOsc f a b + meanOsc g a b := by sorry

theorem meanOsc_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g)
    (a b : ℝ) : meanOsc f a b = meanOsc g a b := by sorry

theorem memBMO_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) :
    MemBMO f ↔ MemBMO g := by sorry

theorem memBMO_const (c : ℝ) : MemBMO (fun _ : ℝ ↦ c) := by sorry

theorem memBMO_const_mul {h : ℝ → ℝ} (hh : MemBMO h) (c : ℝ) :
    MemBMO (fun t ↦ c * h t) := by sorry

theorem memBMO_add {f g : ℝ → ℝ} (hf : MemBMO f) (hg : MemBMO g) :
    MemBMO (fun t ↦ f t + g t) := by sorry

theorem memBMO_neg {h : ℝ → ℝ} (hh : MemBMO h) :
    MemBMO (fun t ↦ -h t) := by sorry

theorem memBMO_sub {f g : ℝ → ℝ} (hf : MemBMO f) (hg : MemBMO g) :
    MemBMO (fun t ↦ f t - g t) := by sorry

theorem meanOsc_le_of_ae_abs_le {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {K : ℝ} (hK : ∀ᵐ t : ℝ, |h t| ≤ K) {a b : ℝ} (hab : a < b) :
    meanOsc h a b ≤ 2 * K := by sorry

theorem memBMO_of_ae_abs_le {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {K : ℝ} (hK : ∀ᵐ t : ℝ, |h t| ≤ K) : MemBMO h := by sorry

theorem memBMO_add_ae_bounded {f g : ℝ → ℝ} (hf : MemBMO f)
    (hg : LocallyIntegrable g) {K : ℝ} (hK : ∀ᵐ t : ℝ, |g t| ≤ K) :
    MemBMO (fun t ↦ f t + g t) := by sorry
```

A pointwise bounded perturbation is obtained by `Eventually.of_forall`.
The local-integrability hypothesis on a bounded perturbation is explicit;
boundedness by itself does not imply measurability. No nonnegative-witness
assumption on a BMO bound is silently imposed: a witness can always be enlarged
to its maximum with zero when an implementation needs a nonnegative number.

## 3. Limits: local L¹ convergence, and Fatou with moving centers

A sequence of BMO functions needs a common quantitative oscillation bound;
separate membership of every term is insufficient. For strong local L¹
convergence, means converge with error at most `L⁻¹ integral_I |f_n-f|`.
Moreover

```
|meanOsc f_n a b - meanOsc f a b|
  ≤ 2 L⁻¹ integral_I |f_n-f|.
```

Consequently the original bound `M` survives unchanged. This is the preferred
interface when regularized phase functions converge locally uniformly, since
local uniform convergence on a finite interval implies the required L¹ limit.

```lean
theorem abs_meanOsc_sub_le {f g : ℝ → ℝ}
    (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    {a b : ℝ} (hab : a < b) :
    |meanOsc f a b - meanOsc g a b| ≤
      2 * ((b - a)⁻¹ * ∫ t in a..b, |f t - g t|) := by sorry

theorem meanOsc_le_of_tendsto_local_L1 {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M)
    (hlim : ∀ a b : ℝ, a < b →
      Tendsto (fun n ↦ ∫ t in a..b, |f n t - g t|) atTop (𝓝 0)) :
    ∀ a b : ℝ, a < b → meanOsc g a b ≤ M := by sorry

theorem memBMO_of_tendsto_local_L1 {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M)
    (hlim : ∀ a b : ℝ, a < b →
      Tendsto (fun n ↦ ∫ t in a..b, |f n t - g t|) atTop (𝓝 0)) :
    MemBMO g := by sorry
```

The following moving-center variants are also implemented. The stronger
center-free Fatou theorem below is the preferred final phase-limit adapter.

For a weaker a.e. limit, allow arbitrary comparison constants `c_n` on each
interval and require that they converge to some constant `c`. Then
`|f_n-c_n| → |g-c|` a.e. Apply Fatou to the nonnegative functions
`ENNReal.ofReal |f_n-c_n|` on the restricted measure. Their integral bound passes
to the limit, after which the arbitrary-comparison estimate gives `2M`.
This proof does not exchange a Bochner integral with a pointwise limit without
control. The following interface keeps local integrability of the limit explicit.

```lean
theorem meanOsc_le_of_ae_tendsto_comparison
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ a b : ℝ, a < b →
      ∃ (c : ℕ → ℝ) (c₀ : ℝ), Tendsto c atTop (𝓝 c₀) ∧
        ∀ n, (b - a)⁻¹ * ∫ t in a..b, |f n t - c n| ≤ M) :
    ∀ a b : ℝ, a < b → meanOsc g a b ≤ 2 * M := by sorry

theorem memBMO_of_ae_tendsto_comparison
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ a b : ℝ, a < b →
      ∃ (c : ℕ → ℝ) (c₀ : ℝ), Tendsto c atTop (𝓝 c₀) ∧
        ∀ n, (b - a)⁻¹ * ∫ t in a..b, |f n t - c n| ≤ M) :
    MemBMO g := by sorry
```

A.e. dominated convergence supplies the stronger local L¹ hypothesis whenever
every bounded interval has a common integrable majorant for `|f_n|` and the
limit is measurable. This can be an adapter at the eventual phase application;
there is no need to impose a global majorant on all of `ℝ`.

### Center-free a.e. convergence by a pairwise integral

The final phase-limit adapter needs neither convergence of interval means nor
local L¹ convergence. Define the unnormalized pairwise integral on `I=(a,b]`:

```lean
def intervalPairIntegral (h : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, |h p.1-h p.2|
    ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))

theorem integrable_intervalPair {h : ℝ → ℝ} (hh : LocallyIntegrable h) (a b : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ |h p.1-h p.2|)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by sorry

theorem meanOsc_le_pairIntegral {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) :
    meanOsc h a b ≤ (b-a)⁻¹ ^ 2 * intervalPairIntegral h a b := by sorry

theorem pairIntegral_le_twice_meanOsc {h : ℝ → ℝ} (hh : LocallyIntegrable h)
    {a b : ℝ} (hab : a < b) :
    intervalPairIntegral h a b ≤ 2 * (b-a)^2 * meanOsc h a b := by sorry
```

For the lower bound, fix `x` and apply the arbitrary-center inequality for the
mean with comparison constant `h x`:

```
|h x - h_I| ≤ L⁻¹ integral_I |h x-h y| dy.
```

Integrate in `x`, multiply by `L⁻¹`, and use Fubini. For the upper bound use
`|h x-h y| ≤ |h x-h_I|+|h y-h_I|`, integrate on the product, and use its finite
marginal masses. Product integrability follows by subtracting the two lifted
integrable functions and taking their absolute value.

A.e. convergence lifts to both coordinates of the product measure. Fatou
therefore bounds the pairwise integral of the limit by `2 L² M`. The lower
sandwich inequality finishes the proof with bound `2M`:

```lean
theorem meanOsc_le_of_ae_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M) :
    ∀ a b : ℝ, a < b → meanOsc g a b ≤ 2*M := by sorry

theorem memBMO_of_ae_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ᵐ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M) :
    MemBMO g := by sorry
```

The pointwise specialization is exported as:

```lean
theorem memBMO_of_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, LocallyIntegrable (f n)) (hg : LocallyIntegrable g)
    (hlim : ∀ t : ℝ, Tendsto (fun n ↦ f n t) atTop (𝓝 (g t)))
    {M : ℝ} (hM : ∀ n a b, a < b → meanOsc (f n) a b ≤ M) :
    MemBMO g := by sorry
```

A pointwise limit is an immediate specialization using `Eventually.of_forall`.
The generic real-valued Fatou helper is implemented in `Pavlov/Fatou.lean`, which
imports only `Defs`. Its public theorem is
`FF.Pavlov.integral_le_of_ae_tendsto_nonneg`: integrable nonnegative sequences
with a.e. convergence and a common integral upper bound pass that bound to an
integrable limit. No assumption on the sign of the proposed upper bound is
needed; it follows from the hypotheses.

The generic helper has this exact interface, in the same namespace:

```lean
theorem integral_le_of_ae_tendsto_nonneg {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ} {K : ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hfn : ∀ n, 0 ≤ᵐ[μ] f n) (hgn : 0 ≤ᵐ[μ] g)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    (hbound : ∀ n, ∫ x, f n x ∂μ ≤ K) :
    ∫ x, g x ∂μ ≤ K := by sorry
```

## 4. An elementary A₂ weight has logarithm in BMO

Assume `w>0` a.e., `w` and `w⁻¹` are locally integrable, and for every interval
`I=(a,b]`,

```
(average_I w) * (average_I w⁻¹) ≤ C.
```

No weighted Hilbert-transform theorem is needed for this implication. A useful
nonsharp bound is `meanOsc (log w) a b ≤ 2(1+C)`.

First, for every `s>0`, the elementary logarithm inequalities imply
`|log s| ≤ s+s⁻¹`. Since `w+w⁻¹` is integrable on every compact interval,
measurability of `log w` and domination prove that `log w` is locally integrable.
Null exceptional sets may be ignored; no pointwise positivity assumption is
needed. Mathlib's total definitions of inverse and logarithm at zero do not
supply integrability and are not used to bypass this argument.

Fix a nonempty interval and write `A=average_I w`. Positivity a.e. and positive
interval measure imply `A>0`. Take the comparison constant `c=log A`. For a.e.
`t∈I`, logarithm division gives

```
|log(w(t))-log A| = |log(w(t)/A)|
  ≤ w(t)/A + A/w(t).
```

The normalized integral of the first summand is exactly one. The normalized
integral of the second is `A * average_I w⁻¹ ≤ C`. Thus the comparison average
is at most `1+C`; §1 changes the comparison center to the true mean, giving the
claimed `2(1+C)` bound. Neither Jensen's inequality nor a lower bound on `A`
uniform in the interval is necessary.

```lean
theorem abs_log_le_add_inv {s : ℝ} (hs : 0 < s) :
    |Real.log s| ≤ s + s⁻¹ := by sorry

theorem locallyIntegrable_log_of_pos_inv {w : ℝ → ℝ}
    (hw : LocallyIntegrable w)
    (hwi : LocallyIntegrable (fun t ↦ (w t)⁻¹))
    (hpos : ∀ᵐ t : ℝ, 0 < w t) :
    LocallyIntegrable (fun t ↦ Real.log (w t)) := by sorry

theorem intervalMean_pos_of_ae_pos {w : ℝ → ℝ}
    (hw : LocallyIntegrable w) (hpos : ∀ᵐ t : ℝ, 0 < w t)
    {a b : ℝ} (hab : a < b) : 0 < intervalMean w a b := by sorry

theorem log_comparison_le_of_A2 {w : ℝ → ℝ}
    (hw : LocallyIntegrable w)
    (hwi : LocallyIntegrable (fun t ↦ (w t)⁻¹))
    (hpos : ∀ᵐ t : ℝ, 0 < w t)
    {C a b : ℝ} (hab : a < b)
    (hA2 : intervalMean w a b * intervalMean (fun t ↦ (w t)⁻¹) a b ≤ C) :
    (b - a)⁻¹ * ∫ t in a..b,
      |Real.log (w t) - Real.log (intervalMean w a b)| ≤ 1 + C := by sorry

theorem meanOsc_log_le_of_A2 {w : ℝ → ℝ}
    (hw : LocallyIntegrable w)
    (hwi : LocallyIntegrable (fun t ↦ (w t)⁻¹))
    (hpos : ∀ᵐ t : ℝ, 0 < w t)
    {C a b : ℝ} (hab : a < b)
    (hA2 : intervalMean w a b * intervalMean (fun t ↦ (w t)⁻¹) a b ≤ C) :
    meanOsc (fun t ↦ Real.log (w t)) a b ≤ 2 * (1 + C) := by sorry

theorem memBMO_log_of_A2 {w : ℝ → ℝ}
    (hw : LocallyIntegrable w)
    (hwi : LocallyIntegrable (fun t ↦ (w t)⁻¹))
    (hpos : ∀ᵐ t : ℝ, 0 < w t)
    {C : ℝ} (hA2 : ∀ a b : ℝ, a < b →
      intervalMean w a b * intervalMean (fun t ↦ (w t)⁻¹) a b ≤ C) :
    MemBMO (fun t ↦ Real.log (w t)) := by sorry

end FF.Pavlov
```

The local A₂ implication is stated separately so the interval product estimate
can be used directly without introducing another global weight predicate into
`Defs`. The global theorem selects the uniform witness `2*(1+C)`.

## 5. Implementation and verification order

1. Prove interval mean algebra and the arbitrary-comparison estimate.
2. Prove BMO algebra, a.e. invariance, and bounded perturbation lemmas.
3. Prove the quantitative L¹ continuity estimate and its limit corollary.
4. Prove the Fatou comparison lemma using nonnegative extended integrals.
5. Prove logarithm local integrability, positivity of the interval mean, the
   local A₂ comparison estimate, and the global logarithm theorem.
6. Build `FourierFrames.Cited.Pavlov.BMO` with every linter warning corrected.
   Check theorem axioms and retain no `sorry`, new axioms, warning suppression,
   or assumption of `PavlovBMO` in the Lean module.

These results finish only the elementary BMO portion. A separate argument must
produce the A₂ weight from interpolation and connect its harmonic-conjugate
phase to the counting discrepancy. The implication `log w ∈ BMO` alone does
not establish Pavlov's theorem, and this module makes no such claim.

## Completed validation

On 2026-11-07, `lake build FourierFrames.Cited.Pavlov.BMO` completed successfully
without warnings, including `Pavlov.Fatou`. All original interfaces and the
center-free limit strengthening are implemented. `meanOsc_const_mul` has the
stronger unconditional signature shown above: local integrability and endpoint
ordering are unnecessary for the scalar identity.

Axiom checks for `memBMO_log_of_A2`, `memBMO_of_ae_tendsto`,
`memBMO_of_tendsto_local_L1`, `memBMO_add_ae_bounded`, and
`memBMO_of_ae_tendsto_comparison` list only `propext`, `Classical.choice`, and
`Quot.sound`. Neither Lean module contains placeholders, new axioms, or warning
suppressions. The independent blueprint review is recorded in
[reviews/R13_Pavlov_Blueprint.md](../reviews/R13_Pavlov_Blueprint.md).
