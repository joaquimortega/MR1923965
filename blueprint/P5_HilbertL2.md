# P5 groundwork: the regularized conjugate Poisson operator on L²

The implementation plan below was independently reviewed in R13 and approved by the
coordinator. `FourierFrames/Cited/Pavlov/ConjugatePoisson.lean` now proves the operator and
kernel-realization statements; it does not assert a principal-value Hilbert-transform theorem. The scope
is `y > 0`; no principal-value limit or boundary convergence is required here.

## 1. Definitions and normalizations

Use Mathlib's convention `𝓕 f ξ = ∫ t, exp (-2π i t ξ) f t`. Define

```
Q_y(t) = t / (π (t² + y²)),
m_y(ξ) = -i sign(ξ) exp(-2π y |ξ|),
T_y = 𝓕₂⁻¹ M_{m_y} 𝓕₂.
```

All operators initially act on complex `L²(ℝ, volume)`. Real inputs and real outputs are
obtained from the kernel formula; a separate real-space operator is unnecessary for the
first construction. In particular the kernel is `Q_y(x-t)`, with this sign. The multiplier
at zero is set to zero. Changing that single value would leave the `L²` operator unchanged.

The implementation can use `Real.sign`, or a piecewise definition `-i exp(-2πyξ)` on `ξ>0`,
`i exp(2πyξ)` on `ξ<0`, and zero at zero. The piecewise version makes the two half-line
integrals and measurability immediate.

Proposed module: `FourierFrames/Cited/Pavlov/ConjugatePoisson.lean`, namespace `FF.Pavlov`.
The following is a declaration scaffold for review, not an unproved Lean source file:

```lean
abbrev C2 := Lp ℂ 2 (volume : Measure ℝ)

def conjugatePoissonKernel (y t : ℝ) : ℝ :=
  t / (Real.pi * (t ^ 2 + y ^ 2))

def conjugatePoissonSymbol (y ξ : ℝ) : ℂ :=
  -Complex.I * (Real.sign ξ : ℂ) *
    (Real.exp (-(2 * Real.pi * y * |ξ|)) : ℂ)

-- These lemmas precede the definition using toLp.
lemma conjugatePoissonSymbol_measurable (y : ℝ) :
  Measurable (conjugatePoissonSymbol y)
lemma conjugatePoissonSymbol_norm_le {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
  ‖conjugatePoissonSymbol y ξ‖ ≤ 1
lemma conjugatePoissonSymbol_integrable {y : ℝ} (hy : 0 < y) :
  Integrable (conjugatePoissonSymbol y)
lemma conjugatePoissonSymbol_memLp_two {y : ℝ} (hy : 0 < y) :
  MemLp (conjugatePoissonSymbol y) 2 volume
lemma conjugatePoissonSymbol_memLp_top {y : ℝ} (hy : 0 < y) :
  MemLp (conjugatePoissonSymbol y) ∞ volume

def conjugatePoissonOperator (y : ℝ) (hy : 0 < y) : C2 →L[ℂ] C2 :=
  MeasureTheory.Lp.fourierMultiplierCLM ℂ
    ((conjugatePoissonSymbol_memLp_top hy).toLp (conjugatePoissonSymbol y))

lemma norm_conjugatePoissonOperator_le {y : ℝ} (hy : 0 < y) :
  ‖conjugatePoissonOperator y hy‖ ≤ 1

lemma fourierInv_conjugatePoissonSymbol {y : ℝ} (hy : 0 < y) (x : ℝ) :
  𝓕⁻ (conjugatePoissonSymbol y) x = (conjugatePoissonKernel y x : ℂ)

lemma conjugatePoissonKernel_memLp_two {y : ℝ} (hy : 0 < y) :
  MemLp (fun t ↦ (conjugatePoissonKernel y t : ℂ)) 2 volume

lemma conjugatePoissonKernel_mul_integrable {y : ℝ} (hy : 0 < y)
    (f : C2) (x : ℝ) :
  Integrable (fun t ↦ (conjugatePoissonKernel y (x-t) : ℂ) * f t)

lemma conjugatePoissonOperator_eq_integral {y : ℝ} (hy : 0 < y) (f : C2) :
  (conjugatePoissonOperator y hy f : ℝ → ℂ) =ᵐ[volume]
    fun x ↦ ∫ t, (conjugatePoissonKernel y (x-t) : ℂ) * f t
```

The all-`L²` realization is useful because it directly implies the off-support hypothesis
of the TauCeti endpoint theorem. Compactly supported `L²` inputs are included, and their
first proof requires no density extension. Complex-to-real restriction should be postponed
until a downstream theorem needs the real continuous linear map.

## 2. Existing proved infrastructure

The six unchanged TauCeti modules used for the multiplier and BMO endpoint are vendored
in `TauCeti/` from the exact release `v4.35.0`,
commit `1f9b4414105d86e487a4ac4c3d3397076a44d0d2` (Apache-2.0). They compile against this
project's Mathlib pin. The vendor also includes selected harmonic modules for separate
P5 work; see `TauCeti/VENDORED.md` for provenance and the axiom audit.

- `MeasureTheory.Lp.fourierMultiplierCLM`,
  `fourierMultiplierCLM_apply`, `fourier_fourierMultiplierCLM`, and
  `norm_fourierMultiplierCLM_le` in `TauCeti/Analysis/Fourier/L2Multiplier.lean` construct
  `T_y` and its `L²` contraction immediately from the bounded symbol.
- `FF.PW1.F2_toLp_ae_eq` and `F2_symm_toLp_ae_eq` in
  `FourierFrames/Cited/PaleyWiener/L2Fourier.lean` already identify the `L²` Fourier and
  inverse Fourier operators with their integral versions on `L¹ ∩ L²`. These are essential;
  an integral equality must not be assumed from Plancherel alone.
- A local two-sided exponential integrability lemma, proved from Mathlib's half-line
  exponential integrability, controls the symbol. Its square is controlled by the same
  exponential with parameter `4πy`, proving `MemLp 2` by
  `memLp_two_iff_integrable_sq_norm`. `MemLp.of_bound` proves the `L∞` bound.
- `integrableOn_exp_mul_complex_Ioi`, `integral_exp_mul_complex_Ioi`, and
  `integral_exp_mul_complex_Iic` in Mathlib's
  `Analysis/SpecialFunctions/ImproperIntegrals.lean` evaluate the inverse transform.
- `Real.fourierInv_eq'` (the explicit complex-exponential inverse integral),
  `MeasureTheory.integral_integral_swap`, `Integrable.mul_prod`, and the product norm bounds supply the Fubini calculation.
  The phase factor has norm one, so `Integrable.mul_prod` followed by domination
  supplies the product-integrability hypothesis; the analytic bound is given below.
- `SchwartzMap.coeFn_fourierMultiplierCLM_toLp` in the vendored multiplier module contains
  a model for extending pointwise kernel realizations from Schwartz inputs to all `L²`:
  use `SchwartzMap.denseRange_toLpCLM`, an a.e.-convergent subsequence of `L²` outputs,
  and continuity of `(lsmul ℂ ℂ).lpPairing volume 2 2` against the translated kernel.

The upstream file `TauCeti/Analysis/Fourier/ExpNegAbs.lean` provides a reference calculation
for splitting at zero and evaluating the two complex exponential integrals. It is **not**
vendored or required: the signed multiplier calculation is short enough to prove locally.
No theorem about a principal-value Hilbert transform is used.

## 3. Proof of the kernel realization

For `a = 2πy > 0` and `b = 2πx`, the inverse Fourier integral is

```
-i ∫₀∞ exp((-a + ib) ξ) dξ + i ∫₋∞⁰ exp((a + ib) ξ) dξ
 = i / (-a + ib) + i / (a + ib)
 = 2b / (a² + b²)
 = x / (π (x²+y²)).
```

All half-line integrals are absolutely convergent because the relevant real parts are
`-a` and `a`. Endpoints are null sets; the multiplier's value at zero causes no correction.
Use positivity of `a` to establish the two denominator nonvanishing facts before `field_simp`.

Apply `F2_symm_toLp_ae_eq` to `m_y ∈ L¹ ∩ L²`. The left side is an `L²` function and the
right side is exactly `Q_y` pointwise, so `MemLp 2` transfers to the explicit kernel by
`MemLp.congr`. Thus the proof of the kernel's square integrability need not evaluate
`∫ Q_y²` separately. Translation and reflection preserve volume, so every
`t ↦ Q_y(x-t)` is in `L²`; Hölder then gives absolute integrability against any `L²` input.

First take `f ∈ L¹ ∩ L²`. The integral transform `𝓕 f` is bounded by `∫‖f‖`, and
`m_y * 𝓕 f` is integrable since `m_y ∈ L¹`. It is in `L²` because the `L²` Fourier transform
of `f` is in `L²` and multiplication by `m_y` is bounded. The existing `L¹ ∩ L²`
identification lemmas therefore give

```
T_y f(x) = ∫ ξ, exp(2πixξ) m_y(ξ) (∫ t, exp(-2πitξ) f(t) dt) dξ
         = ∫ t, [∫ ξ, exp(2πi(x-t)ξ) m_y(ξ) dξ] f(t) dt
         = ∫ t, Q_y(x-t) f(t) dt                         a.e. x.
```

Fubini is justified by `∫∫ |m_y(ξ)| |f(t)| = ‖m_y‖₁ ‖f‖₁ < ∞`. This step never asserts
`Q_y ∈ L¹`; that assertion is false. Compactly supported `L²` functions are `L¹` by
Cauchy–Schwarz on a finite-measure compact support, so this already proves the requested
compact-support realization.

For arbitrary `f ∈ L²`, approximate by Schwartz functions. The `L²` outputs converge because
`T_y` is bounded; take an a.e.-convergent subsequence. At every fixed `x`, the kernel integrals
converge by the continuous `L²` pairing against `Q_y(x-·)`. Their limits agree, proving the
stated all-`L²` realization. This extension is optional for the first milestone but removes
an avoidable restriction from downstream operator APIs.

## Implementation verification

`lake build FourierFrames.Cited.Pavlov.ConjugatePoisson` succeeds without warnings.
The explicit symbol is piecewise at zero and `conjugatePoissonSymbol_eq` identifies it
with `-i sign(ξ) exp(-2π y |ξ|)`. The all-`L²` kernel formula is
`conjugatePoissonOperator_eq_integral`; absolute integrability at every point is
`conjugatePoissonKernel_mul_integrable`. No principal-value boundary limit is introduced.

The Fubini calculation reuses the already proved `FF.PW1.integral_fourier_smul`
rather than reproving an iterated-integral swap. Its hypotheses are the integrability
of the input and of the modulated symbol, so its use is justified by the same product
bound described above. The density step then extends to all `L²` inputs.

## 4. Boundary with the BMO work

The elementary rational identity gives a uniform-in-`y` Hörmander estimate. For
`|t| > 2|h|`,

```
|Q_y(t-h) - Q_y(t)| ≤ (4/π) |h|/t²,
```

since `|Q_y'(s)| ≤ 1/(πs²)` and `|s| ≥ |t|/2` along the segment. Integration over the two
tails bounds the Hörmander constant by an absolute constant, independent of `y > 0`.
Equivalent direct rational algebra can avoid the real mean value theorem. The exact value
of this constant does not matter for `MemBMO`.

The generic TauCeti endpoint bound alone is for `L² ∩ L∞`, not BMO inputs. The intended
BMO extension uses the already formalized John–Nirenberg estimate for local `L²` control,
a near/far split of `u-u_{2I}`, and the convergent tail sum `∑ 2^{-k}(k+1)`.
For global BMO data the integral must be normalized, for example by subtracting the kernel
at a fixed base point in the far part; ordinary unrenormalized convolution need not converge.
The local `L²` part and every compact truncation can use `T_y` above. A uniform-in-`y` BMO
estimate followed by Fatou is sufficient for the Pavlov phase bridge, without defining or
proving convergence of a principal-value Hilbert transform.

Before implementation, review the sign and `2π` normalization, the exact `L²`/integral
comparison APIs, and the downstream need for all-`L²` versus compact-support realization.
The mathematical steps above are independent of A₂ weights and Cartwright factorization.
