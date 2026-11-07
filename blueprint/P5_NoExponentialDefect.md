# No exponential defect: reviewed-interface proposal

Owner: `sol_pavlov_weights`. This helper implements §4 of `P5_Dispersion.md` without a smaller-type assumption.
Imports: `FourierFrames.Cited.Pavlov.Cardinal`, `FourierFrames.HB.Comparable`, `FourierFrames.HB.H2`.
Namespace `FF.Pavlov`. It will not import `Unconditional`.

```lean
theorem no_exponential_defect {Γ : Set ℝ} (hcis : IsCompleteInterpolating Γ)
    {q O : ℂ → ℂ} (hq : Differentiable ℂ q) (hqreal : fstar q = q)
    (hO : IsH2Upper O) {γ a b : ℝ} (hqγ : q (γ : ℂ) ≠ 0)
    (hzeros : ∀ x ∈ Γ, x ≠ γ → q (x : ℂ) = 0)
    (ha : 0 ≤ a)
    (hfactor : ∀ z : ℂ, 0 < z.im →
      Complex.exp (Complex.I * Real.pi * z) * q z =
        Complex.exp (Complex.I * ((a : ℂ)*z+(b : ℂ))) * O z) : a = 0
```

All inputs concern entire q, its real symmetry/zeros, CIS uniqueness, and a genuine Hardy factorization.
No input asserts type lowering, a PW conclusion for the sine product, or a phase/counting theorem.

Proof: if a>0 choose τ=a/2>0. Set f(z)=q(z)sin(τ(z−γ)). The entire multiplier
B(z)=exp(i(az+b))sin(τ(z−γ)) has norm≤1 on the upper half-plane: sine's two exponential
terms, including the factor 1/(2i), each have modulus≤1 after multiplication, so their half-sum norm≤1.
`hO.mul_bounded` and `hfactor` give exp(iπz)f(z)∈H². Conjugation gives f*=f.
The explicit E(z)=exp(−iπz) is HB and has norm exp(π Im z); `memPW_of_memHE` with c=C=1
therefore gives f∈PW. The zero data force f=0 by the zero interpolation datum and CIS uniqueness.
But f'(γ)=q(γ)τ≠0 by the product/chain rules, contradiction. Nonnegativity of a then gives a=0.


Implementation completed in `FourierFrames/Cited/Pavlov/NoExponentialDefect.lean`.
Root and `sol_poisson` independently approved the interface/proof; the latter recorded approval in R13 §10.
The originally displayed `hγ : γ ∈ Γ` premise was removed as redundant: the sine product vanishes on Γ
whether or not the distinguished point belongs to Γ, and its derivative contradiction is evaluated at γ.
No other premise changed. Explicit Lean proofs establish both the bounded sine multiplier and the HB class
and exact norm of `exp(-iπz)`. The final theorem directly proves `a=0`, with no type-lowering assumption.
