# R11 — Independent review of the elementary proof of Theorem F

**Date:** 2026-11-07. **Reviewer:** `theorem_f_review`, independent of the
writer of `blueprint/P4F_Elementary.md`.

**Scope:** the complete mathematical route in `blueprint/P4F_Elementary.md`,
the finite-measure Cauchy helpers in `blueprint/impl_notes/theorem-f-cauchy.md`,
and the probability normalization in `blueprint/P4F_Normalization.md`.
The target is the unchanged `FF.TheoremF` of `FourierFrames/Defs.lean`.

## Verdict

Approved for implementation. No critical or major mathematical issue remains
in the reviewed blueprint. The reviewer independently derived the disk-kernel
positivity argument and the inverse change of measure before comparing with
the assembled blueprint. This is a review of the mathematical plan, not a
claim that the eventual Lean implementation has already been checked.

## Calculations checked

1. With `a = θ(i)`, `d = 1 - |a|²`, and `D = 1 - conjugate(a)θ`, the diagonal
   kernel constant is `κ = |E(i)|² d/(4π) > 0`. The normalized density is
   `|D(t)|²/(π d (1+t²))`; its integral is one by isometry and the kernel norm.
2. The inverse density is `|1+conjugate(a)φ(t)|²/d`. No equality of two
   de Branges spaces or Crofoot-transform theorem is required.
3. The scalar in the reflected-kernel identity is exactly
   `i d (z+i) conjugate(E(i))/(2 D(z) E(z))`. Its sign and factor two follow
   from `K(conjugate(z),t) = -(i/(2π)) E(t)E(z)(θ(t)-θ(z))/(t-z)`.
4. Reproduction of the upper and reflected kernels gives, respectively,
   `F - φH = 1` and `J - c = φF`. At `z=i`, the latter is immediate from
   `J(i)=c` and `φ(i)=0`; dividing by `ξ(i)` is unnecessary.
5. The cross pairing is `∫ Rz Cz dν = F(1-|φ|²)/(1-|ξ|²)`. Cauchy–Schwarz
   therefore yields `|F-1|² ≤ |φ|²|F|²` with the stated constants.
6. Cancellation of `|φ|²` is valid only away from its zeros. This was pointed
   out during review and is explicitly handled in the assembled blueprint
   by continuity and density of the nonzero set. Nonconstancy follows from
   strictness inside and unimodular boundary values. Thus no zero-order or
   factorization assumption is hidden in the Schur bound.
7. The inverse Möbius transform is
   `A = (conjugate(a)+B)/(1+aB)`, where `B=H/F`. The defect identity is
   `|F+aH|²-|conjugate(a)F+H|² = d(|F|²-|H|²)`.
8. Expanding the inverse weight gives
   `d Fo = (1+|a|²)F + conjugate(a)J + aH` and
   `d m = 1+|a|² + conjugate(a)c + a conjugate(c)`. The discrepancy between
   the Cayley expression and `2Fo-m` is purely imaginary; taking real parts
   removes it without a Herglotz representation theorem.
9. The final pointwise Poisson identity is
   `2 Re Cz(t)-1 = Im(z)(1+t²)/|t-z|²`. Integration against
   `dμ/(π(1+t²))` supplies precisely `poissonInt μ z`, with `p=0`.

## Helper reviews

The finite-measure Cauchy-transform plan is sound. Bounded measurable
integrands are Bochner integrable; on `|w|<r<1` the derivative bound is
`M/(1-r)²`. The probability identity gives `Re F ≥ 1/2`, which suffices for
nonvanishing; proving the stronger strict inequality is optional.

The normalization plan is sound. The density denominator is finite and
strictly positive, and measurability follows from continuity of the boundary
quotient. The stated `IsProbabilityMeasure` follows directly from the
isometry applied to `K(i,·)`.

The old factorization route and its false `division_lemma` play no role in
this proof. They must not be used as imports that introduce `sorryAx`.
