# P5 positive harmonic functions with zero boundary

Implemented in `FourierFrames/Cited/Pavlov/HarmonicReflection.lean`. The plan
was independently approved by sol_poisson in review R13 §5 before the principal
proof implementation. The final signature is precisely `P5_Dispersion.md` §3.

1. Define `oddReflection r z = if 0≤z.im then r z else -r(conj z)`.
   Closed-half-plane continuity and zero real boundary imply global continuity
   by the continuous piecewise theorem. This reflection is odd under conjugation.
2. For every radius R>0, apply Tau Ceti's ball Dirichlet theorem to this continuous
   boundary data on the sphere centered at 0. Let h be the harmonic solution.
3. `-h∘conj` is another solution with the same boundary values, by geometric
   invariance of harmonicity under the real linear isometry `Complex.conjLIE`.
   Uniqueness on the compact closed ball gives h(conj z)=-h(z). In particular,
   h=0 on the real diameter.
4. Apply the same uniqueness theorem on
   `K=closedBall 0 R ∩ {z|0≤z.im}` to h and r. Its interior is contained in
   `ball 0 R ∩ UHP`; its frontier lies in the sphere or the real diameter.
   Thus h=r throughout K. Oddness then identifies h with the reflection on
   the whole closed ball.
5. Every point lies in some ball centered at 0, so local equality to h proves
   the reflection harmonic on all ℂ. Mathlib provides an entire analytic H
   with Re H equal to this reflection. Put F=I*H, subtracting a real constant
   if helpful. Then Im F is the reflection and hence nonnegative on UHP;
   F is real on ℝ.
6. Symmetrize algebraically: `P=(F+fstar F)/2` is entire and commutes
   with conjugation. Oddness gives Im P=R, preserving nonnegativity on UHP.
   Existing `FF.entire_pick_linear` then supplies slope a≥0; taking imaginary
   parts yields r(z)=a Im z. No identity theorem is necessary.

Dependencies: existing `EntireHerglotz`; Mathlib harmonic analytic conjugate,
complex conjugation; Tau Ceti roots
`Analysis/PDE/PoissonIntegral/Ball`,
`Analysis/InnerProductSpace/Laplacian/Comparison`, and already vendored
`Analysis/InnerProductSpace/Harmonic/Isometry`. Minimal extra closure and
provenance are recorded by sol_cauchy_schur in `TauCeti/VENDORED.md`. No assumption encodes the
classification, and no boundary continuity of an unknown conjugate is assumed.


Implemented public declarations:

- `oddReflection`: pointwise odd reflection, taking the upper value on the axis;
- `harmonicOnNhd_oddReflection`: entire harmonicity without a positivity assumption;
- `nonneg_harmonic_zero_boundary_eq_mul_im`: the requested classification.

The oddness, global continuity, disk symmetry, and upper-half-disk uniqueness
lemmas are private. All disk arguments cover arbitrary R>0 and use balls
centered at 0 only; radius `‖z‖+1` supplies the neighborhood at each point.
The final symmetrization avoids imposing or proving boundary continuity of an
analytic conjugate.

Validation: `lake build FourierFrames.Cited.Pavlov.HarmonicReflection` succeeds
without warnings. Axiom audits of both public harmonicity/classification
theorems report only `propext`, `Classical.choice`, and `Quot.sound`.
