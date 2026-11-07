# P5 rectangle Harnack helper

Implemented in `FourierFrames/Cited/Pavlov/Harnack.lean` on 2026-11-07, independently of
`Cardinal.lean`, with the signature proposed in `P5_Cardinal.md` §4, strengthened by removing
the redundant `1<M` assumption. The only external
analytic input is the unchanged Tau Ceti theorem `IsCompact.harnack_inequality`.

The rectangle hypothesis cannot be enlarged from `[a,b]` to `[a,a+D]`: a bound on the
length does not extend the zero-free domain. Instead, fix

`δ = r / (8 * (D+r+1))`, `U = rect 0 1 δ`, and `K = {0,1}`.

For each target `z = x+iy`, use the complex-affine map

`A(w) = t₀ + (z-t₀)*w`.

The elementary lemma `affine_mem_rect` proves that `A(U)` lies in the original
rectangle. Its real part lies between `a-Dδ-(r/2)δ` and `b+Dδ+(r/2)δ`, and its
imaginary part has absolute value at most `Dδ+(r/2)(1+δ) < r`. These estimates use
`x,t₀ ∈ [a,b]`, `b-a≤D`, and `|y|≤r/2`. Degenerate intervals and the constant
map `z=t₀` are included; no inverse or positive interval length is needed.

The open convex set `U` and compact subset `K` depend only on `r,D`. Thus the
Harnack theorem provides `C≥0`, uniformly for all functions and all target points.
Apply it to

`u(w) = log M - log ‖f(A(w))‖`.

This is harmonic by Mathlib's `AnalyticAt.harmonicAt_log_norm`, since `f∘A` is
entire and zero-free on `U`; the assumed norm bound makes it nonnegative.
Normalization gives `u(0)=log M`, so `u(1)≤C log M` yields

`exp ((1-C)*log M) ≤ ‖f(z)‖`.

The exponential is strictly positive without needing an explicit Harnack constant.
Normalization already forces `M≥1` whenever the remaining hypotheses are
satisfiable, so the implemented statement removes the redundant `1<M` assumption.

This avoids a manually indexed disk chain and does not change any mathematical
hypothesis: removing `1<M` strengthens the helper and downstream callers simply
omit that argument. The Tau Ceti closure is recorded in
`TauCeti/VENDORED.md`; its library-scoped elaboration options match upstream.
