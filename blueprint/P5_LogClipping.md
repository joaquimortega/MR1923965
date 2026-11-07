# P5 — continuous compact logarithmic cutoffs

File: `FourierFrames/Cited/Pavlov/LogClipping.lean`.
Input: `A : ℂ → ℂ`, a real number `M>0`, and the real boundary bound
`∀t:ℝ, ‖A t‖≤M`. Continuity is sufficient for the continuity/integrability
lemmas; no entire-function or Pavlov hypothesis is added.

Define, for `n:ℕ`,

```
logClipCutoff n t = max 0 (min 1 ((n:ℝ)+1-|t|))
logClip M A n t = logClipCutoff n t *
  (Real.log M - Real.log (max ‖A t‖ (M*Real.exp (-(n:ℝ)))))
```

The floor is strictly positive, at most M, and decreases with n. The
clipped logarithmic deficit is therefore nonnegative and increases with n.
The cutoff lies in [0,1], increases with n, is one on |t|≤n, and vanishes
on |t|≥n+1. Their product is nonnegative and increasing. The floor avoids
all discontinuities of real logarithm at zero, so logClip is continuous
when A restricted to the real line is continuous. Its support is contained
in `[-(n+1),n+1]`, hence compact. Its weighted version is also continuous
with compact support and therefore `LogIntegrable`.

For the diameter bound put r=max(‖A t‖,M exp(-n))>0. Since the cutoff≤1,
g≤logM-logr. Thus exp(g)≤M/r, and ‖A t‖ exp(g)≤M. Squaring gives
`‖A t‖² exp(2g)≤M²`. This argument applies unchanged at zeros and never
rewrites exp(log 0).

At a fixed nonzero boundary point, the floor tends to zero and eventually
lies below ‖A t‖. Also eventually n≥|t| and the cutoff equals one.
Consequently logClip is eventually exactly logM-log‖A t‖, hence tends to
that value. No claim of this convergence is made at boundary zeros.

Planned public declarations, namespace `FF.Pavlov`:

```lean
def logClipCutoff (n : ℕ) (t : ℝ) : ℝ
def logClip (M : ℝ) (A : ℂ → ℂ) (n : ℕ) (t : ℝ) : ℝ
theorem logClip_nonneg (hM : 0<M) (hbd : ∀t:ℝ, ‖A t‖≤M) ...
theorem logClip_monotone (hM : 0<M) (hbd : ∀t:ℝ, ‖A t‖≤M) (t:ℝ) :
  Monotone (fun n : ℕ ↦ logClip M A n t)
theorem continuous_logClip (hM : 0<M)
  (hA : Continuous (fun t:ℝ ↦ A t)) (n:ℕ) : Continuous (logClip M A n)
theorem logClip_eq_zero_of_abs_ge (h : (n:ℝ)+1≤|t|) : logClip M A n t=0
theorem hasCompactSupport_logClip (...) : HasCompactSupport (logClip M A n)
theorem integrable_logClip (hM : 0<M) (hA : Continuous ...) (n:ℕ) :
  Integrable (logClip M A n)
theorem logIntegrable_logClip (...) : LogIntegrable (logClip M A n)
theorem logClip_boundary_bound (hM : 0<M) (hbd : ∀t:ℝ, ‖A t‖≤M) (n:ℕ) (t:ℝ) :
  ‖A t‖^2 * Real.exp (2*logClip M A n t) ≤ M^2
theorem tendsto_logClip {t:ℝ} (ht : A t≠0) :
  Tendsto (fun n : ℕ ↦ logClip M A n t) atTop (𝓝 (Real.log M-Real.log ‖A t‖))
```


Independent review: the Poisson-domination implementer approved the floor
positivity/monotonicity, product monotonicity, support radius, scalar boundary
bound, and eventual offzero equality before implementation. The main review
record is appended to `reviews/R13_Pavlov_Blueprint.md`.

Implemented extra interfaces:

* `logClip_le_nat hM hbd n t` gives the explicit uniform upper bound n.
* `logClip_le_deficit hM hbd n ht` gives g_n(t)≤logM-log‖A t‖ only at nonzeros.
* `eventually_logClip_eq ht` gives eventual exact equality. This and the
  convergence theorem do not require M>0, since the floor tends to zero
  for every real M and the comparison point has positive modulus.

Validation: `lake build FourierFrames.Cited.Pavlov.LogClipping` succeeds
cleanly (9049 jobs). Axiom audits of the boundary bound, monotonicity, and
convergence report only `propext`, `Classical.choice`, and `Quot.sound`.
