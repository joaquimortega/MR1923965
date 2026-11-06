# R5 — Independent referee report: Theorem 2 (M08, M09)

Scope: `blueprint/M08_Theorem2i.md`, `blueprint/M09_Theorem2ii.md`, `FourierFrames/Theorem2i.lean`,
`FourierFrames/Theorem2ii.lean` (+ `Lemma3Uniform.lean`), `theorem2_i`/`theorem2_ii` in
`comparator/statements.lean`, NOTEBOOK N-20..N-26.  Sources checked: page images p-14, p-15, p-16, p-17
(journal pp. 802-805) and `literature/ArxivOrtega.tex` (they agree on every point used below).
Numerical scripts (scratchpad): `t2ii.py`, `ratio.py` (test function for (ii)), `t2i.py` (V = U_psi - log|f| for (i)).

## Overall verdict

* **Theorem 2 (ii): the new proof is correct.**  I re-derived every step (window, matching, envelope,
  zeros, PW membership, left half-line, region (0, x0), final ratio) and found no gap.  I also built the
  test function numerically (exact zeros from the density, product formula) and confirmed envelope,
  growth of the mass and boundedness of the sampling sum.  The writer's critique of the printed proof is
  right on its main point (the printed (11) is false for `psi = log log x`); several secondary claims in
  M09 §8 are not proved but they are not needed.
* **Theorem 2 (i): the blueprint's estimates are correct** under `DensBound`; the printed argument is
  indeed incomplete and the counterexample to its construction is valid.  The formal `theorem2_i` is
  **strictly weaker than the printed theorem** (extra hypothesis `hmono`); that is a fidelity deviation
  (finding 1), justified but not a proof of the printed statement.
* No critical findings.  One major (fidelity), the rest minor.

## Findings

### 1. [major, fidelity] `theorem2_i` carries an extra hypothesis `hmono` not in the paper
`comparator/statements.lean` l.97-101 and `Theorem2i.lean` l.326-331.  The printed Theorem 2 (i)
assumes only `psi'(x) = 1/O(x)` and a logarithmically regular partition.  The formal statement adds
`∃ X, AntitoneOn (deriv ψ) (Ici X)`.  The formal theorem is therefore a *corollary* of the printed one,
not equivalent to it.  Evidence that this is forced by the printed proof, not by laziness: finding 2.
Whether the printed statement is true for spiky `psi` is, as far as I can tell, open (I could not decide it
either, see finding 2).  Recommendation: (a) keep the explicit docstring (already present) and state in
the README/final report that `theorem2_i` is proved only under `hmono`; (b) keep
`theorem2_i_of_regular` (hypothesis `DensBound`, strictly more general than `hmono`) as the headline
technical result; (c) optional generalisation that costs nothing in the proof: replace `AntitoneOn` by
quasi-monotonicity `∃ X K, ∀ X ≤ s ≤ u, deriv ψ u ≤ K * deriv ψ s`; the same one-line argument gives
`psi'(s) <= K psi'(t_{n-1}) <= K/d_{n-1} <= KC/d_n`.

### 2. Counterexample to the paper's construction (N-22, M08 Issue A): **valid**
* Consistency with *all* hypotheses.  Take cell lengths `d_n = sqrt(t_n)` (so `t_n ~ n²/4`, `d_n ≃ d_{n+1}`),
  put the mass `1 - b_n` of cell `n` on a smooth bump of width `ℓ_n = log t_n` inside the cell and add the
  baseline `psi' >= c_0/x` (baseline mass per cell `b_n ≈ c_0 d_n/t_n ≈ c_0/sqrt(t_n)` is small, so the
  bump still carries mass `≈ 1`).  Then: `psi` is C¹, nondecreasing, `psi = 0` on `(-inf,0]` (start
  with `psi' = 0` near 0), `psi' <= 1/ℓ_n + c_0/x -> 0`, `psi' >= c_0/x`, `psi(t_n) = n`, `d_n ≃ d_{n+1}`,
  and the regular-partition sum depends only on `(t_n, d_n)`, i.e. it is the Riemann sum of a Poisson
  kernel with spacing `~ sqrt(x)` in a window of length `x`, hence bounded.  So all hypotheses hold
  (`ψ' = o(1)` included).
* Failure of the construction: for real `x` in the bump of cell `n`, `j_n(x) = ∫ log|s-x| dν_n - log|x - z_n|
  = log ℓ_n + O(1) - log d_n + O(1) -> -∞`, because `|x - z_n| >= |Im z_n| >= (2/π) c d_n`.  By the
  upper bound of M08 §6.7 (no `DensBound` needed) every other `j_m(x) <= O(1)`, and the lower bounds
  of §6.4-6.6 hold for the non-near cells, so `V(x) -> -∞`.  (Decay is slow, `log(log t/sqrt t)`, but
  unbounded.)  Checked by hand, formula is exact.
* What it does *not* show: the writer's "two half-spikes at the ends of a cell defeat every choice of one
  zero per cell" is plausible (one zero at height `h` matches `log h` against `½log ℓ + ½log d` on the two
  bumps) but is only heuristic; and for a single bump one could repair the *construction* by moving the
  zero to `s_0 - i·ℓ_n` (this keeps `φ_f' = Σ h_n/|x - z_n|² -> 0` since `ℓ_n -> ∞`), so the failure is of
  the *paper's particular `f`*, not of the theorem.  Status of the theorem for spiky `psi`: open; the
  blueprint says exactly this.  Verdict **N-22: confirmed** (construction fails; theorem open).
* `hmono` ⇒ density bound: **correct.**  For `n` with `t_{n-2} >= X`: `s ∈ I_n ⇒ psi'(s) <= psi'(t_{n-1})`
  (antitone, `s >= t_{n-1}`), and `psi'(t_{n-1}) <= psi'(u)` for all `u ∈ I_{n-1}`, so
  `psi'(t_{n-1}) <= (1/d_{n-1})∫_{I_{n-1}} psi' = 1/d_{n-1} <= C/d_n`.  The finitely many earlier cells
  are handled by boundedness of the continuous `psi'` on `[0, X]` and `d_n >= min > 0`.  The lemma
  `RegData.densBound_of_antitoneOn` is true as stated.  The hypothesis set is satisfiable
  (`psi = 2(1+x²)^{1/4} - 2` for `x >= 0`: C¹, `psi'(0)=0`, `psi' ~ x^{-1/2}` decreasing, `>= c/x`, log-regular).

### 3. Blueprint M08 estimates — verified line by line (no errors found)
* **Taylor part.**  `h_z(σ) = log|e^σ - z| - σ`, `h_z' = Re(z/(e^σ - z))`, `h_z'' = -Re(z e^σ/(e^σ - z)²)`,
  `|h_z''| <= |z|e^σ/|e^σ - z|²`; the linear Taylor term integrates to `h_z'(s_n)∫(log s - log r_n)dν_n = 0` by
  (9); `|σ - log r_n| <= λ_n = log(t_n/t_{n-1}) <= min(log(1+C), d_n/t_{n-1})`.  Below/Above bounds
  (`2λ_n² t_n/|z|`, `2λ_n²|z|/t_{n-1}`) and the telescoping sums `Σ_{Below} d_n <= |z|/2`,
  `Σ_{Above} d_n/t_{n-1}² <= (1+C)²/(2|z|)` are correct.  Here the log-centre cancellation is essential:
  without it terms are `O(|z|²/r_n²)` whose sum is `~|z|^{1/2}` for `ψ = 2√x` (M08 Issue E: confirmed).
* **Corrected `V_2`.**  `B_n = -½ log(1+v)`, `v = Δ/u²`, `Δ = |z - z_n|² - |z - r_n|²
  = (r_n - a)(2x - a - r_n) + 2yb + b²` (`a = r_n cos θ_n, b = r_n sin θ_n`): I re-expanded this and the bound
  `|v| <= c²(ρ₁ + 9/4) d²/u² + 2c d y/u²` is right; with `u >= K₀ d`, `y <= u`, `K₀ >= 16`, `c < π/8`
  one gets `|v| <= 1/2`.  The first-order term `2 d y/u²` is genuinely present: for `z = i r_n` the difference is
  `≈ θ_n/2 = c d_n/(2 r_n)` while the printed bound is `d_n²/(2 r_n²)`; for `ψ = 2√x`, `d_n/r_n ~ 1/n`, so the
  printed estimate fails by a factor `n`.  Its sum is a Riemann sum: for far `n`, `|z - s| <= (9/8)u` on
  `I_n`, hence `Σ d_n y/u² <= (81/64)∫ y/((x-s)²+y²)ds = 81π/64 <= 9π/4` (`sum_far_im_le` is true).
  **N-23: confirmed** (including the repaired bound).
* **Index classes / near cells.**  Middle ⊆ `W⁺ ∪ {n_1}`; counting `#near <= 3(1+K₀²)M` and
  `Σ_far d²/u² <= 3(1+K₀⁻²)M` follow from `(x₀-t_n)² + d_n² <= 3(|z-r_n|² + d_n²)`: correct.  Near bound
  (§6.7): upper `log(K₀+1) + log(π/(2c))`, lower `-2K - log(K₀+1)` using `ν_n <= (K/d_n)ds` and
  `∫_{-1}^{1} -log|w|dw = 2`: correct; it is the *only* place `DensBound` enters.  **N-24: confirmed**
  (three indices do not suffice for `C > 1`; the real role of the regular-partition sum is counting near cells).
* **`φ_f' -> 0` (N-25): confirmed and correct.**  `phaseDeriv f(x) = Σ|Im z_n|/|x - z_n|²` (sign checked:
  `Im 1/(x - z_n) = Im z_n/|x-z_n|² < 0`), `|Im z_n| <= c d_n`, `|x - z_n| >= (2/π)c d_n`; cases `x <= 0`,
  `r_n <= x/2`, `r_n >= 2x` give `O(1/|x|)`; middle cells give `cΓM/min d_n -> 0` because `d_n -> ∞`.  The paper
  never checks this, though Corollary 2 requires it.  Integrability of the `UPsi` integrand (bounded `psi'`,
  `psi' = 0` on `(-∞,0)`, `|log|1-w| + Re w| <= |w|²` for `|w| <= 1/2`) is correct; the junk-value
  remark is apt.  `RegData` data (`r_n ∈ (t_{n-1},t_n)`, `κ`, `c = π/(4κ)`) are consistent.
* **N-26: confirmed.**  `d_n <= C d_{n-1} <= C t_{n-1}` gives `t_n <= (1+C)t_{n-1}`, which is all that is used;
  `hlow` is not used anywhere (every `ψ'`-lower information enters through `ν_n`).  Keeping it is harmless
  (it only strengthens the hypotheses) and faithful.
* Numerical check (mine): `ψ' = x(1+x²)^{-3/4}` (so `ψ = 2(1+x²)^{1/4} - 2`), 3000 cells, `V = Σ j_n` at
  `z ∈ {0.5, 3, 10, 50, 100+3i, 1000, 1000+500i, 300i, 2000i, -50, -1000+10i, 10⁴, 1.5·10⁴+i, 12345.6}`:
  `V ∈ [-1.01, 0.02]`.  Consistent with `|V| <= B`.

### 4. Printed source issues for (i) (page images)
* **N-20 (integration range): confirmed, with one wording correction.**  Journal p. 802 prints
  `log|f| = Σ ∫_{r_{n-1}}^{r_n}(log|1 - z/z_n| + Re z/t)dψ` and (10) with `∫_{r_{n-1}}^{r_n}`; the mass
  `ψ(r_n) - ψ(r_{n-1})` is not an integer, so this is not `log|f|` of an entire function; `[t_{n-1}, t_n]` is
  forced.  Correction to N-20: it says "the rewriting of `j_n` 'by (9)' ... already use `[t_{n-1}, t_n]`";
  in fact (p. 803, first display) the rewriting of `j_n` *still* has `∫_{r_{n-1}}^{r_n}`, and so does the
  `V_1 + V_2` display; only the final `V_1 = Re Σ ∫_{t_{n-1}}^{t_n} Q_n dψ` and `L(ω)` domain use `t`.
  (Also (9) itself is over `[t_{n-1}, t_n]`, so the printed `j_n` identity is only correct with `t`.)
* **V_2 for nonreal z (N-23): confirmed** (finding 3).
* **Window `n(z) ± 1` (N-24): confirmed.**

### 5. Theorem 2 (ii): step-by-step verification of the new proof (all OK)
1. **Window.**  `h(x) = ε log x - ψ(x)` has `h' = ε/x - ψ' >= 0` on `[R,∞)` when `xψ' <= ε`; hence
   `0 <= ψ(x) - ψ(x₀) <= ε log(x/x₀) <= ε s' = η` on `[x₀, x₀e^{s'}]`.  Existence of `x₀ >= R'` with
   `ψ(x₀) = n+1/2`: `ψ` continuous, unbounded (`h0` excludes the `atBot` alternative of `IsAdmissiblePsi`).
   `a₁ = (x₀-3)/2`, `a₂ = x₀e^{s'}+3`: `16a₁ <= a₂` (`e^{s'} >= 8`), `log(a₂/(4a₁)) >= s' - log 2 >= s`.  OK.
2. **Λ within η of the zeros.**  `l + ψ(l) = k`, so `l - ((k-n-1) + 1/2) = n + 1/2 - ψ(l) ∈ [-η, 0]`.  Zeros of `f`
   on `[2a₁+3, a₂-3]` are exactly `ℤ + 1/2`: I computed `pt_j`, barycentres directly (primitive `= x - 1/2` on
   `[2a₁, a₂]`, cells `[j+1/2, j+3/2]`, `γ_j = j+1`, shift by `1/2`); numerically the window zeros have fractional
   part exactly `.5`, left zeros are `0,-1,-2,...`, zeros beyond `2a₂` are integers.  OK.
3. **Envelope.**  `potW = -½(R_{a₁} + R_{a₂})`, `R_a(x) = (1/a)∫_a^{2a} log|1 - x/t|dt`; `|R_a - log max(1,|x|/a)| <= 4`
   (my numerical supremum over `x ∈ [-50,50] ∪ [10⁻³,10⁶]`, `a = 1`: `2.53`; the case analysis of A4 is right
   and gives `max(1+2log4, log 6) = 3.77`), so `|potW - ½ log env| <= 4` (A5).  `U = π|Im z| + potW + κ Re z`
   (checked `∫(log|1 - z/t| ...) = π|y|` numerically: 2.19911 vs 2.19911).  Envelope check numerically
   (full function, `a₁ ∈ {20,40}`, `L ∈ {3,5}`): `log(|f|²/(env·dist²)) ∈ [-1.3, 2.9]` uniformly, on `x<0`, `(0,2a₁)`,
   `(2a₁,a₂)`, `(a₂,3a₂)`.
4. **PW membership.**  Exponential type `<= π` (not "exactly"; exactly is not needed since `MemPW` is `<=`): for
   `|Im w| >= 1`, `|F| <= e^{U+π}` from `multF_estimate_three` (`π/(2a)/|Im w| <= π`, `a = 1/2`), and
   `potW <= log(2a₂)+1` for *all* complex `z` (A6: `μ <= 0`, `∫|μ| = 1`, `‖μ‖_∞ <= 1/2`,
   `-log‖t-z‖ <= max(0, -log|t - Re z|)`) so `|G(w)| <= C e^{π|Im w|}`; for `|Im w| <= 1` via the Lemma-3 upper
   bound and `infDist <= 3`.  `L²`: `|f| <= 2C√env`, `∫env = 2a₁(2 + log(a₂/a₁))`.  OK.  (`e^{-κz}` is needed:
   `F` alone has `|F| ≃ e^{π|y| + κx}` along the axis, not `L²`-comparable to the envelope.)
5. **Left half-line.**  `Λ ∩ (-∞,0] = ℤ_{<=0}` (`ψ = 0`), and `f(j) = 0` for `j <= 0` since `[j,j+1] ⊂ {m = 1}`
   for `j+1 <= a₁`.  Contribution exactly `0`.  OK.
6. **Region (0, 2a₁+3), where Λ and ℤ are out of phase.**  There `env <= 1`, `|f|² <= 4C₁²` (B4: `infDist <= 1/a = 2`),
   and the number of Λ points is `<= 1 + (1+B)(2a₁+3)` (separation `>= 1/(1+B)` because `g' = 1 + ψ' ∈ [1, 1+B]`
   and `g(λ') - g(λ) ∈ ℤ_{>0}`).  So the sum is `<= C' a₁`, **really `≲ a₁`**, without any phase information.
   (Alternatively `#(Λ ∩ [0,x₀]) = g(x₀) - g(0) + O(1) = x₀ + ψ(x₀) + O(1)` and `ψ(x₀) = O(log x₀)`.)  The
   `η²`-term occurs only on the window.  OK.
7. **Window region and tail.**  On `[2a₁+3, a₂-3]` `|f|² <= C₁²η² a₁/(l+1/2)`, at most `2+B` points per unit
   interval, sum `<= C a₁ η²(1 + log(a₂/a₁))`; beyond `a₂-3`: `Σ env <= 3a₁`.  OK.
8. **Mass.**  `∫_S a₁ d(x)²/(x+1/2) dx >= a₁ Σ_k (1/12)/(k+3/2) >= (a₁/12) log((k₁+3/2)/(k₀+3/2))`,
   `(a₂-5/2)/(2a₁+11/2) >= a₂/(4a₁)` iff `a₂(2a₁ - 11/2) >= 10a₁` (true for `a₁>=8, a₂>=16a₁`).  Correct.
   (The left side `x<0` also carries critical mass since `env` is even; it is simply not used.)
9. **Ratio.**  Final choice (`s`, then `η`, then window) is consistent: `C` depends only on `B = sup ψ'`, not on
   `a₁,a₂,η`; `log(a₂/a₁) = L + log 4 <= L(1+log 4)` for `L >= 1`.  Numerically (mine, `a₁ = 10`, adversarial
   `Λ = ℤ_{<=0} ∪ (ℤ+1/2)_{>0}`): `Σ/‖f‖²` = 0.70, 0.63, 0.57, 0.52 for `L = 1,...,4`; `Σ ≈ 0.9 a₁`
   constant, `‖f‖² ≈ a₁(1.2 + 0.11 L)`, i.e. `~1/L` decay as claimed (slow but monotone).
10. **Uniformity of Lemma 3.**  `lemma3_estimate_uniform` is a `sorry` in `Lemma3Uniform.lean`; I read the vendored
    proof (`Main.lean` l.342-460): `K₁, K₂, K₃` are defined from `(a,b)` only and the final bound is
    `K₃ + 3K₁ + 3K₂`, independent of `m` and of `C`.  So the uniform statement is a pure re-packaging;
    low risk (my numerics also show uniformity for `a₁ = 20, 40`).  It is an upstream obligation, listed as
    such in M09 §0.3: fine.

### 6. Printed proof of (ii) — verdicts on the claimed defects
* `ε_n -> 0`: **false as claimed.**  I solved `∫_{t_n}^{ξ_n} (ψ - n - 1/2) dlog x = 0` for `ψ = log log x`
  (`log x = e^{ψ}`, `u = ψ - n - 1/2`): `(ε-1)e^{ε} + (3/2)e^{-1/2} = 0`, `ε = 0.374217...`, independent of `n` (verified both by this
  closed form and by direct quadrature at `n = 5`).  So `ε_n ≈ 0.37`, not `-> 0`; "it is clear" is wrong.
  For `ψ` locally linear in `log x` the equation gives `ε = 1/2`.
* Typos `ψ_n`, `φ_n' = o(1/t)` (should be `ψ'`): **confirmed** (`φ_n' = -1/ξ_n ≃ 1/t` on `[ξ_n,2ξ_n]`; `φ_n' = -1` on `|t|<1/2`).
  The `∫_0^{|x|}` in the heuristic formula diverges at `0` (`φ_n(0)-1/2 = -1/2`): **confirmed**, should be `∫_1`.
* **The essential defect (this is what makes (11) false), confirmed by the paper's own formulas.**  The paper
  asserts `U_n(x) = -log|x| + O(1)` for `|x| < t_n` and `U_n + ½ log x ≃ 1` on `[(1-o(1))ξ_n, 2ξ_n]`; with its
  slope formula `dU_n/dlog x = φ_n - ½`, these two statements require
  `∫_{t_n}^{ξ_n}(φ_n - ½)dt/t = -½ log(ξ_n/t_n) + ½ log t_n`, i.e. `∫_{t_n}^{ξ_n} φ_n dt/t = ½ log t_n -> ∞`, whereas the
  paper chooses it to be `0`.  Equivalently `U_n(ξ_n) = -½log t_n - ½log ξ_n`.  For `ψ = log log x`, in
  `s = log x`, `2U_n + s = e^n(2v log v - 3v + 2)`, `v = s/e^n ∈ [1, e^{0.87}]`, which is `<= -e^n` on all of
  `[t_n, ξ_n]`: `∫_{[t_n,ξ_n]} e^{2U_n} ≲ 1/t_n`, and on `[2ξ_n,t_{n+1}]` the slope is still `<= -½`, so **(11) fails**
  (`∫_{Ω_n} e^{2U_n} -> 0`, not `∞`); `‖e^{U_n}‖²` stays `≃ 1` (mass near the origin), so `‖f_n‖ -> ∞` is not obtained.
  N-21's statements "`U_n + ½ log x ≃ 1` fails" and "`U_n(ξ_n) ≈ -½ log ξ_n - ½ log t_n`" are **confirmed**.
  (My numeric/analytic check used the literal slope formula; the contradiction above uses only the paper's own
  claims, so it does not depend on how the divergent `∫_0` is regularised.)
* M09 §8 items 6 and 10 (smeared deletion on `[ξ_n,2ξ_n]` shifting `Γ` by up to 1, "peak of comparable mass",
  `dist(λ_k,Γ) -> 0` failing on `[ξ_n,2ξ_n]`) are **plausible but not proved**; they are not needed for the verdict
  and I would soften "fairly sure" to "heuristic".  Item 7 states that `ψ' = o(1/x)` is *equivalent* to the
  existence of arbitrarily long windows with `|ψ - (n+1/2)| <= η`: only "⇒" is true/needed (bursts of `ψ'` in
  between windows are compatible with long windows).  Item 8 minor remarks are right.  Item 9 (linear factor
  `e^{-κz}`; the symmetric product defining `f_n` vs `F`): **confirmed** and necessary.  **N-21: confirmed**, with
  the qualifications above.

### 7. Minor / presentational
* (minor) M09 §8.7 "equivalent" → "implies" (see above).
* (minor) M09 §0.1 quotes numerical ratios `0.71, 0.59, 0.50` (`a₁ = 10`, `L = 2,4,6`); my independent computation gives
  `0.63, 0.52` for `L = 2, 4` (different normalisation/Λ, same qualitative behaviour).  Not an error; do not cite
  as a reproducible figure.
* (minor) `theorem2_ii` does not use `hPW` (kept to match the comparator statement): a linter warning at most.
  The disjunct `Tendsto ψ atBot atBot` of `IsAdmissiblePsi` is impossible under `h0`, as stated.
* (minor) In `theorem2_i`'s `DensBound`/`abs_cellTerm_near`, `K` should be `>= 0`; this is automatic (mass `1` on
  a cell of length `d_n`) but not a hypothesis; the constant `2K + ...` is only meaningful then.  Cosmetic.
* (info) All scaffold lemma statements I inspected in `Theorem2ii.lean` (`dens_isMultWeight`,
  `multPrim_dens_stretch`, `testFn_eq_zero_of_nonpos` (`a₁ >= 2`), `infDist_dens_stretch` (`x ∈ [2a₁+3, a₂-3]`),
  `infDist_multGammaC_le`, `testFn_norm_real`, `pwNormSq_testFn_ge`, `sampleSum_testFn_le`, `exists_window`) are
  true as stated (hypothesis ranges `a₁ >= 8`, `16a₁ <= a₂` match the proofs).  In `Theorem2i.lean` the statements
  `abs_cellTerm_{below,above,far,near}`, `card_near_le`, `sum_far_le`, `sum_far_im_le`, `exists_bound_cellTerm`,
  `exists_approx`, `densBound_of_antitoneOn`, `theorem2_i_of_regular` are true as stated (constants checked against
  the proofs above).

## Faithfulness of the two main statements
* `theorem2_ii`: faithful (hypotheses: `ψ = 0` on `(-∞,0]`, `xψ'(x) -> 0`, plus the standing `IsAdmissiblePsi`).
  Not sampling is shown via the lower bound only, so the upper frame bound in `IsSampling` is irrelevant.  True.
* `theorem2_i`: true (modulo the unproved scaffold) but **not faithful** in the sense of finding 1 (extra
  `hmono`).  Other hypotheses faithful: `hlow` = `ψ' = 1/O(x)`; `hreg` as `IsLogRegularPartition` (existential `t`,
  `d_n ≃ d_{n+1}` in both directions, Poisson-sum bounded) matches the displayed definition.

## Summary of verdicts on NOTEBOOK entries
| entry | verdict |
|---|---|
| N-20 | confirmed (print-checked); fix wording: the `j_n` rewriting on p. 803 still uses `r_{n-1}..r_n` |
| N-21 | confirmed (ε_n ≈ 0.374 verified; (11) false); items 6/10 of M09 §8 and the "equivalent" in 8.7 are overstated |
| N-22 | confirmed: counterexample valid and consistent with all hypotheses; truth for spiky ψ open; hmono ⇒ DensBound correct |
| N-23 | confirmed; the repaired bound with `d_n y/|z-r_n|²` is correct and summable |
| N-24 | confirmed |
| N-25 | confirmed (`φ_f' -> 0` proof correct; integrability of `UPsi` integrand correct) |
| N-26 | confirmed (`hlow` unused; keep for faithfulness) |
