# P5 — Pavlov's theorem, BMO half (`PavlovBMO`)

Lean file: none (no scaffold written, see verdict). Statement: `FF.PavlovBMO` in `FourierFrames/Defs.lean`.
Paper: Theorem A (p. 791), used in the Claim on p. 799. Sources: [Pa79], [HNP81, p. 286].
Depends on: (would need) P3/P4 only for route B. Used by: `FourierFrames/Landau.lean` (hypothesis `hA`).

## 0. Feasibility verdict

**Not feasible as a phase-2 module. Recommendation: keep `PavlovBMO` as the cited hypothesis `hA`.**

Reasons (checked):
* `grep -ril "muckenhoupt|hilbert transform|BoundedMeanOscillation"` over `.lake/packages/mathlib/Mathlib`
  returns nothing. No Hilbert transform on ℝ, no `A_p` weights, no conjugate function, no BMO, no
  Calderón–Zygmund theory, no Hardy-space factorization, no Poisson-integral/harmonic-conjugate theory on
  the half-plane. (Only the `L²` Fourier isometry exists, which would allow defining the Hilbert transform
  as the multiplier `-i sgn ξ` on `L²`.)
* Both routes below need, besides this, the Cartwright/Hardy-class factorization of the generating function and an
  `H¹`–BMO (Fefferman–Stein) or CZ-type argument. Estimate: 6000–10000 Lean lines, several of them genuinely
  research-grade to formalize; far larger than P1–P4 individually. `JohnNirenberg` (P2) is a small fraction of it.
* The *only* downstream use is to feed `JohnNirenberg` and obtain Landau's inequality (p. 799), so the cost/benefit is poor.
* The Lean statement as frozen is true and faithful (CIS here is for `PW` on `[-π,π]`, `h` is a bounded-variation
  step function minus `t`, hence `LocallyIntegrable`; `countFn` is finite on bounded sets for separated Γ). No change requested.

## 1. Classical route (A): Γ CIS ⇒ `|G(x+i)|² ∈ A₂` ⇒ `h ∈ BMO`

Let Γ be separated and CIS for PW. Steps, with every analytic fact used:

1. *Riesz basis of kernels.* CIS ⇔ `{k_γ/‖k_γ‖}_{γ∈Γ}` (`k_γ(z)=sin π(z-γ)/(π(z-γ))`) is a Riesz basis of PW
   (open mapping + closed graph for the sampling map `f ↦ (f(γ))` onto `ℓ²`; this part is already
   essentially in the project under P1/Theorem 1 machinery). Equivalently, `f ↦ (f(γ))_γ` is an isomorphism
   `PW → ℓ²(Γ)`.
2. *Generating function.* Γ separated, CIS ⇒ there is an entire `G` of exponential type π, `G(Γ)=0` simple zeros only,
   with `G/(z-γ) ∈ PW` after a normalization `1/G'(γ)`, and every `f∈PW` is
   `f(z)=G(z) Σ_γ f(γ)/(G'(γ)(z-γ))` (Lagrange interpolation). Needs: construction of `G` as a Lindelöf-type product,
   Cartwright class, Hadamard factorization (Mathlib: partial).
3. *Weighted Hilbert transform.* Put `w(x)=|G(x+i)|^{-2}`-type weight (the correct weight is `|G(x+i)|²`; the
   discrete operator `(c_γ) ↦ Σ c_γ/(x-γ)` is bounded `ℓ²(|G'(γ)|^{-2}…) → L²(|G|^{2}… dx)` by step 1). Pass from the
   discrete operator to the continuous Hilbert transform on `L²(|G(x+i)|²)` using separation and
   `|G(x+i)|` being (comparable to) a constant on each interval `(γ,γ')` up to the factor `|x-γ|`
   (HNP81 §, Lemma on local comparability, `|G(x+i)|² ≍ dist(x,Γ)²·|G'|²` fails near nodes, so one works at height `i`).
   Result: `H` bounded on `L²(w)`.
4. *`A₂`.* `H` bounded on `L²(w)` ⇒ `w ∈ A₂`: test `f=χ_I` (and `χ_J` for adjacent interval `J`, `|I|=|J|`) to get
   `(⨍_I w)(⨍_I w^{-1}) ≤ C` (easy half of Hunt–Muckenhoupt–Wheeden: for `x∈J`, `|Hχ_I(x)| ≥ c` and
   a sandwiching argument; ~1 page).
5. *`A₂ ⇒ log w ∈ BMO`.* With `u=w/⨍_I w`: Jensen gives `⨍_I log u ≤ 0` and `⨍_I log u ≥ -log ⨍ u^{-1} ≥ -log C`; and
   `⨍|log u| ≤ ⨍(u-1) + ⨍(u^{-1}-1)+…`, using `|log s| ≤ (s-1)+(1/s-1)`: osc ≤ `2C`-ish. Elementary.
6. *From log-modulus to the counting function.* `log|G(x+i)|` is the real part of a function analytic in a half-plane; its
   harmonic conjugate on the line is `arg G(x+i)`. One needs (i) the Poisson representation of `log|G|` in
   `ℑz>0` (Cartwright class: `G(z)e^{iπz}∈ H^∞`-ish after division by the exponential factor; `log|G(x+iy)|=πy+P_y[log|G(·+i)|]`-type
   formula, needs Nevanlinna/Smirnov factorization), (ii) the argument principle linking `arg G(x+i)` and
   `π n_Γ(x)`: `|π n_Γ(x) - arg_x G(x+i)| ≤ C` (each zero changes arg by `π ± O(1)`, uses separation; *wrong as
   justified, see §7, R7-18*), and (iii)
   **the Hilbert transform maps BMO into BMO** modulo constants (Fefferman–Stein; or since `log w∈BMO` is
   `L^p_loc` by John–Nirenberg, apply CZ to the localized + tail decomposition). Then
   `π h(x) = ±H[log|G(·+i)|](x) + bounded + linear term cancelled by the type π`, so `h∈BMO`.

Weak point of (A): items 2, 3 and 6 each take a full paper; 6(iii) requires either John–Nirenberg + CZ kernels or
the `H¹`–BMO duality. None exist in Mathlib.

## 2. De Branges route (B)

Γ CIS ⇒ (project: `completeInterpolating_zero_set`, `FourierFrames/Corollary1.lean:270`, which takes `hPW hC hD`)
Γ = `{φ_E ∈ α+πℤ}` for `E` with `H(E)=PW` isometrically(no: with equivalent norms ⇒ `|E|^{-2}` and `1` are
comparable *as norms on `PW`*, not as weights). Then `n_Γ(t)=φ_E(t)/π+O(1)` and one needs `φ_E(t)-πt∈BMO`. Here `φ_E'(x)=πK(x,x)/|E(x)|²`
and `H(E)=PW` again gives that `|E|^{-2}` satisfies a Muckenhoupt-type condition *for the Paley–Wiener projection*, which must still be
converted into `A₂` via steps 3–4 and into BMO of `φ_E - πt = arg`-conjugate via 6. So (B) does not avoid the harmonic-analysis core;
it only replaces step 2 by Theorems C/D (already hypotheses) at the price of depending on P3/P4 (still sorry'd). Not cheaper. Route (A) is the standard
one and what HNP81 do. (*R7-17:* cheaper on the periphery, identical on the core; see §7.)

## 3. Alternative: a direct proof of the BMO estimate

No direct elementary argument is known. Landau-type counting `|n_Γ(b)-n_Γ(a)-(b-a)|=O(log)` (Beurling/Duffin–Schaeffer) is weaker
than BMO and does not suffice for John–Nirenberg exponential integrability needed on p. 799. The p. 799 Claim needs only
`h∈BMO` in the form "mean oscillation bounded", exactly the Lean `MemBMO`.

## 4. Size and risks if someone nevertheless attempts it

* Hilbert transform + A₂ necessity (steps 3–4): ~1500 lines. Real risk: local-to-global transfer in step 3.
* Cartwright class / generating function / argument-principle estimate (2, 6(i)(ii)): ~2500–4000 lines.
* Conjugation on BMO (6(iii)): ~2000–3000 lines (CZ decomposition on ℝ; shares machinery with P2 John–Nirenberg).
* Total 6k–10k lines; none of the infrastructure exists; I would not schedule it.

## 5. Issues in the source

* Theorem A (tex l. 200–207) is stated as iff with the Helson–Szegő decomposition `P₁[h]=ũ+v+C`, `‖v‖_∞<1/4`; only the
  forward implication's weaker consequence `h∈BMO` is used (tex l. 650: "we will only need the fact that h∈BMO"). The Lean
  `PavlovBMO` records exactly that. Confident.
* Lean-edge check: `MemBMO` quantifies over all `a<b`; `countFn Γ t - t` is locally bounded and measurable, so `LocallyIntegrable` holds
  trivially for separated Γ. Confident.

## 6. Requested changes to M00

None. Keep `hA : PavlovBMO` as an explicit hypothesis in the final theorems (or the paper-level theorems stay conditional on it).

## 7. Referee corrections (R7)

From `reviews/R7_Cited.md`, Part 3 (2026-11-07). R7 confirms the statement (`PavlovBMO` is the forward half
of Theorem A weakened to `h ∈ BMO`, all the Claim uses), the Mathlib inventory, and the verdict: not
feasible, keep `hA`.

1. **Route B is undersold, but the core remains (R7-17).** Replace "Not cheaper" in §2 by: *cheaper on the
   periphery (counting function, `φ' ≍ |E|^{-2}`, both available), identical on the core (`A₂`, Poisson
   representation, BMO conjugation).*
   - With `completeInterpolating_zero_set`, `Γ` is exactly a level set `{φ_E ∈ α + πℤ}` of a continuous
     increasing phase, so `|n_Γ(t) − (φ_E(t) − φ_E(0))/π| ≤ 1`. This removes step 2 (the generating
     function) of route A and step 6(ii).
   - `φ'_E ≍ |E|^{-2}` follows from `K_E(x,x) ≍ K_PW(x,x) = 1` and `φ'|E|² = πK_E(x,x)`; the project has it
     as `HEEqPW.phaseDeriv_mul_sq_ge`/`_le` (`HB/DeBranges.lean`).
   - What remains: `|E|² ∈ A₂(ℝ)` from the norm equivalence (necessity half of Hunt–Muckenhoupt–Wheeden, in
     Lyubarskii–Seip form); `log|E| ∈ BMO`; the representation `φ_E(x) − πx = −H̃[log|E|](x) + c` (Cartwright
     class, boundary theory in `ℂ₊`); conjugation on BMO.
   - The coupling of the third item cannot be bypassed: information on `φ'` alone, even `φ' ∈ A₂`, does not
     give BMO. Example: `v(t) = 1 + ½ sin log(1 + |t|)` is bounded above and below (so in `A₂`), but
     `∫_0^t (v − 1)` is `t` times an oscillating factor and is not in BMO. What forces BMO is that
     `log φ' = −2 log|E| + O(1)` and `φ − πx` are harmonic conjugates; asking for "`|E|²` comparable to a
     weight with bounded conjugate behaviour" is the hard direction of Helson–Szegő.
   - Route B also makes `PavlovBMO` conditional on `hC`, `hD`. Net cost at least 4–5k lines; 6–10k for
     route A is the right order. Replacing `hA` by a weaker `Prop` (the two-sided bound
     `osc_I h ≤ A log|I| + B`) would assume Landau-type estimates and empty the Claim; not recommended.
2. **Route A, step 6(ii) is wrong as justified (R7-18).** Exactly,
   `d/dx arg G(x + i) = −Σ_γ 1/((x − γ)² + 1) = −π P_1[dn_Γ](x)`, so `arg G(x + i) = −π P_1[n_Γ](x) + c` and
   `π n_Γ + arg G(x + i) = π(h − P_1[h]) + c`. The per-zero `O(1)` errors have a tail `~ Σ 1/(x − γ)`, a
   conditionally convergent Hilbert-type sum, not `O(1)`. The bound holds a posteriori once `h ∈ BMO`, so
   using it inside the proof is circular; this is why Theorem A is phrased with `P_1[h]`. Route A needs an
   extra lemma: for separated `Γ`, `P_1[h] ∈ BMO ⇒ h ∈ BMO`. Route B avoids the step (item 1). The weight
   sentence of step 3 ("`|G(x+i)|^{-2}`-type weight (the correct weight is `|G(x+i)|²` …)") is garbled and
   should be rewritten if route A is ever used.
