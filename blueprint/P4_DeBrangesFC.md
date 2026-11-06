# P4 — de Branges' Theorems C (book Thm 23) and F (book Thm 32)

**Lean file:** `FourierFrames/Cited/DeBrangesFC.lean` (compiles, only `sorry` warnings; ends with
`theoremC_holds : TheoremC`, `theoremF_holds : TheoremF`).
**Sources:** de Branges, *Hilbert spaces of entire functions* (1968), Thms 19, 23, 32;
Romanov, *Canonical systems and de Branges spaces* (arXiv 1408.6022), Appendix II = proof of the
direction of "Theorem 8" that is our `TheoremF` (his "⇒"); Remling's book for the kernel route to Thm 23.
**Depends on:** `Defs`; P3 `theoremD_holds : TheoremD` (Part F only; declared in an "Upstream interface"
section of the scaffold); project `HB/H2.lean` (H² mean value bounds, `not_isH2Upper_div_of_zero`).
Does **not** use `hPW`.  **Used by:** `Theorem1/Necessity` (`exists_E` uses `hC`, `exists_herglotz_data` uses `hF`).

Notation: `K(w,z) := ι(k w)(z)`; `E^*(z)=conj E(conj z)`; `Θ=E^*/E`; `UHP={Im z>0}`.
Convention of the project: `⟪x,y⟫` is conjugate-linear in `x`; `ι h ζ = ⟪k ζ, h⟫`.

---------------------------------------------------------------------------------------------------
## 0. Summary and honest feasibility

| | route | new infrastructure | est. size | verdict |
|---|---|---|---|---|
| **C** | reproducing kernel → explicit `E` → `H ↪ H(E)` isometric (dense kernels) → equality via reproducing property in `H(E)` | RKHS via `toDual` (in Mathlib); Cauchy formula / reproducing kernel of `H²(ℂ₊)` for `IsH2Upper` functions (**not** in Mathlib; partly in `HB/H2.lean`) | 2.5–4 k lines | feasible but large; no part of it simplifies for `PW` (the paper's only use) except that (H1)–(H3) are already proved (`samp_H1..3`) |
| **F** | Romanov's Appendix II (repaired): Herglotz transform `g` of `μ`, `Ξ=(g-1)/(g+1)`, `A = Ξ/Θ`; `|A| ≤ 1` by Blaschke division + Phragmén–Lindelöf | Herglotz transform (explicit, easy), factorization `Θ = e^{i(az+θ)}B` of a meromorphic inner function with Blaschke division (**big, absent from Mathlib**), kernel computations, Phragmén–Lindelöf (Mathlib has half-plane versions) | 5–8 k lines | feasible only as a long project; highest risk of the whole phase 2 list after `PavlovBMO` |

Special cases for the paper: `PW` with the sampling norm (C) and `μ=∑|E(λ)|²δ_λ` with `H(E)=PW` (F).
(a) For C nothing simplifies: one still needs the kernel/`H²` machinery.  (b) For F the measure is discrete
and separated, so local finiteness and the integrability (F.1) are trivial, but the factorization of
`Θ` and the Herglotz/Blaschke-division part are unchanged.  I see **no** substantially cheaper route to
`theorem1_necessity` without `hC, hF`; the sampling space would still need an `E` (Part C) and the
Herglotz datum (Part F).  If one had to cut, the only cheap special-case theorem is the *easy
converse* (Clark measures), which the paper does not need.

---------------------------------------------------------------------------------------------------
## 1. Part C (Theorem 23)

Let `H, ι` satisfy (H1)–(H3) and `H ≠ 0` (structure `DBAxioms`).

### C.1 `exists_kernel`
For `ζ` nonreal, `h ↦ ι h ζ` is a continuous linear functional (H2), so
`InnerProductSpace.toDual ℂ H` (Mathlib, `Mathlib/Analysis/InnerProductSpace/Dual.lean`) gives
`k ζ` with `ι h ζ = ⟪k ζ, h⟫`.  Choose `k` with `Classical.choose`/`choose` (value at real `ζ` is junk).

### C.2 `kernel_norm_pos`: `K(ζ,ζ)=‖kζ‖²>0`
`ι (k ζ) ζ = ⟪kζ,kζ⟫ = ‖kζ‖²`.  Suppose `kζ = 0`; then every `h ∈ H` vanishes at `ζ`.  Pick `h≠0`;
`ι h` is entire and not identically zero (injectivity), so has finite order `m≥1` at `ζ`
(`analyticOrderAt`).  (H1) gives `g` with `ι g = ι h·(z-ζ̄)/(z-ζ)` off `ζ`; `ι g` is entire, has order
`m-1` at `ζ` (the factor has a simple pole there, `ζ̄≠ζ`).  Iterate `m` times: an element with order 0,
i.e. nonvanishing at `ζ`, contradicting that all elements vanish.  (Lean: induction on `m` with the
statement "no nonzero element of order `m` exists".)

### C.3 `kernel_symm`: `K(w,z)=conj K(z,w)` — `ι(kw) z = ⟪kz,kw⟫ = conj⟪kw,kz⟫ = conj(ι(kz) w)`.

### C.4 `kernel_fstar`: `K(w,·)^* = K(w̄,·)`
By (H3) and injectivity there is a map `S : H→H`, `ι (S h) = (ι h)^*`; it is conjugate-linear (injectivity),
`‖Sh‖=‖h‖`, and `S∘S = id` (`f^{**}=f`).  By polarization `⟪Sx,Sy⟫ = conj⟪x,y⟫`.  Then
`ι h w̄ = conj (ι (Sh) w) = conj⟪kw,Sh⟫ = ⟪S h, kw⟫ = ⟪S kw, SS h⟫... = ⟪S kw, h⟫`
(using `⟪Sh,y⟫ = conj⟪SSh,Sy⟫ = ⟪Sy,h⟫`), so `k w̄ = S(kw)`, i.e. `ι(k w̄) = (ι(kw))^*`.
In particular `K(w̄,w̄)=K(w,w)` (`‖Sx‖=‖x‖`).

### C.5 `kernel_identity` (the key identity, from (H1))
Fix `ζ` nonreal, `H_ζ={h: ι h ζ=0}=(kζ)^⊥` (closed hyperplane by C.2), `T:H_ζ→H`, `ι(Th)=ι h·(z-ζ̄)/(z-ζ)`
(well defined by (H1)+injectivity, linear, isometric).  `T(H_ζ)=H_ζ̄`: `⊆` since `(Tf)(ζ̄)=0`; `⊇` apply
(H1) at `ζ̄` (inverse factor).  Reproducing kernels of the hyperplanes:
`k^ζ_w = k w − (K(w,ζ)... )` more precisely the orthogonal projection of `k w` onto `(kζ)^⊥` is
`k w − ⟪kζ,kw⟫/‖kζ‖² · kζ`, whose function is `K(w,z) − K(ζ,z)K(w,ζ)/K(ζ,ζ)`.
For `f∈H_ζ`: `(Tf)(w) = ⟪k^ζ̄_w, Tf⟫` and also `= (w-ζ̄)/(w-ζ)·⟪k^ζ_w,f⟫`; since `T` is a unitary
`H_ζ→H_ζ̄`, `T^*k^ζ̄_w = conj((w-ζ̄)/(w-ζ))... ` yielding
`(z-ζ̄)(w̄-ζ) k^ζ_w(z) = (z-ζ)(w̄-ζ̄) k^ζ̄_w(z)` — exactly the Lean statement (multiplied form avoids the
singularities `w=ζ`, `z=ζ`).  Lean tip: prove the identity as equality of vectors `T(k^ζ_w) ·(...) = k^ζ̄_w ·(...)`
via `Submodule.orthogonalProjection` (`Submodule.starProjection`) and `LinearIsometry`.

### C.6–C.8 `kernelE`, formula (1), `E∈HB`
Solve the identity for `K(w,z)` with `ζ=i`: the bracket `(z-ζ̄)(w̄-ζ)-(z-ζ)(w̄-ζ̄)=(ζ-ζ̄)(w̄-z)`, so
`K(w,z) = (i/2)[P(z)conj P(w) − Q(z)conj Q(w)]/(z-w̄)` with
`P(z)=(z+i)K(i,z)/√K(i,i)`, `Q(z)=(z-i)K(-i,z)/√K(-i,-i)`; using `K(i,i)=K(-i,-i)` and C.4, `Q=P^*`
(because `(K(i,·))^*=K(-i,·)` and `(z+i)^*=z-i`).  Put `E=√π P` (this is `kernelE`): `K=(i/2π)(E Ē − E^*Ē^*)/(z-w̄)`,
which is `deBrangesKernel` off `z=w̄` (**checked** against `E=e^{-iπz}`, `H=PW`: gives `sin π(z-w̄)/(π(z-w̄))`).
`E` is entire (`ι(k i)` entire).  For `w∈ℂ₊`: `K(w,w)=(|E(w)|²−|E^*(w)|²)/(4π Im w)>0` by C.2, so
`|E^*(w)|<|E(w)|`, hence `E(w)≠0`: `E∈HB` (even strict inequality).

### C.9 `kernel_gram`
For `w∈ℂ₊`, `E(t)^{-1}K(w,t) = (i/2π)(Ē(w) − Ē^*(w)Θ(t))/(t − w̄)` on `ℝ` (`E^*(t)=Ē(t)`).  Write `φ_w=1/(z-w̄)`.
Facts about `H²(ℂ₊)` needed (**to be proved**, from `HB/H2.lean`):
(H²-a) for `g∈H²` (`IsH2Upper`) and `w∈ℂ₊`: Cauchy formula `g(w) = (1/2πi)∫_ℝ g̃(t)/(t-w) dt` where `g̃` is the boundary
function (here `g` extends continuously/meromorphically across `ℝ`, so `g̃(t)=g(t)` where defined: proof by Cauchy on the
line `Im=ε`, `ε↓0`, using the `H²` pointwise decay `|g(x+iy)|²≤C/y` from `IsH2Upper.enorm_sq_le`).
(H²-b) `⟨φ_w, φ_v⟩_{L²} = ∫dt/((t-w̄)(t-v)) = 2πi/(v-w̄)` (residues / Cauchy for `φ`).
(H²-c) `Θ` bounded by 1 on `ℂ₊`, unimodular on `ℝ` (E strict, no real zeros) or `|Θ|≤1` a.e.; and
`⟨Θ φ_w, φ_v⟩ = Θ(v)... ` : by (H²-a) applied to `Θ φ_w ∈ H²`: `∫ Θ(t) φ_w(t) conj φ_v(t) dt` is the Cauchy formula for the
`H²` function `Θφ_w` at `v` (`conj φ_v = 1/(t-v)`), `= 2πi Θ(v)/(v-w̄)`.
Expanding the product gives `∫K(v,t)conj K(w,t)|E|^{-2}dt = (1/4π²)Ē(v)... [..]` and, after the four terms
`1, Θ(v)Θ̄(w)... ` are evaluated with (b),(c) (and `∫ Θ̄ φ_wφ̄_v`, handled by conjugation), equals `K(v,w)`.
(The computation is the usual proof of Thm 19; **do it once for general `E`∈closed HB**, it is also what P3 needs.)
Membership `K(w,·)∈H(E)`: `K(w,·)/E ∈ H²` (the above formula with `|Θ|≤1`: `(a-bΘ)φ_w`),
`K(w,·)^*/E = K(w̄,·)/E = (i/2π)(E^*(w)... )/(z-w)` — **removable singularity at `z=w`** (numerator vanishes there) and
the quotient is `H²` (numerator `bounded holomorphic vanishing at w` divided by `z-w`; elementary: `(a-bΘ(z))/(z-w)` with
`a-bΘ(w)=0`, split `= -b(Θ(z)-Θ(w))/(z-w)` and use Schwarz-type bound `|Θ(z)-Θ(w)|/|z-w|` ≤ `C/|z-w̄|` (Schwarz–Pick on the half-plane; or
avoid: use `|Θ(z)-Θ(w)|≤2` for `|z-w|≥1`, and Cauchy estimate near `w`).)

### C.10 `range_subset` (isometry on all of `H`)
The map `V: span{k w : w∈ℂ₊} → L²(ℝ,dt)`, `Σc_j k_{w_j} ↦ Σ c_j... K(w_j,·)/E` preserves inner products (C.9).
Density of the span in `H`: `f⟂kw ∀ w∈ℂ₊` ⇒ `ι f=0` on `ℂ₊` ⇒ `ι f=0` (identity theorem) ⇒ `f=0`.
For `h∈H` take `h_n→h`, `h_n` in the span. `ι h_n/E` is Cauchy in `H²`; limit `G∈H²`; (H2) gives `ι h_n(z)→ι h(z)`, and `H²`
point evaluation is continuous (`IsH2Upper.enorm_sq_le`), so `G=ι h/E` on `ℂ₊`.  Same for `(ι h)^*` using `S h_n` (C.4). Hence `ι h∈H(E)`;
`heNormSq=lim ‖h_n‖²=‖h‖²` (the boundary function of `G` is `(ι h)(t)/E(t)` a.e. because `ι h /E` is meromorphic across `ℝ`; if `E` has real zeros
`ι h` vanishes there since `ι h/E∈H²` — `not_isH2Upper_div_of_zero` in the project).
**Real zeros of `E` occur** (e.g. `H={f∈PW: f(0)=0}`): so TheoremD (strict, no real zeros) cannot be used; C.9–C.11 must be proved for the
closed class, using only kernels at nonreal points.

### C.11 `reproducing_HE`, C.12 `range_eq`
For `f∈H(E)`, `w∈ℂ₊`: `⟨f/E, K(w,·)/E⟩_{L²} = f(w)`: from (H²-a) applied to `f/E` against `φ_w` and to `f^*/E` against `Θφ`-term:
`⟨f/E,K_w/E⟩ = (1/(−2πi))... [ E(w)^{-1}f(w)Ē... ]`; the `Θ`-term is `⟨f/E, Θ φ_w⟩ = ⟨Θ̄ f/E, φ_w⟩ = ⟨f^*/E̅...⟩`:
use `Θ̄ f/E = conj(f^*... )` i.e. `conj(f/E)·Θ = conj(f^*/E)` on `ℝ`, and `f^*/E∈H²` has boundary function whose Cauchy integral against `φ_w` vanishes
for `w∈ℂ₊`?? — **correct bookkeeping**: `⟨f/E,Θφ_w⟩=∫(f/E)conj(Θ)... = ∫ (f^{*}/E)^{bar}`...; this is the standard identity of de Branges' Thm 19; the term equals `0`
because `conj(f^*/E)` is the boundary function of an `H²` function of the lower half-plane, orthogonal to `φ_w∈H²(ℂ₊)`.  Then `f(w)` is obtained.  (**Implementer: verify the bookkeeping in the 4-term expansion;
this is the single computation behind C.9, C.11 and `TheoremD`.**)
C.12: let `f∈H(E)`; `ι(H)` is closed in `H(E)` (complete, isometric), project: `f=ι h+r`, `r∈H(E)`, `r ⟂ ι(H)`. By C.11, `r(w)=⟨r,K_w⟩_E=0` for all `w∈ℂ₊` (`K_w=ι(k w)∈ι(H)`), so `r=0`. (Needs `H(E)` as an inner product space: define via `heNormSq`/L² inner product of boundary functions; or avoid by the formula
`⟨r,ι(kw)⟩_E=r(w)`, `⟨ι h,r⟩_E...` hmm — implement with the explicit sesquilinear form `∫ (f/E)conj(g/E)`.)

### `theoremC_holds`
`obtain k := exists_kernel`; take `E := kernelE ι k`; `IsHB` (C.8); `∀ f, MemHE E f ↔ f∈range ι` (`range_subset`, `range_eq`); norm identity (`range_subset`).

---------------------------------------------------------------------------------------------------
## 2. Part F (Theorem 32)

Hypotheses: `E` strict, no real zeros; `μ` with `∫⁻‖f/E‖²dμ = ‖f‖_E²` on `H(E)` (`IsIsometricMeasure`).  Conclusion with `p=0`.

### F.1 `isometric_moment`
Apply the isometry to `f=K(i,·)∈H(E)` (TheoremD).  `|K(i,t)/E(t)|² = (1/4π²)|Ē(i)−Ē^*(i)Θ(t)|²/(t²+1)` and `|Θ(t)|=1` (`|E^*(t)|=|E(t)|` on `ℝ`), so
`≥ (|E(i)|−|E^*(i)|)²/(4π²(1+t²))`, `|E(i)|>|E^*(i)|`.  Hence `∫dμ/(1+t²)≤ C·‖K_i‖²<∞`.  Also `μ` is locally finite (not needed).

### F.2 `herglotzG_spec`
`g(z)=−(i/π)∫(1/(t−z) − t/(1+t²))dμ(t)+ic`.  Integrand bounded by `C_z/(1+t²)`, locally uniformly in `z`; holomorphy of parameter integrals
(Mathlib `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, or Morera + Fubini).
`Re(−i/(π(t−z)))=y/(π|t−z|²)`; the second term contributes a purely imaginary number.  So `Re g = poissonInt μ z`
(finite by F.1).  *Only the real part of the Herglotz representation is used; no uniqueness theorem for positive harmonic functions is needed.*

### F.3 `cauchy_pairing_zero` (Romanov (67))
For `w,v∈ℂ₊` with `E^*(w)=E^*(v)=0`: `K(w,t)/E(t)=(i/2π)Ē(w)/(t−w̄)` (no `Θ`-term).  Isometry polarised (TheoremD: `⟨K_v,K_w⟩_E=K(v,w)`):
`(1/4π²)Ē(v)E(w)∫dμ/((t−v̄)(t−w)) = K(v,w) = (i/2π)E(w)Ē(v)/(w−v̄)`, hence the Lean statement `∫dμ/((t−v̄)(t−w)) = 2πi/(w−v̄)`.
(Integrability: Cauchy–Schwarz and F.1.)  Consequence with `1/((t−v̄)(t−w))=(1/(w−v̄))(1/(t−w)−1/(t−v̄))`:
`g(w)+conj g(v) = 2` for the Herglotz transform `g` (with constant `c=0`), i.e. `Re g(w)=1`, `Im g(w)=Im g(v)` on `Z={Θ=0}`.

### F.4 `cauchy_pairing_general`
Pair `K(w₀,·)` (`w₀∈Z`) with `K(z,·)`, `z∈ℂ₊`: `K(z,t)/E(t)=(i/2π)(Ē(z)−Ē^*(z)Θ(t))/(t−z̄)`; the `Θ`-term is bounded in modulus by
`|Ē^*(z)|·(∫dμ/|t−w̄₀|²)^{1/2}(∫dμ/|t−z|²)^{1/2}` and `∫dμ/|t−z|²=πP[μ](z)/y` with `P≲1`.  Dividing by `Ē(z)` (`|Ē^*(z)/Ē(z)|=|Θ(z)|`) gives the stated error `C|Θ(z)|/√y` (use F.5 for `P(z)≤2`).

### F.5 `poisson_diag_estimate`
Isometry on `K(z,·)`: `‖K_z‖²=K(z,z)=(|E(z)|²−|E^*(z)|²)/(4π y)` and
`∫|K(z,t)|²|E|^{-2}dμ=(1/4π²)|E(z)|²∫|1−Θ̄(z)Θ(t)|²dμ/|t−z̄|²` with `|1−Θ̄(z)Θ(t)|∈[1−s,1+s]`, `s=|Θ(z)|`.  With `∫dμ/|t−z̄|²=πP(z)/y`:
`(1−s)²P ≤ 1−s² ≤ (1+s)²P`... i.e. `(1−s)/(1+s) ≤ P(z) ≤ (1+s)/(1−s)`, so `|P−1|≤4s` for `s≤1/2`.

### F.6 `exists_imag_limit`
`u=Re g−1`, `|u|≤Ce^{−ay}` on `y≥1`.  Cauchy estimates for harmonic derivatives: `|∇u(z)|≤C'e^{−a'y}` on `y≥2` (mean value on the disc of radius 1, `a'<a`).  By Cauchy–Riemann `|∂_y Im g|=|∂_x u|`, `|∂_x Im g|=|∂_y u|`, both `≲e^{−a'y}`.  So `Im g(x+iy)` converges as `y→∞` to some `c` independent of `x` and
`|Im g−c|≲e^{−a''y}`.  (Romanov's "locally uniform in `Re w`" suffices; the version here assumes uniform estimates, which F.5 gives since `|Θ(z)|≤e^{−ay}` uniformly in `x`.)

### F.7 `inner_factorization` (**the hard analytic lemma, not in Mathlib**)
`Θ` is holomorphic on `ℂ₊`, `|Θ|≤1`, continuous on a neighbourhood of `ℝ` with `|Θ|=1` there (no real zeros of `E`).  Claim `Θ=e^{i(az+θ)}B`, `a≥0`, `B` Blaschke product of the zeros of `Θ` (the zeros of `E^*` in `ℂ₊`).
Proof outline: (i) Blaschke condition `∑ Im z_j/(1+|z_j|²)<∞` from boundedness: Jensen on discs/Carleman's formula for the half-plane (Mathlib has `JensenFormula` for discs; map half-plane to disc by Cayley, `Mathlib/Analysis/Complex/UpperHalfPlane`).
(ii) The product `B` converges (standard), `|B|≤1`, `Θ/B` zero-free holomorphic with `|Θ/B|≤1` (finite partial products and maximum principle/PL, as in (iii)).
(iii) `log|Θ/B|` is a non-positive harmonic function on `ℂ₊` with boundary values `0` on `ℝ` (continuity of `Θ` and `|B|→1` at the boundary away from accumulation... careful: `B` has no accumulation on `ℝ` since `Θ` is analytic/unimodular near `ℝ`, so zeros are discrete and bounded away from compacts... needs an argument).  A non-positive harmonic function on `ℂ₊` vanishing on `ℝ` is `−a y` (Herglotz/Poisson representation with zero boundary measure — **or** reflect across `ℝ` using Schwarz reflection (harmonic function vanishing on a line extends oddly), then Liouville for harmonic functions with a one-sided bound: `Mathlib/Analysis/Complex/Harmonic/Liouville.lean`).  This reflection trick avoids Herglotz and is the recommended route.  So `Θ/B=e^{−ay+i(\ldots)}=e^{i(az+θ)}`.
Blaschke division (second conjunct): if `Ψ` bounded by `M`, vanishing on zeros of `B` with multiplicity, then `|Ψ|≤M|B|`: for finite sub-products `B_n`, `Ψ/B_n` is holomorphic and `limsup |Ψ/B_n|≤M` at the boundary and at `∞` (the finite Blaschke product is unimodular on `ℝ`, tends to a unimodular limit at `∞`) — maximum principle in `ℂ₊` for bounded functions (Phragmén–Lindelöf, `Mathlib/Analysis/Complex/PhragmenLindelof.lean` has half-plane versions); let `n→∞`.
Orders: `analyticOrderAt`.

### F.8 `division_lemma`
`Ξ_1=Ξe^{−ia'z}` is bounded on `ℂ₊` (by `max(C,e^{a'})`: use `|Ξ|≤1` on `0<y<1`, decay on `y≥1`), vanishes with multiplicity where `Θ` does, so by F.7 `|Ξ_1|≤C_1|B|`, i.e. `|Ξ|≤C_1e^{−a'y}|B|=C_1 e^{(a−a')y}|Θ|`.  Thus `Ψ=Ξ/Θ` (holomorphic: removable singularities at zeros of `Θ`) satisfies `|Ψ|≤C_1e^{(a-a')y}` on `ℂ₊`, and
`limsup |Ψ(z)|≤1` at every real point (`|Ξ|≤1`, `|Θ|→1`).  Apply Phragmén–Lindelöf (bounded version) to `Ψe^{iεz}` with `ε=a−a'`: `|Ψ|≤e^{εy}`; let `ε→0`: `|Ψ|≤1`.

### F.9 Assembly (`theoremF_holds`)
Let `Z={z∈ℂ₊: Θ(z)=0}={zeros of E^*}`; `a` from F.7.  Let `g_0=herglotzG μ 0`.
* **Case `a>0`.**  By F.5 (note `|Θ(z)|≤e^{−ay}`), `|Re g_0−1|≤4e^{−ay}` for `y≥y_0`; F.6 gives `c`, `|g_0−1−ic|≲e^{−a'y}`.  If `Z≠∅`: F.4 and the Herglotz formula give for `w₀∈Z`: `g_0(z)+conj g_0(w₀)→2` as `y→∞`, so `g_0(w₀)=1+ic`: **the constant `c` from decay and the constant from `Z` agree** (this repairs a gap in Romanov: he fixes the constant by decay and claims `Ξ(z)=0` on `Z` from `Re g=1` alone).  For zeros of order `m>1` use the same pairings for the derivative kernels `∂_{w̄}^jK(w,·)` (reproducing property of derivatives; `⟨f,∂^jK_w⟩=f^{(j)}(w)`) — **sketch only, to be checked**.
* **Case `a=0`.**  `Θ=e^{iθ}B`, `Z` is then infinite and `Re g_0=1` on `Z` (F.3); F.3 shows `Im g_0` is the same constant `c_Z` on `Z`, choose `c=−c_Z`... (`Z≠∅` since `Θ` nonconstant by strictness).  No decay is needed: `Ξ/B` is bounded by 1 by Blaschke division, `hdec` is vacuous (`a'<0`... the division lemma with `a=0` follows from F.7 directly with `M=1`).
Set `g=g_0−ic`, `Ξ=(g−1)/(g+1)` (`Re g>0` so `g+1≠0`, `|Ξ|<1`), `A:=Ξ/Θ` (zero set: removable).  By F.8 `|A|≤1`.  `1−ΘA=1−Ξ=2/(g+1)≠0`, `(E+E^*A)/(E−E^*A)=(1+ΘA)/(1−ΘA)=(1+Ξ)/(1−Ξ)=g`,
so `Re(...)=Re g=poissonInt μ z` (F.2) with `p=0`.  `A` is `DifferentiableOn` `UHP`.

---------------------------------------------------------------------------------------------------
## 3. Mathlib / project inventory

* Present in Mathlib: `InnerProductSpace.toDual`, orthogonal projection, `Complex.analyticOrderAt`, Phragmén–Lindelöf (`Analysis/Complex/PhragmenLindelof`), Liouville for harmonic functions (`Harmonic/Liouville`), `Poisson.lean` (Poisson integral formula for **discs** only — no half-plane Poisson kernel, no Herglotz measure representation, no Blaschke products/inner–outer factorization, no `H²(ℂ₊)` Cauchy/Plancherel theory), parametric holomorphic integrals.
* In project: `HB/H2.lean` (`IsH2Upper` closure, pointwise bound `enorm_sq_le`, `not_isH2Upper_div_of_zero`), `Theorem1/Necessity` (`samp_H1`, `samp_H2`, `samp_H3`: exactly the hypotheses of Theorem C for the sampling space; Herglotz-type series).
* Missing (must be written): `H²(ℂ₊)` Cauchy formula + boundary identification (used by C.9, C.11, F); Blaschke products with convergence, Blaschke division, factorization of meromorphic inner functions (F.7); harmonic derivative estimates (F.6).

## 4. Issues in the source / the statements
1. **Romanov, App. II (⇒)** (the proof we follow): "`Re g=1` at a zero of `S` implies `Ξ(z)=0`" needs `Im g=0` there; the imaginary constant is claimed to be fixed by two incompatible requirements (zeros, decay); compatibility is a genuine step (F.4/F.9 above).  Also multiplicities ("easy") are not proved.  Also "`w` a root of `W`" should read root of `W^*` in the upper half-plane (his `W` is HB).  Confidence: high for the first point, medium for the multiplicity gap being real.
2. Romanov's theorem has `c_0≥0` only in the converse; in our direction `p=0` always, so the `p` of `TheoremF` is slack (kept as stated, supply `p=0`).
3. `TheoremC`: statement true; note the conclusion cannot require `E` without real zeros (example `{f∈PW: f(0)=0}`); the project already uses closed `IsHB`.  The `E` produced is even strict on `ℂ₊`.
4. `TheoremF` needs `TheoremD` (P3) for `K(w,·)∈H(E)` and its reproducing property; hence P4-F imports P3's `theoremD_holds`.  (No cycle: D does not use F.)
5. Constant check: with `K` in the norm of `H` and `‖f‖²_E=∫|f/E|²`, `E=√π P` (not `P`), verified on `PW`.

## 5. Risks
* F.7 (factorization of a meromorphic inner function) is the largest single missing piece; if too costly, prove only the special case needed: `E` of exponential type/Paley–Wiener (then `Θ=e^{2πiz}B` could be obtained from the explicit structure of `E` from Part C in the paper's application, but this is **not** the general statement).
* Multiplicity-`>1` zeros of `Θ` in F.9 (derivative kernels): unchecked.
* C.9/C.11: the four-term `H²` bookkeeping must be done carefully (shared with TheoremD).
* If a Lean implementer must cut: do Part C (3–4 k lines, moderate risk) and leave `hF` as a hypothesis.
