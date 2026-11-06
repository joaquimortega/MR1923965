# Implementation notes: `construction` (M07 §2 construction, `Lemma3Uniform`)

Files: `FourierFrames/Construction.lean`, `FourierFrames/Lemma3Uniform.lean`, and aux files
`FourierFrames/Construction/{Gaps,Comparable,PolyHB,Limits,Rigidity,Translate}.lean`.
All statements of the scaffold are proved (no `sorry` in these files); the only `sorry`s reached are
upstream M01/M02 black boxes (`HB/Basic.lean`, `HB/Phase.lean`).  No statement was changed.

## Deviations from the blueprint (proof routes)
* `lemma3_estimate_uniform`: the proof of `OCS.exists_abs_sum_multErr_sub_log_infDist_le` is copied
  (as `exists_abs_sum_multErr_sub_log_infDist_le_uniform`) with the constants
  `K₁, K₂, K₃` fixed from `(a, b)` before `m` is introduced; then the proof of `multF_estimate_two`.
* `norm_compB_comparable` avoids any local analysis at the zeros of `A`/`B`: it uses (i) `B = A₁ P/Q`
  for `|z| ≥ ρ₀`, (ii) a general compactness lemma (`Comparable.comparable_on_compact`: an entire
  function with simple zeros satisfies `c₁ min(1,d(z,Z)) ≤ |F| ≤ c₂ min(1,d(z,Z))` on compacts) applied
  to `B` and `A(·-1/2)`, which also gives `e^{U(z-1/2)}` bounded above and below on compacts off
  `Γ+1/2`; the finitely many points of `(Γ+1/2) ∩ K` need only that `U` is real valued.  No continuity
  of `U` is used (it is not available upstream of `Construction`).
* `exists_hb_of_density` / `_phase`: the choice of `N` uses a stronger gap index
  (`Gaps.exists_gap_index_strong`: gap `> 3/4`) so that `dist(Γ, Γ_B) ≥ η > 0` (`exists_eta`).
* `isHB_compE`, `isHB_compEκ`: both follow from `isHB_genA_sub_lam_compB` (`A - i λ B ∈ HB̄` for every
  `λ > 0`), via the sequence `R = k + N` and `IsHB.of_tendstoLocallyUniformly`.
* `tendsto_polyB`: removal of `Q` via `Limits.tendstoLU_of_mul_prod` (maximum modulus on a large circle).
* `phase_levels`: strictness of the phase via `IsHB.isStrictHB_or_fstar_eq` (E_κ has real zeros of
  `E+E^*`, so `E^* = cE` is impossible) and `IsPhaseFunction.strictMono_of_isStrictHB`;
  `phase_rigidity` via the abstract `Rigidity.phase_drift_small` (IVT argument) and the limit
  `E_κ(z+s_k) → i c e^{-iπ(z-θ)}` (`tendsto_compEκ_translate`).
* `genA_translate_limit` is `Translate.translate_limit` (proved by a fork; the nonvanishing of the
  limit uses a fixed point `θ + 1/2`, and the identification uses `sin_lower` + a removable-singularity
  + Liouville argument).

## Source issues
None found beyond those of R4 (F1–F3 already applied).  The proof confirms the `e^{κ/2}` rescaling:
`λ e^{-κ/2} = 1` is exactly what makes `E_κ(z + s_k) → i c e^{-iπ(z-θ)}` (unit amplitude ratio).

## Upstream dependencies used as black boxes
`IsHB.of_tendstoLocallyUniformly`, `IsHB.isStrictHB_or_fstar_eq`, `IsHB.norm_fstar_le`,
`exists_isPhaseFunction`, `IsPhaseFunction.re_eq`, `IsPhaseFunction.strictMono_of_isStrictHB`,
`IsHB.mul` (all M02).
