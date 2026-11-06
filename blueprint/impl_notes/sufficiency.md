# Implementation notes: `sufficiency` (M04 Theorem 1 sufficiency; Corollary 1 and Landau by fork, see `sufficiency_cor1_landau.md`)

## Files
- `FourierFrames/Theorem1/Sufficiency/Interlace.lean`: `phaseLevel_sepBy_two_aux` (the statement in `Sufficiency.lean` is proved by it).
- `.../Limit.lean`: `levelSet_limit_aux` (+ finite-sum helpers, copy `sampleSum_split_aux`).
- `.../LevelSet.lean`: `levelSet_ineq_aux`, `levelSet_data_aux`, `levelSet_separated_aux`, `levelSet_cis_aux`.
- `.../Phase.lean`: `phase_tendsto_aux`, `phase_mul_bijective_aux`, translation/tail helpers.
- `.../RealFactor/*.lean`: Weierstrass product of variable genus for `exists_realFactor`.

## Deviations from the blueprint
- Aux lemmas are stated with `MemHE E (sAlpha E α)` instead of `Exceptional E α` (the two are defeq; `Exceptional`
  is defined in `Sufficiency.lean`, which imports the aux files).
- Added `Suff.exists_not_exceptional` (a non-exceptional `α` exists for strict `E`); `phase_tendsto` and
  `phase_mul_bijective` take it as a hypothesis in their aux versions.
- `levelSet_limit`: the tail lemma `plancherelPolya_tail_union` gives `η` directly for the union `A ∪ B`, so the
  final bound is `C₀ (T + 2η)` (not `3η`); the limit `η → 0` is taken along `η_m = (m+1)⁻¹` in `ℝ≥0∞`.
- `levelSet_separated`: separation constant `1/(Θ+1)`, `Θ = sqrt((π e)² max(K,0))`, `K = π/(c₁ c)`.
- `phase_tendsto` does not index by `ℤ`; it uses `translate_lower_bound_aux` (norm identity for translates
  of `pwBump`) and `translate_tail`, and bounded-above-ness of `Γ` from finiteness of `Γ ∩ {φ ∈ [a,b]}`.
- `exists_noRealZero_hb`: the hypothesis `hEHB` is unused (frozen statement); silenced by `have _ := hEHB`.
- `exists_realFactor`: variable genus `p_a = m_a + rank(a) + 1`, `rank` an injection of the real zero set into `ℕ`
  (advisor suggestion), instead of `p_x ≥ m_x + |x|` (which needs a separation hypothesis).
- Commit trailers: IMPLEMENTING.md asks for `Claude Opus 5.5`; the session reminder says `Claude Sonnet 5.5`. The
  early commits on this branch lack trailers.
