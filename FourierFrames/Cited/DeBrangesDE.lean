import FourierFrames.Cited.DeBrangesDE.Complete
import FourierFrames.Cited.DeBrangesDE.Space

/-!
# P3 — de Branges' Theorems D and E (phase 2)

Main results `theoremD_holds : TheoremD` and `theoremE_holds : TheoremE`.  See
`blueprint/P3_DeBrangesDE.md` for the full proof plan; the work is in the subfiles

* `Cited/DeBrangesDE/Cauchy.lean` — Cauchy/Poisson formulas for `H²(ℂ₊)` (no boundary theory),
* `Cited/DeBrangesDE/Kernel.lean` — the kernel and the reproducing formula (Theorem D),
* `Cited/DeBrangesDE/Space.lean` — `H(E)` as a Hilbert space (evaluation bound, completeness),
* `Cited/DeBrangesDE/EntireHerglotz.lean` — an entire Pick function is linear,
* `Cited/DeBrangesDE/Orthogonal.lean` — the system `{K(γ,·)}`, the entire function `h = D/S`,
* `Cited/DeBrangesDE/Complete.lean` — completeness and the norm identity (Theorem E).

The two assembly proofs below are complete modulo the `sorry`s of the subfiles.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace FF

/-- **Theorem D** (de Branges [dB68, Theorem 19]): the reproducing kernel of `H(E)`. -/
theorem theoremD_holds : TheoremD := by
  intro E hE h0 w
  exact ⟨memHE_deBrangesKernel hE h0 w, fun f hf ↦ heInner_kernel hE h0 hf w⟩

/-- **Theorem E** (de Branges [dB68, Theorem 22]): orthogonal sampling on `Γ = {φ ∈ α + πℤ}`. -/
theorem theoremE_holds : TheoremE := by
  intro E hE h0 φ hφ α hα
  have D : DBData E φ := ⟨hE, h0, hφ⟩
  exact ⟨fun f hf ↦ theoremE_norm D hα hf, fun a ha ↦ theoremE_interp D a ha⟩

end FF
