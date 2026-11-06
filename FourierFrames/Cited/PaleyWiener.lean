import FourierFrames.Cited.PaleyWiener.Part1
import FourierFrames.Cited.PaleyWiener.Part2

/-!
# P1 — the Paley–Wiener theorem (`FF.PaleyWienerThm`)

See `blueprint/P1_PaleyWiener.md`.  This file does not import `FourierFrames.PW.*` (whose lemmas
take `hPW`), only `Defs`, Mathlib and the vendored Bernstein library.
-/

open MeasureTheory Set Complex

namespace FF

/-- **The Paley–Wiener theorem** (with Plancherel), unconditional. -/
theorem paleyWiener_holds : PaleyWienerThm :=
  ⟨PW1.paleyWiener_part1, PW1.paleyWiener_part2⟩

end FF
