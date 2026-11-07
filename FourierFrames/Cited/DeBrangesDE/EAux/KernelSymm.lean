import FourierFrames.Cited.DeBrangesDE.Space

/-!
# P3 (Theorem E) — Hermitian symmetry of the kernel, self-contained copy

`Kernel.lean` (owned by the Theorem D implementer) states `conj_deBrangesKernel`; its signature
changes between versions (the hypothesis `Differentiable ℂ E` was dropped).  To be independent of
that interface, the files of Theorem E use this self-contained copy, valid for every `E`.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace FF

/-- Hermitian symmetry `conj K(w, z) = K(z, w)`, for every `E : ℂ → ℂ`. -/
theorem deBrangesKernel_conj_symm (E : ℂ → ℂ) (w z : ℂ) :
    conj (deBrangesKernel E w z) = deBrangesKernel E z w := by
  unfold deBrangesKernel
  by_cases hz : z = conj w
  · have hw : w = conj z := by rw [hz, Complex.conj_conj]
    rw [ite_eq_left hz, ite_eq_left hw]
    subst hz
    rw [deriv_fstar, deriv_fstar]
    simp only [map_mul, map_sub, map_div₀, Complex.conj_I, Complex.conj_ofReal,
      Complex.conj_conj, fstar, map_ofNat]
    ring
  · have hw : w ≠ conj z := by rintro rfl; exact hz (Complex.conj_conj z).symm
    rw [ite_eq_right hz, ite_eq_right hw]
    have h1 : z - conj w ≠ 0 := sub_ne_zero.mpr hz
    have h2 : w - conj z ≠ 0 := sub_ne_zero.mpr hw
    have h3 : conj z - w ≠ 0 := by
      intro h; apply h2; rw [← neg_eq_zero, neg_sub]; exact h
    simp only [map_mul, map_sub, map_div₀, Complex.conj_I, Complex.conj_ofReal,
      Complex.conj_conj, fstar, map_ofNat]
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring

end FF
