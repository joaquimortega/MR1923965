# P5 cardinal logarithmic inputs

Implemented in `FourierFrames/Cited/Pavlov/CardinalLog.lean`, importing the proved boundary-weight BMO,
BMO logarithmic integrability, and exact logarithmic Poisson-kernel modules. No `Unconditional` import.

For `d : CardinalData Γ` and `γ ∈ Γ`, the canonical functions are

```
q(z) = cardinal d.G γ z = dslope d.G γ z / deriv d.G γ,
A(z) = cardinalUpper d γ z = exp(I*π*z)*q(z),
v(t) = cardinalLog d γ t = log‖q(t)‖.
```

This uses the normalized cardinal, so `q(γ)=1`. Compared with an unnormalized dslope, the boundary logarithm
has the additional constant `−log‖G'(γ)‖`; that constant is included explicitly in every identity.

`CardinalData.cardinal_log_input d g hΓ hγ : CardinalLogInput d γ` bundles these proved fields:

- `memPW`, `real`, `at_node`, `zeros` for q;
- `upper_entire`, `upper_ne_zero`, `upper_bounded` for A;
- `boundary_norm` identifying A's real-axis modulus with q's;
- `log_G_integrable`, `log_q_integrable`, `log_upper_integrable`;
- `exp_sq_integrable : Integrable (fun t ↦ exp(2*cardinalLog d γ t))`;
- `log_identity : log‖G‖ =ᵐ[volume] v + log|t−γ| + log‖G'(γ)‖`.

The bundle takes separation and an existing grid, both already supplied by the Pavlov hypotheses. Its properties
are derived from proved cardinal identities; none is an additional assumption on complete interpolation.

The pointwise upper-half-plane identities needed by the final dispersion assembly are

```lean
log_generating_eq_cardinal_upper d hγ hz
-- log‖G z‖ = log‖q z‖ + log‖z−γ‖ + log‖G'γ‖

log_cardinalUpper_eq d hγ hz
-- log‖A z‖ = −π*z.im + log‖q z‖
```

`cardinalLog_eq_of_not_mem` and `log_generating_eq_cardinalLog_of_not_mem` give the corresponding real-axis
identities at every `t ∉ Γ`, and `cardinalLog_eq_ae`/`log_generating_eq_cardinalLog_ae` provide their a.e. forms.

Proof details: `deriv_fstar_ofReal` makes G's derivative real; the removable quotient then gives `fstar q=q`
pointwise, including at γ. The PW evaluation bound yields `‖A(z)‖² ≤ d.normBound` on the upper half-plane.
The logarithmic identity and `boundary_log_bmo` give weighted log integrability. PW supplies integrability of
`‖q‖²`; the identity `exp(2log‖q‖)=‖q‖²` is used only outside the countable zero set. Thus the totalized
real logarithm at a zero is never treated as that identity.

Validation: clean `lake build FourierFrames.Cited.Pavlov.CardinalLog`. The bundled input theorem and both
upper logarithm identities depend only on `propext`, `Classical.choice`, and `Quot.sound`.
