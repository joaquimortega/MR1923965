# Vendored Tau Ceti modules

These Lean modules are copied unchanged from
[TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti), release `v4.35.0`,
commit `1f9b4414105d86e487a4ac4c3d3397076a44d0d2`. Copyright headers are preserved;
the upstream Apache-2.0 license is included as `LICENSE`.

The upstream release uses Lean `v4.35.0` and Mathlib commit
`074063781836922cb02701cd12943c9f51731afa`. This project uses Lean `v4.35.0` and
Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The modules are the complete TauCeti import closures of:

- `TauCeti.MeasureTheory.Integral.CalderonZygmund.BoundedMeanOscillation`;
- `TauCeti.Analysis.Fourier.L2Multiplier`;
- `TauCeti.Analysis.PDE.Harnack.Basic`;
- `TauCeti.Analysis.PDE.PoissonIntegral.Ball`;
- `TauCeti.Analysis.InnerProductSpace.Laplacian.Comparison`;
- `TauCeti.Analysis.Complex.BranchLogRoot`.

The vendor contains 41 Lean modules and 8882 lines, including comments and blank lines.
The full file list is recorded below.

The upstream package uses Lean's default `autoImplicit=true` and `relaxedAutoImplicit=true`.
This project scopes those options to the `TauCeti` Lake library, preserving the settings
for its own `FourierFrames` library.

All modules compiled unchanged against this project's pinned Mathlib on 2026-11-07.
Axiom audits of
`ContinuousLinearMap.setLAverage_enorm_sub_setAverage_le_of_hormander` and
`MeasureTheory.Lp.norm_fourierMultiplierCLM_le` report only `propext`,
`Classical.choice`, and `Quot.sound`. No dependency on another external library is introduced.

The BMO endpoint theorem assumes an operator already bounded on `L²`, together with an
off-support integral representation and a first-variable Hörmander bound. It controls
`L² ∩ L∞` inputs; it does not itself extend the operator to every BMO function.
The multiplier module supplies `L²` boundedness but does not supply the classical Hilbert
kernel realization. Those bridges belong to the project, rather than these unchanged files.

## Module inventory

- `TauCeti/Analysis/Calculus/ContDiff/Translation.lean`
- `TauCeti/Analysis/Calculus/DerivativeTest.lean`
- `TauCeti/Analysis/Calculus/FDeriv/ContinuousLinearMap.lean`
- `TauCeti/Analysis/Calculus/FDeriv/Prod.lean`
- `TauCeti/Analysis/Calculus/ParametricIntegral.lean`
- `TauCeti/Analysis/Calculus/SecondDerivative.lean`
- `TauCeti/Analysis/Calculus/TaylorIntegral.lean`
- `TauCeti/Analysis/Complex/BranchLogRoot.lean`
- `TauCeti/Analysis/Distribution/DuBoisReymond.lean`
- `TauCeti/Analysis/Distribution/SchwartzSpace/Convolution.lean`
- `TauCeti/Analysis/Distribution/TestFunction/LineDeriv.lean`
- `TauCeti/Analysis/Fourier/L2Multiplier.lean`
- `TauCeti/Analysis/InnerProductSpace/CompleteSquare.lean`
- `TauCeti/Analysis/InnerProductSpace/Euclidean/Space.lean`
- `TauCeti/Analysis/InnerProductSpace/Harmonic/Ball.lean`
- `TauCeti/Analysis/InnerProductSpace/Harmonic/Dilation.lean`
- `TauCeti/Analysis/InnerProductSpace/Harmonic/Isometry.lean`
- `TauCeti/Analysis/InnerProductSpace/Harmonic/MeanValue/Basic.lean`
- `TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean`
- `TauCeti/Analysis/InnerProductSpace/Laplacian/Comparison.lean`
- `TauCeti/Analysis/InnerProductSpace/Laplacian/LocalExtr.lean`
- `TauCeti/Analysis/InnerProductSpace/Laplacian/MaximumPrinciple.lean`
- `TauCeti/Analysis/InnerProductSpace/Laplacian/ParametricIntegral.lean`
- `TauCeti/Analysis/InnerProductSpace/Laplacian/WeakMaximumPrinciple.lean`
- `TauCeti/Analysis/InnerProductSpace/NormPow.lean`
- `TauCeti/Analysis/Matrix/EuclideanLin.lean`
- `TauCeti/Analysis/Normed/Module/Ball.lean`
- `TauCeti/Analysis/PDE/FundamentalSolution/Euclidean/Basic.lean`
- `TauCeti/Analysis/PDE/GreenFunction/Ball.lean`
- `TauCeti/Analysis/PDE/GreenFunction/BoundaryConcentration.lean`
- `TauCeti/Analysis/PDE/Harnack/Basic.lean`
- `TauCeti/Analysis/PDE/PoissonIntegral/Ball.lean`
- `TauCeti/Analysis/Sobolev/WeakDeriv/Basic.lean`
- `TauCeti/Analysis/Sobolev/WeakDeriv/Laplacian.lean`
- `TauCeti/MeasureTheory/Constructions/HaarToSphere.lean`
- `TauCeti/MeasureTheory/Function/Lp/DominatedConvergence.lean`
- `TauCeti/MeasureTheory/Function/Lp/OperatorLocalBound.lean`
- `TauCeti/MeasureTheory/Group/Integral.lean`
- `TauCeti/MeasureTheory/Integral/Average.lean`
- `TauCeti/MeasureTheory/Integral/CalderonZygmund/BoundedMeanOscillation.lean`
- `TauCeti/Topology/Compactness/Normed.lean`
