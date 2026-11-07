# P5 cancellation at logarithmic boundary zeros

Root approved this route; sol_poisson independently approved before implementation.
The module `Pavlov/LogPoissonBoundary.lean` owns boundary cancellation only; the
separate `LogPoisson.lean` owns domination. No boundedness hypothesis is needed
for the boundary continuity result.

For each real a, the entire A has a nonzero analytic germ: otherwise identity
continuation would give A(i)=0, contradicting upper-half-plane zero-freeness.
The analytic finite-order factor theorem gives natural m and local analytic B,
B(a)≠0, with A(z)=(z-a)^m B(z) near a. Set

`v(t)=log‖A(t)‖`, `w(t)=v(t)-m log|t-a|`,
`w'=Function.update w a (log‖B(a)‖)`.

The local logarithm identity identifies w' with log‖B‖ near a, so w' is
continuous at a. It remains weighted integrable because log-distance is
weighted integrable and changing one point is an a.e. equality.

Linearity of the Schwarz integral and the exact log-distance Poisson formula
then give, throughout UHP,

`Re S[w'] = Re S[v] - m log‖z-a‖`.

Near a in UHP the analytic factor identity gives
`log‖A(z)‖ = m log‖z-a‖+log‖B(z)‖`.
Weighted Poisson boundary convergence for w' and continuity of log‖B‖ therefore
show that the defect `Re S[v]-log‖A‖` tends to zero. This cancels the two
logarithmic singularities before taking a limit.

The extension defined as this defect for Im z>0 and zero otherwise is
continuous globally, hence on closed UHP. Interior continuity uses
holomorphy of S and nonvanishing of A. The boundary proof applies at nonzeros
as well (m=0); no separate zero-countability theorem is required.

Implemented API:

- `tendsto_poisson_log_defect_boundary hA hnz hv a`;
- `poissonLogDefect A`: the defect in UHP and zero elsewhere;
- `continuous_poissonLogDefect hA hnz hv`: global continuity;
- `poisson_log_defect_continuous_zero_boundary hA hnz hv`: closed-UHP continuity.

Validation: `lake build FourierFrames.Cited.Pavlov.LogPoissonBoundary` succeeds
without warnings. All three public theorem axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound`. The local factor, exact log-norm
factor identity, and updated residual continuity lemmas are private.
