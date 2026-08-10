# Paper–Lean alignment notes

This note supplies information for revising `paper_new_region2_v3.tex`; the TeX
source itself has not been edited. It compares the foundations, the common
operator reduction, and the complete `p ≥ 2/3` proof with
`discussions/goodman-style-bound/complete_lean/`.

The later Section 5 scalar argument and the planned short-cycle replacement in
`discussions/goodman-style-bound/short_cycle_by_schur.tex` are deliberately
deferred until their manuscript statements and notation are stable.

## The strict inequality \(\Lambda<1/2\)

The manuscript states

$
0\le M<q<\Lambda<\frac12<p,
$

but the cited operator-norm estimate alone gives only `Λ ≤ 1/2`. Here is the
extra argument needed for strictness.

Let `φ ∈ 1^⊥` be a unit eigenfunction of `A` with `Aφ = Λφ`, and put

$
a_\phi=\int |\phi(x)|\,dx.
$

The quadratic-form estimate used in the norm bound gives

$
2\Lambda\le a_\phi^2\le1.
$

Indeed, writing `φ = φ₊ - φ₋`, mean zero gives
`∫φ₊ = ∫φ₋ = a_φ/2`, and hence

$
\Lambda=\langle\phi,T_U\phi\rangle
\le 2(a_\phi/2)^2=a_\phi^2/2.
$

If `Λ = 1/2`, equality forces `a_φ = 1`. Equality in Cauchy–Schwarz then
implies `|φ| = 1` almost everywhere. Since `U ≥ 0`,

$
\Lambda
\le\langle|\phi|,T_U|\phi|\rangle
=\langle\mathbf1,T_U\mathbf1\rangle=q,
$

contradicting `q < Λ`. Thus `Λ < 1/2`. Lean formalizes this as
`complement_leading_eigenvalue_lt_half` in
`IntermediateRegion/VarianceLowerBound.lean`.

The manuscript should place this immediately after producing an eigenvalue
`Λ > q` and before using the strict chain.

## Multiplicity above \(q\)

“At most one eigenvalue above `q`” should mean multiplicity, not merely one
distinct numerical value. The precise statement needed later is:

> The spectral subspace of `A` associated with `(q,∞)` has dimension at most
> one.

For the finite-step argument, two orthonormal eigenvectors with eigenvalues
`λ₁, λ₂ > q`, even when `λ₁ = λ₂`, would give

$
\operatorname{Tr}(A^2)\ge\lambda_1^2+\lambda_2^2>2q^2>pq,
$

contradicting the Hilbert–Schmidt estimate. Consequently an eigenvalue above
`q`, if present, is simple and its unit eigenfunction is determined up to
sign. Lean’s `complement_leading_eigenvalue_unique` in
`IntermediateRegion/LeadingEigenvalue.lean` is multiplicity-sensitive because
its spectral index includes a basis index within each eigenspace.

## Lean’s direct operator reduction

The manuscript’s finite-step reduction is short and mathematically adequate:
approximate by edge-density-preserving step graphons, work with the finite
block matrix relative to `1 ⊕ 1^⊥`, introduce its finite spectral measure,
derive the cycle identities using determinants and Schur complements, and
pass to the limit.

Lean proves the required identities directly for graphons on an arbitrary
probability space:

- `Kernel.lean` obtains compactness from finite rectangular simple-kernel
  approximations; these are used to prove an operator theorem, not to replace
  the graphon in the final statement.
- `EdgeDensityAtLeastTwoThirds/GraphonMomentRepresentation.lean` constructs the
  centered operator in `L²`, proves the `1/2` norm bound, and uses a finite
  Krylov compression whose atoms reproduce every moment needed for the fixed
  cycle length exactly.
- A foundational module supplies a direct cyclic kernel identity in place of
  the two-sided determinant calculation.
- The intermediate proof uses compact self-adjoint spectral sums and a
  coefficientwise formal power-series identity instead of analytic
  determinants.

Thus the manuscript’s reduction may remain, but a release note should point
out that Lean proves the operator reduction directly and in the more general
ambient probability-space setting.
