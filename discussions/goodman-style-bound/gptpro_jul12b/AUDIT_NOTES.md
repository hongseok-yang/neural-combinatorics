# Audit notes and correction history

## Executive conclusion

Claude's main proof architecture survives the audit:

1. the complement operator has at most one positive mean-zero eigenvalue
   above `q`;
2. the graphon deficit is bounded below by a frontier defect plus two coupling
   payments;
3. eigenfunction geometry eliminates the shape variables exactly and gives
   the scalar Huber inequality;
4. three scalar zones cover the admissible domain.

The supplied manuscript was not correct as written, but its errors are
repairable.  The corrected note proves the result with two exact finite
certificates.  In Zone C the certified lower-bound parameter is
`rho_lo <= rho`; the admissible dual choice is `2*rho_lo*xi` or `1`, rather
than an unsupported assertion that `min(1,2*rho*xi)` itself always pays.

## Corrections made

### 1. Reversed comparison in the cycle-length maximisation

The original proof of the `K(n)` lemma reversed one inequality when deciding
whether the continuous maximiser lies to the left of `n=14`.  The correct
gate is

\[
  n_*\le14
  \quad\Longleftrightarrow\quad
  15(14-A)\lambda\ge A+1.
\]

The original Zone-B implementation already used this orientation; the TeX
has been corrected to agree with it.

### 2. Missing lower bound in the Zone-C interval proof

The supplied Zone-C certifier implicitly needed a lower bound on
`f = alpha - L`.  The corrected note proves, with
`delta = alpha - 1/3` and `d = alpha - q`,

\[
  d+L\le\frac13,\qquad q-L\ge\delta,
  \qquad f\ge d+\delta.
\]

The released certifier now uses the stronger interval endpoint

```text
f_lo = max(alpha_lo - L_up, d_lo + delta_lo).
```

It still certifies the full middle range, with 2,997 verified leaves.

### 3. Unsafe decimal directions

Several handwritten decimals in the original note rounded the wrong way.
The corrected Zone-A and small-Zone-C chains use directed constants
(`0.2781`, `1.9047`, `1.8354`, and related values).  The companion checker
verifies every terminating decimal used in the analytic proof as an exact
rational comparison.

### 4. Turan-corner proof replaced

The original corner bounds included inaccurate intervals (notably for
`q+L`) and depended heavily on numerical spot checks.  They have been
replaced by an analytic proof starting from

\[
  S=q^2-L^2
   =\delta+3\delta^2-
     \left(\frac13+4\delta\right)d+2d^2.
\]

It derives a forcing inequality

\[
  R_m>0 \Longrightarrow (m-2)d>12.4\delta
\]

and a normalized defect bound

\[
  \frac{R_m}{\alpha^3p^{m-2}}
   <43m(m-2)\delta^2x^{m-3}.
\]

The two payment branches then dominate by large margins already at `m=15`.

### 5. No-frontier case made self-contained

The new note proves directly that the mean-zero compression satisfies
`||A|| <= 1/2`, that the shift series has nonnegative coefficients, and that
`lambda_max(A) <= q` implies the desired cycle bound.  This removes an
unnecessary dependency on the earlier project note inside the new Region-II
argument.

### 6. Degenerate Huber shape case expanded

The `K=0` case in the shape elimination is now written out.  The safe-channel
constraint implies `bc >= d sqrt(2 alpha)/2`, which forces
`xi <= v-v^2`; hence the positive-part term vanishes at the relevant `v`.

### 7. Exact certificate status stated honestly

The original abstract described the proof too close to “analytic.”  The
correct statement is: the proof is rigorous and computer-assisted.  Zone B
and the compact middle part of Zone C are finite exact-rational covering
arguments.  Numerical grids are only regression tests.

## Stop-loss idea: why it is not used

An audit-side five-atom stop-loss inequality was proved for a different
scalar parameter involving

\[
  \frac{q-\alpha^2}{1-\alpha}.
\]

The Huber reduction uses

\[
  L=\sqrt{pq-\alpha^2}.
\]

There is no established implication from the stop-loss statement to the
Huber target.  A natural proposed domination between their payments is
false at admissible parameters for large `m`.  The consolidated proof does
not cite or depend on that route.

## Exact-certifier audit checklist

### Zone B

- Confirm each domain skip is one-sided and cannot discard an admissible
  point.
- Check monotonic bounds for `x`, `A`, `Phi`, `rho`, and `epsilon`.
- Check the integer-square-root enclosures.
- Check that reciprocal exponential partial sums give upper bounds on
  `exp(-t)`.
- Check the `K(14)` gate and the continuous-maximiser upper bound.
- Confirm every unresolved leaf triggers failure.

### Zone C

- Check all interval endpoints in `Box.__init__`, especially `L2_lo`,
  `L2_up`, `G2_lo`, `rho_lo_lo`, and `rho_lo_up`.
- Check the strict secant gate is implemented as
  `3 + floor(q_lo*(G2_lo-G2_lo^2/2)/d_up)`.
- Check that the negative geometric term is rounded downward when forming an
  upper defect bound.
- Check the tail criterion: once the positive head alone is below payment,
  all larger exponents pass.
- Check the `kappa -> 0` bottom-out compares
  `exp(-a/kappa)/kappa`, not `exp(-a/kappa)/kappa^2`.
- Confirm every unresolved leaf triggers failure.

## Remaining review risk

The two exact programs are short enough for line-by-line human review, but
they have not been translated into a proof assistant.  Until that is done,
the principal residual risk is an interval-monotonicity or implementation
mistake in those two scripts, rather than a floating-point error.  The TeX
file gives the mathematical contract each script is intended to certify so
that an independent reimplementation is possible.
