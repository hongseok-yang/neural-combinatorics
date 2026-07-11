# Region-II odd-cycle density handoff package

This package summarizes the work on the remaining density range

\[
1/2 < p < 2/3,
\qquad q=1-p \in (1/3,1/2),
\]

for the conjecture

\[
t(C_m,W) \ge p^m - p(1-p)^{m-1}
\]

for every graphon `W` of edge density `p` and every odd `m >= 3`.

## Contents

- `regionII_baton_note.tex`: self-contained LaTeX handoff note.
- `regionII_baton_note.pdf`: compiled PDF of the note.
- `regionII_handoff_checker.py`: lightweight Region-II checker.
- `regionII_handoff_checker.log`: exact algebraic diagnostics only.
- `regionII_handoff_checker_scan.log`: exact diagnostics plus numerical scans of the final scalar target.
- `clean_two_sided_shift_checker.py`: earlier exact checker for the two-sided spectral-shift infrastructure and high-density certificate framework.
- `clean_checker_m61.log`: saved log for the cleaned two-sided/high-density checker run.

## Current mathematical status

The full conjecture is not proved in Region II.  The main result of this
package is a rigorous reduction of Region II to the scalar Huber inequality

\[
R_m \le C_m \psi(\xi,\rho).
\]

All variables in this inequality are explicit functions of `(q, alpha, m)`,
where `alpha` is the unique complement-compression eigenvalue above `q`.
There are no remaining graphon, operator, spectral-measure, or eigenfunction
shape variables in the final target.

The note also records endpoint asymptotics and the failed routes that should
not be reused without repair:

- the shape-free total-coupling relaxation is too weak;
- the smooth Huber lower bound is globally insufficient;
- the naive recurrence for normalized power defects misses a positive term;
- the fixed-dual branch inequalities are still diagnostics, not proofs.

## How to run the checkers

Basic exact Region-II diagnostics:

```bash
python3 regionII_handoff_checker.py
```

This verifies exact rational algebraic checks and prints the known diagnostic
where the smooth Huber route fails.

Optional numerical scans of the final scalar target:

```bash
python3 regionII_handoff_checker.py --scan --random-scan --trials 8000
```

These scans are not proof certificates.  They are included to help future work
locate tight regimes and test proposed inequalities.

The larger two-sided spectral-shift checker can be run with:

```bash
python3 clean_two_sided_shift_checker.py --max-m 43
```

The high-density finite strip run is recorded in `clean_checker_m61.log`.

## Suggested next step

The cleanest continuation target is to prove or certify

\[
R_m \le C_m \psi(\xi,\rho)
\]

on the domain

\[
1/3<q<1/2,
\qquad
q<\alpha\le (\sqrt{q^2+4q}-q)/2,
\qquad
m\ge3 \text{ odd}.
\]

A promising rigorous route is a dual-certificate proof using

\[
\psi(\xi,\rho)=
\max_{0\le\lambda\le1}
\left(\lambda\xi-\frac{\lambda^2}{4(\rho+\lambda)}\right),
\]

with rational interval arithmetic over boxes in `(q, alpha)` after making the
endpoint and large-`m` estimates quantitative.
