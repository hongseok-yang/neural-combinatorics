# Complete Goodman-style odd-cycle bound

This package contains a consolidated, self-contained proof of the following theorem.

> For every graphon `W` of edge density `p` and every odd integer `m >= 3`,
> `t(C_m,W) >= p^m - p(1-p)^(m-1)`.

## Files

- `complete_odd_cycle_bound.tex` — the complete LaTeX manuscript. It has no `\input`, `\include`, external bibliography, figure, or data dependency.
- `complete_odd_cycle_bound.pdf` — the compiled manuscript.
- `odd_cycle_complete_exact_checks.py` — the top-level exact/symbolic audit.
- `regionII_exact_checks.py` — exact checks for the longer Region-II identities, called by the top-level audit.

The Python programs are companion audits only. The proof in the LaTeX manuscript does not assume that they have been run: every finite certificate used logically by the proof is printed in the manuscript.

## Proof map

1. `m=3,5,7`: Goodman's degree argument, one completed square, and a univariate sum-of-squares identity.
2. `p >= 2/3`: two-sided Schur-complement cancellation, complete homogeneous polynomial expansion, Dirichlet diagonalization, beta representation, Laplace-gamma smoothing, and a shifted-gamma moment inequality.
3. `1/2 < p < 2/3`, `m >= 9`: one-frontier spectral reduction, forced variance, two coupling channels, a Huber-type scalar envelope, and its quadratic and linear dual witnesses.
4. `p <= 1/2`: the asserted lower bound is nonpositive and therefore immediate.

The only fixed finite residues in the long-cycle Region-II proof are two exact rational Bernstein coefficient lists for an `m=9` corner. There is no adaptive interval covering and no separate computation for `m=11` or `m=13`.

## Transferable mechanisms developed in the manuscript

The final conceptual section explains and proves the following general patterns.

- A distinguished-vector Schur complement is the first Jacobi coefficient-stripping relation; iterating it gives a Jacobi continued fraction.
- Moment series decompose into first-return excursions, while the logarithmic series performs cyclic excursion assembly; odd complement cancellation removes the uncontrolled stripped tail.
- Complete homogeneous symmetric polynomials admit an exact Dirichlet probabilistic polarization, reducing a cube minimum to the diagonal.
- A beta-prime rational kernel can be converted by a Laplace transform into a positive mixture of shifted-gamma expectations.
- Gamma integration by parts is a Stein/ladder identity, and the shifted even moments are generalized Laguerre polynomials with a nonclassical parameter.
- A single dangerous eigenmode plus two compensating coupling channels naturally produces a Huber active-set envelope.
- The threshold `q=1/3` is matched from both sides: it is both the gamma-moment threshold and the point at which the Hilbert-Schmidt budget changes from allowing two dangerous modes to allowing only one.

## Building

A standard TeX Live installation is sufficient:

```bash
pdflatex complete_odd_cycle_bound.tex
pdflatex complete_odd_cycle_bound.tex
```

## Running the audit

The audit requires Python 3, SymPy, and NumPy. Keep the two Python files in the same directory and run:

```bash
python3 odd_cycle_complete_exact_checks.py
```

A successful run ends with:

```text
All complete-proof checks passed.
```
