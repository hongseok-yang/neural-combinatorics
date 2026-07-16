# Corrected Region-II proof package

This package contains a corrected, consolidated proof of the Goodman-style
odd-cycle bound in the remaining density range

\[
  \frac12<p<\frac23,
  \qquad
  t(C_m,W)\ge p^m-p(1-p)^{m-1}
\]

for every odd `m`.  The new work is for `m >= 15`; the already established
cases `m <= 13` are recorded in `provenance/earlier_consolidated_note.tex`.

## Mathematical status

The proof is **rigorous but computer-assisted**.  Its operator reduction and
most scalar estimates are pencil-and-paper arguments.  Two compact scalar
regions are closed by deterministic finite subdivisions in exact rational
arithmetic:

- Zone B: `zoneB_certifier.py`;
- moderate-e Zone C: `zoneC_certifier.py` (using the admissible dual choice
  `lambda = 2*rho_lo*xi` or `lambda = 1`).

No theorem relies on floating-point sampling.  The file
`regionII_scalar_checker.py` is a regression and stress-testing companion;
its grid checks are not part of the proof.

The earlier five-atom stop-loss idea is deliberately absent.  It uses a
quantity different from the Huber reduction's
`L = sqrt(pq - alpha^2)`, and the tempting domination needed to connect the
two scalar statements is false.

## Main files

- `regionII_corrected_solution.tex` — source of the consolidated proof.
- `regionII_corrected_solution.pdf` — compiled working note.
- `zoneB_certifier.py` — exact Zone-B certificate (standard library only).
- `zoneC_certifier.py` — exact moderate-Zone-C certificate (standard library
  only).
- `regionII_scalar_checker.py` — exact identity/constant checks plus optional
  high-precision numerical stress tests (`sympy`, `mpmath`).
- `AUDIT_NOTES.md` — correction history and a proof-dependency checklist.
- `logs/` — recorded outputs of all checks and LaTeX compilation.
- `SHA256SUMS` — hashes of the distributed source files.
- `provenance/` — the two original notes supplied for this audit.

## Reproduce the checks

From this directory:

```bash
python3 zoneB_certifier.py
python3 zoneC_certifier.py
python3 regionII_scalar_checker.py --scan
```

Expected exact-certificate summaries:

```text
boxes verified: 23, skipped (outside domain): 3, max depth: 8
ZONE-B BATTLE CERTIFIED (exact rational arithmetic)

boxes verified: 2997 (bottom-out: 5), skipped: 87, max depth: 28, max battle m: 1716
ZONE-C-MODERATE CERTIFIED on e <= 1/3 - 1/1000 (exact rational arithmetic)
```

The first two scripts exit nonzero if a box remains unresolved.  Their
acceptance branches use only `fractions.Fraction`, integer square roots, and
outward rational bounds for the exponential and powers.  Float conversion is
used only when printing a failed box.

Compile the note with:

```bash
pdflatex -interaction=nonstopmode -halt-on-error regionII_corrected_solution.tex
pdflatex -interaction=nonstopmode -halt-on-error regionII_corrected_solution.tex
pdflatex -interaction=nonstopmode -halt-on-error regionII_corrected_solution.tex
```

Or run all checks with:

```bash
bash run_all_checks.sh
```

## Suggested order for human audit

1. Verify the block-operator identity, the compression bound, and the
   no-frontier lemma.
2. Check the one-frontier square-mass budget and the exact Huber elimination,
   paying special attention to the `K=0` shape case.
3. Check the `(e,kappa)` chart and the frontier-gap lemma
   `f >= d + delta`.
4. Audit Zone A and small-e Zone C as ordinary inequalities.
5. Read the certificate protocol in the TeX file alongside each exact
   certifier.
6. Check the new Turan-corner proof independently; its final inequalities
   have substantial slack.

## Important scope note

`regionII_corrected_solution.tex` is self-contained for the new Region-II
argument at odd `m >= 15`, including the no-frontier case.  Its corollary for
all densities additionally invokes the earlier high-density and short-cycle
results in `provenance/earlier_consolidated_note.tex`; those prior modules were
not re-audited in this package.
