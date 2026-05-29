# HANDOFF — lower-bound-shape

Portable, committed resume point for the work on the two graphon-optimisation
problems. Unlike `SESSION_STATE.md` (which is **gitignored** and lives only on
the office machine as finer-grained working notes), this file is in the repo so
the project can be resumed from any machine.

## The one file to read first

[`paper.tex`](paper.tex) is the **single consolidated document**: it merges the
progress report and all four companion notes (rigorous certificates, $T_k$
stability, balancing reduction, global-reduction strategy) plus the numerical
Step-A1 evidence into one self-contained paper. Everything below is a pointer
into it.

- Status of every piece: §13 ("Where the project currently stands").
- Open problems: §13.2. Research directions: §14. Collaborator checklist: §15.
- Script index: Appendix C.

**Build:** from `discussions/lower-bound-shape/`,
```sh
pdflatex paper.tex && pdflatex paper.tex   # twice, for the ToC and cross-refs
```
No bibtex needed (the bibliography is inline). Compiles clean to ~25 pages.

## Tooling note (read before running scripts)

The `sympy` verification scripts in `scripts/` need **python3 with sympy ≥ 1.14**.
- On the **office machine**, that is `/opt/miniconda3/bin/python3` (the system
  `/usr/bin/python3` does NOT have sympy).
- On a **different machine** (home), install sympy first
  (`pip install sympy`) and use whatever python has it.

To re-confirm everything still verifies:
```sh
cd scripts
<python-with-sympy> verify_reduced_problems.py     # certificates §9 (curvature etc.)
<python-with-sympy> verify_gap.py                  # stationary-vs-boundary, Thm 9.x
<python-with-sympy> verify_balancing_reduction.py  # Step A2
<python-with-sympy> optimize_graphon.py            # numerical Step-A1 probe (numpy)
```
All exit 0 with no AssertionError.

## What is done (rigorous unless noted)

- Problem 1: benchmark/competitor values; circular $k=5$ value $24349/187500$;
  first-order stability of $T_k$ for $k\ge6$ (averaging step explicit).
- Problem 2: $K_3\sqcup K_3$ kills the all-graphs extension; clique curves are
  piecewise concave; $K_4^\dagger$ and $K_3\cup_{K_2}K_4$ are NOT minimised by
  the LS clique template (explicit better fillings at $x=17/25$).
- Reduced curves $\Psi_P,\Psi_J$ derived; certified by Sturm sequences:
  branch uniqueness, monotone parametrisation, endpoints, the in-family minimum
  beats the boundary, and **mixed convex-then-concave curvature** on $[2/3,3/4]$
  (inflections $x^*_P\approx0.6788$, $x^*_J\approx0.7132$).
- **Step A2** (in-family reduction to balanced parts) closed in corrected
  global form; the naive per-$\alpha$ balancing is false (explicit
  counterexample).
- Numerical evidence for **Step A1** (the $t(P)$-minimiser is a 3-blowup
  skeleton with $K_4$-density just above $g_{4,3}$).

## What is open (priority order)

0. **(small)** Finish the all-$x$ Mantel-domination Sturm certificate to fully
   close Step A2 — see paper.tex §11 "Rigour status" (the degree-18 factor
   $D_{18}(x)$; isolate the correct algebraic branches so the certificate sees
   only the true positive difference).
1. **Step A1** — the cut-metric stability forcing an arbitrary minimiser onto a
   3-blowup skeleton (paper.tex §10, Lemma "K4-supersaturation stability").
   This is the real bottleneck for $f_P=\Psi_P$. First move: literature survey
   of Pikhurko–Razborov-type stability for the LS 4-partite template.
2. Flag-algebra SDP for the $k=5$ circular value $24349/187500$ at $p=4/5$
   (Problem 1); and parametric certificates for $\Psi_P,\Psi_J$ on $[2/3,3/4]$
   (the mixed curvature forces the interpolation to split at $x^*$).
3. Later Turán intervals: the analogue of $\Psi_P,\Psi_J$ on $[3/4,4/5]$
   (4-blowup with a triangle-free filling) and its curvature.
4. Second-order analysis of $T_k$ for $k\ge6$ (Hessian of $t(H,S_{k,a,b})$ at
   $(0,0)$): find a negative-eigenvalue direction or strengthen the local-min
   statement.

## Recent session log

- Consolidated the progress report + 4 companion notes + the new step-graphon
  experiment into `paper.tex`.
- Added `scripts/optimize_graphon.py` (direct $t(P)$/$t(K_4)$ step-graphon
  minimiser; supplies the Step-A1 evidence in §12). Uses Reiher's closed form
  $g_{4,3}(s)=\tfrac89 s(1-s)^3$.
- Proofread `paper.tex` with an independent sympy re-derivation of ~70 algebraic
  claims and a re-run of all committed certificates. Fixed two transcription
  errors: the $k=3,4,5$ values of $6k^3-55k^2+142k-111$ (now $-18,-39,-26$),
  and the unbalanced $t(J)$ bracket (now $2\alpha^2\beta\gamma[(\alpha+3s)q
  +4\alpha D_2]$). All other claims verified correct.

## Conventions / gotchas

- $\alpha\in(1/3,1/2)$ in the parametric form $\leftrightarrow$ $x\in(2/3,3/4)$
  in the original form, via the bijection $x_P(\alpha)$ (resp. $x_J$).
- The branch sqrt-prefactor differs between $P$ and $J$:
  $q_P=(-B_P+\alpha\sqrt{\Delta_P})/(2A_P)$ but
  $q_J=(-B_J+2\alpha\sqrt{\Delta_J})/(2A_J)$ (since
  $B_J^2-4A_JC_J=4\alpha^2\Delta_J$, not $\alpha^2\Delta_J$).
- The displayed on-branch polynomials sit over a denominator $\propto
  \alpha(\alpha+1)^2$ — the proportionality hides a positive constant (8, 4, 16,
  1 for $\Phi_{aa}^P,\Phi_{aa}^J,\det^P,\det^J$); irrelevant to signs.
- `SESSION_STATE.md` is gitignored (office-machine working notes only). Do not
  re-add it to the repo.
