# Turan--Sidorenko handoff package

This package summarizes the current state of the project on the chromatic-polynomial lower bound

\[
  t(H,W) \ge (1-p)^{v(H)} \chi_H\left(\frac{1}{1-p}\right),
  \qquad p=t(K_2,W),
\]

on the top Turan branch.  The guiding interpretation is that the right-hand side is the value of an equivalence-relation/Turan anticorrelation graphon.

## Suggested reading order

1. `docs/colleague_cover_memo.pdf`  
   A short memo explaining the project, the main target, the current status, and the questions where advice would be most helpful.

2. `docs/turan_sidorenko_detailed_handoff.pdf`  
   A detailed self-contained technical report.  It includes the main inequality, the anticorrelation interpretation, the odd-atomic positive-core conjecture, the revised rooted framework, all current partial results, the smoothed Goodman target, the bipodal reduction, obstacles, and a plan.

3. `scripts/bipodal_delta2_reduction.py`  
   Symbolic script deriving the bipodal defect Delta_2, verifying the rank-two identity, and checking several exact bipodal subfamilies.

4. `scripts/bipodal_delta2_formalization.py`  
   Formalization aid for the full bipodal target.  It derives Delta_2, verifies the rank-two identity, runs the Bernstein subdivision search, and rechecks the accepted boxes with exact integer/rational Bernstein arithmetic.  The unresolved boxes are boundary-layer boxes, not counterexamples.

5. `scripts/bipodal_delta2_checker.py`  
   Earlier exploratory checker for the bipodal polynomial.  This is less polished than the two scripts above but useful for reproducing the numerical exploration.

## Most important current target

Prove or refute the smoothed Goodman trace inequality

\[
  \operatorname{Tr}(T_W^2 K_W T_W^2) \ge 0,
  \qquad
  K_W(x,y)=W(x,y)(T_W^2(x,y)-(2p-1)).
\]

Equivalently,

\[
  t(C_3\cup_{K_2}C_5,W) \ge (2p-1)t(C_5,W), \qquad p\ge 1/2.
\]

This is the first genuinely mixed rooted clique-gluing inequality in the programme.

## Current status of this target

Proved for:

- p-regular graphons;
- complete multipartite graphons;
- equal-weight bipodal graphons;
- rank-one graphons;
- one-sided threshold bipodal graphons;
- Boolean bipodal graphons.

General bipodal graphons: exact four-variable polynomial reduction plus partial exact Bernstein certificate; a boundary-layer lemma remains.

Arbitrary graphons: open.

## Dependencies for scripts

The scripts use Python 3 with `sympy` and `numpy`.  They are intended as reproducibility aids, not as finalized proof certificates.  The exact Bernstein formalization script explicitly reports what has and has not been certified.
