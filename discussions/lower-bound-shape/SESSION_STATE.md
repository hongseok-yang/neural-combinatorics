# Session state — discussions/lower-bound-shape

Last updated: 2026-05-29 (afternoon session).

This file is the resumption point for the work on the two graphon-optimisation
problems described in [two_problems.pdf](two_problems.pdf), with current state
documented in [two_problems_progress_report.tex](two_problems_progress_report.tex).
The most recent session **closed Step A2** of the global reduction — the
reduction of the unbalanced tripartite-filling family to the balanced one —
and in doing so **corrected an error in the strategy note**.

> **Tooling note:** `sympy` is **not** installed for `/usr/bin/python3`. Use
> **`/opt/miniconda3/bin/python3`** to run every script in `scripts/`
> (it has sympy 1.14). The SESSION_STATE references below have been updated.

## Previous session (morning, kept for context)

That session focused on making the §7 reduction rigorous and on the
mixed-curvature finding; see the "older" TL;DR further down.

---

## TL;DR (this session — Step A2)

1. **Exact unbalanced in-family densities** (regular filling, derived two ways —
   by hand and by a finite stochastic-block-model sum):
   $t(P,W)=3\alpha^2\beta\gamma\,q\,(2\alpha q+2\alpha+3(\beta+\gamma))$,
   $t(J,W)=2\alpha^2\beta\gamma\,q\,(4\alpha q+\alpha+3(\beta+\gamma))$,
   with $x=2(\alpha\beta+\alpha\gamma+\beta\gamma)+\alpha^2 q$. These reduce to
   the §7 balanced formulas when $\beta=\gamma$.
2. **The strategy note's per-$\alpha$ balancing lemma (Lemma 4.5) is FALSE.**
   Explicit counterexample: at $\alpha=11/20>1/2$, $x=2/3$, the unbalanced
   config with $q=1/2$ gives $t(P,W)\approx0.0139<0.0289$ = balanced value.
   (The failure is confined to $\alpha>1/2$ near the Mantel filling bound.)
3. **The correct (global) Step A2 is proved:** for $x\in(2/3,3/4)$, the
   minimum of $t(P,\cdot)$ / $t(J,\cdot)$ over the *whole* tripartite-filling
   family (parts $\alpha,\beta,\gamma$ unconstrained, any triangle-free
   filling) equals the balanced reduced value $\Psi_P(x)$ / $\Psi_J(x)$; the
   minimiser has $\beta=\gamma$ and a regular filling. Proof = Jensen
   (regular filling) + the feasible region is the "balanced–Mantel lens"
   (two perfect-square Turán thresholds $(3\alpha-1)^2,(3\alpha-2)^2$) + the
   unique interior critical point is a **saddle** ($T_{qq}<0$, certified by a
   resultant with no root in $(2/3,3/4)$) + Mantel-arc domination.
4. **Conceptual:** the Mantel arc ($q=1/2$) IS the complete 4-partite
   Lovász–Simonovits template, so Step A2 says *the filling construction beats
   the clique template* — exactly the §5–§6 numerical finding, now structural.

## TL;DR (older — making §7 rigorous + curvature)

1. **All of §7 of the progress note is now rigorous** — branch uniqueness,
   monotonicity, endpoint values, and the within-family global minimum are
   all certified by Sturm sequences on explicit rational polynomials.
2. **New rigorous finding: both $\Psi_P$ and $\Psi_J$ have mixed curvature on
   $[2/3, 3/4]$** — convex on $(2/3, x^*)$, concave on $(x^*, 3/4)$, with
   $x^*_P \approx 0.6787853539$ and $x^*_J \approx 0.7132424244$ (rationally
   bracketed to 12 decimal places). This refutes the original Problem 2
   classification of $P, J$ as "piecewise concave on Turán intervals" already
   on the first Turán interval, conditional on the global reduction.
3. **§3.4 of the progress note** (the first-order stability proof for $T_k$
   with $k\ge 6$) is patched: the averaging step is now spelled out
   explicitly in a stand-alone note.
4. **Strategy note** for the remaining global reduction $f_P = \Psi_P$,
   $f_J = \Psi_J$ on $[2/3, 3/4]$ written: three independent attack plans
   (A: stability + symmetrisation; B: flag-algebra SDP; C: rooted clique-
   density region), with a concrete prioritised task list.

---

## Files in this directory

| File | Status | Purpose |
|---|---|---|
| `two_problems.pdf` | original | The two problems as posed. |
| `two_problems_progress_report.tex` | original | The current overall state; sections §1–§8 unchanged. |
| **`rigorous_certificates.tex`** | new (7 pages) | Companion appendix to §7: Sturm certificates for branch uniqueness, monotonicity, endpoints, mixed curvature, and the stationary-vs-boundary gap (formerly Lemma 5.5, now Theorem 6.1 — rigorous). |
| **`Tk_first_order_stability.tex`** | new (~5 pages) | Replacement for §3.4 of the progress note with the averaging step made explicit. |
| **`global_reduction_strategy.tex`** | original (this session) | Research-direction note: three plans (A/B/C). **NB: its Lemma 4.5 (per-$\alpha$ balancing) is now known FALSE — superseded by `balancing_reduction.tex`.** |
| **`balancing_reduction.tex`** | new (this session, ~6 pages) | The corrected Step A2: unbalanced densities, the counterexample to per-$\alpha$ balancing, and the proof that the global in-family minimum equals the balanced $\Psi_P,\Psi_J$ (saddle + Mantel-domination). |
| `scripts/verify_reduced_problems.py` | from prev session | sympy script for the certificates in `rigorous_certificates.tex` items 1–5. Run via `/opt/miniconda3/bin/python3`. |
| `scripts/verify_gap.py` | from prev session | sympy script for the stationary-vs-boundary gap (Theorem 6.1). |
| **`scripts/verify_balancing_reduction.py`** | new | The Step A2 certificate (Parts 0–5): exact unbalanced densities, counterexample, Turán thresholds, saddle resultant, Mantel domination. Exits 0, no AssertionError. |
| **`scripts/derive_unbalanced.py`** | new | SBM derivation of the unbalanced $t(P,W),t(J,W)$ (independent check of the hand formulas). |
| **`scripts/explore_global_infamily.py`** | new | numpy sanity scan confirming the global in-family min equals the balanced min across $[2/3,3/4]$. |

The note PDFs are gitignored (auto-built from the .tex files via `pdflatex`).

---

## What is now rigorous (verified)

Cross-references below refer to `rigorous_certificates.tex` unless stated otherwise.

- **Discriminants:** $\Delta_P, \Delta_J > 0$ on $(1/3, 1/2)$. (Lemma 2.1.)
- **Branch range:** $q_P, q_J \in (0, 1/2)$ on $(1/3, 1/2)$, the unique stationary
  branches there, with $q_*(1/3) = 0$, $q_*(1/2) = 1/2$. (Theorem 2.2.)
- **Monotonicity:** $x_P'(\alpha), x_J'(\alpha) > 0$ on $(1/3, 1/2)$, so
  $\alpha \mapsto x_*(\alpha)$ is a bijection $[1/3, 1/2] \to [2/3, 3/4]$.
  (Theorem 3.1.)
- **Endpoint values:** $\Psi_P(2/3) = \Psi_J(2/3) = 0$,
  $\Psi_P(3/4) = 9/128$, $\Psi_J(3/4) = 3/64$. (Theorem 4.1.)
- **$\Phi_{\alpha\alpha} > 0$ on the branch** (so the envelope formula's sign
  is the sign of the Hessian determinant). (Proposition 5.1.)
- **Mixed curvature:** $\Psi_P''(x), \Psi_J''(x)$ each change sign exactly
  once on $(2/3, 3/4)$, with
  $x^*_P \in [0.6787853539, 0.6787853540]$ and
  $x^*_J \in [0.7132424244, 0.7132424245]$. (Theorem 5.2.)
  - For $J$, uniqueness follows from a single-root Sturm bound on $L^2 - M^2\Delta$.
  - For $P$, $L^2 - M^2\Delta$ has 2 roots in $(1/3, 1/2)$; the second is a
    root of the conjugate $L - M\sqrt{\Delta}$, identified by the sign-product
    test $\operatorname{sign}(L) \cdot \operatorname{sign}(M)$ at Sturm-isolated rational sub-intervals.
- **Stationary < boundary:** $\Psi_P^{\text{stat}}(x) < (9/8)(x-1/2)^2$ and
  $\Psi_J^{\text{stat}}(x) < (3/4)(x-1/2)^2$ on $(2/3, 3/4)$, with equality
  only at $x = 3/4$. (Theorem 6.1.) **Closes the in-family reduction.**
- **First-order stability of $T_k$ for $k\ge 6$:** clean averaging argument
  in `Tk_first_order_stability.tex` (Theorem 4.1 there).
- **In-family reduction to balanced parts (Step A2), corrected form:** for
  $x\in(2/3,3/4)$ the minimum of $t(P,\cdot)$/$t(J,\cdot)$ over the unbalanced
  tripartite-filling family equals the balanced $\Psi_P$/$\Psi_J$.
  (`balancing_reduction.tex`; certificates in `verify_balancing_reduction.py`.)
  Rigorous and uniform in $x$ except the Mantel-domination step, which is
  exact at 98 dense rational points + shown positive/monotone to 0 at $x=3/4$
  (its all-$x$ Sturm endgame is the one remaining formalisation — see below).

---

## What is still open

In rough priority order:

0. **(small) Finish the all-$x$ Mantel-domination Sturm certificate.** Step A2
   is done modulo this one step: show $M_P(\alpha_M^+(x))-\Psi_P(x)>0$ for all
   $x\in(2/3,3/4)$, where $\alpha_M^+=\frac{3+\sqrt{9-12x}}{6}$. The resultant
   (computed in `verify_balancing_reduction.py`) factors as
   $x^6(2x-1)^4(3x-2)^2(4x-3)^2\cdot D_{18}(x)$; the only root of $D_{18}$ in
   $(2/3,3/4)$ is $x\approx0.74948$, and it is **spurious** (the actual
   difference is $\approx 4.2\times10^{-5}>0$ there — it is a Mantel-*local-max*
   vs balanced-stationary coincidence). To finish: isolate the correct
   algebraic branches (smaller root of the $z$-quadratic = Mantel min; minimal
   feasible root of the balanced-stationary quintic = $\Psi_P$) so the
   univariate certificate sees only the true difference.
1. ~~Step A2~~ **DONE** (corrected, global form) — see `balancing_reduction.tex`.
   The original per-$\alpha$ form (strategy note Lemma 4.5) was false.
2. **Step A1** (3-blowup skeleton from $K_4$-supersaturation stability): the
   cut-metric stability of the LS 4-partite template at $K_4$-density is
   the bottleneck. Needs a literature survey (Pikhurko–Razborov and follow-ups).
3. **Flag-algebra SDP** for the $k = 5$ circular construction in Problem 1
   (the lower bound $t(H, W) \ge 24349/187500$ at $t(K_2, W) = 4/5$).
4. **Flag-algebra SDP** for $\Psi_P, \Psi_J$ at a sample point such as
   $x = 17/25$. Mixed curvature constrains any parametric interpolation
   to split at $x^*$.
5. **Second-order analysis of $T_k$ for $k \ge 6$**: compute the Hessian
   of $a, b \mapsto t(H, S_{k, a, b})$ along a two-parameter symmetric
   family at $(0, 0)$. Either find a negative-eigenvalue direction (settles
   non-optimality for some $k \ge 6$) or strengthen the local-min statement.

---

## How to resume in a fresh session

1. **Read the abstracts** of `rigorous_certificates.tex`,
   `balancing_reduction.tex`, and `global_reduction_strategy.tex`
   (remembering the latter's Lemma 4.5 is now superseded).
2. **Re-run the scripts** to confirm everything still verifies
   (note: **`/opt/miniconda3/bin/python3`**, not `/usr/bin/python3`):
   ```sh
   cd scripts
   /opt/miniconda3/bin/python3 verify_reduced_problems.py
   /opt/miniconda3/bin/python3 verify_gap.py
   /opt/miniconda3/bin/python3 verify_balancing_reduction.py
   ```
   All three should exit 0 with no `AssertionError`.
3. **Pick a next task** from the "What is still open" list. The smallest is
   task 0 (the Mantel Sturm endgame, finishing Step A2); the real bottleneck
   for $f_P=\Psi_P$ is **Step A1**.
4. **Update this file** as the work progresses.

---

## Conventions

- The companion sympy scripts use only exact rational arithmetic. Floating
  point appears only as a sanity print.
- The interval is consistently $\alpha \in (1/3, 1/2)$ in the parametric form
  and $x \in (2/3, 3/4)$ in the original form; they are related by the
  bijection $x_P(\alpha)$ (resp.\ $x_J$).
- The branch's sqrt prefactor differs between $P$ and $J$:
  $q_P = (-B_P + \alpha\sqrt{\Delta_P})/(2 A_P)$ but
  $q_J = (-B_J + 2\alpha\sqrt{\Delta_J})/(2 A_J)$
  (because $B_J^2 - 4 A_J C_J = 4\alpha^2 \Delta_J$, not $\alpha^2 \Delta_J$).
  This was a bug I caught early on; flag it if you start a new script.

---

## Headline narrative for a future paper

The cleanest one-paragraph summary, suitable for an introduction:

> The two problems posed in [two_problems.pdf](two_problems.pdf) had ill-formed
> statements, as the progress report documents. After correction, both reduce
> to one-dimensional algebraic minimisations $\Psi_P, \Psi_J$ inside a
> tripartite Turán-filling family. We prove (rigorous certificates note) that
> these reduced curves have mixed convex-then-concave curvature on the first
> Turán interval $[2/3, 3/4]$, with unique inflection points
> $x^*_P \approx 0.679$ and $x^*_J \approx 0.713$. We further prove the
> in-family minimisation reduces to balanced parts with a regular filling
> (the unbalanced freedom never helps), so the only remaining hypothesis for
> $f_P=\Psi_P$, $f_J=\Psi_J$ is the cut-metric stability that forces a
> minimiser onto a 3-blowup skeleton (Step A1). Conditional on that, this
> rigorously refutes the original Problem 2 classification of $K_4^\dagger$
> and $K_3 \cup_{K_2} K_4$ as "piecewise concave on Turán intervals", already
> on the first Turán interval.
