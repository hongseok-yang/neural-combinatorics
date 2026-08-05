# Renaming dictionary — `paper_new_region2_v2.tex`

Companion to `TERMINOLOGY.md`. Records (A) display-text renames already performed, (B) the
old→new **label-key dictionary** to be executed in one batch once all display names are settled
(labels are shared with the Lean side and its docs, so paper + Lean + cross-reference docs must
move together), and (C) decisions still open.

Started 2026-08-06.

## Decisions taken (owner: TY Kim, 2026-08-06)

- **Region names:** threshold-relative. §4 = "Below the threshold ($q\le1/3$)",
  §5 = "Above the threshold ($1/3<q<1/2$)". "dense region" / "intermediate region" retired.
- "subcritical" REJECTED (stat-mech connotation) → use "No eigenvalue above $q$".
- "forced variance" → "variance lower bound" (accepted).
- Direct condition-based names preferred over metaphors: "[Bounds for $T_N$]",
  "[The regime $\zeta\ge N$]", "[The regime $\zeta\le N$]", "The exceptional case $N=7$".
- Both "defect" and "excess" are unsatisfying; "master" too strong. Prefer direct names
  (statement-of-content style). Final choice pending (see Open).
- Abstract: rewrite LAST, after all other renames.
- §8 (transferable mechanisms): revise LAST.
- Label keys WILL be renamed (not only display text), with this dictionary as the migration map.

## A. Display-text renames performed (2026-08-06; labels untouched)

| Line (old) | Old display text | New display text |
|---|---|---|
| 1302 | §4 "The dense region $p\ge2/3$: Dirichlet and gamma smoothing" | "Below the threshold $q\le1/3$: Dirichlet averages and gamma smoothing" |
| 1311 | §4.1 "A two-sided spectral shift and cancellation of the tail" | "A two-sided Schur-complement identity and cancellation of the odd trace" |
| 1595 | §4.4 "Dirichlet diagonalization: a probabilistic polarization" | "Diagonalization by a Dirichlet average" |
| 1943 | §4.6 "The nonpositive diagonal is pointwise safe" | "The case $\ell\le0$: pointwise nonnegativity" |
| 1998 | lemma "[Gamma smoothing]" (`lem:dense-gamma-smoothing`) | "[Laplace--gamma representation]" |
| 2436 | §4.10 "Completion of the dense-region proof" | "Completion of the proof for $q\le1/3$" |
| 2438 | theorem "[Dense-region theorem]" (`thm:dense-region`) | "[The theorem for $q\le1/3$]" |
| 2469 | §5 "The intermediate region: the one-frontier reduction for $m\ge9$" | "Above the threshold $1/3<q<1/2$: the single-outlier reduction for $m\ge9$" |
| 2573 | §5.2 "No frontier, and uniqueness of a frontier" | "At most one eigenvalue above $q$" |
| 2575 | lemma "[No-frontier case]" (`lem:no-frontier`) | "[No eigenvalue above $q$]" |
| 2623 | §5.3 "The forced-variance ceiling" | "A variance lower bound and the eigenvalue upper bound" |
| 2627 | lemma "[Forced variance]" (`lem:forced-variance`) | "[Variance lower bound]" |
| 3231 | lemma "[Defect bounds]" (`lem:T-bounds`) | "[Bounds for $T_N$]" |
| 3558 | lemma "[Above the cycle scale]" (`lem:linear-high-zeta`) | "[The regime $\zeta\ge N$]" |
| 3684 | §"Below the cycle scale: the growth lemma" | "The regime $\zeta\le N$: the growth lemma" |
| 3929 | lemma "[Below the cycle scale]" (`lem:linear-low-zeta`) | "[The regime $\zeta\le N$]" |
| 3968 | §"The exceptional cycle scale $N=7$, i.e. $m=9$" | "The exceptional case $N=7$, i.e. $m=9$" |
| 3331 | §"The quadratic Huber branch" | "The regime $2\rho\xi\le1$" |
| 3391 | prop "[Quadratic branch]" (`prop:quadratic-branch`) | "[The regime $2\rho\xi\le1$]" |
| 3452 | §"The linear Huber branch" | "The regime $2\rho\xi>1$" |
| 4171 | prop "[Linear branch]" (`prop:linear-branch`) | "[The regime $2\rho\xi>1$]" |
| 3554 | §"Two broad estimates for the linear payment" | "The cases $\zeta\ge N$ and $v\ge5/8$" |

Prose touch-ups tied to these: "the forced-variance lemma" → "the variance lower bound" (§5.2 end);
"the forced-variance inequality" → "the variance lower bound" (Equality-and-stability remark).
Typos fixed in the same pass: proof-map missing period; "contradicts with"; "gives"→"give";
"seciton"; "the both side"; "only $\ell>0$ case"; "centre"→"center"; "the the".

## B. Label-key dictionary (planned; NOT yet executed)

Execute in ONE batch: rename in the .tex (definition + every `\ref`/`\Cref`/`\eqref`), then update
Lean docstrings and `COMPLETE_LEAN_PLAN.md`, `FIDELITY_PLAN.md`, `CERTIFICATE_REPLACEMENT.md`,
`PHASE_R_PLAN.md`. Keep this table as the permanent old→new map for released cross-references.

Settled targets (rename when batch runs):

| Old label | New label |
|---|---|
| `lem:HS-budget` | `lem:HS-bound` |
| `eq:HS-budget` | `eq:HS-bound` |
| `sec:dense-region` | `sec:below-threshold` |
| `thm:dense-region` | `thm:below-threshold` |
| `sec:regionII-operator` | `sec:above-threshold` |
| `lem:no-frontier` | `lem:no-eigenvalue-above-q` |
| `eq:alpha-frontier` | `eq:alpha-above-q` |
| `lem:forced-variance` | `lem:variance-lower-bound` |
| `subsec:forced-variance` | `subsec:variance-lower-bound` |
| `eq:forced-variance` | `eq:variance-lower-bound` |
| `eq:alpha-ceiling` | `eq:alpha-upper-bound` |
| `eq:alpha-ceiling-poly` | `eq:alpha-upper-bound-poly` |

Pending the open decisions below:

| Old label | Candidate new label | Blocked on |
|---|---|---|
| `eq:dense-defect` | `eq:dense-lower-identity` (?) | defect naming |
| `prop:master-defect`, `eq:master-defect`, `subsec:master-defect` | tbd | defect/master naming |
| `eq:k-safe`, `lem:safe-channel`, `eq:safe-channel`, `eq:gs-safe-lower` | tbd | coupling/overlap naming |
| `lem:direct-channel`, `eq:direct-channel` | tbd | coupling/overlap naming |
| `eq:shape-defs`, `eq:shape-budget`, `eq:H-shape`, `eq:Q-shape`, `subsec:shape-elim`, `thm:huber-elim`, `eq:huber-payment` | tbd | shape/parameters naming |
| `prop:huber-dual`, `sec:huber` | tbd | envelope naming (likely `prop:envelope-dual`, `sec:envelope`) |
| `sec:quadratic`, `sec:linear`, `prop:quadratic-branch`, `prop:linear-branch` | tbd | branch naming |
| `eq:trace-payment`, `eq:shift-payment`, `eq:*-payment-*` | tbd | payment replacement |
| `eq:F-def` (normalized defect $F_N$) | tbd | defect naming |

## C. Open decisions (each marked with a `\tk{TODO (naming): ...}` in the .tex)

1. **defect / master / payment** (`subsec:master-defect`) — rejected so far: defect, excess,
   master, payment, contribution, "Reduction to the inequality ..." (too long),
   "Lower bound in terms of ..." (too weak). No candidate yet.
2. **"coupling" vs "overlap"** for $\gamma=\langle g,\phi\rangle$ (the two channel lemmas).
   Origin of "coupling": $g$ is the off-diagonal block of $T_U$, coupling the constant
   direction to the mean-zero block. "Overlap upper bound" felt off to the owner; undecided.
   Lean currently `coupling_*`.
3. **"shape" of $\phi$** = the triple $(a_\phi,b,K)$ from $|\phi|=a_\phi\one+b\phi+k$ — NOT the
   $(v,\zeta)$ chart. Rejected: shape, profile. "It is at last a decomposition of $|\phi|$" —
   no settled name for the variables or the optimization step yet.
4. **"envelope"** for $\psi(\xi,\rho)$ (`sec:huber`, `thm:huber-elim`, `prop:huber-dual`) —
   "Huber" will be dropped from display text, but "envelope" alone was judged not good either;
   undecided.
5. **leading vs outlier eigenvalue** for the prose sweep of "frontier" (§5 title already uses
   "single-outlier"); decide before the global prose sweep.

Resolved this round (2026-08-06, second pass): branch subsections/props are titled purely by
condition, "The regime $2\rho\xi\le1$" / "The regime $2\rho\xi>1$" (no "witness" in titles);
"Two broad estimates for the linear payment" → "The cases $\zeta\ge N$ and $v\ge5/8$".
