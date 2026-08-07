# Renaming dictionary — `paper_new_region2_v2.tex`

Companion to `TERMINOLOGY.md`. Records (A) display-text renames already performed, (B) the
old→new **label-key dictionary** — fully executed in the .tex on 2026-08-07 in two batches
(content renames up to `\tk{Revised until here.}`, then region prefixes over ALL of §4 and §5;
labels are shared with the Lean side and its docs, so this file is the permanent migration map
for Lean-verification pointers), and (C) decisions still open.

Started 2026-08-06; label batches executed 2026-08-07.

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

## A2. Symbol renames performed (2026-08-06, §5 and proof-map Part 3 only)

| Old | New | Reason |
|---|---|---|
| `\alpha` (the one eigenvalue above `q`) | `\Lambda` | the largest eigenvalue; `\alpha` was arbitrary. Not renamed elsewhere: the dummy scalar in the block determinant identity (§4.1), the multi-indices in §4.3–4.4, the Laguerre parameter in §7 |
| `L` (bound on the other eigenvalues) | `M` | `L` collided with the generating function `L_-(z)` two subsections earlier |
| `A_m` | `\Lambda_m` | named after the eigenvalue it is evaluated at: `\Lambda_m = 2M^{m-2}+mk_m(\Lambda)` |
| `B_m` | `M_m` | likewise `M_m = 2M^{m-2}+mk_m(M)`; the parallel structure is now visible |
| `K_A` | `K_\Lambda` | follows `A_m → \Lambda_m` (its companion `K_L` became `K_M` automatically) |
| `R_m` | unchanged | accepted as "residual" |

## A3. Symbol renames performed in §5.4 (2026-08-06/07, second pass)

| Old | New | Reason |
|---|---|---|
| `C_m` | `\Omega_m` | collided with the cycle `C_m`. Ω, Π, Υ, Ψ are the only unused uppercase Greek; Ψ clashes visually with the adjacent ψ in `\Omega_m\psi(\xi,\rho)`, Π reads as a product |
| `\cH` | `\kappa` | `\mathcal H` reads as a Hilbert space. κ is unused and — unlike τ — cannot be confused with the variable `t` of the polyhedron `\overline S`. Preamble macro `\cH` deleted |
| `\cQ` | removed | every use was of the form "Q ≥ …", so the displays now carry the quantity they bound; also collided with the chart's `Q`. Preamble macro deleted |
| `d = \Lambda-q`, `f = \Lambda-M`, `e = 1-2\Lambda` | written out | `f` and `d` are re-used as `f(\eta)` and `d = N+1-\eta` in the growth lemma; `e` collided with `e^t` in the compensation lemma. One gain: `\Lambda^2+e = (1-\Lambda)^2`, so `\beta(\gamma)=\sqrt{(1-\Lambda)^2-2\gamma\sqrt{2\Lambda}}-\Lambda` |
| `z = a_\phi^2` | `a_\phi^2` | `z` was the formal variable of `L_-(z)`, `Y(z)` in §5.1–5.3; `\sqrt z` became `a_\phi` |
| `K = \norm k^2` | `\norm{\phi_\perp}^2` | `K` collided with the kernel `K` of §3 and with `K_\Lambda`, `K_M`; the AM–GM step now uses a neutral bound variable `t` |
| `k` (part of `|\phi|` orthogonal to `\one,\phi`) | `\phi_\perp` | `k` read as a constant, not a function, and collided with summation indices |

Labels not yet touched, to go in the batch below: `eq:Am-def`, `eq:Bm-def`, `eq:AB-order`,
`eq:KA-def`, `eq:KA-sum`, `eq:L-def`, `eq:L-order`, `eq:alpha-frontier`, `eq:alpha-ceiling`,
`eq:alpha-ceiling-poly`, `subsec:forced-variance`.

Prose touch-ups tied to these: "the forced-variance lemma" → "the variance lower bound" (§5.2 end);
"the forced-variance inequality" → "the variance lower bound" (Equality-and-stability remark).
Typos fixed in the same pass: proof-map missing period; "contradicts with"; "gives"→"give";
"seciton"; "the both side"; "only $\ell>0$ case"; "centre"→"center"; "the the".

## B. Label-key dictionary (original → current)

### Naming scheme (2026-08-07, region-prefix pass)

Two batches were executed in the .tex on 2026-08-07: first, content renames for everything
before `\tk{Revised until here.}`; second, region prefixes over ALL labels of §4 and §5
(including labels after the marker, whose jargon stems are still unrevised — see B2). Every
`\label` and every `\ref`/`\Cref`/`\eqref` was updated; verified: no dangling references, no
duplicate labels. **Lean docstrings and the plan docs (`COMPLETE_LEAN_PLAN.md`,
`FIDELITY_PLAN.md`, `CERTIFICATE_REPLACEMENT.md`, `PHASE_R_PLAN.md`) still quote ORIGINAL keys —
B1 below is the permanent migration map for them and for Lean-verification pointers.**

The scheme:

- Every label defined inside §4 ($p\ge2/3$) carries the region prefix **`pge23-`**; every label
  defined inside §5 ($1/2<p<2/3$ — which includes the chart and the two branch subsections, i.e.
  everything up to `sec:assembly`) carries **`plt23-`**. New labels in these two sections must
  take the prefix; cross-region key conflicts are then impossible. (`plt23` = "$p$ less than
  $2/3$", strict, since §5 assumes $p<2/3$; switching to `ple23` would be one global replace.)
- The old `dense-` namespace is absorbed into `pge23-` (e.g. `eq:dense-rho` → `eq:pge23-rho`).
- Section-level labels: `sec:pge23` (§4), `sec:plt23` (§5), and §4's closing theorem
  `thm:pge23-main`.
- **Pairing of the two Schur-complement identities** (they are the mirror lemmas of the two
  regions): `subsec:pge23-two-sided-schur` / `lem:pge23-two-sided-identity` /
  `eq:pge23-two-sided-identity` ↔ `subsec:plt23-one-sided-schur` /
  `lem:plt23-one-sided-identity` / `eq:plt23-one-sided-identity`. The second identity inside
  `lem:pge23-two-sided-identity` — the rearrangement for $t(C_m,W)$ alone, former
  `eq:dense-defect` — is keyed `eq:pge23-one-sided-identity`, mirroring §5's one-sided identity
  (owner's choice, 2026-08-07). Display texts untouched (owner: pair the labels only).
- Deliberately UNPREFIXED exceptions — defined in §4 but used by §5's proof (they are really §3
  material): `eq:logdet-cycle`, `eq:block-determinant-identity`. A `\tk{TODO (structure)}` in
  §3.3, after `eq:finite-trace-cycle`, marks the planned move into §3; the move itself is NOT
  yet performed (owner's decision).
- `sec:chart`, `sec:quadratic`, `sec:linear` were `\subsection`s carrying a wrong `sec:` type
  prefix; they are now `subsec:plt23-chart`, `subsec:plt23-quadratic`, `subsec:plt23-linear`.
- Removed: `eq:dense-rho-pointwise` (dead label inside an unnumbered `align*`, never
  referenced). Collapsed: the unreferenced triple alias
  `subsec:forced-variance`+`sec:huber`+`subsec:shape-elim` → single `subsec:plt23-minimization`.

### B1. Consolidated map: original label → current label

Original = the key as it appears in the Lean docstrings / plan docs (pre-2026-08-07). Labels not
listed here were never renamed (§1–§3, `sec:assembly`, `sec:transferable`, `app:bernstein`, and
the two unprefixed exceptions above).

| Original label | Current label |
|---|---|
| `cor:two-witnesses` | `cor:plt23-two-witnesses` |
| `eq:AB-order` | `eq:plt23-Lambdam-Mm-positive` |
| `eq:Am-def` | `eq:plt23-Lambdam-def` |
| `eq:Bm-def` | `eq:plt23-Mm-def` |
| `eq:C-xi-rho` | `eq:plt23-C-xi-rho` |
| `eq:D-Q` | `eq:plt23-D-Q` |
| `eq:E-N` | `eq:plt23-E-N` |
| `eq:F-T` | `eq:plt23-F-T` |
| `eq:F-def` | `eq:plt23-F-def` |
| `eq:H-N` | `eq:plt23-H-N` |
| `eq:H-identity` | `eq:plt23-H-identity` |
| `eq:H-lower` | `eq:plt23-H-lower` |
| `eq:HS-budget` | `eq:plt23-HS-bound` |
| `eq:J-domain` | `eq:plt23-J-domain` |
| `eq:J-ineq` | `eq:plt23-J-ineq` |
| `eq:K-AMGM` | `eq:plt23-K-AMGM` |
| `eq:K-N-def` | `eq:plt23-K-N-def` |
| `eq:KA-AMGM` | `eq:plt23-KA-AMGM` |
| `eq:KA-def` | `eq:plt23-KA-def` |
| `eq:KA-sum` | `eq:plt23-KA-sum` |
| `eq:KL-def` | `eq:plt23-KL-def` |
| `eq:KL-first-term` | `eq:plt23-KL-first-term` |
| `eq:KL-sum` | `eq:plt23-KL-sum` |
| `eq:L-N-def` | `eq:plt23-L-N-def` |
| `eq:L-def` | `eq:plt23-M-def` |
| `eq:L-order` | `eq:plt23-M-Lambda-order` |
| `eq:L-series` | `eq:plt23-Lminus-def` |
| `eq:L9-data` | `eq:plt23-L9-data` |
| `eq:M-lower` | `eq:plt23-M-lower` |
| `eq:N-def` | `eq:plt23-N-def` |
| `eq:N7-corner` | `eq:plt23-N7-corner` |
| `eq:P-N` | `eq:plt23-P-N` |
| `eq:P9-small` | `eq:plt23-P9-small` |
| `eq:Q-chart` | `eq:plt23-Q-chart` |
| `eq:Q-shape` | `eq:plt23-min-over-Sbar` |
| `eq:Q-upper` | `eq:plt23-Q-upper` |
| `eq:Q10` | `eq:plt23-Q10` |
| `eq:R-log-derivative` | `eq:plt23-R-log-derivative` |
| `eq:Rm-def` | `eq:plt23-Rm-def` |
| `eq:Sbar` | `eq:plt23-Sbar` |
| `eq:T-bound-one` | `eq:plt23-T-bound-one` |
| `eq:T-bound-two` | `eq:plt23-T-bound-two` |
| `eq:T-def` | `eq:plt23-T-def` |
| `eq:T-geometric-cancel` | `eq:plt23-T-geometric-cancel` |
| `eq:T-high-zeta` | `eq:plt23-T-high-zeta` |
| `eq:T-positive` | `eq:plt23-T-positive` |
| `eq:T-tangent-bound` | `eq:plt23-T-tangent-bound` |
| `eq:T7-middle` | `eq:plt23-T7-middle` |
| `eq:X-coeff` | `eq:plt23-Y-coeff` |
| `eq:absphi-lower` | `eq:plt23-absphi-lower` |
| `eq:alpha-ceiling` | `eq:plt23-alpha-ceiling` |
| `eq:alpha-ceiling-poly` | `eq:plt23-alpha-ceiling-poly` |
| `eq:alpha-frontier` | `eq:plt23-Lambda-above-q` |
| `eq:aphi-lower` | `eq:plt23-aphi-lower` |
| `eq:b-gamma-budget` | `eq:plt23-b-gamma-budget` |
| `eq:beta-gamma` | `eq:plt23-beta-gamma` |
| `eq:beta-rational` | `eq:plt23-beta-rational` |
| `eq:chart-basic` | `eq:plt23-chart-basic` |
| `eq:chart-d-e` | `eq:plt23-chart-d-e` |
| `eq:chart-domain` | `eq:plt23-chart-domain` |
| `eq:chart-inverse-1` | `eq:plt23-chart-inverse-1` |
| `eq:compensation` | `eq:plt23-compensation` |
| `eq:cxi-crude` | `eq:plt23-cxi-crude` |
| `eq:cxi-small-v-poly` | `eq:plt23-cxi-small-v-poly` |
| `eq:dense-Lminus` | `eq:pge23-Lminus` |
| `eq:dense-Lplus` | `eq:pge23-Lplus` |
| `eq:dense-P-in-h` | `eq:pge23-P-in-h` |
| `eq:dense-Phi` | `eq:pge23-Phi` |
| `eq:dense-Pmr` | `eq:pge23-Pmr` |
| `eq:dense-Ptilde` | `eq:pge23-Ptilde` |
| `eq:dense-Ptilde-in-c` | `eq:pge23-Ptilde-in-c` |
| `eq:dense-Rminus` | `eq:pge23-Rminus` |
| `eq:dense-Rplus` | `eq:pge23-Rplus` |
| `eq:dense-Sm` | `eq:pge23-Sm` |
| `eq:dense-beta-first` | `eq:pge23-beta-first` |
| `eq:dense-beta-h` | `eq:pge23-beta-h` |
| `eq:dense-beta-h-deriv` | `eq:pge23-beta-h-deriv` |
| `eq:dense-beta-integral` | `eq:pge23-beta-integral` |
| `eq:dense-beta-second` | `eq:pge23-beta-second` |
| `eq:dense-cycle-path` | `eq:pge23-cycle-path` |
| `eq:dense-cycle-sum` | `eq:pge23-two-sided-identity` |
| `eq:dense-defect` | `eq:pge23-one-sided-identity` |
| `eq:dense-diagonal-min` | `eq:pge23-diagonal-min` |
| `eq:dense-diagonal-target` | `eq:pge23-diagonal-target` |
| `eq:dense-dirichlet-identity` | `eq:pge23-dirichlet-identity` |
| `eq:dense-dirichlet-moment` | `eq:pge23-dirichlet-moment` |
| `eq:dense-even-expansion` | `eq:pge23-even-expansion` |
| `eq:dense-expansion` | `eq:pge23-expansion` |
| `eq:dense-gamma-smoothing` | `eq:pge23-laplace-gamma` |
| `eq:dense-h-diagonal` | `eq:pge23-h-diagonal` |
| `eq:dense-h-gf` | `eq:pge23-h-gf` |
| `eq:dense-h-split` | `eq:pge23-h-split` |
| `eq:dense-n` | `eq:pge23-n` |
| `eq:dense-path-gf` | `eq:pge23-path-gf` |
| `eq:dense-q` | `eq:pge23-q` |
| `eq:dense-rho` | `eq:pge23-rho` |
| `eq:dense-rho-centered` | `eq:pge23-rho-centered` |
| `eq:dense-rho-derivative` | `eq:pge23-rho-derivative` |
| `eq:dense-rho-pointwise` | *(removed)* |
| `eq:dense-shifted-positive` | `eq:pge23-shifted-positive` |
| `eq:dense-xj` | `eq:pge23-xj` |
| `eq:direct-channel` | `eq:plt23-gamma-upper-bound` |
| `eq:direct-pairing` | `eq:plt23-phiplus-pairing` |
| `eq:discriminant-check` | `eq:plt23-discriminant-check` |
| `eq:ell-small-v` | `eq:plt23-ell-small-v` |
| `eq:forced-variance` | `eq:plt23-forced-variance` |
| `eq:g-decomp` | `eq:plt23-g-decomp` |
| `eq:gZ-step` | `eq:plt23-gZ-step` |
| `eq:gamma-G` | `eq:pge23-gamma-G` |
| `eq:gamma-Gprime` | `eq:pge23-gamma-Gprime` |
| `eq:gamma-H` | `eq:pge23-gamma-H` |
| `eq:gamma-H-integral` | `eq:pge23-gamma-H-integral` |
| `eq:gamma-Hbstar` | `eq:pge23-gamma-Hbstar` |
| `eq:gamma-L` | `eq:pge23-gamma-L` |
| `eq:gamma-L-rational` | `eq:pge23-gamma-L-rational` |
| `eq:gamma-Lprime` | `eq:pge23-gamma-Lprime` |
| `eq:gamma-Lsecond` | `eq:pge23-gamma-Lsecond` |
| `eq:gamma-ODE` | `eq:pge23-gamma-ODE` |
| `eq:gamma-Stein` | `eq:pge23-gamma-Stein` |
| `eq:gamma-bstar` | `eq:pge23-gamma-bstar` |
| `eq:gamma-crossing` | `eq:pge23-gamma-crossing` |
| `eq:gamma-ibp-max` | `eq:pge23-gamma-ibp-max` |
| `eq:gamma-max-ratio` | `eq:pge23-gamma-max-ratio` |
| `eq:gamma-moment` | `eq:pge23-gamma-moment` |
| `eq:gamma-moment2` | `eq:pge23-gamma-moment2` |
| `eq:gamma-recurrence` | `eq:pge23-gamma-recurrence` |
| `eq:gs-safe-lower` | `eq:plt23-gs-norm-lower` |
| `eq:h-sufficient` | `eq:plt23-h-sufficient` |
| `eq:huber-payment` | `eq:plt23-huber-payment` |
| `eq:k-safe` | `eq:plt23-km-min-at-M` |
| `eq:key-log-comp` | `eq:plt23-key-log-comp` |
| `eq:km-def` | `eq:plt23-km-def` |
| `eq:laplace-kernel` | `eq:pge23-laplace-kernel` |
| `eq:large-v-target` | `eq:plt23-large-v-target` |
| `eq:linear-branch` | `eq:plt23-linear-branch` |
| `eq:linear-comp-expanded` | `eq:plt23-linear-comp-expanded` |
| `eq:linear-core` | `eq:plt23-linear-core` |
| `eq:linear-payment-start` | `eq:plt23-linear-payment-start` |
| `eq:linear-shift-lower` | `eq:plt23-Lminus-linear-lower` |
| `eq:log-shape-bound` | `eq:plt23-log-shape-bound` |
| `eq:master-defect` | `eq:plt23-splitting-lower-bound` |
| `eq:middle-target` | `eq:plt23-middle-target` |
| `eq:one-d-gamma` | `eq:plt23-one-d-gamma` |
| `eq:one-d-t` | `eq:plt23-one-d-t` |
| `eq:overapprox` | `eq:plt23-overapprox` |
| `eq:phi-parts` | `eq:plt23-phi-parts` |
| `eq:psi-def` | `eq:plt23-psi-def` |
| `eq:psi-dual` | `eq:plt23-psi-dual` |
| `eq:quad-payment-M` | `eq:plt23-quad-payment-M` |
| `eq:quad-payment-final` | `eq:plt23-quad-payment-final` |
| `eq:quadratic-branch` | `eq:plt23-quadratic-branch` |
| `eq:quadratic-payment-start` | `eq:plt23-quadratic-payment-start` |
| `eq:regionII` | `eq:plt23-range` |
| `eq:rho-def` | `eq:plt23-rho-def` |
| `eq:safe-channel` | `eq:plt23-gs-inner-lower` |
| `eq:scalar-target` | `eq:plt23-scalar-target` |
| `eq:shape-budget` | `eq:plt23-absphi-normalization` |
| `eq:shape-defs` | `eq:plt23-absphi-decomp` |
| `eq:shift` | `eq:plt23-one-sided-identity` |
| `eq:shift-factorization` | `eq:plt23-one-sided-factorization` |
| `eq:shift-payment` | `eq:plt23-Lminus-lower` |
| `eq:sigma-lower-J` | `eq:plt23-sigma-lower-J` |
| `eq:small-v-square-diff` | `eq:plt23-small-v-square-diff` |
| `eq:sqrt-compensation` | `eq:plt23-sqrt-compensation` |
| `eq:trace-payment` | `eq:plt23-trace-upper` |
| `eq:varphi-7/10` | `eq:plt23-varphi-7/10` |
| `eq:varphi-cxi` | `eq:plt23-varphi-cxi` |
| `eq:witness-linear` | `eq:plt23-witness-linear` |
| `eq:witness-quadratic` | `eq:plt23-witness-quadratic` |
| `eq:xi-comp-bound` | `eq:plt23-xi-comp-bound` |
| `eq:xi-def` | `eq:plt23-xi-def` |
| `eq:xi-small-v` | `eq:plt23-xi-small-v` |
| `eq:xi-zeta-v` | `eq:plt23-xi-zeta-v` |
| `eq:y-middle` | `eq:plt23-y-middle` |
| `eq:zeta-domain` | `eq:plt23-zeta-domain` |
| `eq:zeta-lower` | `eq:plt23-zeta-lower` |
| `eq:zeta-simple-lower` | `eq:plt23-zeta-simple-lower` |
| `eq:zeta-upper-Z` | `eq:plt23-zeta-upper-Z` |
| `eq:zeta-v-def` | `eq:plt23-zeta-v-def` |
| `eq:zeta-v-inverse` | `eq:plt23-zeta-v-inverse` |
| `lem:HS-budget` | `lem:plt23-HS-bound` |
| `lem:J-growth` | `lem:plt23-J-growth` |
| `lem:N7-middle-v` | `lem:plt23-N7-middle-v` |
| `lem:N7-small-v` | `lem:plt23-N7-small-v` |
| `lem:T-bounds` | `lem:plt23-T-bounds` |
| `lem:analytic-reading` | `lem:series-expansions` |
| `lem:chart-domain` | `lem:plt23-chart-domain` |
| `lem:compensation` | `lem:plt23-compensation` |
| `lem:dense-beta` | `lem:pge23-beta` |
| `lem:dense-cancellation` | `lem:pge23-two-sided-identity` |
| `lem:dense-dirichlet` | `lem:pge23-dirichlet` |
| `lem:dense-ell-negative` | `lem:pge23-ell-negative` |
| `lem:dense-gamma-smoothing` | `lem:pge23-laplace-gamma` |
| `lem:direct-channel` | `lem:plt23-gamma-upper-bound` |
| `lem:forced-variance` | `lem:plt23-forced-variance` |
| `lem:gamma-moment` | `lem:pge23-gamma-moment` |
| `lem:linear-high-zeta` | `lem:plt23-linear-high-zeta` |
| `lem:linear-large-v` | `lem:plt23-linear-large-v` |
| `lem:linear-low-zeta` | `lem:plt23-linear-low-zeta` |
| `lem:no-frontier` | `lem:plt23-eigenvalues-above-q` |
| `lem:quad-coeff` | `lem:plt23-quad-coeff` |
| `lem:safe-channel` | `lem:plt23-gs-lower-bound` |
| `lem:shift` | `lem:plt23-one-sided-identity` |
| `prop:dense-expansion` | `prop:pge23-expansion` |
| `prop:dense-gamma-positive` | `prop:pge23-gamma-positive` |
| `prop:huber-dual` | `prop:plt23-huber-dual` |
| `prop:linear-branch` | `prop:plt23-linear-branch` |
| `prop:master-defect` | `prop:plt23-splitting-lower-bound` |
| `prop:quadratic-branch` | `prop:plt23-quadratic-branch` |
| `rem:dense-threshold` | `rem:pge23-threshold` |
| `sec:chart` | `subsec:plt23-chart` |
| `sec:dense-region` | `sec:pge23` |
| `sec:huber` | `subsec:plt23-minimization` |
| `sec:linear` | `subsec:plt23-linear` |
| `sec:quadratic` | `subsec:plt23-quadratic` |
| `sec:regionII-operator` | `sec:plt23` |
| `subsec:forced-variance` | `subsec:plt23-minimization` |
| `subsec:gamma-moment-proof` | `subsec:pge23-gamma-moment-proof` |
| `subsec:master-defect` | `subsec:plt23-splitting-lower-bound` |
| `subsec:shape-elim` | `subsec:plt23-minimization` |
| `subsec:shift` | `subsec:plt23-one-sided-schur` |
| `subsec:two-sided` | `subsec:pge23-two-sided-schur` |
| `thm:dense-region` | `thm:pge23-main` |
| `thm:huber-elim` | `thm:plt23-huber-elim` |

Notes on the non-mechanical renames (stem changes, not just prefixes):

- `lem:*-two-sided-identity`/`eq:*-two-sided-identity`: see the pairing bullet above.
- `lem:plt23-eigenvalues-above-q` (was `lem:no-frontier`): display "[Eigenvalues above $q$]";
  the statement now contains both "at most one" and "if none, the theorem holds", so the earlier
  planned key `lem:no-eigenvalue-above-q` no longer fit.
- Symbol-driven: `eq:plt23-Lambda-above-q`, `eq:plt23-M-def`, `eq:plt23-M-Lambda-order`,
  `eq:plt23-Lambdam-def`, `eq:plt23-Mm-def` follow the symbol renames $\alpha\to\Lambda$,
  $L\to M$, $A_m\to\Lambda_m$, $B_m\to M_m$ (§A2); `eq:plt23-Y-coeff` follows the series
  rename $X\to Y$; `eq:plt23-Lminus-def` replaced "L-series" (number-theory collision).
- `eq:plt23-Lambdam-Mm-positive` (was `eq:AB-order`): the displayed content changed — it now
  states $\Lambda_m>0$, $M_m>0$, no ordering claim.
- `eq:plt23-trace-upper` (was `eq:trace-payment`): upper bound for $\Tr(A^m)$, displayed as a
  lower bound for $-\Tr(A^m)$; `eq:plt23-Lminus-lower`/`eq:plt23-Lminus-linear-lower` are the
  lower bounds for $m[z^m]L_-$ (final form / linear-term form).
- `lem:plt23-gamma-upper-bound` ("[Upper bound for $\gamma$]", $\gamma=\langle g,\phi\rangle$ —
  not the Gamma law, which lives under `pge23-gamma-*`), `lem:plt23-gs-lower-bound`
  ("[Lower bound for $\|g_s\|$]") with `eq:plt23-gs-inner-lower` (inner-product form, defines
  $\mathcal H$) and `eq:plt23-gs-norm-lower` (Cauchy--Schwarz form); `eq:plt23-phiplus-pairing`
  is $\langle\phi_+,T_U\phi\rangle\le a_\phi^2/4$.
- `eq:plt23-absphi-decomp` / `eq:plt23-absphi-normalization`: the decomposition
  $|\phi|=a_\phi\mathbf1+b\phi+\phi_\perp$ and its normalization $a_\phi^2+b^2+\|\phi_\perp\|^2=1$
  (sidesteps the rejected "shape/profile" naming).
- `eq:plt23-km-min-at-M`: $k_m(\lambda)\ge k_m(M)$ on $[-M,M]$. `eq:plt23-min-over-Sbar`: the
  minimization over the polyhedron $\overline S$ (`eq:plt23-Sbar`).
- `*:plt23-splitting-lower-bound` (was `*:master-defect`): named after the settled display
  "A lower bound via splitting $g$ along the eigenfunction of $\Lambda$".
- `lem:pge23-laplace-gamma` etc.: display "[Laplace--gamma representation]" (was "gamma
  smoothing"). `lem:series-expansions` (§3, unprefixed): display "[Series expansions used
  below]".

### B2. Planned stem renames — after-marker labels (keys already prefixed; revise stems together
with their display text when the revision pass reaches them)

| Current label | Planned | Status |
|---|---|---|
| `lem:plt23-forced-variance` | `lem:plt23-variance-lower-bound` | settled (display already "[Variance lower bound]") |
| `eq:plt23-forced-variance` | `eq:plt23-variance-lower-bound` | settled |
| `eq:plt23-alpha-ceiling` | `eq:plt23-Lambda-upper-bound` | settled ($\alpha\to\Lambda$) |
| `eq:plt23-alpha-ceiling-poly` | `eq:plt23-Lambda-upper-bound-poly` | settled |
| `thm:plt23-huber-elim`, `prop:plt23-huber-dual`, `eq:plt23-huber-payment` | tbd | envelope naming (open C.4) |
| `eq:plt23-quadratic-payment-start`, `eq:plt23-quad-payment-M`, `eq:plt23-quad-payment-final`, `eq:plt23-linear-payment-start` | tbd | payment stems; follow the `eq:plt23-Lminus-lower`/`eq:plt23-trace-upper` style |
| `eq:plt23-F-def` (normalized defect $F_N$) | tbd | defect naming |
| `eq:plt23-log-shape-bound` | tbd | shape stem |
| `eq:plt23-b-gamma-budget` | tbd | budget stem |

### B3. (resolved 2026-08-07)

The former TODO `eq:dense-defect`/`eq:pge23-defect` — the identity
$t(C_m,W)-(p^m-pq^{m-1})=q^{m-1}+S_m-t(C_m,U)$ — is now **`eq:pge23-one-sided-identity`**
(owner's choice): it states the identity for $t(C_m,W)$ alone, mirroring §5's
`eq:plt23-one-sided-identity`.

## C. Open decisions (updated 2026-08-07 after the label batches)

1. **defect / master / payment** — RESOLVED in the revised region by direct statement-of-content
   names taken from the settled display text: `prop:plt23-splitting-lower-bound`,
   `eq:plt23-trace-upper`, `eq:plt23-Lminus-lower`, and `eq:pge23-one-sided-identity` (B3).
   Residue: only `eq:plt23-F-def` (after marker) still carries "defect".
2. **"coupling" vs "overlap"** — SIDESTEPPED: displays are symbol-based ("Upper bound for
   $\gamma$" / "Lower bound for $\|g_s\|$"), so labels follow the symbols
   (`lem:plt23-gamma-upper-bound`, `lem:plt23-gs-lower-bound`). The word choice only matters now
   for the prose sweep and the Lean `coupling_*` names.
3. **"shape" of $\phi$** — SIDESTEPPED for the labels: named after the object itself
   (`eq:plt23-absphi-decomp`, `eq:plt23-absphi-normalization`). No display name needed so far.
4. **"envelope"** for $\psi(\xi,\rho)$ (`thm:plt23-huber-elim`, `prop:plt23-huber-dual`) — still
   OPEN; those labels are after the marker. Note `sec:huber` no longer exists (was an
   unreferenced alias, collapsed into `subsec:plt23-minimization`).
5. **leading vs outlier eigenvalue** for the prose sweep of "frontier" (§5 title already uses
   "single-outlier"); decide before the global prose sweep.

Resolved this round (2026-08-06, second pass): branch subsections/props are titled purely by
condition, "The regime $2\rho\xi\le1$" / "The regime $2\rho\xi>1$" (no "witness" in titles);
"Two broad estimates for the linear payment" → "The cases $\zeta\ge N$ and $v\ge5/8$".
