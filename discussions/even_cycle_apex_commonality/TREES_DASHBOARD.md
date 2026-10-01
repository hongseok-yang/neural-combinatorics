# Verification dashboard — independent apices of trees

Single live status page for the Lean formalization described in
[`TREES_VERIFICATION_PLAN.md`](TREES_VERIFICATION_PLAN.md) of
[`trees_apices_commonness.tex`](trees_apices_commonness.tex).  Maintained by the formalizing agent;
every status change must cite its evidence.  The even-cycle dashboard
[`DASHBOARD.md`](DASHBOARD.md) is frozen and is not touched by this work.

Status legend: ✅ done (gate passed, evidence recorded) · 🚧 under construction (started, gate not
passed; a one-line reason if blocked) · ❌ not started · — not applicable (replaced or excluded by a
design decision in the plan).

Hardness: Easy · Medium · Hard — an estimate for an axiom-free Lean proof, not for the paper argument.

Last updated: 2026-10-02 (complete: T0–T9 ✅; P1–P5 proved, axiom-clean; deviations Y1–Y10 in `TREES_DEVIATIONS.md`, all internal)

## Milestones

| Milestone | What it is | Status | Hardness | Gate / evidence |
|---|---|:---:|:---:|---|
| T0 | `TreeApex` library in the existing package (T-D7), index, `CheckAxiomsTree.lean`, smoke theorem, import-closure check, regression script with `--host` | ✅ | Easy | `smoke_density_near_host` `[propext, Classical.choice, Quot.sound]`; `CheckImportsTree.lean` OK (16 light modules); script 300+200 trials, `--negative` trips; 2026-10-02 |
| T1 | `apexGraph` and its edge split, `apexCycle_eq_apexGraph`, connectivity, edge count, `K₂ P₃ K₃`, `RecTree`/`treeGraph`/`treeEdges`, the `IsTree ↔ RecTree` bridge, `apexGraph_comap`, density invariance | ✅ | Hard | `exists_recTree_iso`, `prod_edgePairs_apexGraph`, `apexGraph_edgeCount`, `homDensity_apexGraph_of_iso` (15 decls) `[propext, Classical.choice, Quot.sound]` or a subset; 2026-10-02 |
| T2 | `ProbHost`, scalars `deg cod tri E D R` and their `hostDensity` identifications and bounds, reference weights `ρ_Y ρ_B ρ_T`, `hostDensity_apexGraph_treeGraph`, leaf recursion, doubled host and block identity, Goodman on hosts, two regression hosts | ✅ | Medium | `hostDens_apexGraph_treeGraph`, `SymLaw.treeWeight_snoc`, `hostDens_double_of_connected`, `host_half_le_sigma`, `host_goodman_identity`, 10 regression values (`regHost₁/₂_E/D/R/sigma/tau`) `[propext, Classical.choice, Quot.sound]`; 2026-10-02 |
| T3 | Finite relative entropy: `relEnt`, Gibbs, `KL ≥ 0`, product chain rule, reindexing, marginal/conditional conventions, Jensen for `log` | ✅ | Medium | `relEnt_le_log_sum`, `relEnt_prod`, `relEnt_one` + generic tree extension `SymLaw.relEnt_treeLaw` etc. `[propext, Classical.choice, Quot.sound]`; Jensen not needed (Gibbs from `log u ≤ u − 1`); 2026-10-02 |
| T4 | Triangle law (`h_ge`, `I_le`) and book law (`relEnt_book`, `g_eq`, `pages_kl`, `g_ge`) | ✅ | Hard | `g_ge` `[propext, Classical.choice, Quot.sound]` (with `h_ge`, `I_le`, `relEnt_book`, `g_eq`, `pages_kl`); 2026-10-02 |
| T5 | Tree law TE1–TE5 and **`finite_counting_inequality`** (weighted `thm:finite`) | ✅ | Hard | `ProbHost.finite_counting_inequality` `[propext, Classical.choice, Quot.sound]`; TE1/TE2/TE4/TE5 in `Entropy/TreeLaw.lean` (generic), TE3 not needed; 2026-10-02 |
| T6 | Doubled-host two-colour inequality, `commonness_scalar`, **`host_commonness`**, star case | ✅ | Medium | `host_commonness`, `host_star_commonness`, `host_two_colour_polynomial`, `commonness_scalar` `[propext, Classical.choice, Quot.sound]`; 2026-10-02 |
| T7 | Transfer layer; **headlines `tree_apex_one_colour`, `tree_apex_two_colour_polynomial`, `half_le_commonalityM_path`, `goodman_identity`, `tree_apex_two_colour`, `tree_apex_common`** | ✅ | Medium | all six + `tree_apex_one_colour'`, `tree_apex_two_colour_polynomial'` `[propext, Classical.choice, Quot.sound]`; T-D5 statements restated verbatim in `CheckStatementsTree.lean` and closed by the theorems; 2026-10-02 |
| T8 | (optional) Appendix A: `host_tree_sidorenko`, `tree_sidorenko`, `tree_common` | ✅ | Easy–Medium | `tree_sidorenko`, `tree_common` `[propext, Classical.choice, Quot.sound]` (edge law as a `SymLaw` over `Unit`); 2026-10-02 |
| T9 | Final audit: `CheckAxiomsTree.lean` coverage of plan §6, README section, label map, forbidden-token scan, import-closure check | ✅ | Easy | §6 list audited under the plan's exact names (`PaperNames.lean`), 114 audit lines all standard; README section "Trees with independent apices"; even-cycle `CheckAxioms.lean` 166 declarations unchanged and clean; `lean/EvenCycleApex*` and `CheckAxioms.lean` byte-identical to 12b365e3; 2026-10-02 |

Overall: **10 / 10 milestones complete.**  The user's goal P4 (`tree_apex_common`) and the optional P5 are proved.  Headlines: P1 `tree_apex_one_colour`, P2
`tree_apex_two_colour` (+ polynomial form), P3 `goodman_identity` + `half_le_commonalityM_path`,
P4 `tree_apex_common`; optional P5 `tree_sidorenko`, `tree_common`.

## Paper statements

One row per labelled statement of the paper (line numbers refer to `trees_apices_commonness.tex`).
Weighted forms are those of plan §2.4–2.6 (decision T-D4).  Keep this table in step with the code:
a row becomes ✅ only when the named declaration builds and passes `#print axioms`.

| Label | Line | Statement | Lean name (`TreeApex.`) | Milestone | Status | Hardness |
|---|---:|---|---|:---:|:---:|:---:|
| sec:statements | 78 | `T^{+k}`, `t(F,W)`, `m(F,W)`, `P₃`, `B_k` | `apexGraph`; `homDensity`, `commonalityM` (even-cycle); `pathGraph 3`, `⊤ : SimpleGraph (Fin 2/3)`; `edgePairs_K₂/P₃/K₃` | T1 | ✅ | Easy |
| eq:sizes | 92 | `v(T^{+k}) = n + k`, `e(T^{+k}) = (k+1)n − 1` | `apexGraph_edgeCount` | T1 | ✅ | Easy |
| eq:common-definition | 112 | `m(F,W) ≥ 2^{1−e(F)}` | the form of `tree_apex_common` (`4 / 2^((k+1)n)`, with `apexGraph_edgeCount`) | T7 | ✅ | — |
| thm:common | 119 | `T^{+k}` common for every tree, every `k ≥ 1` | `tree_apex_common` (already subtraction-free; no primed version needed) | T7 | ✅ | Medium |
| thm:two-color | 126 | `σ ≥ 1/2`; `m(T^{+k}) ≥ τ^{k(n−1)} / σ^{(k−1)(n−2)}` | `half_le_commonalityM_path`, `tree_apex_two_colour`, `tree_apex_two_colour_polynomial` (+ primed) | T7 | ✅ | Medium |
| thm:one-color | 143 | `t(T^{+k}) t(K₂)^{n+k−3} t(P₃)^{(k−1)(n−2)} ≥ t(K₃)^{k(n−1)}` | `tree_apex_one_colour` (+ `tree_apex_one_colour'`) | T7 | ✅ | Medium |
| lem:entropy | 196 | chain rule, support bound, conditioning, subadditivity, `I ≥ 0`, `eq:mi-subadditivity` | — replaced (T-D4): `relEnt_prod` (chain rule, product form), `relEnt_le_log_sum` (support bound), `relEnt_nonpos_of_law` (`KL ≥ 0`, used for `eq:mi-subadditivity` in `pages_kl`) | T3 | ✅ | Medium |
| lem:tree-extension | 260 | Markov extension along a tree; edge marginals; `eq:tree-entropy` | generic in `SymLaw` (any symmetric finite law): `SymLaw.treeLaw`, `treeLaw_sum` (TE1), `treeLaw_marginal` (TE2, test functions), `relEnt_treeLaw` (TE4), `treeLaw_support` (TE5); TE3 not needed (support proved directly) | T5 | ✅ | Hard |
| eq:exchangeability | 263 | `Q(s,x,y) = Q(s,y,x)` | `SymLaw.symm`; for the book `ProbHost.bookQ_symm` | T4 | ✅ | Easy |
| eq:tree-law | 306 | the product law conditional on `S` | `SymLaw.treeLaw` (definition, by `Fin.snoc` recursion from one vertex) | T5 | ✅ | Medium |
| thm:finite | 350 | `hom(T^{+k}) E^{n+k−3} D^{(k−1)(n−2)} ≥ R^{k(n−1)}` on finite hosts | `ProbHost.finite_counting_inequality` (weighted hosts on any `Fintype`, plan §2.5) | T5 | ✅ | Hard |
| eq:triangle-entropy | 377 | `H(X,Y,Z) = log R` | — not needed: only the marginals `P₂`, `P₁` of the triangle law are used (`ProbHost.P₂`, `P₁`) | T4 | — | Easy |
| lem:triangle | 385 | `h ≥ log(R/E)`, `I ≤ log(D/R)`, `eq:triangle-symmetry` | `ProbHost.h_ge` (T1), `ProbHost.I_le` (T2, as `A − 2h ≤ log D − log R`); symmetry inlined in the definitions of `h`, `A` | T4 | ✅ | Hard |
| eq:triangle-neighborhood-counts | 428 | `Σ a(x) = R`, `Σ d(x)² = D`, `P(X=x) = a(x)/R` | definitions `ProbHost.R`, `D`; `sum_P₂` (`Σ_y P₂ = P₁`), `sum_P₁` | T2 / T4 | ✅ | Easy |
| lem:book | 484 | `eq:book-entropy`, `eq:book-extension` | `ProbHost.relEnt_book` (B1, identity `= log R + j h`, `k = j + 1`), `g_eq`, `g_ge` (B2) | T4 | ✅ | Hard |
| eq:pages-mi | 514 | `I(Y;Z₁..Z_k∣X) ≤ kI` | `ProbHost.pages_kl` (one `KL ≥ 0` on `(Z⃗, X)`, not per `x`), `sum_marg_page` | T4 | ✅ | Medium |
| eq:support-global | 560 | `log hom(T^{+k}) ≥ H_P(S,X⃗)` | `SymLaw.relEnt_book_add_le_log` (Gibbs on the tree law), used in `finite_counting_inequality` | T5 | ✅ | Easy |
| rem:arbitrary-k | 581 | remark | — | — | — | — |
| lem:approximation | 600 | W-random graphs converge | — replaced by L¹ transfer (T-D3): `le_of_step_graphons_cont`, `le_of_hosts_cont` (copied, `Transfer.lean`), `homDensity_cont`, `commonalityM_cont`, `stepHost`, `commonalityM_step` | T7 | — | — |
| eq:collision-bound | 656 | injective vs. all maps | — replaced (T-D3) | — | — | — |
| eq:exponents, eq:vertex-balance | 678 | `a, b, c`; `(n+k) + 2a + 3b = 3c` | `ProbHost.vertex_balance` (`ring`), used (inline) in `host_two_colour_polynomial` | T6 | ✅ | Easy |
| eq:disjoint-union | 709 | the two-block graphon `U` on `[0,1]` | — replaced by `ProbHost.double` (T-D8) | T2 | — | — |
| eq:connected-blocks | 718 | `t(F,U) = 2^{−v} m(F,W)` for connected `F` | `ProbHost.hostDens_double_of_connected` (host form, doubled host on `Bool × V`) | T2 | ✅ | Medium |
| eq:two-color-polynomial | 748 | `m(T^{+k}) σ^b ≥ τ^c` | `ProbHost.host_two_colour_polynomial` (host), `tree_apex_two_colour_polynomial` (graphon) | T6 / T7 | ✅ | Medium |
| lem:goodman | 757 | `σ ≥ 1/2`, `τ = (3/2)σ − 1/2`, `τ ≥ 1/4`, `τ/σ ≥ 1/2` | `ProbHost.host_half_le_sigma`, `host_goodman_identity` (host, via `sigma_eq`, `tau_eq`, `Mh_K₂`); `half_le_commonalityM_path`, `goodman_identity` (graphon); the bounds inside `commonness_scalar` | T2 / T7 | ✅ | Medium |
| proof of thm:common (display) | 807 | `τ^c/σ^b ≥ 2^{2−(k+1)n}`; the star `K_{1,k}` | `ProbHost.commonness_scalar`, `host_commonness`, `hostDens_star`, `host_star_commonness` | T6 | ✅ | Medium |
| remark (sharpness) | 838 | equality at `W ≡ 1/2`; role of the tree hypothesis | — (not a theorem) | — | — | — |
| prop:tree-sidorenko | 858 | `t(T) ≥ t(K₂)^{n−1}`; `T` common | `ProbHost.host_tree_sidorenko'`, `host_tree_common`, `tree_sidorenko`, `tree_common` (T8) | T8 | ✅ | Medium |
| app:finite-commonness | 891 | finite Ramsey-multiplicity formulation | — out of scope (T-D11) | — | — | — |
| — (T-D2) | — | the weighted host with `[0,1]` kernel; step graphons as hosts | `ProbHost` (any `Fintype`), `hostDens`, `Mh`, `Mc`, `double`; `stepHost`, `homDensity_step`, `homDensity_cmpl_step`, `commonalityM_step` | T2 / T7 | ✅ | Easy |
| — (T-D4) | — | `relEnt`, Gibbs, `KL ≥ 0`, product chain rule, reindexing | `relEnt`, `relEnt_le_log_sum`, `relEnt_nonpos_of_law`, `relEnt_prod`, `relEnt_equiv`, `relEnt_congr`, `relEnt_one` (`log_jensen` not needed) | T3 | ✅ | Medium |
| — (T-D6) | — | every Mathlib tree on `Fin (m+1)` is a relabelled recursive tree | `treeGraph par m` (clamped parents `parV`, no `RecTree` subtype), `edgePairs_treeGraph`, `prod_edgePairs_treeGraph`, `exists_recTree_iso` (BFS route A), `apexGraph_comap`, `homDensity_apexGraph_of_iso`, `homDensity_tree_of_iso` | T1 | ✅ | Hard |
| — (cross-check) | — | `apexCycle n k = apexGraph (cycleGraph n) k` | `apexCycle_eq_apexGraph` (`rfl`) | T1 | ✅ | Easy |
| — | — | reference weights and their identification with `hostDensity` | `RefFactors` (`ρ_S`, `ν`, `η`), `RefFactors.treeWeight`, `bookWeight`, `ProbHost.bookRef`, `hostDens_apexGraph_treeGraph`, `hostDens_eq_sum_treeWeight`, `SymLaw.treeWeight_snoc` | T2 / T5 | ✅ | Medium |
| — | — | headline P4 | `tree_apex_common` | T7 | ✅ | — |

## Build and audit record

| Check | Result | Date |
|---|---|---|
| `python tools/tree_entropy_check.py 300 20261002` | 300 trials (264 with `R > 0`), all checks passed (re-run at T9) | 2026-10-02 |
| `python tools/tree_entropy_check.py 200 7` | 200 trials, all checks passed | 2026-10-02 |
| `lake build TreeApex` | Build completed successfully (8576 jobs); `lake build --no-build EvenCycleApex` all up-to-date (8622 jobs) | 2026-10-02 |
| `lake env lean CheckAxiomsTree.lean` | 114 audit lines (86 declarations of T0–T8 and the 31 names of plan §6, overlapping), all `[propext, Classical.choice, Quot.sound]` or a subset; no `sorryAx`, no `Lean.ofReduceBool` | 2026-10-02 |
| `lake build` (default target `EvenCycleApex`) | Build completed successfully (8622 jobs), nothing rebuilt | 2026-10-02 |
| `lake env lean CheckAxioms.lean` (even-cycle, unchanged) | 166 declarations, all `[propext, Classical.choice, Quot.sound]` or a subset | 2026-10-02 |
| `git diff 12b365e3 -- lean/EvenCycleApex lean/EvenCycleApex.lean lean/CheckAxioms.lean` | empty (the even-cycle library is untouched; `lakefile.toml` gains only the `TreeApex` block) | 2026-10-02 |
| forbidden tokens (`sorry`, `admit`, `native_decide`, `decide +native`, `ofReduceBool`, `axiom`) in `lean/TreeApex*`, `lean/Check*Tree.lean` | none | 2026-10-02 |
| `lake env lean CheckStatementsTree.lean` | the eight T-D5 statements (P1–P5), copied verbatim from the plan, elaborate and are closed by the theorems | 2026-10-02 |
| import closure of `TreeApex` (T-D7) | `lake env lean CheckImportsTree.lean`: Foundation (8), Graph (5), Host.{Defs, Bridge, EdgeDensity}; no heavy module (re-checked after T7) | 2026-10-02 |
| `python tools/tree_entropy_check.py --negative` | asymmetric kernel trips 200/200, perturbed log trips 157/200 | 2026-10-02 |
