# Notes — independent apices of trees

Chronological log for [`TREES_VERIFICATION_PLAN.md`](TREES_VERIFICATION_PLAN.md): decisions taken inside
the plan's freedom, Lean gotchas, blockers, and gate evidence.  Live status is in
[`TREES_DASHBOARD.md`](TREES_DASHBOARD.md).

## 2026-10-02 — T0: scaffold and regression

* Branch `tree-apex-lean` (from `main` at 9286ff5a; the even-cycle library is on `main`, last commit
  touching `lean/` is 12b365e3).
* `lean/lakefile.toml`: added the `[[lean_lib]] name = "TreeApex"` block (the one permitted edit,
  T-D7).  `defaultTargets` is unchanged, so a bare `lake build` still builds only `EvenCycleApex`; the
  tree library is built with `lake build TreeApex`.  After the edit,
  `lake build --no-build EvenCycleApex` reports "All targets up-to-date (8622 jobs)": nothing in the
  even-cycle library is invalidated.
* New files: `lean/TreeApex.lean` (index), `lean/TreeApex/Smoke.lean`, `lean/CheckAxiomsTree.lean`
  (audit), `lean/CheckImportsTree.lean` (import-closure check: lists the `EvenCycleApex` modules in
  the environment after `import TreeApex` and throws if a heavy one is present).
* Smoke theorem `smoke_density_near_host`: for a graphon `W`, a graph `F`, a permutation `e` and
  `ε > 0`, there is a weighted host (`w ≥ 0`, `Σ w = 1`, `M` symmetric `[0,1]`) with
  `|t(F.comap e, W) − hostDensity w F M| ≤ e(F) ε`.  It uses `homDensity_comap_equiv`,
  `exists_stepGraphon_l1_close`, `exists_host_of_isStepKernel`, `step_homDensity_eq_host`,
  `homDensity_L1_lipschitz`.
* Timings (this machine, ≈ 3.4 GB free RAM): first `lake build TreeApex` 5 min 43 s, of which
  `TreeApex.Smoke` 311 s (cold load of Mathlib, imported through `Foundation/Graphon`); afterwards a
  single-file check `lake env lean CheckAxiomsTree.lean` takes ≈ 35 s.
* Regression script: added `--host` (exact `Fraction` scalars of a rational host, computed from
  scratch as homomorphism densities, with assertions `m(K₂) = 1`, `σ ≥ 1/2`, `τ = 3σ/2 − 1/2`) and
  `--negative` (the negative controls the plan mentions were not in the script; now reproducible:
  an asymmetric kernel, and `log u ↦ log u + u/100`; the mode asserts that both trip).

Exact values of the plan §2.2 regression hosts (for the T2 `norm_num` lemmas):

| host | `E` | `D` | `R` | `σ_h` | `τ_h` |
|---|---|---|---|---|---|
| `w = (1/2, 1/2)`, `M = [[1/4, 1], [1, 0]]` | 9/16 | 41/128 | 49/512 | 33/64 | 35/128 |
| `w = (1/3, 2/3, 0)`, `M = [[1, 1/2, 0], [1/2, 1/3, 1], [0, 1, 1]]` | 13/27 | 121/486 | 205/1458 | 130/243 | 49/162 |

(Hand check of the first: `deg = (5/8, 1/2)`, `E = 9/16`, `D = 41/128`, `σ = 1 − 2E + 2D = 33/64`.)

### Design notes for T1–T5 (inside the plan's freedom; no public statement affected)

Worked out before coding, from plan §2.3–2.5:

* **Hosts on any `Fintype`.**  `ProbHost V` for a `Fintype V`, with its own density `hostDens`
  (definitionally `hostDensity` when `V = Fin d`).  The doubled host is then `Bool × V`, and the
  block identity is a sum over colourings `Fin v → Bool` (constant colourings give `M` and `1 − M`;
  a non-constant one has a bichromatic edge since `F` is connected), instead of splitting
  `Fin (d + d)`.  The transfer instantiates `V = Fin d`.
* **Generic tree extension.**  `lem:tree-extension` is proved for an arbitrary symmetric law
  `Q : S × X × X → ℝ` on finite types with reference factors `ρ_S`, `ν`, `η`
  (`ρ_B(s,x,y) = ρ_S s · ν s x · ν s y · η x y`); the host instantiates `S = Fin k → V`, `X = V`.
* **Tree law from one vertex.**  `P_0(s, x) = μ(s, x₀)` (the `(S,X)` marginal) and
  `P_{m+1}(s, snoc x y) = P_m(s, x) · K(s, x_{par m}, y)`; then `P_1 = Q` pointwise, and
  `relEnt ρ_{m+1} P_{m+1} = relEnt ρ_1 P_1 + m · g` is a uniform induction.
* **Vertex marginals with test functions** (TE2): `Σ_{s,x} P_m(s,x) f(s, x_u) = Σ_{s,a} μ(s,a) f(s,a)`
  for every `f` and every vertex `u`; this is exactly what collapses the chain-rule term to `g`.
  TE3 (edge marginals) is not needed: the support of the tree law (TE5) is proved directly by
  induction.
* **Clamped parents.**  A recursive tree is any `par : ℕ → ℕ`; the parent of vertex `i + 1` is
  `min (par i) i`, so no hypothesis is carried and the restriction to fewer vertices is the same
  function.  The `IsTree` bridge produces `par` with `par i ≤ i`.
* **T2 and the pages step by Gibbs only.**  `I ≤ log(D/R)` is two Gibbs inequalities (references
  `w_x tri_x w_y M_xy / (R deg_x)` on pairs and `w_x deg_x² / R` on vertices), and `pages_kl` is one
  `KL ≥ 0` on `X × S` against `r(x, z⃗) = w_x ∏_j (w_{z_j} M_{x z_j} cod(x, z_j)) / (R tri_x^{k−1})`,
  which avoids per-`x` conditional laws.  So `log_jensen` is not needed.

### T0 gate evidence (2026-10-02)

```text
lake build TreeApex                       Build completed successfully (8576 jobs)
lake build --no-build EvenCycleApex       All targets up-to-date (8622 jobs)
lake env lean CheckAxiomsTree.lean
  'TreeApex.smoke_density_near_host' depends on axioms: [propext, Classical.choice, Quot.sound]
lake env lean CheckImportsTree.lean       16 EvenCycleApex modules: Foundation.{Continuity, Defs,
  Factored, Fubini, Graphon, GraphonL2Operator, Kernel, StepApprox}, Graph.{Apex, DensityAlgebra,
  HomDensity, Lipschitz, PairMarginal}, Host.{Bridge, Defs, EdgeDensity};
  "import closure OK: no heavy EvenCycleApex module"
python tools/tree_entropy_check.py 300 20261002   300 trials, 264 with R > 0, 36 with R = 0; all checks passed
python tools/tree_entropy_check.py 200 7          200 trials, 169 with R > 0, 31 with R = 0; all checks passed
python tools/tree_entropy_check.py --negative     asymmetric kernel tripped 200/200; perturbed log tripped 157/200
python tools/tree_entropy_check.py --host         the two hosts above
```

## 2026-10-02 — T1: graphs, recursive trees, the `IsTree` bridge

* `TreeApex/Graph/Apex.lean`: `apexGraph G k` (no decidability needed for the definition; the
  `DecidableRel` instance takes `[DecidableRel G.Adj]`), the four adjacency `simp` lemmas,
  `apexCycle_eq_apexGraph` (`rfl`), `edgePairs_apexGraph` / `prod_edgePairs_apexGraph` (verbatim
  `ApexEdges.lean`, `crossEdges` imported), `card_edgePairs_apexGraph`, `apexGraph_edgeCount`
  (from `IsTree.card_edgeFinset` via the even-cycle `card_edgePairs`), `apexGraph_connected`
  (`0 < n`, `0 < k`), `apexEquiv e k` (extension by the identity on the apices, via
  `finSumFinEquiv`) and `apexGraph_comap`, the `DecidableRel (pathGraph m).Adj` instance (Mathlib
  has none; plan risk F), `edgePairs_K₂/P₃/K₃` by `decide`, connectivity of the three small graphs.
* `TreeApex/Graph/RecTree.lean`.  **Representation change inside T-D6's freedom:** instead of the
  subtype `RecTree m = {par // ∀ i < m, par i ≤ i}`, a recursive tree is any `par : ℕ → ℕ` with
  parent `parV par i = min (par i) i` of vertex `i + 1`.  No proof obligations travel with `par`,
  and the restriction to `m` vertices is the same function.  `treeGraph par m`,
  `edgePairs_treeGraph` (image of `i ↦ (parV par i, i.succ)`), `prod_edgePairs_treeGraph`.
* **Bridge, route A, closed in one pass.**  Generic part on any tree `T` with root `r`:
  `rootPath` (a shortest path, `Connected.exists_path_of_dist`), `treeParent` = its penultimate
  vertex, `dist_treeParent` (`dist v = dist (parent v) + 1`, from `IsAcyclic.path_concat`),
  `eq_treeParent_of_adj` (a neighbour closer to the root is the parent: if it lies on the
  root path of `b`, `path_concat` identifies the penultimate vertex; otherwise
  `mem_support_of_ne_mem_support_of_adj_of_isPath` puts `b` on the root path of `a` and
  `path_concat` gives `dist a = dist b + 1`).  On `Fin (m + 1)`: `bfsOrder = Tuple.sort (dist 0)`,
  `bfsOrder_lt` (closer to the root ⇒ earlier), `bfsOrder_zero`, `bfsPar`, `parV_bfsPar`
  (`par i ≤ i`, so the clamp is inactive), `exists_recTree_iso`:
  `T = (treeGraph (bfsPar hT) m).comap (bfsOrder).symm`; the forward direction splits on
  `IsTree.dist_ne_of_adj`.
* `homDensity_congr` (density independent of the `DecidableRel` instance, by `subst; congr`),
  `homDensity_apexGraph_of_iso`, `homDensity_tree_of_iso`.
* Lean gotchas: a section variable used only inside proofs (`hT`) must be `include`d; then
  `omit hT in` for lemmas that do not need it.

### T1 gate evidence (2026-10-02)

```text
lake build TreeApex                       Build completed successfully (8579 jobs); no warnings
lake env lean CheckAxiomsTree.lean        16 declarations; every line [propext, Classical.choice,
  Quot.sound] except apexGraph_connected, apexGraph_comap: [propext, Quot.sound]
  including exists_recTree_iso, prod_edgePairs_apexGraph, apexGraph_edgeCount,
  homDensity_apexGraph_of_iso
grep forbidden tokens in lean/TreeApex    none
```

## 2026-10-02 — T3, T4, T5 (and the scalar part of T2)

Order: T3 was pulled forward (plan §4 allows it), then T2's scalars, T4, T5.  The doubled host,
Goodman and the regression hosts (rest of T2) come with T6.

* **T3 `Entropy/RelEnt.lean`.**  `relEnt`, `relEnt_congr` (evaluate the log on the support only —
  the workhorse of every later log computation), `relEnt_one`, `relEnt_equiv`, `sum_pos_of_support`,
  `relEnt_le_log_sum` (Gibbs), `relEnt_nonpos_of_law`, `relEnt_prod`.  Gibbs is proved from
  `Real.log_le_sub_one_of_pos` termwise (`p log(ρ/p) − p log Z ≤ ρ/Z − p`), so neither
  `ConcaveOn.le_map_sum` nor a separate `log_jensen` is needed.  `relEnt_prod` needs no
  nonnegativity at all, only the row sums and the two support conditions.
* **T3+ `Entropy/TreeLaw.lean` (generic `lem:tree-extension`).**  Structures `SymLaw S X`
  (symmetric law `Q`) and `RefFactors L` (`ρ_S`, `ν`, `η`, nonnegative, nonzero on `supp Q`); `marg`,
  `kern` (`Q / marg`, zero rows off the support), `marg_mul_kern` (holds also when `marg = 0`),
  `treeLaw` (recursion from one vertex, `Fin.init`/`Fin.last`; `treeLaw_snoc` by `simp`),
  `RefFactors.treeWeight` (closed product; `treeWeight_snoc` by `Fin.prod_univ_castSucc`),
  `treeLaw_support` (TE5 together with "every vertex marginal is nonzero"), `treeLaw_sum_last`
  (pointwise consistency), `treeLaw_sum` (TE1), `treeLaw_marginal` (TE2 with test functions),
  `relEnt_treeLaw_succ` (`relEnt_equiv` along `snocEquiv'`, then `relEnt_prod`, then TE2 at the
  parent of the new leaf), `relEnt_treeLaw_one` (`P₁ = Q` via `piFinTwoEquiv`), `relEnt_treeLaw`
  (TE4), `relEnt_book_add_le_log`, `sum_treeWeight_pos`.
* **T2 (part) `Host/ProbHost.lean`.**  `ProbHost V` over any `Fintype V` (design note above),
  `hostDens` (`= hostDensity` by `rfl` on `Fin d`), `sum_fun_succ` (the even-cycle `vecCons`
  idiom), `hostDens_K₂/P₃/K₃` in any kernel, the scalars, bounds (`cod_le_deg`, `tri_le_deg_sq`,
  `R ≤ D ≤ E`, `pos_of_R_pos`), support lemmas (`cod_pos_of`, `tri_pos_of`, `deg_pos_of_tri_pos`),
  `hostDens_K₂_eq/P₃_eq/K₃_eq`.
* **T4 `Entropy/Triangle.lean`.**  `P₂`, `P₁`, `h`, `A`, `Ldeg`; `h_ge` (Gibbs on `V × V` against
  `w w M`); `A_sub_Ldeg_le_h` (`KL ≥ 0` against the law `w_x tri_x w_y M_xy / (R deg_x)`),
  `two_Ldeg_sub_A_le` (Gibbs on `V` against `w_x deg_x² / R`), `I_le`.  The paper's
  `eq:triangle-entropy` (`H(X,Y,Z) = log R`) is not needed as a separate statement: only `P₂`, `P₁`
  enter.
* **T4 `Entropy/Book.lean`.**  `sum_pages_prod`, `sum_pages_prod_mul` (one distinguished page, via
  `Fintype.prod_sum` and `Fin.prod_univ_succAbove`), `bookQ = bookNum / (R cod^j)` with `k = j + 1`,
  `sum_bookQ_pages` (`= P₂`), `bookLaw : SymLaw`, `bookRef : RefFactors` (`bookWeight_eq`:
  `ρ_B = bookNum`), `relEnt_book` (B1), `bookPhi`, `g_eq`, `sum_bookQ_page`, `sum_marg_page` (every
  page has the pair law `P₂` with the shared vertex), `sum_marg_pages`, `marg_support`, `pages_kl`,
  `g_ge` (B2).
* **T5 `Finite/OneColour.lean`.**  `hostDens_apexGraph_treeGraph` (closed form for any `k`;
  `appendEquiv`, `Fin.prod_univ_add`, the two edge-product lemmas with the function given
  explicitly), `hostDens_eq_sum_treeWeight` (`rfl` after `Fintype.sum_prod_type`),
  `finite_counting_inequality'` (`n = m + 2`, `k = j + 1`) and `finite_counting_inequality` (plan
  form: `m ≥ 1`, `k ≥ 1`, tree on `m + 1` vertices, exponents `k m`, `m + k − 2`, `(k−1)(m−1)`).
* Lean gotchas: `rw` with `prod_edgePairs_*` cannot solve the higher-order pattern
  `?g p.1 p.2` — pass the function explicitly; `set x := … with h` does not capture occurrences that
  appear only after a later `unfold`/`simp` (goals then mix `L.marg` and `(K.bookLaw j hR).marg`),
  so the book proofs use the terms directly or `let`; `Fin (0 + 1)`/`Fin (1 + 1)` products need
  `Fin.prod_univ_succ`/`Fin.prod_univ_zero` rather than `Fin.prod_univ_one/two`; in Git Bash a
  heredoc containing `'` can confuse the tool wrapper — write long Lean snippets with the file tool
  and splice them with Python.

### T3–T5 gate evidence (2026-10-02)

```text
lake build TreeApex                       Build completed successfully (8585 jobs); no warnings
lake env lean CheckAxiomsTree.lean        41 declarations, all [propext, Classical.choice,
  Quot.sound] (two T1 lemmas: [propext, Quot.sound]); including relEnt_le_log_sum, relEnt_prod,
  SymLaw.relEnt_treeLaw, SymLaw.relEnt_book_add_le_log, ProbHost.h_ge, ProbHost.I_le,
  ProbHost.relEnt_book, ProbHost.pages_kl, ProbHost.g_ge, ProbHost.finite_counting_inequality
```
