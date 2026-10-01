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

## 2026-10-02 — T2 (rest) and T6

* `Host/Double.lean`: `Mc = 1 − M`, `Mh F = t(F, M) + t(F, 1 − M)`, `colM b` (`M` on `true`,
  `1 − M` on `false`), `compl`, `double : ProbHost (Bool × V)` (weights `w/2`, kernel `colM` on equal
  colours, `0` across), `exists_bichromatic_edge` (`Walk.exists_boundary_dart` on the set of
  `true`-coloured vertices; the sorted pair of the dart is in `edgePairs F`),
  `hostDens_double_of_connected` (reindex `Fin v → Bool × V` by
  `Equiv.arrowProdEquivProdArrow`, then `Fintype.sum_eq_add` at the two constant colourings).
* `Host/Goodman.lean`: `sum3_add` and the seven triple sums (`sum3_one`, `sum3_xy/xz/yz`,
  `sum3_xy_xz/xy_yz/xz_yz`), `Mh_K₂`, `sigma_eq` (`σ = 1 − 2E + 2D`), `tau_eq` (`τ = 1 − 3E + 3D`),
  `host_half_le_sigma` (`σ − 1/2 = 2 ∑ w (deg − 1/2)²`), `host_goodman_identity`.
* `Host/Regression.lean`: `regHost₁`, `regHost₂` and the ten values of the T0 table, `σ_h`, `τ_h`
  evaluated from the raw triple sums in `M` and `1 − M` (independent of Goodman's identity); all
  match `tools/tree_entropy_check.py --host`.
* `Finite/TwoColour.lean`: `double_E/D/R` (`1/4`, `σ/8`, `τ/8`), `vertex_balance`,
  `host_two_colour_polynomial` (`finite_counting_inequality'` on `K.double`; the identity
  `8^c = 2^{n+k} 4^a 8^b`), `commonness_scalar` (base-2 bookkeeping with an opaque `u = 1/2` so that
  `ring` handles the variable exponents), `host_commonness`, `hostDens_star`
  (`t(K_{1,k}, L) = ∑ w_x (∑ w_z L_xz)^k`), `host_star_commonness` (`add_pow_le`).
* Lean gotchas: `set u : ℝ := 1/2` makes `u` a let-binding that `linarith`/`ring` see through
  inconsistently — use `obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1/2 := ⟨_, rfl⟩`; `simp only [← sum_add_distrib]`
  does not merge nested triple sums — prove `sum3_add` by three explicit `rw`; `norm_num` cannot
  evaluate `![a, b, c] 2` but the `Matrix.cons_val` simproc can (`norm_num [Matrix.cons_val]`).

### T2 and T6 gate evidence (2026-10-02)

```text
lake build TreeApex                       Build completed successfully (8589 jobs); no warnings
lake env lean CheckAxiomsTree.lean        65 declarations; all [propext, Classical.choice,
  Quot.sound] or a subset (apexGraph_connected, apexGraph_comap: [propext, Quot.sound];
  vertex_balance: [propext]); including hostDens_double_of_connected, host_half_le_sigma,
  host_goodman_identity, regHost₁/₂ (10 values), host_two_colour_polynomial, commonness_scalar,
  host_commonness, host_star_commonness
```

## 2026-10-02 — T7: transfer and the headlines P1–P4

* `TreeApex/Transfer.lean`: the `L1ContAt` layer copied from
  `EvenCycleApex/Equality/Functionals.lean @ 12b365e3` (provenance header; only imports and the
  namespace changed): `L1ContAt`, `.of_lipschitz`, `.const`, `.prod`, `.comp`,
  `le_of_step_graphons_cont`, `le_of_hosts_cont`.  New: `L1ContAt.mul`, `L1ContAt.pow`,
  `homDensity_cont` (Lipschitz constant `e(F)` from `homDensity_L1_lipschitz` with `B = 1`),
  `commonalityM_cont`, `stepHost` (the `ProbHost (Fin d)` of a step graphon), `homDensity_step`,
  `homDensity_cmpl_step`, `commonalityM_step` (two instances of `step_homDensity_eq_host`).
  The plan's alternative (moving the layer into the frozen even-cycle library) was not needed.
* `TreeApex/Main.lean`: `half_le_commonalityM_path`, `goodman_identity` (two transfers,
  `le_antisymm`); for recursive trees `treeGraph_apex_one_colour`,
  `treeGraph_apex_two_colour_polynomial`, `treeGraph_star_common` (each one `le_of_hosts_cont`
  with the host theorem); for every Mathlib tree `tree_apex_one_colour`,
  `tree_apex_two_colour_polynomial`, `tree_apex_two_colour` (`div_le_iff₀`, `σ ≥ 1/2`),
  `tree_apex_common` (`n = 1`: the star; `n ≥ 2`: `commonness_scalar` applied at the graphon level
  to P2 and P3, as in the paper's display), and the primed forms `tree_apex_one_colour'`,
  `tree_apex_two_colour_polynomial'` (`n = m + 2`, `k = j + 1`).  The bridge enters through
  `exists_recTree_iso`, `homDensity_apexGraph_of_iso`, `commonalityM_apexGraph_of_iso`.
* `CheckStatementsTree.lean`: `#check` of the headlines, `#print apexGraph`, and each T-D5
  statement copied verbatim from the plan as an `example` closed by the theorem (the line-by-line
  comparison of the T7 gate, done by the elaborator), plus `apexGraph_edgeCount` documenting
  `4 / 2^((k+1)n) = 2^{1−e(T^{+k})}`.
* No deviation from T-D5: the statements are exactly the locked shapes.

### T7 gate evidence (2026-10-02)

```text
lake build TreeApex                       Build completed successfully (8591 jobs); no warnings
lake env lean CheckAxiomsTree.lean        80 declarations; all [propext, Classical.choice,
  Quot.sound] or a subset; the six headlines and the two primed corollaries exactly
  [propext, Classical.choice, Quot.sound]
lake env lean CheckStatementsTree.lean    no errors (the verbatim T-D5 statements are proved)
lake env lean CheckImportsTree.lean       import closure OK: no heavy EvenCycleApex module
grep forbidden tokens in lean/TreeApex    none
```

## 2026-10-02 — T8: appendix A (trees themselves)

* `TreeApex/Appendix/Sidorenko.lean`.  Plan §2.8 offered two routes; neither the `k = 0` book nor
  a separate direct proof was needed: the edge law `Q(x, y) = w_x w_y M_xy / E` is an instance of
  the generic `SymLaw` with `S = Unit` (`edgeLaw`, `edgeRef` with `ρ_S = 1`, `ν = w`, `η = M`), so
  the tree law, its support and `relEnt_book_add_le_log` are reused unchanged.
  `hostDens_treeGraph` (closed form), `hostDens_treeGraph_eq_sum_treeWeight`, `relEnt_edge`
  (`= log E`), `edgeLaw_Q`, `edgeLaw_marg` (`μ(a) = w_a deg_a / E`), `edge_condRelEnt_ge`
  (`g = ∑ μ log deg ≥ log E` by Gibbs against the law `w`), `host_tree_sidorenko'`
  (`E^{m+1} ≤ t(T)`, tree on `m + 2` vertices), `hostDens_treeGraph_zero` (one vertex: `t = 1`),
  `E_le_one`, `host_tree_common` (`add_pow_le` with `t(K₂, 1 − M) = 1 − E` from `Mh_K₂`), and the
  graphon forms `tree_sidorenko`, `tree_common` (T-D5 shapes, checked verbatim in
  `CheckStatementsTree.lean`).
* Lean gotcha: after `Fintype.sum_unique` the `Unit` point appears as `default`, not `()`; state
  lemmas such as `edgeLaw_marg` for an arbitrary `u : Unit`.

### T8 gate evidence (2026-10-02)

```text
lake build TreeApex                       Build completed successfully (8592 jobs); no warnings
lake env lean CheckAxiomsTree.lean        86 declarations; tree_sidorenko, tree_common,
  host_tree_sidorenko', host_tree_common, relEnt_edge, edge_condRelEnt_ge all
  [propext, Classical.choice, Quot.sound]
lake env lean CheckStatementsTree.lean    no errors (P5 statements included)
```
