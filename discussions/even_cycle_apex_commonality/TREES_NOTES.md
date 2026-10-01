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
