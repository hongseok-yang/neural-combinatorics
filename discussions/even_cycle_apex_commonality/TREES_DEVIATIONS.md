# Deviations from TREES_VERIFICATION_PLAN.md

Changes to the plan's text (design decisions T-D1–T-D11, §2 Lean notes, §3 layout, §6 audit list).
**No public statement of T-D5 changed**: the six headlines and the two appendix theorems have
exactly the locked shapes, and `lean/CheckStatementsTree.lean` restates each one verbatim from the
plan and proves it from the theorem.  Every entry below is internal.

Each choice was logged in `TREES_NOTES.md` when it was made (as a design note inside the plan's
freedom).  This file was created at T9 to collect the ones that depart from the plan's literal
text, as the protocol (§7) asks.

| # | Plan text | What was done | Why | Affects |
|---|---|---|---|---|
| Y1 | T-D2: `structure ProbHost (d : ℕ)` on `Fin d`, densities by `hostDensity` | `structure ProbHost (V : Type*) [Fintype V]` on any finite type, densities by `hostDens` (`hostDens_eq_hostDensity` : equal by `rfl` when `V = Fin d`) | the doubled host of T-D8 is then `Bool × V` and its block identity is a sum over colourings `Fin v → Bool`, instead of splitting `Fin (d + d)` | internal; the transfer instantiates `V = Fin d` (`stepHost`) |
| Y2 | T-D6: `RecTree m = {par : ℕ → ℕ // ∀ i < m, par i ≤ i}` | a recursive tree is any `par : ℕ → ℕ`; vertex `i + 1` is attached to `parV par i = min (par i) i` | no proof obligation travels with `par`; the restriction to fewer vertices is the same function; every `par` is a tree, and the `IsTree` bridge produces `par` with `par i ≤ i` (`parV_bfsPar`) | internal (`treeGraph par m`, `exists_recTree_iso`) |
| Y3 | §2.3–2.5 list `log_jensen`, `relEnt_triangle`, `marg`/`cond` conventions, `bookLaw_page`, `bookLaw_vertex`, `treeLaw_marginal_edge` (TE3) | not formalized as such | not needed: Gibbs is proved from `log u ≤ u − 1`, and `I_le` is two Gibbs inequalities (so no Jensen); only the marginals `P₂`, `P₁` of the triangle law enter (no `eq:triangle-entropy`); `SymLaw.marg`/`kern` replace the conventions; `sum_marg_page`/`sum_marg_pages` replace the page and vertex marginals; the support of the tree law (TE5) is proved directly, so TE3 is unused | internal |
| Y4 | §2.5: the tree law starts from `Q` at `m = 1` | it starts from one vertex, `P₀(s, x) = μ(s, x₀)`, with `P₁ = Q` pointwise (`relEnt_treeLaw_one`) | the induction for TE1, TE2, TE4, TE5 is uniform from `m = 0` | internal |
| Y5 | §2.4 B2 step 2: one `KL ≥ 0` per vertex `x`, between conditional laws | one `KL ≥ 0` on `(Z⃗, X)` between the law `μ` and `w_x ∏ᵢ (w_{zᵢ} M_{x zᵢ} cod(x, zᵢ)) / (R tri(x)^{k−1})` (`pages_kl`) | avoids dividing by `P₁(x)`; the same inequality after summing over `x` | internal |
| Y6 | §2.4 lists `lem:tree-extension` for the book law | proved for an arbitrary symmetric law on finite types (`SymLaw`, `RefFactors` in `Entropy/TreeLaw.lean`) and instantiated twice: the book law (`bookLaw`, `S = Fin k → V`) and, in appendix A, the edge law (`edgeLaw`, `S = Unit`) | appendix A needs neither the `k = 0` book nor a separate proof | internal |
| Y7 | §6 names such as `TreeApex.h_ge`, `TreeApex.finite_counting_inequality`, `TreeApex.relEnt_treeLaw`, `TreeApex.hostDensity_double_of_connected` | the results live in the namespaces of their structures (`TreeApex.ProbHost.h_ge`, `TreeApex.SymLaw.relEnt_treeLaw`, …); `TreeApex/PaperNames.lean` restates each under the plan's exact name, and `CheckAxiomsTree.lean` audits the §6 list under those names | dot notation (`K.h_ge hR`) | names only |
| Y8 | T-D5: subtraction-free corollaries `…'` | `tree_apex_one_colour'`, `tree_apex_two_colour_polynomial'`; no `tree_apex_common'` | `tree_apex_common` has no natural subtraction | none |
| Y9 | §3 layout: `CheckAxiomsTree.lean` at the package root | also `CheckStatementsTree.lean` (headline statements verbatim) and `CheckImportsTree.lean` (import closure, T-D7) at the package root; `Host/Scalars.lean`, `Host/TreeWeight.lean` are `Host/ProbHost.lean` and `Finite/OneColour.lean` (merged, as §3 allows) | the T7 gate's statement comparison and the T0/T9 closure check, done by Lean instead of by hand | none |
| Y10 | §6: "every line must read `[propext, Classical.choice, Quot.sound]`" | three audited declarations print a strict subset: `apexGraph_connected`, `apexGraph_comap` (`[propext, Quot.sound]`), `ProbHost.vertex_balance` (`[propext]`) | they do not use choice; a subset is what the README of the even-cycle library also accepts | none |
