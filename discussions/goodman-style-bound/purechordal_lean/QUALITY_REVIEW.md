# purechordal_lean quality review and fix plan

Audit date: 2026-07-26. Scope: all 26 `.lean` files (~7,300 lines). Method: full
read of every file plus a project-wide cross-reference index of all 440 top-level
declarations. No build was run (machine cannot build Lean projects); all findings
are from reading, and every refactor below must be re-verified by a full build on
a capable machine.

## Verdict

Mathematically solid and tactically disciplined (no `sorry`, no non-terminal
`simp` anywhere, consistent `simp only` usage), but **not yet at the readability
bar of a high-quality Lean repository**. The main deficits are (a) copy-paste
duplication and incremental lemma chains, (b) missing docstrings on core
definitions and headline theorems, and (c) several organizational seams
(inverted imports, oversized files, cloned APIs). Estimated ~600–800 lines
removable with the plan below.

---

## Findings by criterion

### Criterion 1 — incremental / duplicated proof structure (worst axis)

**Verbatim copy-paste blocks:**
- `Gibbs.lean` 82–115 vs 159–192: the 35-line bound `‖f·log(g/f)‖ ≤ b·C` is
  duplicated character-for-character between
  `integral_mul_log_div_nonpos_of_two_sided_bounds` and
  `integrable_mul_log_div_of_two_sided_bounds`.
- `CliqueTreeCombinatorics.lean` 111–138 clones `Certificate.lean`'s public API
  verbatim: `bagIndicesBefore` = `bagIndicesLT` (Certificate:48), and its two
  lemmas duplicate `bagIndicesLT_succ` / `index_not_mem_bagIndicesLT`.
- `CliqueMarginals.lean` 277–288 duplicates the `hunion` set-identity block of
  `MarginalAlgebra.lean` 102–113; `lmarginal_cliqueWeightOnENN_eq_self_of_disjoint`
  (249–267) re-proves the generic `FinsetDependsOn.lmarginal_eq_self_of_disjoint`.
- `ChromaticFactorization.lean` `extendColor_current_injective` (181–257): two
  membership subproofs each inlined **three times**, and the same subproofs recur
  in `newColorEmbedding` (304–329) and `fiberEmbedding` (393–431).
- `WeightedCauchySchwarz.lean`: dead `have hquad_int` (48–58) and the `hfun`
  funext/ring block duplicated (49–57 vs 65–72).
- `CliquePolynomialBound.lean` 27–81: `cliqueStepFactor_nonneg` /
  `cliqueStepFactor_pos_of_lt` are ~25-line twins differing only in `≤` vs `<`.
- `CliqueMarginals.lean` `integral_cliqueWeightOn` (424–509): the 30-line
  `hcomp` bijection re-proves `cliqueWeightOn_eq_graphWeight` (150–171) inline.
- `JunctionDensity.lean` `lmarginal_univ_bagWeightENN` (146–159) re-derives
  `lintegral_cliqueWeightOnENN` (CliqueMarginals:511) inline;
  `lmarginal_normalizedBagENN_separator` (432–476) and `_ownSeparator` (477–509)
  are near-duplicate twins.
- `EntropyGluing.lean`: the same integrability/mass-one proof pair appears
  verbatim for `normalizedGraphDensity` and `separatorTiltDensity`
  (295–318 vs 649–670).

**Incremental weakening chains (the "bad example" pattern):**
- `Gibbs.lean`: five public entry points for one fact —
  `integral_mul_log_div_nonpos` → `_of_bound` → `_of_two_sided_bounds` →
  `_of_exists_bounds`, plus the parallel `integrable_*` pair. Only the core lemma
  and the two `_of_exists_bounds` forms are consumed outside the file.
- Triple definition of "everything before index i": `previousVertices`
  (Certificate:44) ≡ `accumulatedVerticesLT` (Certificate:53) with a `rfl`
  bridge (Certificate:129); same pattern for `previousPairs` vs
  `accumulatedPairs` (CliqueTreeCombinatorics:39/115/148).
- `ChromaticFactorization.lean`: `chromaticPolynomialEval` (639) parallels
  `chromaticPolynomial` (643), spawning wrapper pairs
  (`*_natCast` ×2, `certificateBound_eq_*` ×2).
- `EntropyGluing.lean`: four parallel "density API" tracks
  (normalizedGraph / normalizedBagNew / normalizedSeparator / separatorTilt),
  each with the same 6-lemma litany (`measurable_*`, `*_ne_zero`, `*_ne_top`,
  `*_eq`, `*_exists_lower_bound`, `*_exists_upper_bound`) — six ~18-line
  structurally identical bound proofs at 331–483 alone. Root cause: the Gibbs
  entry point takes ten unbundled arguments.

**Monolithic proofs (>80 lines):**
- `JunctionDensity.lean` `partialJunctionENN_bagMarginal` (513–663, ~150 lines).
- `EntropyGluing.lean` `homDensity_mul_sep_ge_cliqueDensity_pow` (1042–1158,
  ~117 lines; the ε-arithmetic block 1112–1136 is self-contained).
- `CliquePolynomialBound.lean` `cliqueDensity_step_lower_and_pos` (83–191,
  109 lines; the algebraic core 119–181 is a pure real-number lemma).
- `CliqueMarginals.lean` `integral_cliqueWeightOn` (85 lines; fixed by dedup).

### Criterion 2 — jargon / unused terms

**Verified dead code** (no textual reference anywhere in the project; none carry
`@[simp]`):

| Declaration | Location |
|---|---|
| `sepCard_le_pred` | Certificate.lean:120 |
| `card_vertices` | Certificate.lean:284 (milestone 28 — decide: document as API or delete) |
| `homDensity_ge_cliquePoly_quotient` | CertificatePolynomialBound.lean:161 |
| `eval_chromaticPolynomial_natCast` | ChromaticFactorization.lean:703 |
| `finsetPermFixing_map_diff` | CliqueMarginals.lean:120 |
| `pairsIn_mono` | CliqueTreeCombinatorics.lean:25 |
| `measurable_normalizedBagNewDensity` | EntropyGluing.lean:106 |
| `measurable_normalizedSeparatorDensity` | EntropyGluing.lean:111 |
| `integral_toReal_mul_eq_of_lmarginal_eq` | MarginalAlgebra.lean:340 (~55 lines) |
| `UpdateInvariant.mul`, `UpdateInvariant.inv` | MarginalAlgebra.lean:163/171 |

Keep-with-comment (intentional sanity checks, currently indistinguishable from
dead code): `diamondGraph_adj_iff` (Diamond:22), `goldnerHarary_degrees` +
`goldnerHararyDegree` (GoldnerHarary:84/90).

Cannot confirm without a build (all `@[simp]`, may fire implicitly):
`cliquePoly_le_one`, `restrictPrefix_apply`, `extendColor_of_mem_old/new`,
`optionAssignment_none/some`, `finTwoEquiv_zero/one`,
`pairToZeroOnePerm_apply_right`, `cliqueStepFactor_two`, `diamond_root`,
`diamond_separator_zero_card`, `goldnerHarary_root`, `cliqueDensity_zero`,
`separator_root`, `previousVertices_root`, `balancedMultipartiteGraphon_apply`.
Check by removing on a build machine and rebuilding.

**Coined terms needing definition or renaming:**
- "pure" (`PureCliqueTreeDecomp`, `HasPureMaximalCliques`, project name):
  defensible (pure simplicial complexes) but the provenance is never stated —
  add one sentence to `ChordalStructure.lean`'s docstrings.
- `separatorTilt*` (EntropyGluing:41/56): no docstring anywhere explains the
  "tilt"; document or rename.
- "cube inequality" (CubeInequality/IntegratedCube file names and lemma names):
  not standard terminology, unexplained in either module docstring.
- `chromaticTail`: appears **only inside lemma names**
  (ChromaticFactorization:657/730) and names no declaration — phantom term.
- `IsProperAssignment` (BalancedMultipartite:86): the standard object is a
  proper coloring; the file imports `SimpleGraph.Coloring.Vertex` yet never
  uses `Coloring`. Connect via one equiv or rename and drop the import.
- "old" (`old_eq_parentSeparator`, `old_eq_separator`): informal; document.
- `FinsetDependsOn` (MarginalAlgebra:26): **confirmed reinvention** of Mathlib's
  `DependsOn` (`Mathlib/Logic/Function/DependsOn.lean:64`, used in exactly this
  lmarginal setting). `FinsetDependsOn A f` is `DependsOn f ↑A`; replace it.

### Criterion 3 — file organization

- **Inverted import**: `MarginalAlgebra` (fully generic, no graph content)
  imports `CliqueMarginals`. Reverse the arrow; the CliqueMarginals duplication
  in criterion 1 then collapses to one-liners.
- **`EntropyGluing.lean` (1162 lines) → split 3 ways** at clean seams:
  25–670 normalized-density API, 672–948 the gluing argument proper,
  950–1158 ε-regularization limit (belongs with `Regularization`). Zero internal
  section headers currently.
- **`ChromaticFactorization.lean` (832 lines) → split at line 636**:
  prefix-coloring counting vs chromatic-polynomial identity. Move
  `pureChordal_balancedMultipartite_minimal` (798) to `Main.lean` — it is a
  second final-facing theorem hiding in a machinery file, undercutting
  milestone 49's "sole final theorem in Main".
- **Merge** `CubeInequality.lean` (64 lines, single consumer) into
  `IntegratedCube.lean`.
- **Rename** `Algebra.lean` → `CliquePolynomial.lean` (it defines only
  `cliquePoly`), and `Example.lean` → `Corollaries.lean` (clash with
  `Examples/`).
- **Misplaced lemmas**: `cliquePolyTail` (+`cliquePoly_mul_tail_eq`) from
  CertificatePolynomialBound → CliquePolynomialBound;
  `abs_finset_prod_sub_prod_le_sum_abs` (Regularization:23) →
  ProductInequalities; MoonMoser's relabeling gadgets
  (`topDeleteIncidenceIso`, `topDeleteOneEdgeIso`, `finTwoEquiv`,
  `pairToZeroOnePerm`) → Relabeling; CliqueMarginals 22–138 (pure Finset/Equiv
  combinatorics) → Relabeling; the color-free `PureCliqueTreeDecomp` lemmas in
  ChromaticFactorization (41, 115, 285, 708) → the combinatorics layer;
  ChromaticFactorization's graphon tail of CliqueTreeCombinatorics (231–246)
  → downstream.
- **Root `PureChordal.lean` import list is inconsistent**: 20 modules explicit,
  5 transitive (incl. `BalancedMultipartite`, which therefore looks orphaned),
  1 redundant. List all modules explicitly.
- Verified milestone 49 layout holds: Example.lean is the only importer of
  Main.lean — but Example.lean never *uses* Main's theorem (corollaries go
  through the certificate form); add an explanatory comment.

### Criterion 4 — other Mathlib-bar issues

- **Docstrings — the largest gap**: EntropyGluing has 4 docstrings for ~55
  public declarations, all 10 core `def`s undocumented. Main.lean and
  Example.lean lack module docstrings (the two API-facing files!). Headline
  theorems missing docstrings across HomDensity, Relabeling,
  WeightedCauchySchwarz, CubeInequality, IntegratedCube, Gibbs,
  ProductInequalities, CliqueMoments, CliquePolynomialBound.
- **Unused hypotheses**: `hconnected` in **both** final theorems (Main.lean:17,
  ChromaticFactorization:803) is never used — drop or rename `_hconnected` with
  a paper-fidelity comment. Also: `[DecidableEq V]` on `assignmentMeasure`
  (HomDensity:37), `hf_int`/`hg_int` in Gibbs' two-sided-bounds lemmas
  (derivable), `hf : Measurable f` in `lmarginal_mul_of_left_updateInvariant`
  (MarginalAlgebra:178), the artificial `x₀ : I → Ω` witness argument in
  `lintegral_mul_eq_of_lmarginal_eq` (MarginalAlgebra:297; derive from
  `IsProbabilityMeasure` and drop from EntropyGluing call sites), `3 ≤ r` where
  `2 ≤ r` suffices (CliquePolynomialBound:27–81).
- **Trust surface**: `IsChordal` (ChordalStructure:45) is *defined* as existence
  of a `MaximalCliqueTreeDecomp`; equivalence with textbook chordality is not
  proven. State this prominently on the definition's own docstring (long-term:
  prove one direction from a perfect-elimination ordering).
- **Repeated hypothesis noise**: the quadruple
  `(W) {δ} (hδpos : 0 < δ) (hδ : ∀ a b, δ ≤ W a b)` appears in ~28 EntropyGluing
  and ~20 JunctionDensity signatures — factor via `variable` or a named
  predicate (e.g. `W.UniformlyPositive δ`). Same for the threshold hypothesis
  `1 - 1/(r-1) ≤ cliqueDensity 2 W` in 6 signatures (name the threshold).
  CliqueMoments repeats `{α} [Fintype α] [DecidableEq α]` in ~18 signatures.
- **Naming**: `ge` lemmas → `le` form (`homDensity_mul_sep_ge_cliqueDensity_pow`
  + `_of_lower_bound`, `homDensity_ge_cliquePoly_quotient`,
  `cliqueDensity_ge_cliquePoly`); `*_lower_bound`/`*_upper_bound` suffixes →
  conclusion-named; `bagIndicesLT_card`/`accumulatedVerticesLT_card` state
  `= univ`, not card facts; `edgeDensity_balancedMultipartite` names a
  nonexistent `edgeDensity`; `bagTransition_toReal_*` drops the `ENN` suffix
  inconsistently; `notMem` spelling.
- **Tactic robustness**: `field_simp; nlinarith` closing an algebraic identity
  (EntropyGluing:789) → `linear_combination`; `dsimp at *` + `field_simp` +
  `nlinarith` finish in WeightedCauchySchwarz (95–96) → explicit discriminant
  step; non-terminal `norm_num` in Example.lean:19/34; fragile `change` at
  CliqueMoments:432 (make `twoExtensionGraph` a `def` with an unfolding simp
  lemma); pervasive `unfold` in EntropyGluing → `simp only [defn]`; many
  `:= by exact` one-liners → term mode.
- **Nat-subtraction hack**: `cliqueStepFactor` via `((j - 1 : ℕ) : ℝ)`
  (CliquePolynomialBound:20) forces repeated cast-repair blocks; define with
  real subtraction or shift the index.
- Mathlib overlaps (**checked against the pinned checkout, no build needed**):
  `DependsOn` exists (`Mathlib/Logic/Function/DependsOn.lean:64`) → replace
  `FinsetDependsOn`; `dist_prod_prod_le` exists
  (`Mathlib/Analysis/Normed/Group/Basic.lean:860`) → strong replacement candidate
  for `abs_finset_prod_sub_prod_le_sum_abs` (verify the ℝ specialization fits).

---

## Progress log

- **2026-07-26 · P0/P1 resolved.** `purechordal_lean` committed as a green
  baseline (`.lake` ignored). Builds **work on this machine** (full `lake build`
  = 3287 jobs, green); v4.31.0 toolchain, Mathlib reused from `complete_lean`. So
  a real verification loop exists — every workstream below is build-verified.
- **WS-C done** (commit `ece9fec`). Gibbs collapsed 218 → 169 lines: the
  copy-pasted 35-line bound extracted to one private `norm_mul_log_div_le`, the
  redundant `_of_bound` intermediate removed; external `*_of_exists_bounds` API
  unchanged.
- **WS-E done** (commit `95bac0f`). Deleted the three verbatim `bagIndicesBefore`
  clones of Certificate's public API from CliqueTreeCombinatorics (249 → 216 lines).
- **WS-H done** (commit `f2e62a7`). Merged the twin `cliqueStepFactor_nonneg` /
  `cliqueStepFactor_pos_of_lt` (nonneg now delegates to the strict form, handling
  only the `j = r` boundary). Skipped the real-subtraction refactor: the
  Nat-subtraction form aligns `cliqueStepFactor` definitionally with `cliquePoly`
  at the `cliquePoly_succ` interface, so switching would relocate cast-repair, not
  remove it.
- **WS-F done** (commits `152c227`, `66d1af7`). Reversed the
  MarginalAlgebra ← CliqueMarginals import (MarginalAlgebra now imports the
  Mathlib marginal API directly), then deduplicated two CliqueMarginals lemmas
  against the generic `lmarginal_compl_subset` /
  `FinsetDependsOn.lmarginal_eq_self_of_disjoint` (523 → 484 lines).
  **Deferred:** the `FinsetDependsOn` → Mathlib `DependsOn` swap — it needs a full
  rewrite of ~8 combinators + ~20 sites against the Set-based API for no functional
  gain.
- **WS-G done** (commit `6c9ff91`). Extracted `mem_separator_of_mem_accumulated`
  and `mem_newVertices_of_notMem_accumulated`; the 77-line
  `extendColor_current_injective` inlined these eight times, now one-liners.
- **WS-I (module moves) done** (commits `79e7d25`, `9dde12b`). Renamed
  `Algebra` → `CliquePolynomial`, merged `CubeInequality` → `IntegratedCube`,
  rewrote the root import list to name every module, and moved
  `pureChordal_balancedMultipartite_minimal` to Main. **Deferred:** the
  `Example` → `Corollaries` rename (the FINAL task reworks `Examples/` anyway) and
  the two large file *splits* (ChromaticFactorization ~776 lines, EntropyGluing
  1162) — delicate new-file surgery, moderate value; do as a focused pass.
- **WS-A (documentation) largely done** (commits `43889dd`, `1cb4d92`, `03f7e0d`).
  Docstrings for all 10 EntropyGluing normalized-density defs + four section
  headers + expanded module docstring; module docstring for Main; docstrings for
  the ProductInequalities deficit lemmas, weighted Cauchy–Schwarz, `homDensity_iso`,
  the integrated cube inequality, and the graphWeight/homDensity lower bounds.
  HomDensity's core objects were already documented.
- **Still deferred (reasoned):**
  - **File splits** (ChromaticFactorization ~776, EntropyGluing 1162): section
    headers now give EntropyGluing internal structure, mitigating the size
    concern; the actual new-file surgery is delicate for modest gain.
  - **EntropyGluing density-API bundling**: highest-risk edit in the plan
    (~300 lines but rewrites four proof tracks); not attempted.
  - **Naming sweep** `ge`→`le`: not pure renames — each flips the inequality
    direction in the *statement* and touches call sites; churny and semantics-
    adjacent, deferred.
  - **Fine lint** (`linter.unusedSectionVars`, `linter.unnecessarySimpa`):
    benign style warnings; each fix rebuilds deep files for marginal gain.
- **~~WS-D / WS-J / WS-A remaining:~~ (superseded by the two entries above)** EntropyGluing density-API bundling (highest
  risk — a `BoundedDensity` structure rewriting four tracks; ~300 lines but high
  breakage risk), section headers + docstrings, the `ge`→`le` / `*_lower_bound`
  naming sweep, and the compiler's accumulated lint (unused section variables,
  `simpa`→`simp`, unused `hf`/`hsr` binders). All lower-risk polish except the
  bundling.
- **FINAL workstream added (deferred to the very end by user request):** replace
  the Diamond/Goldner–Harary examples with k-partite optimality proofs for all 17
  non-clique pure chordal graphs on ≤ 6 vertices (1+2+5+13 = 21 total, minus 4
  cliques). **Prerequisite discovered:** instantiating
  `pureChordal_balancedMultipartite_minimal` needs `IsChordal H` +
  `HasPureMaximalCliques H r`, i.e. `Maximal H.IsClique` reasoning that the current
  `PureCliqueTreeDecomp`-based examples avoid. Requires a decidable maximal-clique
  bridge lemma + computable per-graph `DecidableRel` adjacency (Diamond's
  `Classical.decRel` cannot be `decide`d), then a generator emitting the 17
  certificates. Non-trivial; plan separately before executing.
- **WS-B (partial) done** (commit `84465d2`). Deleted six zero-reference
  *infrastructure* declarations (`UpdateInvariant.mul/.inv`,
  `integral_toReal_mul_eq_of_lmarginal_eq`, two `measurable_*Density` wrappers,
  `finsetPermFixing_map_diff`). **Deferred pending decision:** the
  "meaningful but unused" declarations and the unused `hconnected` (see the
  open decisions below / criteria 2 and 4).

## Execution plan

### Blocking facts (established 2026-07-26)

- **`purechordal_lean/` is entirely untracked in git.** No baseline, no diff, no
  rollback point. Nothing below may start until it is committed.
- **No CI and no build automation exist**, and this machine cannot run a cold
  `lake build` (16 GB RAM; a full build needs ~32 GB). Refactoring Lean without a
  build loop is unsafe: dedup, renames, and moves break compilation silently.
- Mathlib is a **prebuilt local path dependency** (shared from `complete_lean`,
  Lean v4.31.0); a full `.lake/build` already exists. So *incremental single-file*
  rebuilds may fit in 16 GB even though a cold full build does not — the key
  unknown (P1).

### Prerequisites (in order, before any Tier ≥1 work)

- **P0 — Commit a green baseline.** Add a `.gitignore` for `.lake/`, commit the
  current passing sources. Non-negotiable; without it no refactor is recoverable.
- **P1 — Establish the verification loop.** One experiment: trivially edit a leaf
  file (`Example.lean`) and `lake build PureChordal.Example`, watching peak RAM.
  - *Fits* → a real (slow) local loop exists; use it: one workstream → build →
    commit green.
  - *Does not fit* → secure a ≥32 GB build environment (remote/cloud/second
    machine) before Tier ≥1. Until then restrict to Tier 0.
- **P2 — Cheap Mathlib lookups (DONE, no build needed):** `DependsOn` and
  `dist_prod_prod_le` both exist (see criteria 2 and 4) — bake into WS-F/WS-I.

### Risk tiers (govern what is safe given the P1 outcome)

- **Tier 0 — cannot break a proof.** Docstrings, module docstrings, comments,
  coined-term provenance, `IsChordal` note, sanity-check labels. Safe even with
  no build; build once at the end for typos.
- **Tier 1 — mechanically safe, build-confirmed.** Delete verified-dead
  *non-`@[simp]`* decls; drop provably-unused hypotheses; `:= by exact` → term
  mode. Reviewable by eye; needs one confirming build.
- **Tier 2 — `@[simp]` deletions and renames.** Implicit simp firing and missed
  reference sites make these build-only. Never without a working loop.
- **Tier 3 — dedup / proof refactor.** The real readability win; each unit needs
  a build. Highest correctness risk.
- **Tier 4 — file moves, splits, import reversal.** High blast radius but
  fast-failing (import errors surface immediately). Do after line-level edits so
  moves don't invalidate them.

### Workstreams (each = one buildable, committable unit)

Ordered by value ÷ risk and dependency. Under a working loop, build+commit after
each; with only remote build access, each is one round-trip. Maps to the detailed
tasks below.

1. **WS-A · Documentation & trust surface** (Tier 0) — Q4.1–4.3. All docstrings,
   Main/Example module docstrings, coined-term docs, kill phantom `chromaticTail`,
   `IsChordal` caveat, sanity-check comments. **Start here:** zero proof risk,
   safe before P1 resolves.
2. **WS-B · Dead code & unused hypotheses** (Tier 1) — Q1. The 11 dead decls,
   `hconnected` ×2, other unused hypotheses, the `x₀` witness, `:= by exact`
   sweep. `@[simp]` candidates handled as test-removals once a build exists.
3. **WS-C · Gibbs collapse** (Tier 3, self-contained) — Q2.1. 5 lemmas → 3. Low
   blast radius.
4. **WS-D · EntropyGluing bundle + split** (Tier 3+4) — Q2.4, Q3.2. Bundled
   `BoundedDensity` interface (~300 lines), then split at ~672/~950. Largest win.
5. **WS-E · Certificate / CliqueTreeCombinatorics clones** (Tier 3) — Q2.2. Delete
   3 clones, unify `previousVertices`/`previousPairs`, drop `rfl` bridges. High
   fan-out → large rebuild.
6. **WS-F · Marginal import reversal + dedup** (Tier 4→3) — Q3.1, Q2.5. Reverse
   `MarginalAlgebra ← CliqueMarginals`; replace `FinsetDependsOn` with `DependsOn`;
   collapse F1–F4; move CliqueMarginals 22–138 to Relabeling.
7. **WS-G · ChromaticFactorization extraction + split** (Tier 3+4) — Q2.3, Q3.3.
   Two membership helpers (pay off 4×), collapse `chromaticPolynomialEval`, split
   at 636, move `pureChordal_balancedMultipartite_minimal` to Main.
8. **WS-H · CliquePolynomialBound** (Tier 3) — Q2.6. Twin-merge, real subtraction,
   extract the induction's algebraic core. (Plus WS-C-adjacent WeightedCauchySchwarz
   cleanup, Q2.7.)
9. **WS-I · File reorg** (Tier 4, last) — Q3.4–3.5. Merge CubeInequality→
   IntegratedCube; rename `Algebra`→`CliquePolynomial`, `Example`→`Corollaries`;
   move `cliquePolyTail` / relabeling gadgets to homes (replace
   `abs_finset_prod_sub_prod_le_sum_abs` via `dist_prod_prod_le`); complete root
   imports; update PROOF_PROGRESS.md.
10. **WS-J · Naming sweep** (Tier 2, near-last) — Q4.4–4.6. `ge`→`le`,
    `*_lower_bound`→conclusion-named, `_card` misnomers, `ENN` consistency, plus
    the `variable`/predicate hypothesis factoring and tactic-robustness swaps.
    Batch as one build since renames touch many sites.

### Recommended immediate next step

This machine cannot build, so: do **P0 (commit baseline)** and **WS-A
(documentation)** now — both safe and valuable without a build — while resolving
**P1** in parallel (confirm incremental builds fit in 16 GB, or line up a 32 GB
environment). Everything from WS-B onward waits on that loop. Do **not** attempt
Tier ≥2 edits blind.

---

## Detailed task list

Concrete edits, grouped as originally scoped; each phase maps into the
workstreams above. **Every phase requires a `lake build` verification before its
commit** (per P1).

### Phase Q1 — dead code and mechanical hygiene (low risk, ~1 session)
1. Delete the 11 verified-dead declarations in the table above (decide on
   `card_vertices`: delete or docstring as intentional API).
2. Add "sanity check" comments to the Diamond/GoldnerHarary check lemmas.
3. Remove unused hypotheses: `hconnected` (both final theorems),
   `[DecidableEq V]` on `assignmentMeasure`, `Measurable f` in
   `lmarginal_mul_of_left_updateInvariant`, the `x₀` witness argument, Gibbs'
   redundant integrability arguments.
4. Mechanical lint: `:= by exact` → term mode, unused binders → `_`, dead
   `letI` (ChromaticFactorization:509), dead `have hquad_int`
   (WeightedCauchySchwarz:48).
5. On the build machine: test-remove the unverifiable `@[simp]` candidates.

### Phase Q2 — deduplication (the core readability fix, ~2–3 sessions)
1. **Gibbs**: extract the pointwise bound `norm_mul_log_div_le`; collapse
   5 lemmas → core + `integrable_*_of_exists_bounds` +
   `integral_*_nonpos_of_exists_bounds` (derived in 3 lines).
2. **Certificate/CliqueTreeCombinatorics**: delete the three clones; redefine
   `previousVertices := accumulatedVerticesLT ·.val` (same for pairs); drop the
   `rfl` bridges; reuse `bagIndicesLT_card` at its three inline re-proof sites.
3. **ChromaticFactorization**: extract
   `mem_separator_of_mem_bag_of_mem_accumulated` and
   `mem_newVertices_of_mem_bag_of_notMem_accumulated`; deduplicate the three
   embedding proofs; collapse `chromaticPolynomialEval` into the polynomial.
4. **EntropyGluing**: introduce a bundled `BoundedDensity` (or similar)
   structure carrying measurable/integrable/mass-one/two-sided-bounds; rewrite
   the four density tracks as instances (~300 lines saved); add the
   `c⁻¹ * f` ne_zero/ne_top helper.
5. **CliqueMarginals/JunctionDensity**: fix the F2/F3/F4 inline re-derivations;
   split `partialJunctionENN_bagMarginal` at its three natural seams.
6. **CliquePolynomialBound**: merge the twin `cliqueStepFactor` lemmas; extract
   the algebraic core of the 109-line induction; switch to real subtraction in
   `cliqueStepFactor`.
7. **WeightedCauchySchwarz**: factor `hfun`, split the integral identity from
   the discriminant step.

### Phase Q3 — reorganization (~1–2 sessions)
1. Reverse the MarginalAlgebra ← CliqueMarginals import; move CliqueMarginals
   22–138 to Relabeling; then apply the F1 one-liner collapses.
2. Split EntropyGluing at lines ~672 and ~950 (regularization stratum toward
   Regularization); add `/-! ### -/` headers regardless.
3. Split ChromaticFactorization at line 636; move
   `pureChordal_balancedMultipartite_minimal` to Main.lean; move the stranded
   decomposition lemmas to the combinatorics layer.
4. Merge CubeInequality into IntegratedCube; rename Algebra.lean and
   Example.lean; move `cliquePolyTail` and
   `abs_finset_prod_sub_prod_le_sum_abs` to their homes; move MoonMoser's
   relabeling gadgets to Relabeling.
5. Complete the root import list; update PROOF_PROGRESS.md milestone 49 wording.

### Phase Q4 — documentation and naming (~1 session)
1. Docstrings: all 10 EntropyGluing defs, headline theorems everywhere, module
   docstrings for Main/Example.
2. Coined-term docs: "pure", "tilt", "cube", "old"; kill phantom
   "chromaticTail"; connect or rename `IsProperAssignment`.
3. `IsChordal` trust-surface docstring.
4. Renames: `ge` → `le` forms, `*_lower_bound` → conclusion-named, `_card`
   misnomers, `ENN` consistency, `notMem`.
5. Hypothesis factoring: `UniformlyPositive` predicate + `variable` blocks
   (EntropyGluing, JunctionDensity, CliqueMoments); named edge-density
   threshold.
6. Tactic robustness swaps (`linear_combination`, discriminant calc,
   terminal-norm_num fixes).
