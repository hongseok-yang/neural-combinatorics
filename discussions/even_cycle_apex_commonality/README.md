# Commonality of even cycles with independent apices

Let `n ≥ 4` be even and `k ≥ 1`.  `C_n^{+k}` is the cycle `C_n` together with `k` new vertices, each
joined to every cycle vertex and to no other new vertex (`k = 1` is the even wheel).  For a graphon
`W` and a finite graph `F` write

```
  t(F, W) = ∫_{Ω^V(F)} ∏_{ij ∈ E(F)} W(x_i, x_j) dμ^{⊗V(F)},
  M(F, W) = t(F, W) + t(F, 1−W).
```

Then, for every graphon `W` on every probability space `(Ω, μ)`:

```
  H1  (commonality)      M(C_n^{+k}, W) ≥ 2^{1 − n(k+1)}                       (every k ≥ 1)
  H2  (equality)         equality in H1  ⟺  W = 1/2 almost everywhere
  H3  (relative form)    2^{n(k+1)−1} M(C_n^{+k}, W) ≥ 2^{n−1} M(C_n, W) ≥ 1   (every k ≥ 3)
```

`W : Ω² → [0,1]` is symmetric and jointly measurable, and `(Ω, μ)` is an arbitrary probability
space — not `[0,1]`, not finite, not standard Borel, and `W` is not a step function.  The proof
followed is the blueprint `even_apex_blueprint.tex`, with the changes listed in its verification
plan (decisions D1–D10) and in `DEVIATIONS.md` (X1–X4); the blueprint and the plan are not part of
this repository (see "Files not in the repository" at the end).  The Lean development is in
`lean/`.

The results are in `EvenCycleApex`:

| | |
|---|---|
| `commonality_all_even_all_apices` | H1 |
| `commonality_equality_iff_constant` | H2 |
| `apex_relative_of_three_le` | H3, first inequality |
| `one_le_cycle_normalized` | H3, second inequality (`2^{n−1} M(C_n, W) ≥ 1`) |
| `commonality_one_apex`, `commonality_two_apices` | H1 for `k = 1` and `k = 2`, proved without certificates |
| `all_even_graphon_apex_bounds` | the explicit lower bounds behind H1 (blueprint `thm:graphon-main`) |

## Building

Requires Lean `v4.31.0` (via `elan`) and mathlib `v4.31.0`.  On the development machine
`lean/.lake/packages` is a junction to an already built copy; elsewhere `lake exe cache get` downloads the prebuilt mathlib.  In `lean/`:

```
lake build                        # must end "Build completed successfully"
lake env lean CheckAxioms.lean    # axiom audit; see below
```

A clean build produces no warnings.  Rebuilding the whole development (mathlib prebuilt) takes about
18 minutes on an 8-thread machine and peaks at about 6 GB of memory; most of it is the kernel check
of the certificates (the budget table in `DASHBOARD.md`).

## Reading the statement

The claim to check is that the Lean theorems say what the blueprint's `thm:main` says (H1–H3
above).  Read these files in order.

| Read | For |
|---|---|
| `lean/EvenCycleApex/Main.lean` | H1 and H3 |
| `lean/EvenCycleApex/Equality/Main.lean` | H2 (`commonality_equality_iff_constant`, at the end) |
| `lean/EvenCycleApex/Graph/Apex.lean` | `apexCycle n k` (`C_n^{+k}`) and `edgePairs` |
| `lean/EvenCycleApex/Graph/HomDensity.lean` | `homDensity` (`t(F, W)`) |
| `lean/EvenCycleApex/Foundation/Defs.lean` | `cmpl W = 1 − W` |
| `lean/EvenCycleApex/Foundation/Graphon.lean` | `IsGraphon` — the hypothesis on `W` |

These are the definitions the theorems are stated in; there is no separate summary to trust.
Points worth checking explicitly:

* `IsGraphon W μ` asks only for joint measurability, symmetry and `0 ≤ W ≤ 1`.  `Ω` is an
  arbitrary `MeasurableSpace` with an `IsProbabilityMeasure`.
* `homDensity F W μ` is the integral over `Fin v → Ω` against `Measure.pi (fun _ => μ)` of the
  product of `W (x i) (x j)` over the pairs `i < j` adjacent in `F`: one factor per edge, no
  operator or trace encoding.
* `cycleGraph n` is mathlib's cycle on `Fin n` (`a ~ b ↔ a − b = 1 ∨ b − a = 1`).  `apexCycle n k`
  lives on `Fin (n + k)`: the first `n` vertices carry `cycleGraph n`, each of the last `k` is
  adjacent to all of the first `n`, and two of the last `k` are never adjacent.
  `apexCycle_edgeCount` confirms `|E(C_n^{+k})| = n(k+1)`.
* Powers of two avoid natural-number subtraction: `2^{1−n(k+1)}` is written `2 / 2 ^ (n * (k + 1))`,
  and `2^{m−1}` is `2 ^ m / 2`.
* In H2, "`W = 1/2` almost everywhere" is `(fun p => W p.1 p.2) =ᵐ[μ.prod μ] fun _ => 1/2`, the
  product measure on `Ω × Ω`.

## Reading the proof

`lake env lean CheckAxioms.lean` prints, for each audited result (the verification plan's §6
list and every milestone's key lemmas, 166 in all), the axioms it depends on.
Every line reads

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

or a subset of it.  These three are the standard classical axioms of mathlib.  Anything else — in
particular `sorryAx`, or `Lean.ofReduceBool`, which `native_decide` would introduce — means something
is unproved or was evaluated outside the kernel.  Equivalently,
`grep -rnE "sorry|admit|native_decide|decide \+native|ofReduceBool|^axiom" lean/` returns nothing.

**Certificates.**  For `k ≥ 3` the proof uses three six-vertex graph inequalities
(`three_universal_graph_inequalities`), each proved by a sum-of-squares certificate.  Nothing about
the certificates is trusted:

* the three target polynomials are built in `Certificate/Targets.lean` from their literal edge sets,
  independently of the certificate files;
* the certificate data (`Certificate/Data/*.lean`, generated from `certificates/*.json` by
  `tools/gen_cert_data.py`) is only an input; `Certificate/Checks/*.lean` check it with
  `decide +kernel`, i.e. by evaluation inside the Lean kernel — the 57 rational `LDLᵀ`
  factorizations, the relabelling witnesses, and the identity between each target and the certificate
  sum (`all_certificate_checks` collects these facts);
* `cert_sound` (`Certificate/Sound.lean`) proves that data passing these checks makes the target
  nonnegative on every finite weighted host.

`k = 1` and `k = 2` use no certificate: nothing under `Certificate/` is imported by
`commonality_one_apex` or `commonality_two_apices`.

**Outline.**  Every density inequality is first proved on a finite weighted host (weights `w ≥ 0`
of total mass one and a symmetric kernel `|U| ≤ 1`, `U = 2W − 1`) and then transferred to every
graphon: step graphons are finite hosts (`step_homDensity_eq_host`), step graphons are `L¹`-dense
(`exists_stepGraphon_l1_close`), and densities are `L¹`-Lipschitz (`homDensity_L1_lipschitz`).  On a
host, `A_{n/2,k} = 2^{n(k+1)−1} M(C_n^{+k}, W)` is an average of traces of `n`-th powers of conditional
matrices (`conditional_trace_bound`), so spectral trace bounds reduce everything to fourth moments:
`k = 1` by the diamond bound, `k = 2` by the certificate-free route of plan D10, `k = 3` by the
weighted fourth-moment comparison built on the three certificate inequalities, and every `k ≥ 3`
from `k = 3` by apex-number lifting.  H2 comes from continuity of the scalar lower bounds in `W`
and `c = 0 ⟺ 2W − 1 = 0` a.e. (`fourth_signed_cycle_zero_iff`).

The development is laid out as follows.

```
lean/EvenCycleApex.lean          index, one import group per milestone
lean/CheckAxioms.lean            the axiom audit
lean/EvenCycleApex/
  Main.lean          H1 and H3, by transfer from finite hosts
  Transfer.lean      the transfer lemma; H1 for k = 1, 2
  BlueprintNames.lean  the blueprint's declaration names that are restatements (plan §6)
  Graph/             C_n^{+k}, homDensity via Measure.pi, pair marginals, L¹-Lipschitz bounds,
                     colour normalization
  Host/              the finite weighted host: densities as sums, step graphons as hosts,
                     the matrix model, spectral trace bounds, scalars, the even-cycle lower bound
  Conditional/       conditional second spectral moments, the trace representation, diamond bound
  Moments/           finite Jensen/majorization inequalities, length lifting, apex-number lifting
  Finite/            the finite-host theorems: one, two and three apices, then every k
  Certificate/       graph polynomials, the targets, the checker and its soundness (M6);
    Data/            generated certificate data (literal lists)
    Checks/          the kernel checks (decide +kernel) of that data (M7)
  Equality/          continuity of the scalar bounds, c = 0 ⟺ U = 0, the equality case (H2)
  Foundation/        copied from schur_decomposition/cycle_commonality (plan D7) and pruned to
                     what is used: graphons, kernel algebra, Fubini, L¹ step approximation
tools/gen_cert_data.py   certificate JSON → Certificate/Data/*.lean and Checks/*.lean
```

`DASHBOARD.md` maps every labelled statement of the blueprint to its Lean name; `NOTES.md` is the
engineering log, with the gate evidence of each milestone.

## Trees with independent apices

A second library, `TreeApex`, in the same Lake package formalizes the paper *Commonness of
independent apices of trees* (`trees_apices_commonness.tex`, not part of this repository).
For a tree `T` on `n` vertices and `k ≥ 1`, `T^{+k}` is `T` together with `k` new vertices, each
joined to every vertex of `T` and to no other new vertex.  With `t`, `m` as above, `σ = m(P₃, W)` and
`τ = m(K₃, W)` (`P₃` the path with two edges), for every graphon `W` on every probability space:

```
  P1  (one colour, n ≥ 2)   t(T^{+k}) · t(K₂)^{n+k−3} · t(P₃)^{(k−1)(n−2)} ≥ t(K₃)^{k(n−1)}
  P2  (two colours, n ≥ 2)  m(T^{+k}) ≥ τ^{k(n−1)} / σ^{(k−1)(n−2)}
  P3  (Goodman)             σ ≥ 1/2,  τ = (3/2)σ − 1/2
  P4  (commonness)          m(T^{+k}) ≥ 2^{1 − e(T^{+k})} = 2^{2 − (k+1)n}          (every tree, every k ≥ 1)
  P5  (appendix A)          t(T) ≥ t(K₂)^{n−1}  (n ≥ 2)  and  m(T) ≥ 2^{2−n}
```

The verification plan (decisions T-D1–T-D11) is not part of this repository; every change to it
is recorded in `TREES_DEVIATIONS.md`, the status and the label-to-name map in `TREES_DASHBOARD.md`,
and the log with every gate's evidence in `TREES_NOTES.md`.

| | |
|---|---|
| `tree_apex_one_colour` | P1 |
| `tree_apex_two_colour`, `tree_apex_two_colour_polynomial` | P2 (divided and polynomial forms) |
| `half_le_commonalityM_path`, `goodman_identity` | P3 |
| `tree_apex_common` | P4 |
| `tree_sidorenko`, `tree_common` | P5 |
| `tree_apex_one_colour'`, `tree_apex_two_colour_polynomial'` | P1, P2 without natural subtraction (`n = m + 2`, `k = j + 1`) |

### Building and auditing

```
lake build TreeApex                    # builds only TreeApex and the light even-cycle modules it imports
lake env lean CheckAxiomsTree.lean     # axiom audit (plan §6 list and every milestone's key lemmas)
lake env lean CheckStatementsTree.lean # the headline statements, copied verbatim from the plan, are proved
lake env lean CheckImportsTree.lean    # import closure: no certificate or spectral module of EvenCycleApex
```

`TreeApex` uses no computational certificate.  Its import closure contains only
`EvenCycleApex.Foundation.*`, `EvenCycleApex.Graph.*` and `EvenCycleApex.Host.{Defs, Bridge,
EdgeDensity}`, so building it never triggers the 18-minute certificate chain.  A bare `lake build`
still builds only `EvenCycleApex` (`defaultTargets` is unchanged).

### Reading the statement

| Read | For |
|---|---|
| `lean/TreeApex/Main.lean` | P1–P4 |
| `lean/TreeApex/Appendix/Sidorenko.lean` | P5 (`tree_sidorenko`, `tree_common`, at the end) |
| `lean/TreeApex/Graph/Apex.lean` | `apexGraph T k` (`T^{+k}`) |
| `lean/EvenCycleApex/Graph/HomDensity.lean` | `homDensity`, `commonalityM` (shared with the even-cycle theorems) |
| `lean/EvenCycleApex/Foundation/Defs.lean`, `Foundation/Graphon.lean` | `cmpl`, `IsGraphon` |

Points worth checking explicitly:

* `T` is any `SimpleGraph (Fin n)` with Mathlib's `T.IsTree` (connected and acyclic); no tree
  encoding appears in the statements.  `apexGraph T k` lives on `Fin (n + k)`: `T` on the first `n`
  vertices, each of the last `k` adjacent to all of the first `n`, and no two of the last `k`
  adjacent.  `apexCycle_eq_apexGraph` shows that the even-cycle `apexCycle n k` is
  `apexGraph (cycleGraph n) k` (by `rfl`).
* `K₂` and `K₃` are `⊤ : SimpleGraph (Fin 2)` and `⊤ : SimpleGraph (Fin 3)`; `P₃` is Mathlib's
  `pathGraph 3`.
* `2^{2−(k+1)n}` is written `4 / 2 ^ ((k + 1) * n)`; `apexGraph_edgeCount` proves
  `|E(T^{+k})| = (k + 1) n − 1`, so this is `2^{1 − e(T^{+k})}`.  Exponents with natural subtraction
  (`n − 1`, `n + k − 3`, `(k − 1)(n − 2)`) occur only under `2 ≤ n`, `1 ≤ k`, where they are exact.
* P4 has no `n ≥ 2` hypothesis: the one-vertex tree (`T^{+k}` is the star `K_{1,k}`) is included.

### Reading the proof

Every density inequality is first proved on a finite weighted host with a `[0,1]` kernel
(`ProbHost`: weights `w ≥ 0` of mass one, symmetric `M`) and then transferred to graphons by the
even-cycle library's `L¹` step approximation (`Transfer.lean`, which copies that library's
`L1ContAt` layer with a provenance header).  The paper proves its finite inequality for simple
graphs and passes to graphons through W-random graphs; on weighted hosts its entropies become
relative entropies `relEnt ρ p = ∑ p log (ρ / p)` against the host's reference weights, and the one
analytic input is Gibbs' inequality `relEnt ρ p ≤ log ∑ ρ`.  In order:

* `Entropy/RelEnt.lean`: Gibbs (from `log u ≤ u − 1`), `KL ≥ 0`, the chain rule.
* `Entropy/TreeLaw.lean`: the paper's extension along a tree, for any symmetric finite law `Q`:
  the Markov tree law is a law with the right vertex marginals and support, and
  `relEnt ρ_{m+1} P_{m+1} = relEnt ρ_B Q + m g`.
* `Entropy/Triangle.lean`, `Entropy/Book.lean`: the random triangle (`h ≥ log R − log E`,
  `I ≤ log D − log R`) and the book law of conditionally independent pages
  (`relEnt ρ_B Q = log R + (k − 1) h`, `g ≥ k log R − log E − (k − 1) log D`).
* `Finite/OneColour.lean`: `finite_counting_inequality`, the paper's `thm:finite` on weighted hosts.
* `Host/Double.lean`, `Host/Goodman.lean`, `Finite/TwoColour.lean`: the two colours on one doubled
  host (`Bool × V`; `t(F, double) = m(F) / 2^{v(F)}` for connected `F`), Goodman's identity, and
  commonness on hosts, including the star.
* `Graph/RecTree.lean`: every Mathlib tree on `Fin n` is a relabelled recursive tree
  (`exists_recTree_iso`, vertices listed by distance from a root), and densities are invariant
  under the relabelling.

```
lean/TreeApex.lean             index, one import group per milestone
lean/CheckAxiomsTree.lean      the axiom audit;  CheckStatementsTree.lean, CheckImportsTree.lean as above
lean/TreeApex/
  Main.lean        P1–P4 for every tree, by transfer from hosts and the tree bridge
  Transfer.lean    the L¹ transfer (copied layer), continuity of densities, step graphons as hosts
  PaperNames.lean  the plan's §6 declaration names, where the development's names differ
  Graph/           apexGraph and its edges, recursive trees, the IsTree bridge
  Host/            ProbHost and its scalars, the doubled host, Goodman, two regression hosts
  Entropy/         relative entropy, the generic tree extension, the triangle and the book
  Finite/          the finite counting inequality, two colours and commonness on hosts
  Appendix/        appendix A: tree Sidorenko and commonness of trees
  Smoke.lean       the T0 smoke test of the imported pipeline
```

## Files not in the repository

The dashboards and notes refer to working files that are kept outside the repository: the
verification plans and agent prompts (`VERIFICATION_PLAN.md`, `OPUS_PROMPT.md`,
`TREES_VERIFICATION_PLAN.md`, `TREES_OPUS_PROMPT.md`), the mathematical sources
(`even_apex_blueprint.tex`, `trees_apices_commonness.tex`), the independent numerical checkers
(`certificates/independent_audit.py`, `certificates/verify_algebra.py`,
`certificates/verify_six_vertex.py`, `certificates/run_verification.sh`,
`tools/tree_entropy_check.py`), the extractor of the blueprint's embedded files
(`tools/extract_embedded.py`) and the M0 kernel-performance spike (`lean/Bench/`,
`tools/gen_bench.py`).  None of them is needed to build or audit the Lean development.  The
certificate data under `lean/EvenCycleApex/Certificate/` is regenerated by
`python tools/gen_cert_data.py {schema,data,checks}` from the tracked files
`certificates/*_sos.json` and `certificates/lean-data/*.json` (the witness files that
`independent_audit.py --export` produced).
