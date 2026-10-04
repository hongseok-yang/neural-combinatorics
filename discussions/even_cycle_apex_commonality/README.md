# Commonness of independent apices of trees and even cycles

A Lean 4 formalization of the paper in `paper/`.  For a graph `H` and `k ≥ 1`, `H^{+k}` is `H`
together with `k` new vertices, each joined to every vertex of `H` and to no other new vertex.  For a
graphon `W` and a finite graph `F` write

```
  t(F, W) = ∫_{Ω^V(F)} ∏_{ij ∈ E(F)} W(x_i, x_j) dμ^{⊗V(F)},
  M(F, W) = t(F, W) + t(F, 1−W).
```

`W : Ω² → [0,1]` is symmetric and jointly measurable, and `(Ω, μ)` is an arbitrary probability
space — not `[0,1]`, not finite, not standard Borel, and `W` is not a step function.  For every such
`W`, and with `W` omitted from `t` and `M` below:

**Even cycles** (Theorem 1.4 of the paper): for even `n ≥ 4` (`k = 1` is the even wheel),

```
  H1  (commonness)          M(C_n^{+k}) ≥ 2^{1 − n(k+1)}                          (every k ≥ 1)
  H2  (equality)            equality in H1  ⟺  W = 1/2 almost everywhere
  H3  (relative form)       2^{n(k+1)−1} M(C_n^{+k}) ≥ 2^{n−1} M(C_n) ≥ 1          (every k ≥ 3)
```

**Trees** (Theorems 1.2 and 1.3): for a tree `T` on `n` vertices, with `σ = M(P₃)` and
`τ = M(K₃)` (`P₃` the path with two edges),

```
  P1  (one colour, n ≥ 2)   t(T^{+k}) · t(K₂)^{n+k−3} · t(P₃)^{(k−1)(n−2)} ≥ t(K₃)^{k(n−1)}
  P2  (two colours, n ≥ 2)  M(T^{+k}) ≥ τ^{k(n−1)} / σ^{(k−1)(n−2)}
  P3  (Goodman)             σ ≥ 1/2,  τ = (3/2)σ − 1/2
  P4  (commonness)          M(T^{+k}) ≥ 2^{1 − e(T^{+k})} = 2^{2 − (k+1)n}           (every k ≥ 1)
  P5  (trees themselves)    t(T) ≥ t(K₂)^{n−1}  (n ≥ 2)  and  M(T) ≥ 2^{2−n}
```

| | |
|---|---|
| `commonality_all_even_all_apices` | H1 |
| `commonality_equality_iff_constant` | H2 |
| `apex_relative_of_three_le` | H3, first inequality |
| `one_le_cycle_normalized` | H3, second inequality (`2^{n−1} M(C_n) ≥ 1`) |
| `commonality_one_apex`, `commonality_two_apices` | H1 for `k = 1` and `k = 2`, proved without certificates |
| `all_even_graphon_apex_bounds` | the explicit lower bounds behind H1 (the paper's Proposition 4.6, with a different bound for `k = 2`) |
| `tree_apex_one_colour` | P1 |
| `tree_apex_two_colour`, `tree_apex_two_colour_polynomial` | P2 (divided and polynomial forms) |
| `half_le_commonalityM_path`, `goodman_identity` | P3 |
| `tree_apex_common` | P4 |
| `tree_sidorenko`, `tree_common` | P5 |
| `tree_apex_one_colour'`, `tree_apex_two_colour_polynomial'` | P1, P2 without natural subtraction (`n = m + 2`, `k = j + 1`) |

## Contents

| | |
|---|---|
| `lean/` | the Lake package with the library `ApicesCommonness` and the check files `Check*.lean` |
| `certificates/` | the three sum-of-squares certificates that the even-cycle proof checks, and the witness data that goes with them (see "Certificate files") |
| `tools/gen_cert_data.py` | generates the certificate modules under `lean/ApicesCommonness/Cycles/Certificate/` from `certificates/` |
| `paper/` | the manuscript *Commonness of independent apices of trees and even cycles* (see "The paper") |

The library has three parts, in the order of the paper:

| | |
|---|---|
| `ApicesCommonness/Common/` | graphons, homomorphism densities, weighted finite hosts and the transfer from hosts to graphons (§2), used by both proofs |
| `ApicesCommonness/Trees/` | the tree proof (§3) |
| `ApicesCommonness/Cycles/` | the even-cycle proof (§4) |
| `ApicesCommonness/Main.lean` | the main results: Theorems 1.2–1.4 of the paper, stated in full (see "Reading the statements") |

`Trees` and `Cycles` import nothing from each other, and `Common` imports neither.  All
declarations are in the namespace `ApicesCommonness`.

## Building

Requires Lean `v4.31.0` (via `elan`) and mathlib `v4.31.0`; `lake exe cache get` downloads the
prebuilt mathlib.  In `lean/`:

```
lake build                           # the whole library; must end "Build completed successfully"
lake build ApicesCommonness.Trees    # Common and Trees only, without the certificate checks
lake env lean CheckAxioms.lean       # axiom audit; see "Reading the proofs"
lake env lean CheckImports.lean      # Trees and Cycles are independent, Common imports neither
```

A clean build produces no warnings.  Building the whole library (mathlib prebuilt) takes about
25 minutes on an 8-thread machine, about 12 of them for `ApicesCommonness.Trees`.  The largest
single Lean process, a kernel check of the certificates (used only by `Cycles`), peaks at about
5.5 GB of memory.

## Reading the statements

`lean/ApicesCommonness/Main.lean` states the main results of the paper in full, in the namespace
`ApicesCommonness.MainResults`, each proved by the corresponding theorem in the table above:

| | |
|---|---|
| `trees_common` | Theorem 1.2: `T^{+k}` is common for every tree `T` and every `k ≥ 1` (P4) |
| `trees_two_colour` | Theorem 1.2: the two-colour inequality, with a positive denominator (P2, P3) |
| `trees_one_colour` | Theorem 1.3: the one-colour inequality (P1) |
| `cycles_common` | Theorem 1.4: `C_n^{+k}` is common for every even `n ≥ 4` and every `k ≥ 1` (H1) |
| `cycles_equality_iff` | Theorem 1.4: equality exactly when `W = 1/2` almost everywhere (H2) |
| `cycles_relative` | Theorem 1.4: `M(C_n^{+k}) ≥ 2^{−nk} M(C_n) ≥ 2^{1−n(k+1)}` for `k ≥ 3` (H3) |

The claim to check is that these statements say what the paper's theorems say.  They use the
following definitions, besides mathlib's.

| Definition | File |
|---|---|
| `IsGraphon` — the hypothesis on `W` | `lean/ApicesCommonness/Common/Foundation/Graphon.lean` |
| `homDensity` (`t(F, W)`) and `commonalityM` (`M(F, W)`) | `lean/ApicesCommonness/Common/Graph/HomDensity.lean` |
| `cmpl W = 1 − W` | `lean/ApicesCommonness/Common/Foundation/Defs.lean` |
| `edgePairs` (the edges of a graph) and `apexCycle n k` (`C_n^{+k}`) | `lean/ApicesCommonness/Common/Graph/Apex.lean` |
| `apexGraph T k` (`T^{+k}`) | `lean/ApicesCommonness/Trees/Graph/Apex.lean` |

P5 is not a main result of the paper; `tree_sidorenko` and `tree_common` are at the end of
`lean/ApicesCommonness/Trees/Appendix/Sidorenko.lean`.  Points worth checking explicitly:

* `IsGraphon W μ` asks only for joint measurability, symmetry and `0 ≤ W ≤ 1`.  `Ω` is an
  arbitrary `MeasurableSpace` with an `IsProbabilityMeasure`.
* `homDensity F W μ` is the integral over `Fin v → Ω` against `Measure.pi (fun _ => μ)` of the
  product of `W (x i) (x j)` over the pairs `i < j` adjacent in `F`: one factor per edge, no
  operator or trace encoding.
* `cycleGraph n` is mathlib's cycle on `Fin n` (`a ~ b ↔ a − b = 1 ∨ b − a = 1`).  `apexCycle n k`
  lives on `Fin (n + k)`: the first `n` vertices carry `cycleGraph n`, each of the last `k` is
  adjacent to all of the first `n`, and two of the last `k` are never adjacent.
  `apexCycle_edgeCount` confirms `|E(C_n^{+k})| = n(k+1)`.
* `T` is any `SimpleGraph (Fin n)` with mathlib's `T.IsTree` (connected and acyclic); no tree
  encoding appears in the statements.  `apexGraph T k` is built like `apexCycle`, with `T` on the
  first `n` vertices, and `apexCycle_eq_apexGraph` shows that `apexCycle n k` is
  `apexGraph (cycleGraph n) k` (by `rfl`).
* `K₂` and `K₃` are `⊤ : SimpleGraph (Fin 2)` and `⊤ : SimpleGraph (Fin 3)`; `P₃` is mathlib's
  `pathGraph 3`.
* Commonness of `F`, `M(F, W) ≥ 2^{1−e(F)}`, is written
  `2 / 2 ^ (edgePairs F).card ≤ commonalityM F W μ`.  `apexGraph_edgeCount` and `apexCycle_edgeCount` give
  `e(T^{+k}) = (k + 1) n − 1` and `e(C_n^{+k}) = n(k+1)`.
* Powers of two avoid natural-number subtraction: `2^{1−n(k+1)}` is written `2 / 2 ^ (n * (k + 1))`
  and `2^{−nk} x` is `x / 2 ^ (n * k)`.  Exponents with natural subtraction in the tree
  inequalities (`n − 1`, `n + k − 3`, `(k − 1)(n − 2)`) occur only under `2 ≤ n`, `1 ≤ k`, where they
  are exact.
* P4 has no `n ≥ 2` hypothesis: the one-vertex tree (`T^{+k}` is the star `K_{1,k}`) is included.
* In H2, "`W = 1/2` almost everywhere" is `(fun p => W p.1 p.2) =ᵐ[μ.prod μ] fun _ => 1/2`, the
  product measure on `Ω × Ω`.

## Reading the proofs

`lake env lean CheckAxioms.lean` prints, for each audited result (the main results and their
supporting lemmas, 271 in all), the axioms it depends on.  Every line reads

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

or a subset of it.  These three are the standard classical axioms of mathlib.  Anything else — in
particular `sorryAx`, or `Lean.ofReduceBool`, which `native_decide` would introduce — means something
is unproved or was evaluated outside the kernel.  Equivalently,
`grep -rnE "sorry|admit|native_decide|decide \+native|ofReduceBool|^axiom" lean/` returns nothing.

### Common

Every density inequality is first proved on a finite weighted host and then transferred to every
graphon: step graphons are finite hosts (`step_homDensity_eq_host`), step graphons are `L¹`-dense
(`exists_stepGraphon_l1_close`), densities are `L¹`-Lipschitz (`homDensity_L1_lipschitz`), and an
inequality between `L¹`-continuous functionals that holds on every step graphon holds on every
graphon (`le_of_step_graphons_cont`).

```
lean/ApicesCommonness/Common/
  Foundation/      graphons, kernel algebra, Fubini, L¹ step approximation
  Graph/           C_n^{+k} and its edges, homDensity via Measure.pi, pair marginals,
                   L¹-Lipschitz bounds, relabelling invariance
  Host/            the finite weighted host: densities as sums, densities of edge sets,
                   step graphons as hosts
  Transfer.lean    L¹-continuous functionals and the transfer from step graphons to graphons
```

### Even cycles

**Outline.**  On a host (weights `w ≥ 0` of total mass one and a symmetric kernel `|U| ≤ 1`,
`U = 2W − 1`), `A_{n/2,k} = 2^{n(k+1)−1} M(C_n^{+k}, W)` is an average of traces of `n`-th powers of
conditional matrices (`conditional_trace_bound`), so spectral trace bounds reduce everything to
fourth moments: `k = 1` by the diamond bound, `k = 2` by a certificate-free scalar bound, `k = 3` by
the weighted fourth-moment comparison built on the three certificate inequalities, and every `k ≥ 3`
from `k = 3` by apex-number lifting.  H2 comes from continuity of the scalar lower bounds in `W` and
`c = 0 ⟺ 2W − 1 = 0` a.e. (`fourth_signed_cycle_zero_iff`).

**Certificates.**  For `k ≥ 3` the proof uses three six-vertex graph inequalities
(`three_universal_graph_inequalities`), each proved by a sum-of-squares certificate.  Nothing about
the certificates is trusted:

* the three target polynomials are built in `Certificate/Targets.lean` from their literal edge sets,
  independently of the certificate files;
* the certificate data (`Certificate/Data/*.lean`, generated from the files in `certificates/` by
  `tools/gen_cert_data.py`; see "Certificate files") is only an input; `Certificate/Checks/*.lean`
  check it with `decide +kernel`, i.e. by evaluation inside the Lean kernel — the 57 rational `LDLᵀ`
  factorizations, the relabelling witnesses, and the identity between each target and the certificate
  sum (`all_certificate_checks` collects these facts);
* `cert_sound` (`Certificate/Sound.lean`) proves that data passing these checks makes the target
  nonnegative on every finite weighted host.

`k = 1` and `k = 2` use no certificate: nothing under `Certificate/` is imported by
`commonality_one_apex` or `commonality_two_apices`.

```
lean/ApicesCommonness/Cycles/
  Main.lean            H1 and H3, by transfer from finite hosts
  Transfer.lean        the transfer of apex densities; H1 for k = 1, 2
  BlueprintNames.lean  restatements of results under the names the axiom audit uses
  Foundation/          eigensystems and traces of powers, matrices as operators, the weighted
                       matrix model as a sum over closed walks
  Host/                the matrix model, spectral trace bounds, scalars, the even-cycle lower bound
  Conditional/         conditional second spectral moments, the trace representation, diamond bound
  Moments/             finite Jensen/majorization inequalities, length lifting, apex-number lifting
  Finite/              the finite-host theorems: one, two and three apices, then every k
  Certificate/         graph polynomials, the targets, the checker and its soundness
    Data/              generated certificate data (literal lists)
    Checks/            the kernel checks (decide +kernel) of that data
  Equality/            continuity of the scalar bounds, c = 0 ⟺ U = 0, the equality case (H2)
```

### Trees

The tree proof uses no computational certificate.  Its hosts have a `[0,1]` kernel (`ProbHost`:
weights `w ≥ 0` of mass one, symmetric `M`).  As in §3 of the paper, entropies are relative entropies
`relEnt ρ p = ∑ p log (ρ / p)` against the host's reference weights, and the one analytic input is
Gibbs' inequality `relEnt ρ p ≤ log ∑ ρ`.  In order:

* `Entropy/RelEnt.lean`: Gibbs (from `log u ≤ u − 1`), `KL ≥ 0`, the chain rule.
* `Entropy/TreeLaw.lean`: the extension along a tree (the paper's Lemma 3.1), for any symmetric
  finite law `Q`: the Markov tree law is a law with the right vertex marginals and support, and
  `relEnt ρ_{m+1} P_{m+1} = relEnt ρ_B Q + m g`.
* `Entropy/Triangle.lean`, `Entropy/Book.lean`: the random triangle (`h ≥ log R − log E`,
  `I ≤ log D − log R`) and the book law of conditionally independent pages
  (`relEnt ρ_B Q = log R + (k − 1) h`, `g ≥ k log R − log E − (k − 1) log D`); Lemmas 3.2 and 3.3.
* `Finite/OneColour.lean`: `finite_counting_inequality`, the paper's Proposition 3.4.
* `Host/Double.lean`, `Host/Goodman.lean`, `Finite/TwoColour.lean`: the two colours on one doubled
  host (`Bool × V`; `t(F, double) = M(F) / 2^{v(F)}` for connected `F`), Goodman's identity, and
  commonness on hosts, including the star.
* `Graph/RecTree.lean`: every mathlib tree on `Fin n` is a relabelled recursive tree
  (`exists_recTree_iso`, vertices listed by distance from a root), and densities are invariant
  under the relabelling.

```
lean/ApicesCommonness/Trees/
  Main.lean        P1–P4 for every tree, by transfer from hosts and the tree bridge
  Transfer.lean    continuity of densities, step graphons as ProbHost
  PaperNames.lean  restatements of results under the names the axiom audit uses
  Graph/           apexGraph and its edges, recursive trees, the IsTree bridge
  Host/            ProbHost and its scalars, the doubled host, Goodman, two regression hosts
  Entropy/         relative entropy, the generic tree extension, the triangle and the book
  Finite/          the finite counting inequality, two colours and commonness on hosts
  Appendix/        P5: tree Sidorenko and commonness of trees
  Smoke.lean       a smoke test of the transfer pipeline from Common
```

## Certificate files

`certificates/` holds the certificates of the paper's appendix A that the Lean proof uses, in the
form `tools/gen_cert_data.py` reads.

| | |
|---|---|
| `mean_three_sos.json` | `Q_3`, the mean target for three apices |
| `negative_majority_sos.json`, `positive_majority_sos.json` | `Q_−` and `Q_+`, the two weighted targets |
| `lean-data/feature_schema.json` | the nineteen rooted blocks (roots, root type, new vertices, features) shared by all targets |
| `lean-data/ldl_witnesses.json` | exact `LDLᵀ` factorizations of the integer numerators of every block matrix |
| `lean-data/normalization_witnesses.json` | for each of the `2^15` edge masks on six vertices, its normal form (one of 156 isomorphism classes) and a relabelling to it |

Each `*_sos.json` gives the target's name, the dimensions of its nineteen blocks, and the integer
numerators of its nineteen positive definite matrices over a common denominator.
`ldl_witnesses.json` also contains the factorizations for the paper's fourth target `Q_2`
(`mean_two`), which the Lean proof does not use; the generator reads only those of the three targets
above, 57 matrices in all.  To regenerate the certificate modules, run from this directory:

```
python tools/gen_cert_data.py schema    # lean/ApicesCommonness/Cycles/Certificate/Schema.lean
python tools/gen_cert_data.py data      # Certificate/Data/{Witnesses,Target_*}.lean
python tools/gen_cert_data.py checks    # Certificate/Checks/{MeanThree,Neg,Pos}.lean
```

## The paper

`paper/apices_commonness.tex`, with its bibliography `apices_commonness.bib`, is the manuscript
*Commonness of independent apices of trees and even cycles*, whose proofs are the ones formalized
here.  §2 collects the tools both proofs share, §3 is the tree proof, §4 the even-cycle proof, §5
compares both with the Lean library, and appendix A specifies the four certificates.  To compile,
in `paper/`:

```
pdflatex apices_commonness
bibtex apices_commonness
pdflatex apices_commonness
pdflatex apices_commonness
```

§5 records where the Lean development differs from the paper.  The paper's graphons live on
`[0,1]`, Lean's on any probability space.  The paper uses four certificates (`Q_2`, `Q_3`, `Q_−`,
`Q_+`); Lean checks three and proves the case of two apices without `Q_2`, through a different
scalar bound that does not give the paper's stronger two-apex inequality.  Lean proves the cycle
equality case through a finite spectral remainder estimate instead of the spectral theorem.  The
paper's appendix B (finite colourings) is not formalized.
