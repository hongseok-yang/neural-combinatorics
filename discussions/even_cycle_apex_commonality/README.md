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
followed is `even_apex_blueprint.tex`, with the changes listed in `VERIFICATION_PLAN.md` (D1–D10)
and `DEVIATIONS.md` (X1–X4).  The Lean development is in `lean/`.

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
`lean/.lake/packages` is a junction to an already built copy (`VERIFICATION_PLAN.md` §1.6);
elsewhere `lake exe cache get` downloads the prebuilt mathlib.  In `lean/`:

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

`lake env lean CheckAxioms.lean` prints, for each audited result (the list of
`VERIFICATION_PLAN.md` §6 and every milestone's key lemmas, 166 in all), the axioms it depends on.
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
lean/Bench/          the M0 kernel-performance spike (not part of the library)
tools/gen_cert_data.py   certificate JSON → Certificate/Data/*.lean and Checks/*.lean
```

`DASHBOARD.md` maps every labelled statement of the blueprint to its Lean name; `NOTES.md` is the
engineering log, with the gate evidence of each milestone.
