# Engineering and mathematical log

Chronological.  Decisions inside the plan's freedom, spike timings, Lean gotchas, blockers, and gate
evidence.  Status lives in [`DASHBOARD.md`](DASHBOARD.md); changes to the plan in
[`DEVIATIONS.md`](DEVIATIONS.md).

## 2026-09-27 — M0 (scaffold, data, kernel spike)

### Plan documents aligned with the certificate-free `k = 2` route

The user asked that `k = 2` use the existing hand proof, not the `mean_two` certificate.  Plan D10
already did this, but `DASHBOARD.md`, `VERIFICATION_PLAN.md` (D6, §2.5, §3, M7) and `OPUS_PROMPT.md`
still called the `mean_two` data "kept but unused / optional".  Reworded everywhere to "excluded
(D10)"; the JSON stays in `certificates/` only because `independent_audit.py` reads all four files.
Recorded as DEVIATIONS X2.  The D10 chain was re-derived by hand: `K_{1,2,2} = C₄⁺¹` (8 edges each),
and `(1+2b)⁴ − (1+b)²(1+6b) = 11b² + 26b³ + 16b⁴`.

### Scaffold

* `lean/` created per plan §1.6: `lakefile.toml` (package `EvenCycleApex`), `lean-toolchain`
  (`leanprover/lean4:v4.31.0`), `lake-manifest.json` copied from `goodman-style-bound/complete_lean`
  with the root `name` changed to `EvenCycleApex`, and `.lake/packages` a directory junction to the
  built packages of `complete_lean`.  First `lake build`: Mathlib replayed, not rebuilt (the first
  built job was our own module, job 8558/8578); 11 min wall time, all of it the copied modules.
* Foundation copied from `schur_decomposition/cycle_commonality/lean` at commit `e2d96440` into
  `lean/EvenCycleApex/Foundation/`, each file with a four-line provenance header; changes are only
  `import` paths and the prefix `CycleCommonality → EvenCycleApex` (sed).  The D7 list is not the
  full import closure: `Model/StepModel.lean` imports `Spectral/RankOneTrace.lean`, which pulls in
  `Spectral/Interlace.lean` (where `rankOne` lives) and `Majorization/{Karamata,Bump,RankOne}.lean`.
  All five copied as well (DEVIATIONS X1).  Build: 0 warnings, 0 errors.
* Note: the copied `StepGraphon` has a `[0,1]`-valued `U`; our finite host will carry a `[-1,1]`
  signed kernel, so `FiniteHost` (M2) is a new structure that reuses only `trace_weighted_pow_eq_sum`
  and the matrix/unit-vector pattern.
* Smoke theorem `EvenCycleApex.foundation_smoke` (`EvenCycleApex/Smoke.lean`) uses `IsGraphon`,
  `exists_stepGraphon_l1_close`, `StepGraphon.trace_op_pow`, `EigenSystem.ofSymmetric` and
  `EigenSystem.trace_pow_eq_sum`.

### Certificate data

* `tools/extract_embedded.py` wrote CRLF line endings on Windows (on-disk sizes larger than the
  printed byte counts).  Patched to `open(..., newline='')`; the eight files now match the embedded
  byte counts exactly (e.g. `mean_three_sos.json` 110,862 bytes).
* `python independent_audit.py --certificates . --export lean-data`: all PASS (32,768 witnesses,
  156 normal forms, 4 × 19 LDLᵀ, 956 pivots, 13,708 entries, 131,072 coefficient slots), 57 s.
* Data facts used for the encoding: matrix entries ≤ 26 digits; LDLᵀ numerators ≤ 373 digits,
  denominators ≤ 350 digits (the three proof-path targets); 156 normal forms, so an orbit index
  fits in 8 bits; a base-6 permutation code is < 6⁶ = 46,656.

### Kernel spike (plan §4 M0)

Generator `tools/gen_bench.py certificates lean/Bench`; the benchmark files import only `Init` and
are not part of the library.  Timings are the profiler's "type checking" line (kernel time).

* **(a) one 15×15 rational FactorOK**, core `Rat` via `mkRat`, `positive_majority` block 16 (the
  block with the largest LDLᵀ numbers, up to 500 digits in numerator + denominator): **0.87 s**.
  Negative control (one matrix entry +1): `decide` fails, as it must.
* **Profiler caveat.**  Lean 4.31 kernel-checks declarations in parallel tasks, and the profiler's
  per-declaration "type checking took" line then measures from a shared start (the lines of a
  32-theorem file grew 1 s, 2 s, …, 29 s and summed to 484 s against 50.6 s wall).  Multi-theorem
  timings below are therefore wall-clock with `lake env lean --threads=1`, which includes parsing
  and elaborating the data.
* **(b) 32,768 relabelling witnesses, plan encoding** (typeclass notation `>>>`, `%`, `testBit`,
  base-6 codes, all 32 chunks in one conjoined theorem): **aborted** after 336 s CPU at 5.7 GB
  resident (the machine had 1 GB free).  One kernel cache for the whole check is the problem.
* **(b′) the same 32,768 witnesses, optimized**: direct `Nat.shiftRight/land/mod/lor/beq` (the
  kernel's GMP-accelerated primitives, no instance unfolding), 3-bit permutation fields, a packed
  6×6 pair-index table, bijectivity as `OR of 1 <<< π(i) = 63`, one theorem per 1024-chunk:
  **81.7 s wall single-threaded** for the whole file (≈ 2 ms per witness), 50.6 s wall with the
  default parallelism.
* **(c) trie accumulation, plan encoding**: the eleven `r = 4` blocks of `mean_three` expanded
  naively, 158,400 signed monomials inserted into a depth-15 binary trie keyed by the mask, path
  forced at every insertion: **aborted** after 343 s CPU at 7.9 GB resident.  (The lazy variant
  was not run: unforced accumulators build a 158,400-deep term.)  Kernel lesson: the kernel
  substitutes arguments unevaluated and caches every whnf, so an accumulator must be (1) forced at
  every step — here by `match Nat.beq acc 0 with | true => k acc | false => k acc` — and (2) small,
  because every intermediate version stays in the cache.
* **(c2) redesign**: the same `r = 4` group, but each skeleton `(a, b, T)` gets one merged
  coefficient `Σ_t (−1)^{|T∖t|} A⁽ᵗ⁾_ab` computed in Lean from the eleven literal matrices
  (14,400 updates), the orbit id of the skeleton supplied as data, and the accumulator two packed
  naturals `(pos, neg)` with one 128-bit slot per orbit (156 × 128 bits), forced at each step:
  **18.2 s kernel, 29.7 s wall, 3.5 GB peak**, one theorem.  Negative control (one orbit id
  changed): `decide` proves the proposition false, as it must.  Memory per theorem will be bounded
  by splitting at literal checkpoints (e.g. one theorem per `a`-row, ≈ 1000 updates).
* **Decision** (DEVIATIONS X3): per-occurrence relabelling witnesses `(orbit, π)` for the 15,548
  target-independent skeletons and the target pieces, instead of the global 32,768-entry table;
  merged per-skeleton coefficients; packed orbit accumulators with checkpoints; dense subset
  enumeration of `P_ε(E)`.  Soundness needs one new elementary lemma (base-2¹²⁸ digits are unique
  under a total-mass bound).  Estimated total kernel time for all three targets: FactorOK ≈ 30 s,
  skeleton witnesses ≈ 35 s, pieces ≈ 10 s, accumulations ≈ 3 × 20 s — a few minutes.
* `certificates/lean-data/normalization_witnesses.json` and the generated `Data/Perm.lean` (the
  global table) are superseded by X3; `Perm.lean` stays until M6 generates the per-occurrence data.

### Data files

`tools/gen_lean_data.py certificates lean/EvenCycleApex/Certificate/Data` writes
`Matrices_{MeanThree,Neg,Pos}.lean` (19 `List (List Int)` blocks each), `LDL_{MeanThree,Neg,Pos}.lean`
(strict lower rows of `L` and the diagonal `δ` as `(Int × Nat)` pairs; the generator asserts the
unit diagonal and zero upper part it drops), and `Perm.lean` (32 chunks of 1024).  All import only
`Init`; each elaborates in about 47 s (parallel).  `lakefile.toml` now names
`EvenCycleApex.Certificate.Data.+` in `globs`, so `lake build` elaborates them.

### M0 gate evidence (2026-09-27)

```text
lake build                     Build completed successfully (8586 jobs); 0 warnings
lake env lean CheckAxioms.lean
'EvenCycleApex.foundation_smoke' depends on axioms: [propext, Classical.choice, Quot.sound]
'EvenCycleApex.exists_stepGraphon_l1_close' depends on axioms: [propext, Classical.choice, Quot.sound]
'EvenCycleApex.EigenSystem.trace_pow_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'EvenCycleApex.trace_weighted_pow_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'EvenCycleApex.cycleDensity_of_factored' depends on axioms: [propext, Classical.choice, Quot.sound]
forbidden-token scan (native_decide, decide +native, sorry, admit, ofReduceBool, axiom): none
```

## 2026-09-27 — M1 (graph densities on an arbitrary probability space)

Files `lean/EvenCycleApex/Graph/{Apex,HomDensity,PairMarginal,Lipschitz,DensityAlgebra}.lean`.

* **Graphs.**  `cycleGraph n` is Mathlib's `SimpleGraph.cycleGraph` (with its `DecidableRel`
  instance), so the public statements use the library definition.  `apexCycle n k` is defined by
  `Fin.addCases` on both endpoints; the four simp lemmas `apexCycle_adj_castAdd_castAdd` (↔ cycle
  adjacency), `…_castAdd_natAdd`, `…_natAdd_castAdd` (always) and `apexCycle_not_adj_natAdd_natAdd`
  are its characterization; decidability by the same case split.
* **Edge counts.**  `edgePairs F` (ordered pairs `i < j`, the index set of `homDensity`) is put in
  bijection with Mathlib's `edgeFinset` (`card_edgePairs`), so counts come from the handshake lemma
  `sum_degrees_eq_twice_card_edges`: `cycleGraph_card_edgePairs` from Mathlib's
  `cycleGraph_degree_three_le`, and `apexCycle_edgeCount` from the degrees `2 + k` (cycle vertex)
  and `n` (apex), split with `Fin.sum_univ_add`.
* **Density and normalization.**  `homDensity` is literally plan D4.  `signedKernel W = 2W − 1`,
  `colourKernel σ U = 1 + σU`; `colour_normalization` is `(t(F,S₊) + t(F,S₋))/2 = 2^|E|/2 · M(F,W)`
  (a pointwise identity: `S₊ = 2W`, `S₋ = 2(1 − W)`, and `homDensity_const_mul`).
  `normalizedApexDensity`/`normalizedCycleDensity` are D5's `A_{n/2,k}`/`R_n`, and
  `normalizedApexDensity_eq_colour_mean` rewrites `A_{n/2,k}` as the colour average (uses
  `apexCycle_edgeCount`).
* **Pair marginal** (plan §2.1, risk E did not materialize): `Measure.prod_eq` on rectangles; the
  preimage of `s ×ˢ t` is the box `Set.univ.pi` with `s` at `i`, `t` at `j`; `Measure.pi_pi` plus
  a factorization `μ(box l) = [l = i ? μ s : 1]·[l = j ? μ t : 1]` and `Finset.prod_ite_eq'`.
* **Lipschitz.**  Telescoping `abs_prod_sub_prod_le` (`|∏f − ∏g| ≤ B^{|s|−1} Σ|f − g|`, by
  `Finset.induction_on`; the `B · B^{|s|−1} ≤ B^{|s|}` step splits on `s = ∅`).  Then
  `homDensity_L1_lipschitz` with the blueprint's exact constant `e B^{e−1}`, and the graphon form
  `commonalityM_L1_lipschitz`: `|M(F,W) − M(F,V)| ≤ 2e‖W − V‖₁` (what the transfer uses).
* **Density algebra.**  `homDensity_comap_equiv`: relabelling by a permutation, for symmetric `L`
  (`MeasurableEquiv.piCongrLeft` change of variables, edges reindexed by `sortPair`).  Isolated
  vertices and disjoint unions are only used on finite hosts (certificate masks, `a = m²`, `mτ`);
  they are proved there in M2 as finite-sum identities, not at graphon level.
* **Statement lock check.**  The three D5 headline statements, with `sorry` placeholders in a
  scratch file outside `lean/`, elaborate against these definitions.
* Lean gotchas: `Sym2.mk` is curried in this Mathlib — use `s(a, b)`; `Measurable.comp` against a
  lambda needs the inner map's type stated first (`have h : Measurable fun x => (x a, x b) := …`);
  `MeasurableEquiv.piCongrLeft_apply_apply` needs `(β := fun _ => Ω)`; `integral_finset_sum` and
  `integrable_finset_sum` are deprecated in favour of `…finsetSum`; keep `[MeasurableSpace Ω]` out of
  sections with pure kernel algebra, or the unused-section-variable linter warns.

### M1 gate evidence (2026-09-27)

```text
lake build                     Build completed successfully (8591 jobs); 0 warnings
'EvenCycleApex.apexCycle_edgeCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'EvenCycleApex.cycleGraph_card_edgePairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'EvenCycleApex.colour_normalization' depends on axioms: [propext, Classical.choice, Quot.sound]
'EvenCycleApex.normalizedApexDensity_eq_colour_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
'EvenCycleApex.normalizedCycleDensity_eq_colour_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
'EvenCycleApex.pairMarginal_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound]
'EvenCycleApex.integral_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'EvenCycleApex.homDensity_L1_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'EvenCycleApex.commonalityM_L1_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'EvenCycleApex.homDensity_comap_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 2026-09-27 — M2 (weighted finite host)

Files `lean/EvenCycleApex/Host/{Defs,Bridge,EdgeDensity,Matrix,Spectral,Scalars,ScalarBounds,EvenCycle,Regression}.lean`.

* **Host structure (plan D2, choice recorded).**  `FiniteKernel d` bundles weights `w` and the
  signed kernel `U`.  Weights are required to be **nonnegative**, not positive: the step bridge then
  needs no restriction to cells of positive mass, and every blueprint argument survives with "at
  every point" read as "at every point of positive mass" (e.g. `D_s = 0 ⟹ w(x) h(x) = 0`).
* **Step bridge.**  `step_homDensity_eq_host` (any graph `F`, cell weights `μ(σ⁻¹{i})`), the
  argument of `cycleDensity_of_factored` for an arbitrary edge set.  `exists_host_of_isStepKernel`
  restricts a step graphon to the range of its cell map so its matrix is symmetric and `[0,1]`-valued
  at every entry.
* **Density algebra on hosts** (`EdgeDensity.lean`), on raw edge sets `Finset (Fin v × Fin v)`:
  relabelling by an equivalence (`edgeDensity_map_equiv`), by a permutation with re-sorted pairs for
  symmetric kernels (`edgeDensity_image_sortPair`, `edgeDensity_eq_of_iso` — the permutation only has
  to exist, so `decide` finds it), disjoint unions (`edgeDensity_append`), isolated vertices
  (`edgeDensity_castAdd`), and `lem:parity` both as an algebraic identity
  (`colour_parity_expansion[_odd]`) and for densities (`edgeDensity_colour_even/odd`).  With this,
  the host part of `lem:density-algebra` is complete.
* **Small graphs are evaluated by `simp`.**  `sum_fun_fin_succ` expands a sum over
  `Fin (n+1) → Fin d` with `Matrix.vecCons`; `simp` then evaluates every vertex index (with `Fin.cons`
  it got stuck at index `2`).  Combined with `decide` for edge-set equalities, powersets and the
  existence of an isomorphism (24 permutations of `Fin 4` in a few seconds), `lem:fourth-traces`
  became: parity over the four edges of `C₄`, then 14 subgraphs each recognised as an edge, a path, a
  matching, a three-edge path or `C₄`.  This is the method for the diamond and codegree expansions
  in M3.
* **Spectral.**  `lem:finite-spectral` for any real symmetric matrix, stated with `dotProduct`/
  `mulVec`; internally the copied `EigenSystem` of `Matrix.toEuclideanLin B`.  The bridges are
  definitional (`toEuclideanLin A (toLp x) = toLp (A *ᵥ x)`, `⟪toLp x, toLp y⟫ = y ⬝ᵥ x`).  The
  weighted Jensen inequalities `Real.pow_arith_mean_le_arith_mean_pow[_of_even]` give the lower
  bounds; `sum_rpow_le_rpow_sum` (third part of `lem:moment-basics`, proved here) the upper bound.
* **Scalars** are defined as the blueprint's explicit iterated sums, with lemmas identifying them
  with edge-set densities and traces; `lem:scalar-bounds` including `‖T‖_op ≤ r` and `|p₃| ≤ br`
  (via `p₃ = ⟨F, TF⟩`, `F = Tu`, `‖F‖² = b`) and `c = ∑ wᵢwⱼK(i,j)²`.  The blueprint's host-level
  `c = 0 ⟺ U = 0` is not formalized: only the graphon version (M10, D9) is used.
* **Regression.**  The three exact 2-point hosts of `verify_algebra.py` reproduce all its values
  (`m, b, c, τ, p₃, R₄, r_{±,4}`), with `R₄` and `r_{±,4}` computed from scratch as four-cycle
  densities of `S_σ` — an independent check of `fourth_colour_traces`' normalization.
* Lean gotchas: `Real.rpow_le_self_of_le_one` (nonnegative base) instead of
  `rpow_le_rpow_of_exponent_ge` (positive base); `Sym2.map_pair_eq` → `Sym2.map_mk`; `diag` is
  ambiguous under `open Finset Matrix` (use `Matrix.diag_apply`); a `←` rewrite whose pattern is an
  implicit-size `edgeDensity` can match the wrong side — rewrite with an explicit equation instead.

### M2 gate evidence (2026-09-27)

```text
lake build                     Build completed successfully (8600 jobs); 0 warnings
lake env lean CheckAxioms.lean 38 declarations, all [propext, Classical.choice, Quot.sound], including
  step_homDensity_eq_host, hostDensity_cycle_eq_trace, normSq_pow_le_trace_pow,
  rayleigh_pow_le_trace_pow, trace_pow_le_trace_four_rpow, FiniteKernel.fourth_colour_traces,
  FiniteKernel.basic_scalar_bounds, FiniteKernel.even_cycle_lower_bound, Regression.host{1,2,3}_*
forbidden-token scan: none
```

## 2026-09-27 — M3 (conditional second spectral moments)

Files `lean/EvenCycleApex/Graph/ApexEdges.lean`, `lean/EvenCycleApex/Conditional/{Defs,Trace,Diamond}.lean`.

* **Sampling space.**  `Sample d s = Bool × (Fin s → Fin d)`, `prob = ½ ∏ w(zⱼ)`, `E F = ∑ prob · F`.
  All conditional quantities are functions of a sample; `x / 0 = 0` gives the blueprint's `D = 0`
  branches of `Q` and `Q♯ = √(Π/D)` for free, and `D = 0 ⟹ w·h = 0` (nonnegative weights) gives
  `N = Π = 0`.
* **`prop:conditional-trace`.**  `edgePairs_apexCycle` (sorted edges of `C_n^{+s}` = cycle edges on
  `castAdd` ∪ the `n s` pairs `(castAdd i, natAdd j)`) → `hostDensity_apexCycle` (split the vertex map
  by `Fin.append`) → per colour `t(C_n^{+s}, S_σ) = ∑_z ∏w(z) Tr B_{σ,z}ⁿ` (the closed-walk expansion
  with weights `w·h`; `∏ᵢ h(xᵢ) = ∏ᵢ∏ⱼ S(xᵢ, zⱼ)`).  No `ξ(x)^s` is needed here.  `Tr Bⁿ ≥ (Q♯)ⁿ`
  from `normSq_pow_le_trace_pow` at `gₓ = √(wₓhₓ)/√D` (`‖Bg‖² = (Q♯)²`), and `0 = (Q♯)ⁿ ≤ Tr Bⁿ` when
  `D = 0`.
* **`lem:quartic-support`.**  `(Q♯)⁴ − (2Π − D²) = (Π/D − D)²`; `E Π = E D (Q♯)²` and weighted
  Cauchy–Schwarz (`sum_sq_le_sum_mul_sum_of_sq_le_mul`, no square roots needed).
* **`lem:diamond`.**  `Z₁ = 1 + b` by direct algebra (`D₁ = 1 + σ f(t)`); `E Π₁` is the colour average
  of the diamond density, and parity over its 5 edges gives 16 even subsets, each recognised by
  `decide` (1 empty, 2 matchings, 8 paths, 1 four-cycle, 4 triangles with a pendant):
  `X = 1 + 2a + 8b + c + 4q`.  `q² ≤ bc` by Cauchy–Schwarz on pairs with `c = ∑ wᵢwⱼ K(i,j)²`;
  `X ≥ 1 + 2b + c/3` by `nlinarith` from `(6b − 2c/3)² ≥ 0`.  The blueprint's `|q| ≤ √(bc)` is stated
  as `q² ≤ bc`.
* **Deferred to where they are consumed** (no change of statement): `lem:codegree-moments` —
  `Z₂ = R₄` and `E Π₂ = A_{2,1}` in M5 (plan D10), `Z₃ ≥ R₄^{3/2}` and the `K_{1,2,3}`/`K_{2,3}`
  identities in M8; `def:three-apex-polynomial` in M8; the variance identity of
  `lem:conditional-vector` (not used by any later step).
* Lean gotchas: in statements, `K.E (fun ω => …)` needs `ω : Sample d s` — the section's `s` is not
  inferred through `E`; `rw [← colour_true]` also rewrites the `1` inside `-1`; `simp (disch := decide)
  only [sum_insert, sum_singleton]` expands a sum over an explicit finset of finsets in one step.

### M3 gate evidence (2026-09-27)

```text
lake build                     Build completed successfully (8604 jobs); 0 warnings
lake env lean CheckAxioms.lean 49 declarations, all [propext, Classical.choice, Quot.sound], including
  FiniteKernel.conditional_trace_bound, FiniteKernel.sharp_fourth_support,
  FiniteKernel.diamond_lower_bound, FiniteKernel.hostDensity_apexCycle_eq_sum_trace
forbidden-token scan: none
```

## 2026-09-27 — M4 (moment inequalities; first headline, one apex)

Files `lean/EvenCycleApex/Moments/{Basic,ApexLifting}.lean`, `lean/EvenCycleApex/Finite/OneApex.lean`,
`lean/EvenCycleApex/Transfer.lean`.

* **Finite one-apex bound** (`FiniteKernel.one_apex_bound`): `A_{n/2,1} ≥ E(Q♯)ⁿ ≥ (E(Q♯)⁴)^{n/4} ≥
  (X²/(1+b))^{n/4} ≥ 1` — conditional trace, weighted Jensen at the real exponent `n/4`
  (`E_pow_ge_rpow`, from `Real.rpow_arith_mean_le_arith_mean_rpow`), quartic support with `Z₁ = 1+b`,
  diamond.  `(x⁴)^{n/4} = xⁿ` is `pow_four_rpow` (plan D8: natural powers except where the exponent is
  genuinely real).
* **Transfer** (plan D3): `hostOfStep` builds the finite kernel of a step graphon (cell masses,
  `U = 2M − 1`); `normalizedApexDensity_step` identifies `A_{n/2,k}` of the step graphon with the
  host's (`step_homDensity_eq_host` for both colour kernels); `normalizedApexDensity_lipschitz`:
  `|A(W) − A(V)| ≤ 2^{n(k+1)} n(k+1) ‖W − V‖₁`; `one_le_normalizedApexDensity_of_hosts`: a finite
  bound `1 ≤ K.A n k` on all hosts gives `1 ≤ A_{n/2,k}(W)` for every graphon (choose `V` with
  `C‖W − V‖₁ < δ`, then `le_of_forall_pos_lt_add`).  It is stated for every `k`, so M5 and M9 reuse
  it unchanged.
* **Headline** `commonality_one_apex`: exactly plan D5's H1 shape at `k = 1`
  (`2 / 2 ^ (n * (1 + 1)) ≤ homDensity (apexCycle n 1) W μ + homDensity (apexCycle n 1) (cmpl W) μ`),
  for every graphon on every probability space; the elaborated statement was printed and checked
  against `homDensity`, `IsGraphon`, `cmpl`.
* **Moments** (`Moments/Basic.lean`): `moment_monotone` (Jensen, `1 ≤ p ≤ q`), `convex_two_point`
  (two-point Karamata straight from `ConvexOn`'s definition, instead of slope lemmas),
  `two_coordinate_power_comparison` (`lem:pair-majorization`, four sorting cases reduced to one),
  `length_lifting_two_fourth_moments` (`lem:length-lifting`, real exponent `q ≥ 4`).
* **Apex lifting** (`Moments/ApexLifting.lean`): `hostDensity_apexCycle_eq_xi`
  (`t(C_n^{+s}, L) = ∑ₓ ∏w · cyc · ξ(x)^s` with the apex codegree `ξ`, via `Fintype.prod_sum`) and
  `FiniteKernel.apex_number_moment_lifting` (`lem:apex-lifting` on hosts; Jensen for `ν / R_n`).  The
  blueprint states it on any probability space; only the host version is used (finite-first, then
  transfer), so this is the version formalized.

### M4 gate evidence (2026-09-27)

```text
lake build                     Build completed successfully (8608 jobs); 0 warnings
#print axioms EvenCycleApex.commonality_one_apex
  'EvenCycleApex.commonality_one_apex' depends on axioms: [propext, Classical.choice, Quot.sound]
lake env lean CheckAxioms.lean 61 declarations, all [propext, Classical.choice, Quot.sound]
forbidden-token scan: none
```

## 2026-09-27 — M5 (two apices, certificate-free, plan D10)

File `lean/EvenCycleApex/Finite/TwoApex.lean`; headline in `lean/EvenCycleApex/Transfer.lean`.

* `two_apex_scalar_inequality`: `(1 + 2b + c/3)⁴ − (1 + b)²(1 + 6b + c) = c/3 + 11b² + 6bc + 2c²/3 +
  26b³ + 15b²c + 8bc²/3 + 4c³/27 + (2b + c/3)⁴` (checked by `ring`), so `Θ(b, c) ≥ 1`, and `Θ > 1` when
  `c > 0` (`one_lt_twoApexTheta`, for H2).
* `Z_two` (`Z₂ = R₄`): `E D₂²` is the colour average of the four-cycle `z₀ – x – z₁ – y`; the
  iterated-sum identity needs one `sum_comm` and the kernel's symmetry.
* `twoApex_Pi_eq_oneApex` (`E Π₂ = A_{2,1}`): `E_z Π₂` is the density of the 8-edge graph
  `K_{1,2,2}` on `Fin 5` (`pi2Edges`); `edgePairs (apexCycle 4 1)` is computed by `decide`, and the
  relabelling between them is found by `decide` over `Equiv.Perm (Fin 5)` (0.2 s).
* `two_apex_fourth_moment_ge_one`: `Θ(b, c) ≤ E (Q♯₂)⁴` — quartic support with `Z₂ = R₄ ≥ 1`,
  `E Π₂ = A_{2,1} ≥ X²/(1+b)` (the `k = 1` bound at `n = 4`, exponent `4/4 = 1`),
  `X ≥ 1 + 2b + c/3 ≥ 0`, `R₄ ≤ 1 + 6b + c` (`a ≤ b`).
* `two_apex_bound`: `A_{n/2,2} ≥ Θ^{n/4} ≥ 1`; `commonality_two_apices` via the unchanged transfer.
* The `k ≤ 2` path imports no `Certificate/` module (checked with `grep` on the imports of
  `Finite/`, `Moments/`, `Conditional/`, `Transfer.lean`).

### M5 gate evidence (2026-09-27)

```text
lake build                     Build completed successfully (8609 jobs); 0 warnings
#print axioms EvenCycleApex.commonality_two_apices
  'EvenCycleApex.commonality_two_apices' depends on axioms: [propext, Classical.choice, Quot.sound]
lake env lean CheckAxioms.lean 68 declarations, all [propext, Classical.choice, Quot.sound]
forbidden-token scan: none
```

## 2026-09-27 — M6 (certificate language and soundness)

Files `lean/EvenCycleApex/Certificate/{Mask,Rooted,Accum,LDL,Checker,Targets,Schema,Sound}.lean`;
generator `tools/gen_cert_data.py` (so far: `schema`).

**Soundness chain** (`cert_sound`, restated on natural-number totals as `cert_sound_of_totals`):

1. *Masks* (`Mask.lean`): `maskEdges g` = the sorted pairs at the set bits; `maskEdges_lor`;
   `relabel g code` (kernel primitives, permutation in 3-bit fields) with `maskEdges_relabel` and
   `evalMask_relabel` (`lem:normalform-soundness` for one mask).
2. *Rooted splitting* (`Rooted.lean`): `edgeDensity_rooted_split` on `Fin (r + (k + (k + p)))`
   (roots, first copy, second copy, padding summing to one); `evalMask_skeleton` reads a six-vertex
   skeleton `h ∪ F_a ∪ σF_b` there through `Fin.cast` and pull-backs (`pull`); the second copy is the
   relabelling by the block swap `σ`, checked by `swapOK`.
3. *Root types*: the checker enumerates the submasks of the root mask (`subMasks`, bit recursion);
   `prod_one_add_subMasks` expands `∏_{e ∈ R} (1 + f_e)` over them, `sgnGo_eq` gives the sign
   `(−1)^{|h ∖ t|}`, `typeFactor_expand` assembles `∑_h (−1)^{|h∖t|} ∏_h U = ∏_{e∈R} (1 ± U_e)`
   (`= 2^{C(r,2)} p_t`; the blueprint's normalization `2^{6−C(r,2)}` is carried as the group weight).
   `block_nonneg`: `∑_{a,b} A_ab ∑_h (−1)^{|h∖t|} t(h ∪ F_a ∪ σF_b) = ∑_z ∏w · ∏(1 ± U) · Φᵀ A Φ ≥ 0`
   for positive semidefinite `A`.
4. *LDLᵀ* (`LDL.lean`): `factorOK` (core `Rat`/`mkRat`, lockstep `all2`) checks `δ > 0` and every
   entry of `L diag(δ) Lᵀ`; `factorOK_sound` proves positive semidefiniteness (`xᵀAx = ∑ δ (Lᵀx)²`),
   which is all that is used (definiteness is not needed).
5. *Packed accumulators* (`Accum.lean`): `accStep` (forced), `accList_eq` (closed form `posOf`,
   `negOf`, `massOf`), `digits_zero` (base-`B` digits are unique when `|D_o| < B`),
   `list_sum_eq_of_packed`: equal packed values and total mass `< 2^128` ⇒ equal orbit-wise sums
   ⇒ equal `∑ c · f(o)` for every `f`.  No bound on the number of orbits is needed (any finite list),
   and the orbit representatives can be any function `rep` — only `evalMask K (rep o)` is used.
6. *Checker* (`Checker.lean`): a `GroupCert` = schema + witnesses `W a b` (per skeleton, in
   `subMasks` order) + matrices merged entrywise `M a b = [A⁽ʲ⁾_ab]ⱼ` + LDL data.  `GroupCert.valid`
   (schema checks, `witRow` for every row, `ldlOK` for every block) ⇒ `itemSum_nonneg`.  The kernel
   loops `accT`/`accCols`/`accRows` (CPS, forced) and `accTarget` equal `accList` of the item lists
   (`accRows_eq`, `accTarget_eq`), so chunk results can be checked against literals (`claimOK`,
   `accRows_claim`, `accTarget_claim`, `itemsRows_add`).
7. *Targets* (`Targets.lean`): built from the literal edge lists `E_s`, `B_s` and the masks of
   `def:certificate-targets` (`parityPoly` by dense submask enumeration, `polyScale`, `polyMul`,
   `mono`).  Cross-check: `#eval` of the three Lean targets, merged by mask, equals
   `independent_audit.targets()` exactly (992, 6150, 6151 nonzero monomials; 1056, 6349, 6349 listed).
8. *Schema* (`Schema.lean`, generated): five groups `r = 0, …, 4`, `schemas_ok` and `schema_dims`
   (`[3, 5, 19, 19, 7 × 4, 15 × 11]`) by `decide`.

Design notes.  (i) Polynomials are monomial lists, duplicates allowed; nothing needs a vector in
`ℚ^Mask`.  (ii) The group weights `2^{6−C(r,2)}` and the target scale `64𝒟` enter only the final
natural-number comparison (`cert_sound_of_totals`), so accumulations use the raw integer entries.
(iii) The M0 data files `Certificate/Data/{Matrices,LDL}_*.lean` are in per-block layout and
`Data/Perm.lean` is the superseded global table; M7 regenerates the data in the `GroupCert` layout
and removes `Perm.lean`.

### M6 gate evidence (2026-09-27)

```text
lake build                     Build completed successfully (8617 jobs); 0 warnings
lake env lean CheckAxioms.lean 91 declarations; 86 print exactly [propext, Classical.choice, Quot.sound]
  (one of them wrapped over three lines), 5 a strict subset (accList_eq, schemas_ok: [propext];
  accRows_eq, accTarget_eq: [propext, Quot.sound]; schema_dims: none) — including cert_sound, cert_sound_of_totals,
  meanThree_nonneg_of_checks, negMajority_nonneg_of_checks, posMajority_nonneg_of_checks,
  block_nonneg, factorOK_sound, list_sum_eq_of_packed, evalMask_skeleton
forbidden-token scan (sorry, admit, native_decide, decide +native, ofReduceBool, axiom): none
targets vs independent_audit.targets(): equal (mean_three 992, negative_majority 6150,
  positive_majority 6151 merged monomials)
```

## 2026-09-27 — M7 (kernel-checked certificates)

Generator `tools/gen_cert_data.py` (`schema`, `data`, `checks`); data
`lean/EvenCycleApex/Certificate/Data/{Witnesses,Target_MeanThree,Target_Neg,Target_Pos}.lean`; group
certificates `Certificate/Groups.lean`; kernel checks `Certificate/Checks/{Witness,MeanThree,Neg,Pos}.lean`;
headline `Certificate/Main.lean`.  The M0 files `Data/{Matrices,LDL}_*.lean`, `Data/Perm.lean` and the old
generator `tools/gen_lean_data.py` were removed (superseded by the `GroupCert` layout, X3).

* **Data.**  Skeleton witnesses `W{r} a b` (orbit id + 256 · permutation code) in `subMasks` order,
  shared by the targets; per target, the matrices of each group merged entrywise, the `LDLᵀ` data per
  block, the target witnesses in chunks of 1024, and the expected packed totals (`claim{r}_{a}`,
  `claimT_{k}`).  The generator rebuilds every list in the order of the Lean definitions and checks
  the whole identity in Python before writing (`SCALE · T = ∑ weight · groups`, mass `< 2^98`).  Cross
  checks: the raw Lean target lists (`#eval`) equal the generator's lists element by element.
* **Checks** (`decide +kernel` only).  `wit0` … `wit4`: all 15,548 skeleton witnesses.  Per target:
  `*_ldl0..4` (19 factorizations), `*_acc*` (group accumulations against literal totals; `r = 4` in
  row ranges `[0,5)`, `[5,10)`, `[10,15)`), `*_t*` (target chunks: witnesses and totals in one theorem,
  `tchunk`), `*_end` (the chunks cover the target), `*_fin` (`totalsOK`: `64𝒟 · target = ∑ 2^{6−C(r,2)}
  · groups` as packed naturals, total mass `< 2^128`).  Assembled by `cert_sound_of_chunks` into
  `meanThree_nonneg`, `negMajority_nonneg`, `posMajority_nonneg`, and `three_universal_graph_inequalities`.
* **Kernel memory.**  Relabelling checks cost ≈ 0.3–0.5 MB each in the kernel cache (per declaration):
  the unchunked `P₋` witness theorem (6,349 monomials) peaked at 6.4 GB (import baseline 3.1 GB).  Hence
  the target chunks (`tchunk`, `target_chunks`, `cert_sound_of_chunks` in `Sound.lean`) and the import
  chain `Checks/MeanThree → Neg → Pos` so that `lake build` never evaluates two target files at once.
  Measured peak for the whole chain: 5.6 GB (sum over all Lean processes).
* **Timings** (single-threaded `lake env lean --threads=1`, wall, including ≈ 22 s of imports):
  `Witness` 60 s, `MeanThree` 69 s, `Neg` 118 s, `Pos` 118 s.

### M7 gate evidence (2026-09-27)

```text
lake build                     Build completed successfully (8620 jobs); 0 warnings
#print axioms EvenCycleApex.three_universal_graph_inequalities
  depends on axioms: [propext, Classical.choice, Quot.sound]
lake env lean CheckAxioms.lean 104 declarations: 94 print exactly [propext, Classical.choice, Quot.sound]
  (one wrapped), the other 10 a strict subset (the 5 of M6, and the kernel-check theorems
  Checks.meanThree_acc4_10, meanThree_t1, meanThree_fin, neg_t6, pos_t6: [propext]);
  no Lean.ofReduceBool, no sorryAx
forbidden-token scan (sorry, admit, native_decide, decide +native, ofReduceBool, axiom): none
```
