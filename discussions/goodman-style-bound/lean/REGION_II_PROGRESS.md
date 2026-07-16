# Region II Lean Formalization Progress

| Milestone | Status | Short description |
|---|:---:|---|
| 0. Blueprint and provenance | ✅ | The authoritative blueprint, corrected July 12b sources, checksum metadata, and deterministic certificate emitters are present. |
| 1. Centered spectral foundation | ✅ | Centered-operator identification, compact self-adjoint spectrum, trace powers, finite Krylov moments, and the sharp Hilbert--Schmidt budget compile. |
| 2. One-sided spectral shift | ✅ | The finite block-power identity, formal resolvent/logarithm bridge, arbitrary-graphon shift identity, nonnegativity, and linear lower bound compile. |
| 3. Frontier and Huber reductions | ✅ | No-frontier, unique frontier, forced variance, ceilings, master defect, direct/safe coupling, exact Huber formulas, and the corrected `K = 0` branch compile. |
| 4. Scalar zones | ✅ | The coordinate chart, Zones A/B/C, moderate-Zone-C correction, Turán corner, overlap handling, and scalar Huber assembly compile. |
| 5. Verified certificates | ✅ | Sound exact rational interval/tree and multivariate Bernstein checkers compile; Lean verifies the Zone B, Zone C, and C13 payloads. |
| 6. `C13` frontier | ✅ | The density-independent path identity, frontier-plus-Krylov split, safe support `[-1/2, 7/50]`, exact moment-defect positivity, and unconditional `C13_frontier_bound` compile. |
| 7. Public assembly | ✅ | The theorem-only `Main.lean` facade follows the requested naming convention. Assembly is complete; `odd_cycle_regionII_conditional_bound` explicitly retains the external triangle-density hypothesis. |
| 8. Final verification | ✅ | The full library builds; Python regressions, deterministic payload/hash checks, endpoint audit, placeholder scan, and the four-theorem axiom report all pass. |

## Emoji legend

- ✅ **Proven:** implemented and compiled in Lean.
- 🚧 **Work in progress:** substantial implementation exists, but the milestone is not complete.
- ⬜ **Yet to be handled:** required implementation or verification has not started or still wholly remains.
- 🟨 **Conditional:** the Lean statement is proved only through an explicitly assumed external interface or awaits machinery intentionally kept out of scope.

Milestone 7 is ✅ because the public assembly itself is complete. The final
all-odd theorem is nevertheless a conditional mathematical statement because
formalizing the Razborov--Reiher triangle theorem remains outside this
blueprint; its public statement assumes `TriangleDensityLowerBoundUpTo
(103 / 200)`.

## Authoritative plan

The development contract is
[REGION_II_LEAN_BLUEPRINT.md](REGION_II_LEAN_BLUEPRINT.md). This dashboard
reports current state and does not replace or revise that blueprint.

## Compiled headline components

- `OddCycleBound.RegionII.Scalar.Assembly`
  proves `AdmissibleParams.scalar_huber_bound` for every admissible odd
  exponent at least `15`.
- `OddCycleBound.RegionII.C13FrontierAtoms`
  gives the exact frontier-plus-Krylov moment representation, nonnegative
  weights, universal half-interval support, and certified safe support.
- `OddCycleBound.RegionII.C13MomentPositivity`
  lifts the exact C13 Bernstein certificates through the atomic measure and
  proves nonnegativity of the actual complemented graphon's C13 moment defect.
- `OddCycleBound.RegionII.Certificate.ZoneBVerified` and
  `OddCycleBound.RegionII.Certificate.ZoneCVerified`
  check the deterministic rational certificate trees inside Lean.
- `OddCycleBound.RegionII.Certificate.C13BernsteinSound`
  checks the exact frontier and full-support Bernstein certificates and
  exposes their range-facing positivity theorems.

## Public assembly

- `C3_bound`, `C5_bound`, and `C7_bound` are unconditional at every
  density.
- `C9_path_bound` and `C11_path_bound` expose their unconditional partial
  ranges.
- `C13_path_bound` is unconditional on the combined range
  `51/100 <= p`; it joins the certified frontier and high-density path
  proofs at `519/1000`.
- `C9_conditional_bound`, `C11_conditional_bound`, and
  `C13_conditional_bound` are all-density theorems under the indicated
  triangle-density interface. `C13_path_conditional_bound` exposes its
  partial conditional branch separately.
- `odd_cycle_regionII_large_bound` is unconditional for odd `m >= 15`
  and `1/2 < p < 2/3`.
- `odd_cycle_regionII_conditional_bound` dispatches every odd `m >= 3`
  in Region II and assumes only
  `TriangleDensityLowerBoundUpTo (103 / 200)`.
- `OddCycleBound.lean` exports `OddCycleBound.Main` directly.

## Verified certificate facts

Lean checks deterministic payloads matching the corrected July 12b runs:

- Zone B: 23 verified boxes, 3 skipped boxes, maximum depth 8.
- Zone C: 2997 verified boxes, 5 bottom-out leaves, 87 skipped boxes,
  maximum depth 28, maximum checked `m = 1716`.
- C13: exact rational Bernstein certificates for the linear safe/frontier,
  quadratic safe/frontier combinations, and full-support kernels of orders
  three through six.

Python is used only as an independent deterministic emitter/regression check;
all certificate soundness implications used by the mathematics are Lean
theorems.

## Final verification results

- `lake build OddCycleBound` succeeds with the pinned Lean 4.31.0
  toolchain and Mathlib.
- The corrected Python certifiers reproduce Zone B
  `23/3/depth 8` and Zone C `2997/5/87/depth 28/max m 1716`.
- Regenerating both Lean certificate payloads is byte-for-byte deterministic;
  all eight vendored files present in the upstream manifest pass SHA-256.
- The scalar assembly checks the closed boundaries `ξ = 1` and
  `e = 1/60`; the corrected `K = 0` branch, frontier ceiling, Turán
  split, skips, and bottom-out leaves occur in compiled proof paths.
- The source scan finds no `sorry`, `admit`, project `axiom`, `opaque`,
  or unsafe theorem. See [REGION_II_AXIOM_REPORT.md](REGION_II_AXIOM_REPORT.md).

Last updated: 2026-07-16.
