# Low-rank certificate investigation — C13 L2/L3 (conclusion)

**Date:** 2026-06-23. **Verdict:** low-rank SDP rationalization is a dead end for the
Lean certificate. Recorded so it is not re-attempted.

## Question
The C13 defect pieces L2 (bivariate, degree-8 kernel, `sos2var5`) and L3 (trivariate,
degree-6, `sos3var4`) overflow Lean's `ring`/heartbeat budget. The margin-maximizing SDP
produces **full-rank** Grams → ~95 squares for L2. Could a rank-minimizing solve cut the
square count enough to fit?

## What was measured (`lowrank_proto.py`, C13 L2, Nb=5)
| solve | Gram ranks | total squares |
|---|---|---|
| margin-max (current pipeline) | [35,20,20,20] | 95 |
| trace-min | [9,3,2,4] | 18 |
| reweighted trace-min (log-det surrogate) | [9,1,2,2] | **14** |

So the certificate's **intrinsic rank is ~14** — a 6.8× reduction, *numerically*.

## Why it does not translate to a rational Lean certificate
Low-rank PSD matrices sit on the **boundary** of the PSD cone. Entrywise rational rounding
of the trace-min solution was tested at denominators up to 65536: **every block fails to
stay PSD, including the rank-1 block** (rounding `vvᵀ` breaks the `vᵢvⱼ` vs `vᵢ²` relations).
The minimal-rank face is a generic irrational rotation — confirmed to have no axis-aligned
structure (energy spread over all 35 monomials; no monomial droppable) and no rational points.

This is the **Peyrl–Parrilo tension**: exact rational SOS certification requires an *interior*
(full-rank) point of the spectrahedron, which is precisely why the standard pipeline maximizes
margin. Rational ⟹ ~full rank of the basis.

## Rational-robust levers also exhausted
- **Newton-polytope reduction:** basis is already Newton-minimal (no monomials prunable).
- **Symmetry (l↔m):** block-diagonalizes the Grams but preserves total rank → no square-count win.

## Recalibration (what actually builds)
| block | squares | engine | built? |
|---|---|---|---|
| C11 L2 | 50 | sos2var4 | ✅ |
| C11 L3 | 70 | sos3var3 | ✅ |
| C13 L2 | 95 | sos2var5 | ✗ timed out |

Lean budget is ~50–70 squares/block. C13 L2's 95 is only ~1.4× over; the timeout is driven by
**squares × per-square form size** (sos2var5 expands to ~81 moment terms/square vs sos2var4's
smaller forms), not the rank. A valid **rational 95-square cert was generated** and exact-match
verified (`cert13_L2.txt`, D=16); the only blocker is Lean `ring` performance.

## Remaining viable directions (not pursued yet)
1. **Bespoke Hankel/Cauchy–Schwarz certificates** for L2/L3 — using `s_{i+j}² ≤ s_{2i}s_{2j}`
   and `(q-poly ≥ 0)·(moment power)` as building blocks (the C11 L4/L5 hand style). Plausibly
   ~10–20 *rational* squares. Bespoke math per piece, not a generic pipeline.
2. **Brute-force the existing 95-square cert** with Lean assembly tuning (chunk=1, lighter
   combiner rings, higher heartbeats).

`lowrank_proto.py` is kept as the reproducible diagnostic.
