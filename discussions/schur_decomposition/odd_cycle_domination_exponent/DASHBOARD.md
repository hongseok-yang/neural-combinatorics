# Verification dashboard

This is the single live status dashboard for the graphon formalization described in
[`VERIFICATION_PLAN.md`](VERIFICATION_PLAN.md).

Status legend:

- ✅ complete: the milestone gate has passed;
- 🚧 under construction: active work has begun, but the gate has not passed;
- ❌ not complete: work has not begun or the gate is currently unmet.

Hardness is an engineering estimate for an axiom-free Lean proof, not a statement about the length
of the paper argument.

Last updated: 2026-08-22

| Milestone | Verification deliverable | Status | Hardness | Gate/evidence |
|---|---|:---:|:---:|---|
| M0 | Scope, graphon target, proof architecture, and audit standard fixed | ✅ | Easy | `VERIFICATION_PLAN.md` written; awaiting only requested revisions |
| M1 | Lean scaffold and reuse of the audited `CycleCommonality` graphon foundation | ❌ | Medium | Clean smoke build using `IsGraphon`, `cycleDensity`, integral bridge, and step approximation |
| M2 | Finite probability, entropy, KL nonnegativity, and finite chain rule | ❌ | Very hard | Core KL declarations compile and pass `#print axioms` |
| M3 | Full Saglam same-parity matrix inequality, including zero cases and parity iteration | ❌ | Very hard | `Saglam.main` builds, matches the source statement, and is axiom-audited |
| M4 | Edge-rooted graphon kernels, deletion bounds, and gluing identities | ❌ | Hard | Rooted/unrooted and glued-cycle identities proved on arbitrary probability spaces |
| M5 | Weighted step interpolation, arbitrary-graphon interpolation, and the `b = 2` edge anchor | ❌ | Hard | Exact anchor constraint used by domination is exported and audited |
| M6 | Weighted step-graphon pruning with retained cycle mass and uniform rooted richness | ❌ | Very hard | Explicit pruning theorem proved with no black-box BRRW assumption |
| M7 | Rooted gluing plus the weighted even-cycle lower bound | ❌ | Hard | Inequality `y >= K/L * a * p^(2*delta+1)` obtained |
| M8 | Algebraic elimination of edge density and preliminary polylogarithmic domination | ❌ | Medium | Integer-power theorem `y^E >= K * L^(-B) * a^F` builds |
| M9 | Graphon tensor powers, density multiplicativity, and removal of logarithmic loss | ❌ | Hard | Exact domination inequality proved for every step graphon |
| M10 | `L1` transfer from step graphons to arbitrary graphons | ❌ | Hard | Integer-power and integral-form theorems proved on arbitrary probability spaces |
| M11 | `Real.rpow` form and optional graphon domination-exponent wrapper | ❌ | Medium | Final exponent matches Theorem 1.4 symbolically |
| M12 | Clean build, full axiom audit, theorem map, and final documentation | ❌ | Medium | All completion criteria in the plan pass |

Overall: **1 / 13 milestones complete**.

