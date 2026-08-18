# Region II Axiom Report

Generated on 2026-07-16 with Lean 4.31.0 and the Mathlib revision pinned by
this project.  The reproducible command is:

```text
lake env lean CheckRegionII.lean
```

The report covers:

- `OddCycleBound.RegionII.Scalar.AdmissibleParams.scalar_huber_bound`
- `OddCycleBound.RegionII.regionII_large_odd_bound`
- `OddCycleBound.RegionII.C13_frontier_bound`
- `OddCycleBound.C3_bound`
- `OddCycleBound.C5_bound`
- `OddCycleBound.C7_bound`
- `OddCycleBound.C9_path_bound`
- `OddCycleBound.C11_path_bound`
- `OddCycleBound.C13_path_bound`
- `OddCycleBound.C9_conditional_bound`
- `OddCycleBound.C11_conditional_bound`
- `OddCycleBound.C13_path_conditional_bound`
- `OddCycleBound.C13_conditional_bound`
- `OddCycleBound.odd_cycle_regionII_large_bound`
- `OddCycleBound.odd_cycle_regionII_conditional_bound`

Every reported theorem depends only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`.  No theorem reports a native-evaluation
bridge or a project-declared mathematical axiom.

The Zone-B and C13 certificate propositions are proved with
`decide +kernel`.  The larger Zone-C tree is emitted as 341 bounded subtrees;
Lean kernel-checks each subtree independently and joins them with ordinary
proof terms.  This keeps the full result within a bounded-memory serial build
without extending the trusted base to native code generation.
A source scan of `OddCycleBound/RegionII` and the copied
`OddCycleBound/HighDensity` foundation found no `sorry`, `admit`,
`axiom`, `opaque`, or unsafe theorem declaration.
