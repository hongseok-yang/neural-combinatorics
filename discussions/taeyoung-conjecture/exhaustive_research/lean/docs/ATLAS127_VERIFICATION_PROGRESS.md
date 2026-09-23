# Atlas127 compact verification record

Atlas127 is **verified** (2026-09-23). The fresh **97-file** build passed in **43m30s** (2609.641 seconds), at **11.90 GiB** peak process-tree private memory. The installed-source recheck brings combined verification to **43m37s** (2617.469 seconds).
All source hashes remained unchanged. The final theorem has only the three
standard axioms. Its catalogue example and classification are updated;
no believed row remains.

The fresh run includes both interval bounds, chromatic counts, graph
identification, complete `SatisfiesLowerBound` theorem, and catalogue example.
Row artifacts were absent at the start. Compilation was sequential with
`LEAN_NUM_THREADS=1`, Lean `-M 12288 -j 1`, a 16 GiB process-tree watchdog,
and one 3,600-second deadline for all 97 row files.

- **Lower** interval `[1/2,2/3]`: 47 files; `p=(3+1*s)/6`, common denominator `186624000000000000` and interpolation scale `7776`. The ten integer positive factors have orders `57, 101, 65, 60, 12, 32, 52, 34, 30, 6`.
- **Upper** interval `[2/3,1]`: 47 files; `p=(2+1*s)/3`, common denominator `23328000000000000` and interpolation scale `243`. The ten integer positive factors have orders `50, 98, 62, 60, 12, 23, 48, 30, 30, 6`.

The row uses 250 prebuilt shared project modules.
The reusable affine interval coefficient lemma is recorded in
`verification_runs/atlas147/shared_affine_1/summary.json` (8.875 seconds,
4.83 GiB peak private memory). Earlier compact common component costs are in
`verification_runs/atlas118/shared_components.json`: 57 modules, 2,884.982
seconds summed compilation, 12.32 GiB peak. These are successful, source-matching
component measurements, not fresh builds of the complete shared closure.
Older project dependencies and Mathlib are prebuilt. No row-specific
certificate data have been moved into the shared accounting.

Accepted records:

- `verification_runs/atlas127/fresh_row_1/manifest.json` and `summary.json`.
- `verification_runs/atlas127/fresh_row_1/catalogue_compile.log`.
- `verification_runs/atlas127/installed_example_1.json` and `.log`.
- `verification_runs/atlas127/completed_row.json`.

Separate discovery and arithmetic audit records are `lower_face_discovery_1`, `upper_face_discovery_1`, `lower_independent_audit_1`, and `upper_independent_audit_1`.
Development runs and any unsuccessful fresh
attempts remain separate from the accepted measurement. The Lean development
run is `merged_block_pilot_1` (`Coloring` and the heaviest module
`Lower.Block01`, 392.1 seconds, 11.88 GiB peak). The interval, contraction and
right modules were not piloted separately: every generated module of this row
is within two per cent of Atlas151's, whose accepted run took 2,755 seconds.

## This row does not use the smoothed Goodman theorem

The accepted mathematics for Atlas 127 was the smoothed Goodman theorem,
`t(theta_{1,2,4},W) >= (2p-1) t(C_5,W)`, whose certificate is a ground-8
multiplier flag SOS: 184 PSD blocks, orders up to 272, 1,431,052 integer
entries and 12,346 per-graph inequalities. That certificate was measured
against this envelope and does not fit. A synthetic block at its largest order
was compiled to check: order 102 passes (134 seconds, 6.54 GiB for the data
module alone), while order 272 exhausts the 16 GiB watchdog after 2,259
seconds on the data module, before any proof obligation is attempted. The
whole route projects at roughly 800 to 1,200 files and 25 to 40 hours.

The catalogue bound proved here is weaker than that theorem and needs none of
it. `Phi_127(p) = p (2p-1)^2 (2p^2-2p+1)` is certified directly in the same
ground-6 four-root cone as the other compact rows, at the usual cost. The
smoothed Goodman theorem remains a true and stronger statement about this
graph, and remains unformalized.

The single interval `[1/2,1]` does not work: its maximum block margin is zero,
so every feasible Gram is singular and the rationalizer, which takes a Cholesky
factor, cannot round it. `sdp_faces_1` (CLARABEL, 82.6 seconds) reports margin
-6.9e-08 and `sdp_faces_2` (SCS at 1e-9, 988.6 seconds) reports +3.5e-08, with
block ranks collapsing to 32 of 50 and 59 of 98. Splitting at `2/3` removes the
degeneracy entirely: `sdp_lower_clarabel_1` (210.7 seconds) reaches margin
2.24e-05 and `sdp_upper_clarabel_1` (122.8 seconds) reaches 1.47e-04, both at
full rank in every block. This is not the second-order tangency of `Phi_127` at
`p = 1/2`; Atlas 151 has the same `(2p-1)^2` factor and rationalizes on
`[1/2,2/3]` without trouble.

The exact certificates are `experiments/atlas127_exact_lower_interval_sos.json`
and `atlas127_exact_upper_interval_sos.json`, from `rationalize_lower_1` and
`rationalize_upper_1` (32.1 and 30.2 seconds), with smallest exact
diagonal-dominance margins 0.99585 and 0.99972. The Turan faces are
`turan_faces_1` (3.3 seconds).

See [the certificate explanation](../../notes/atlas127_compact_certificate.md).
