# Atlas168 compact verification record

Atlas168 is **verified** (2026-09-22). The fresh **97-file** build passed in **44m34s** (2673.719 seconds), at **11.84 GiB** peak process-tree private memory. The installed-source recheck brings combined verification to **44m42s** (2682.204 seconds).
All source hashes remained unchanged. The final theorem has only the three
standard axioms. Its catalogue example and classification are updated;
Atlas151 is next.

The fresh run includes both interval pieces, chromatic counts, graph
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

- `verification_runs/atlas168/fresh_row_1/manifest.json` and `summary.json`.
- `verification_runs/atlas168/fresh_row_1/catalogue_compile.log`.
- `verification_runs/atlas168/installed_example_1.json` and `.log`.
- `verification_runs/atlas168/completed_row.json`.

Separate discovery and arithmetic audit records are `lower_face_discovery_1`,
`upper_face_discovery_1`, `lower_independent_audit_1`, and
`upper_independent_audit_1`. Development runs and any unsuccessful fresh
attempts remain separate from the accepted measurement.

See [the certificate explanation](../../notes/atlas168_compact_certificate.md).
