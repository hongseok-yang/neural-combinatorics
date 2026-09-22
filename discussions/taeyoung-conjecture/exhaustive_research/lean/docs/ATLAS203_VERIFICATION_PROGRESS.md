# Atlas203 compact verification record

Atlas203 is **verified** (2026-09-22). The fresh **100-file** build passed in **37m20s** (2239.532 seconds), at **9.26 GiB** peak process-tree private memory. The installed-source recheck brings combined verification to **37m28s** (2247.782 seconds).
All source hashes remained unchanged. The final theorem has only the three
standard axioms. Its live catalogue example and classification are updated;
Atlas147 is next.

The fresh run includes both `[2/3,3/4]` and `[3/4,1]`, the chromatic target,
graph identification, complete `SatisfiesLowerBound` theorem, and catalogue
example. Row artifacts were absent at the start. Compilation was sequential,
with `LEAN_NUM_THREADS=1`, Lean `-M 12288 -j 1`, a 16 GiB process-tree watchdog,
and one 3,600-second deadline for all 100 row files.

The row has 17,757,402 source bytes and uses
388 prebuilt shared project modules. The two new
reusable interval lemmas took 16.719 seconds summed compilation, at
4.82 GiB peak private memory; see
`verification_runs/atlas203/shared_intervals_1/summary.json`.

Earlier common component costs are recorded in
`verification_runs/atlas130/induced_shared_components.json` (138 modules,
2,438.453 seconds summed compilation, 11.70 GiB peak) and
`verification_runs/atlas118/shared_components.json` (57 modules,
2,884.982 seconds, 12.32 GiB peak). These are successful, source-matching
component measurements, not fresh builds of the complete shared closure.
Older common modules and Mathlib are prebuilt. No Atlas203-specific certificate
data are moved into that shared accounting.

Accepted records:

- `verification_runs/atlas203/fresh_row_1/manifest.json` and `summary.json`.
- `verification_runs/atlas203/fresh_row_1/catalogue_compile.log`.
- `verification_runs/atlas203/installed_example_1.json` and `.log`.
- `verification_runs/atlas203/completed_row.json`.

The separate discovery/audit reports are `induced_independent_audit_1`,
`lower_compact_export_1`, `upper_face_discovery_2`, and
`upper_independent_audit_1` under `verification_runs/atlas203/`.
The first upper discovery attempt only supplied an incorrect input filename.
Development component runs are retained separately from acceptance.

See [the certificate explanation](../../notes/atlas203_compact_certificate.md).
