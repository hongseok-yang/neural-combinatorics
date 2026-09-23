# Atlas188 compact verification record

Atlas188 is **verified** (2026-09-23). The fresh **98-file** build passed in **40m55s** (2454.734 seconds), at **11.90 GiB** peak process-tree private memory. The installed-source recheck brings combined verification to **41m03s** (2462.530 seconds).
All source hashes remained unchanged. The final theorem has only the three
standard axioms. Its catalogue example and classification are updated;
Atlas171 is next.

The fresh run includes all three interval bounds, chromatic counts, graph
identification, complete `SatisfiesLowerBound` theorem, and catalogue example.
Row artifacts were absent at the start. Compilation was sequential with
`LEAN_NUM_THREADS=1`, Lean `-M 12288 -j 1`, a 16 GiB process-tree watchdog,
and one 3,600-second deadline for all 98 row files.

- **Low** interval `[1/2,3/5]`: one hand-written file; the catalogue target is nonpositive there, so the bound is the nonnegativity of the homomorphism density. No certificate data.
- **Middle** interval `[3/5,2/3]`: 47 files; `p=(9+1*s)/15`, common denominator `2332800000000000000` and interpolation scale `759375`. The ten integer positive factors have orders `60, 102, 66, 60, 12, 32, 52, 34, 30, 6`.
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

- `verification_runs/atlas188/fresh_row_1/manifest.json` and `summary.json`.
- `verification_runs/atlas188/fresh_row_1/catalogue_compile.log`.
- `verification_runs/atlas188/installed_example_1.json` and `.log`.
- `verification_runs/atlas188/completed_row.json`.

Separate discovery and arithmetic audit records are `middle_face_discovery_1`, `upper_face_discovery_1`, `middle_independent_audit_1`, and `upper_independent_audit_1`.
Development runs and any unsuccessful fresh
attempts remain separate from the accepted measurement. The development runs
here are `low_module_1` (`Coloring` and the hand-written `Low.lean`, 31.5
seconds, of which `Low.lean` took 7.6), `merged_block_pilot_1` (the heaviest
module `Middle.Block01` alone, 306.4 seconds at 11.79 GiB) and
`interval_components_1` (the eighteen interval modules of both pieces, 197.0
seconds). Every module measured there ran faster than its Atlas151
counterpart, which projected the row at about 2,700 seconds before the
acceptance run was started.

See [the certificate explanation](../../notes/atlas188_compact_certificate.md).
