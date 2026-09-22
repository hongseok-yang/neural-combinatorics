# Atlas174 compact verification record

Atlas174 is **verified** (2026-09-23). The fresh **98-file** build passed in **40m52s** (2451.969 seconds), at **11.91 GiB** peak process-tree private memory. The installed-source recheck brings combined verification to **41m00s** (2459.782 seconds).
All source hashes remained unchanged. The final theorem has only the three
standard axioms. Its catalogue example and classification are updated;
Atlas153 is next.

The fresh run includes all three interval bounds, chromatic counts, graph
identification, complete `SatisfiesLowerBound` theorem, and catalogue example.
Row artifacts were absent at the start. Compilation was sequential with
`LEAN_NUM_THREADS=1`, Lean `-M 12288 -j 1`, a 16 GiB process-tree watchdog,
and one 3,600-second deadline for all 98 row files.

- **Low** interval `[1/2,7/12]`: one hand-written file; the catalogue target is nonpositive there, so the bound is the nonnegativity of the homomorphism density. No certificate data.
- **Middle** interval `[7/12,2/3]`: 47 files; `p=(7+1*s)/12`, common denominator `33094220544000000000000` and interpolation scale `248832`. The ten integer positive factors have orders `60, 102, 66, 60, 12, 32, 52, 34, 30, 6`.
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

- `verification_runs/atlas174/fresh_row_1/manifest.json` and `summary.json`.
- `verification_runs/atlas174/fresh_row_1/catalogue_compile.log`.
- `verification_runs/atlas174/installed_example_1.json` and `.log`.
- `verification_runs/atlas174/completed_row.json`.

Separate discovery and arithmetic audit records are `middle_face_discovery_1`, `upper_face_discovery_1`, `middle_independent_audit_1`, and `upper_independent_audit_1`.
Development runs and any unsuccessful fresh
attempts remain separate from the accepted measurement. The development runs
here are `low_module_1` (`Coloring` and the hand-written `Low.lean`, 32.7
seconds, of which `Low.lean` took 7.6) and `merged_block_pilot_1` (the heaviest
module `Middle.Block01` alone, 309.4 seconds at 11.86 GiB). The interval,
contraction and right modules were not piloted separately: they are within a
few hundred bytes of Atlas188's, measured earlier the same day in
`verification_runs/atlas188/interval_components_1` and in that row's accepted
run. Those figures projected this row at about 2,560 seconds, against the
2,451.969 measured.

This row's middle certificate came from the weakest source interval SOS of the
family, whose smallest diagonal-dominance margin is 0.8831. Exact face
rationalization nevertheless produced relative margins above 0.999998 on all
ten blocks, so no alternative rounding denominator or pivot method was needed.
Its common denominator, 23 digits, is the longest of the compact rows so far.

See [the certificate explanation](../../notes/atlas174_compact_certificate.md).
