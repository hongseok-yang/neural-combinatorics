# Atlas130 compact verification record

Atlas130 is **verified** (2026-09-22). The fresh **100-file** build passed in **34m30s** (2069.860 seconds), with **9.21 GiB** peak process-tree private memory. The installed-source recheck brings combined verification to **34m38s** (2078.110 seconds).
The complete catalogue theorem has only the three standard axioms. All source
hashes remained unchanged during verification. The live example and
classification are updated; Atlas203 is next.

The fresh build covers both `[1/2,2/3]` and `[2/3,1]`, the chromatic target,
graph identification, complete `SatisfiesLowerBound` theorem, and catalogue
example. It includes all 100 row files (15,717,794 bytes).
Row artifacts were absent at the start. Compilation was sequential, with
`LEAN_NUM_THREADS=1`, Lean `-M 12288 -j 1`, a 16 GiB process-tree watchdog,
and one 3,600-second deadline for the entire row.

## Shared infrastructure

The row uses 387 prebuilt shared project modules.
The 138 new induced/interpolation modules have successful,
source-matching component measurements totaling
2438.453 seconds
(40m38s), with
11.70 GiB peak private memory. Their total
source size is 7,490,648 bytes. These are component
measurements, **not** a fresh build of the complete shared closure.
See `verification_runs/atlas130/induced_shared_components.json` for each
source hash and originating run.

The previously recorded 57 compact shared modules took 2,884.982 seconds
summed across successful component runs, with a 12.32 GiB peak; see
`verification_runs/atlas118/shared_components.json`. Older shared modules
and Mathlib are prebuilt. No row-specific certificate data are charged to
the shared infrastructure.

## Records

- `verification_runs/atlas130/fresh_row_1/manifest.json`: complete source closure and hashes.
- `verification_runs/atlas130/fresh_row_1/summary.json`: fresh row acceptance.
- `verification_runs/atlas130/fresh_row_1/catalogue_compile.log`: complete theorem axiom audit.
- `verification_runs/atlas130/installed_example_1.json` and `.log`: installed-source recheck.
- `verification_runs/atlas130/completed_row.json`: acceptance summary.
- `verification_runs/atlas130/induced_independent_audit_1.json`: original induced audit.
- `verification_runs/atlas130/lower_compact_export_2.json`: integer conversion and completion-count audit.
- `verification_runs/atlas130/upper_independent_audit_1.json`: independent upper-piece audit.

Development failures and successful component runs are retained separately.
See [the certificate explanation](../../notes/atlas130_compact_certificate.md).
