# Atlas124 compact verification progress

Atlas124 is **verified**, following Atlas126, Atlas118, and Atlas122. The
fresh build passed on 2026-09-22 and the catalogue example and classification
are updated. Atlas181 is now the active row.

The complete fresh verification took **1,541.437 seconds (25 minutes
41 seconds)**, with **9,756,794,880 bytes (9.09 GiB)** peak process-tree private
memory. All 89 row files were rebuilt sequentially against prebuilt common
dependencies. The installed-source recheck took 8.265 seconds, giving
**1,549.702 seconds (25 minutes 50 seconds)** combined verification. All source
hashes stayed unchanged. The final catalogue theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`.

The new integer certificate has common Gram denominator
`10368000000000000`. Discovery took 10.953 seconds and the independent exact
audit took 9.296 seconds. The audit passed all 407 coefficient equations and
ten positivity witnesses; these external checks are not Lean acceptance.

The fresh run is `verification_runs/atlas124/fresh_row_1`. Its manifest records
89 row files (9,174,205 source bytes) and 249 prebuilt shared project modules.
The shared closure and source hashes match Atlas118 exactly. No additional
common compilation was needed. The shared component accounting remains in
`verification_runs/atlas118/shared_components.json`: 57 reusable modules,
48 minutes 5 seconds summed across successful component runs, and 12.32 GiB
peak private memory. This does not measure a fresh rebuild of all 249 shared
modules.

The full graphon theorem, coloring and catalogue conversion, and standard
axiom audit passed. The driver enforced a one-hour whole-row deadline and
16 GiB process-tree memory limit, with one Lean compiler and one compiler
thread at a time. No proof-source repairs were needed during the fresh run.

The accepted reports are `verification_runs/atlas124/fresh_row_1/summary.json`,
`verification_runs/atlas124/installed_example_1.json`, and
`verification_runs/atlas124/completed_row.json`. The manifest records the
complete source closure and hashes.

See [the certificate explanation](../../notes/atlas124_compact_certificate.md).
