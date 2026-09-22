# Atlas122 compact verification progress

Atlas122 is **verified**, following Atlas126 and Atlas118. The fresh build
passed on 2026-09-22 and the catalogue example and classification are updated.
Atlas124 is now the active row.

The complete fresh verification took **1,543.829 seconds (25 minutes
44 seconds)**, with **9,757,290,496 bytes (9.09 GiB)** peak process-tree private
memory. All 89 row files were rebuilt sequentially against prebuilt common
dependencies. The installed-source recheck took 8.047 seconds, so combined
verification took **1,551.876 seconds (25 minutes 52 seconds)**. All source
hashes stayed unchanged, and the final catalogue theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`.

The new exact certificate has a 17-digit common Gram denominator,
`10368000000000000`. Discovery took 11.563 seconds and the independent exact
audit took 9.516 seconds. All 407 coefficient equations and ten integer
positivity witnesses passed the external audit. These are discovery checks,
not Lean acceptance.

The fresh sequential build is `verification_runs/atlas122/fresh_row_1`.
Its manifest contains 89 row files, including the final catalogue example,
and 249 prebuilt shared project modules. Row source size is 9,083,136 bytes.
The shared dependency order and source hashes match Atlas118 exactly; no
additional common compilation is required. The earlier shared component
measurements remain in `verification_runs/atlas118/shared_components.json`:
57 new reusable modules totaling 48 minutes 5 seconds across successful
component runs, with a 12.32 GiB peak. This is not a fresh build measurement
of all 249 shared modules.

The complete graphon theorem, catalogue conversion, and standard-axiom audit
passed. The driver enforced the one-hour aggregate deadline and 16 GiB
process-tree memory limit, with one Lean compiler and one compiler thread at
a time. No proof-source repairs were required during this fresh run.

The accepted reports are `verification_runs/atlas122/fresh_row_1/summary.json`,
`verification_runs/atlas122/installed_example_1.json`, and
`verification_runs/atlas122/completed_row.json`. The manifest records the
complete row and common dependency closure and all source hashes.

See [the certificate explanation](../../notes/atlas122_compact_certificate.md).
