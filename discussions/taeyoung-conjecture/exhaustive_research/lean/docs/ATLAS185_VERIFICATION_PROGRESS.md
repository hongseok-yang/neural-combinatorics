# Atlas185 compact verification record

Atlas185 is **verified** (2026-09-22). The fresh 89-file build passed in **28m28s** (1708.375 seconds), with **9.23 GiB** peak process-tree private memory. The installed-source recheck passed too, bringing combined verification to **28m37s** (1716.640 seconds).
All source hashes remained unchanged throughout the fresh build. The final
catalogue theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.
The example and classification are updated; Atlas199 is next.

The full interval is `[2/3,1]`. The row contains 89 files and
10,005,837 source bytes. Every row file was rebuilt sequentially against
250 prebuilt common project modules. Lean used one thread and a 12 GiB
heap cap; the process-tree watchdog enforced 16 GiB and a 3,600-second
whole-row deadline. Row artifacts were absent at the start of the fresh run.

The integer certificate has common denominator `7776000000000000`.
Discovery took 11.562 seconds; the independent
exact audit took 9.281 seconds. Those external
discovery checks are separate from Lean acceptance.

Shared costs are accounted for separately. The 57 reusable compact modules
recorded in `verification_runs/atlas118/shared_components.json` took 48m05s
summed across successful component runs, with a 12.32 GiB peak. This is not
a fresh rebuild measurement of the complete common closure. Mathlib and
the older shared classification infrastructure are prebuilt.

Additional shared component reports:

- `lean/verification_runs/atlas181/shared_third_interval_1/summary.json`: 8.672 seconds summed compilation, 4.82 GiB peak private memory.

Accepted row records:

- `verification_runs/atlas185/fresh_row_1/summary.json` and `manifest.json`.
- `verification_runs/atlas185/installed_example_1.json` and its axiom log.
- `verification_runs/atlas185/completed_row.json`.

See [the certificate explanation](../../notes/atlas185_compact_certificate.md).
