# Atlas181 compact verification progress

Atlas181 is **verified**, after Atlas126, Atlas118, Atlas122, and Atlas124.
The fresh sequential build passed on 2026-09-22; its catalogue example and
classification are updated. Atlas157 is now the active row.

The full fresh verification took **1,606.671 seconds (26 minutes 47 seconds)**,
using **9,907,847,168 bytes (9.23 GiB)** peak process-tree private memory.
The installed-source recheck took 8.047 seconds, giving **1,614.718 seconds
(26 minutes 55 seconds)** combined verification. All source hashes remained
unchanged, and the final catalogue theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`. No proof-source repair was required.

The new exact certificate has common Gram denominator `7776000000000000`.
Discovery took 11.562 seconds and its independent audit took 9.281 seconds.
All 407 coefficient equations and ten positivity witnesses passed that
external audit. Lean subsequently checked the complete catalogue theorem.

The fresh run is `verification_runs/atlas181/fresh_row_1`. Its manifest records
89 row files (9,753,714 source bytes) and 250 prebuilt common project modules.
The common closure consists of the unchanged 249 modules used for Atlas118,
plus `ThirdIntervalCoefficients.lean`, which checks `p=(2+s)/3`.
The new shared module compiled in 8.672 seconds at 4.82 GiB private memory;
its report is `verification_runs/atlas181/shared_third_interval_1/summary.json`.
The previous 57 reusable modules' component costs remain separately recorded
in `verification_runs/atlas118/shared_components.json` (48 minutes 5 seconds
summed across successful runs, 12.32 GiB peak). The old shared infrastructure
and Mathlib are prebuilt; a fresh rebuild of the complete common closure has
not been timed.

The row covers the full required interval `[2/3,1]`. The driver enforced a
one-hour whole-row deadline and 16 GiB process-tree memory limit, with one
Lean compiler and one thread at a time. It installed the prepared catalogue
example after the complete theorem and standard-axiom audit passed.

Accepted reports are `verification_runs/atlas181/fresh_row_1/summary.json`,
`verification_runs/atlas181/installed_example_1.json`, and
`verification_runs/atlas181/completed_row.json`. Including the new shared
module's measured compilation adds 8.672 seconds, giving 1,623.390 seconds
(27 minutes 3 seconds) for that module plus the row and installed recheck.

See [the certificate explanation](../../notes/atlas181_compact_certificate.md).
