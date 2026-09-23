# Remaining Lean verification order

Initial planning snapshot: 2026-09-21. At the start of this plan, example-source
metadata marked 97 of 117 rows verified; the 20 initially remaining rows are
listed below. Completed rows are marked individually as execution proceeds.
A fresh build and axiom audit of the original 97 rows was not performed for
this plan.

## Agreed resource envelope

Interpret the user's limits as verification/build costs for one complete row:

- At most one hour for all row-specific compilation and checks, including all
  interval pieces and the final catalogue theorem.
- At most 16 GiB aggregate peak memory across the verification processes.
- Approximately 100 certificate-specific Lean source files per row is acceptable.
  Count all interval pieces, data modules, and assembly modules together.
- Measure a rebuild with that row's artifacts absent, against already-built
  common dependencies. Record shared infrastructure's build cost and file count
  separately; moving row-specific generated files into a shared directory does
  not remove them from the row's accounting.
- These limits concern verification runtime, not the time required to discover
  or implement the proof. Reusing a completely cached row is not a useful timing.
- Completion requires the full `SatisfiesLowerBound` theorem, full interval
  coverage, and an axiom audit admitting only the project's standard axioms.

If a row exceeds the envelope, retain the diagnostic results and revise its
certificate or checker. Do not resume the old mass-generation approach or mark
an algebraic-only result as a completed row.

The user's subsequent execution instruction requires sequential compilation
and completing the current row before proceeding to the next one. Update its
`Examples/GraphNNN.lean` and the Markdown classification only after the complete
theorem has passed verification. An over-budget or incomplete row therefore
stays active until its proof or implementation is repaired.

## Preparatory checks

Before expanding certificate verification, benchmark a difficult existing Atlas
118 coefficient and then the complete finite arithmetic of the Atlas 130 lower
certificate. Test the proposed factored, integer-arithmetic representation.
These are feasibility checks, not completed catalogue rows. The graphon
interpretation must also be completed before the first certificate row is closed.

## Complete-row order

Atlas126 completed its fresh verification on 2026-09-21: 100 files including
one shared checker, 2705.406 seconds (45 minutes 5 seconds), and 9.73 GiB peak
process-tree private memory. All sources were rebuilt sequentially; the final
catalogue theorem reports only the three standard axioms. Its example and
classification entry are now updated.
See [the verification record](lean/docs/ATLAS126_VERIFICATION_PROGRESS.md).

Atlas118 completed on 2026-09-22. Its new exact certificate reduces the common
Gram denominator to 16 digits. The complete fresh build passed: 89 row files,
25 minutes 33 seconds, and 9.09 GiB peak private memory, sequentially against
249 prebuilt shared project modules. The catalogue theorem reports only the
three standard axioms; its example and classification are updated. The
installed-source check brings combined verification time to 25 minutes 41
seconds. See
[the verification record](lean/docs/ATLAS118_VERIFICATION_PROGRESS.md).

Atlas122 completed on 2026-09-22 using the same shared infrastructure. Its
fresh 89-file build took 25 minutes 44 seconds at 9.09 GiB peak private memory;
the installed-source recheck brings combined verification to 25 minutes
52 seconds. The complete theorem has only the three standard axioms. Its
example and classification are updated. See
[the verification record](lean/docs/ATLAS122_VERIFICATION_PROGRESS.md).

Atlas124 completed on 2026-09-22. Its fresh 89-file build took 25 minutes
41 seconds at 9.09 GiB peak private memory; the installed-source recheck
brings combined verification to 25 minutes 50 seconds. The final theorem
has only the three standard axioms, and its example and classification are
updated. See
[the verification record](lean/docs/ATLAS124_VERIFICATION_PROGRESS.md).

Atlas181 completed on 2026-09-22. The full `[2/3,1]` catalogue proof passed
in a fresh 89-file build: 26 minutes 47 seconds and 9.23 GiB peak private
memory. The installed-source recheck brings this to 26 minutes 55 seconds;
one new shared interval lemma took another 8.672 seconds. The final theorem
has only the standard axioms, and the example and classification are updated.
See
[the verification record](lean/docs/ATLAS181_VERIFICATION_PROGRESS.md).

Atlas157 completed on 2026-09-22. Its fresh 89-file full `[2/3,1]` catalogue proof passed in 26m52s at 9.20 GiB peak private memory; the installed recheck brings combined verification to 27m00s. The final theorem has only the standard axioms, and its example and classification are updated. See [the verification record](lean/docs/ATLAS157_VERIFICATION_PROGRESS.md).

Atlas169 completed on 2026-09-22. Its fresh 89-file full `[2/3,1]` catalogue proof passed in 26m48s at 9.23 GiB peak private memory; the installed recheck brings combined verification to 26m56s. The final theorem has only the standard axioms, and its example and classification are updated. See [the verification record](lean/docs/ATLAS169_VERIFICATION_PROGRESS.md).

Atlas194 completed on 2026-09-22. Its fresh 89-file full `[2/3,1]` catalogue proof passed in 26m40s at 9.21 GiB peak private memory; the installed recheck brings combined verification to 26m48s. The final theorem has only the standard axioms, and its example and classification are updated. See [the verification record](lean/docs/ATLAS194_VERIFICATION_PROGRESS.md).

Atlas185 completed on 2026-09-22. Its fresh 89-file full `[2/3,1]` catalogue proof passed in 28m28s at 9.23 GiB peak private memory; the installed recheck brings combined verification to 28m37s. The final theorem has only the standard axioms, and its example and classification are updated. See [the verification record](lean/docs/ATLAS185_VERIFICATION_PROGRESS.md).

Atlas199 completed on 2026-09-22. Its fresh 89-file full `[2/3,1]` catalogue proof passed in 26m42s at 9.23 GiB peak private memory; the installed recheck brings combined verification to 26m50s. The final theorem has only the standard axioms, and its example and classification are updated. See [the verification record](lean/docs/ATLAS199_VERIFICATION_PROGRESS.md).

Atlas130 completed on 2026-09-22. Both interval pieces and the full catalogue proof passed in a fresh 100-file build: 34m30s at 9.21 GiB. The installed recheck brings combined verification to 34m38s. The final theorem has only the standard axioms; its example and classification are updated. See [the verification record](lean/docs/ATLAS130_VERIFICATION_PROGRESS.md).

Atlas203 completed on 2026-09-22. Both interval pieces and its full catalogue proof passed in a fresh 100-file build: 37m20s at 9.26 GiB. The installed recheck brings combined verification to 37m28s. The theorem has only the standard axioms; its example and classification are updated. See [the verification record](lean/docs/ATLAS203_VERIFICATION_PROGRESS.md).

Atlas147 completed on 2026-09-22. Both four-root interval pieces and the full catalogue proof passed in a fresh 97-file build: 43m38s at 11.84 GiB. The installed recheck brings combined verification to 43m46s. The theorem has only the standard axioms; its example and classification are updated. See [the verification record](lean/docs/ATLAS147_VERIFICATION_PROGRESS.md).

Atlas168 completed on 2026-09-22. Both four-root interval pieces and the full catalogue proof passed in a fresh 97-file build: 44m34s at 11.84 GiB. The installed recheck brings combined verification to 44m42s. The theorem has only the standard axioms; its example and classification are updated. See [the verification record](lean/docs/ATLAS168_VERIFICATION_PROGRESS.md).

Atlas151 completed on 2026-09-22. Both four-root interval pieces and the full catalogue proof passed in a fresh 97-file build: 46m04s at 11.83 GiB. The installed recheck brings combined verification to 46m13s. The theorem has only the standard axioms; its example and classification are updated. See [the verification record](lean/docs/ATLAS151_VERIFICATION_PROGRESS.md).

Atlas43 and Atlas196 were downgraded to believed on 2026-09-22. Their example
metadata had said verified, but the classification table had listed both as
believed since 2026-08-26, and the discrepancy was resolved against the
existing proof. That proof (`Taeyoung.Methods.RootedSOS.Atlas43*`, reached
through `Atlas196`) is complete and sorry-free: a 1,097-module chain of
`decide +kernel` cells, 1,028 of them gitignored and regenerated by
`experiments/generate_atlas43_lean_checks.py`. The whole chain was then compiled one module at a time
(`experiments/run_bounded_lean.py`, `lake env lean -j 1`, 16 GiB process-tree
cap): all 1,097 modules pass, the four chain theorems
(`Atlas43Coefficients.certificate_identity`, `Atlas43.certificateIdentity`,
`Atlas43.satisfiesLowerBound_house`, `Atlas196.satisfiesLowerBound_coneHouse`)
report only the three standard axioms, and every source is unchanged since it
was compiled. Cost: 6.0 hours sequentially in total (2.9–212 seconds per
module, mean 20 seconds); peak 15.4 GiB on `Atlas43CoresRows56`, which fails
under the 12 GiB Lean heap that `verify_lean_modules.py` sets but passes with
`-M 16384`; 56 further modules exceed 12 GiB. So the proof is correct and fits
the 16 GiB cap, but needs six times the one-hour budget. Records:
[lean/verification_runs/atlas43/](lean/verification_runs/atlas43/). A parallel
`lake build` of the same chain exhausted 64 GiB of RAM and 123 GiB of commit and
crashed the machine; never build it with more than one worker. On that
evidence both rows were restored to verified the same day: their example
theorems are the real proofs again, the catalogue audit prints their axioms,
and the classification records the six-hour cost. The chain is no longer
imported directly by `Taeyoung.lean`; it enters the default build only through
`Taeyoung.Examples.Graph043`, and `Taeyoung/CheckAtlas43.lean` audits it on
its own. Rows 21 and 22 below are therefore optional: a compact certificate
would bring the two rows inside the envelope but is not needed for their
status.

Atlas188 completed on 2026-09-23. Its three interval bounds and the full catalogue proof passed in a fresh 98-file build: 40m55s at 11.90 GiB. The installed recheck brings combined verification to 41m03s. The theorem has only the standard axioms; its example and classification are updated. See [the verification record](lean/docs/ATLAS188_VERIFICATION_PROGRESS.md).

Atlas171 completed on 2026-09-23. Its three interval bounds and the full catalogue proof passed in a fresh 98-file build: 42m16s at 11.88 GiB. The installed recheck brings combined verification to 42m24s. The theorem has only the standard axioms; its example and classification are updated. See [the verification record](lean/docs/ATLAS171_VERIFICATION_PROGRESS.md).

Atlas174 completed on 2026-09-23. Its three interval bounds and the full catalogue proof passed in a fresh 98-file build: 40m52s at 11.91 GiB. The installed recheck brings combined verification to 41m00s. The theorem has only the standard axioms; its example and classification are updated. See [the verification record](lean/docs/ATLAS174_VERIFICATION_PROGRESS.md).

Atlas153 completed on 2026-09-23. Its three interval bounds and the full catalogue proof passed in a fresh 98-file build: 40m48s at 11.90 GiB. The installed recheck brings combined verification to 40m56s. The theorem has only the standard axioms; its example and classification are updated. See [the verification record](lean/docs/ATLAS153_VERIFICATION_PROGRESS.md).

Atlas127 completed on 2026-09-23. Its two interval bounds and the full catalogue proof passed in a fresh 97-file build: 43m30s at 11.90 GiB. The installed recheck brings combined verification to 43m37s. The theorem has only the standard axioms; its example and classification are updated. See [the verification record](lean/docs/ATLAS127_VERIFICATION_PROGRESS.md).

| Priority | Atlas | Proposed route and reason |
|---:|---:|---|
| 1 | 126 | **Completed.** Compact supporting planes, exact integer Bernstein checks, graphon integration, coloring counts and catalogue isomorphism all passed the fresh build and axiom audit within the agreed limits. |
| 2 | 118 | **Completed.** First complete compact S4 row: exact integer Gram matrices, sparse contractions, the full `[1/2,1]` graphon inequality, coloring and catalogue theorem passed in 89 files and 25m33s at 9.09 GiB. |
| 3 | 122 | **Completed.** Reused the compact single-interval structure with a 17-digit denominator. The full fresh catalogue proof passed in 89 files and 25m44s at 9.09 GiB. |
| 4 | 124 | **Completed.** Finished the house-with-leaf family with the same shared machinery. The fresh complete catalogue proof passed in 89 files and 25m41s at 9.09 GiB. |
| 5 | 181 | **Completed.** First full `[2/3,1]` compact row, with one small shared interval lemma. The fresh catalogue proof passed in 89 files and 26m47s at 9.23 GiB. |
| 6 | 157 | **Completed.** Full `[2/3,1]` compact catalogue proof; fresh 89-file build in 26m52s at 9.20 GiB. |
| 7 | 169 | **Completed.** Full `[2/3,1]` compact catalogue proof; fresh 89-file build in 26m48s at 9.23 GiB. |
| 8 | 194 | **Completed.** Full `[2/3,1]` compact catalogue proof; fresh 89-file build in 26m40s at 9.21 GiB. |
| 9 | 185 | **Completed.** Full `[2/3,1]` compact catalogue proof; fresh 89-file build in 28m28s at 9.23 GiB. |
| 10 | 199 | **Completed.** Full `[2/3,1]` compact catalogue proof; fresh 89-file build in 26m42s at 9.23 GiB. |
| 11 | 130 | **Completed.** Induced lower interval and four-root upper interval; fresh full 100-file catalogue proof in 34m30s at 9.21 GiB. |
| 12 | 203 | **Completed.** Induced lower interval and four-root upper interval; fresh full 100-file catalogue proof in 37m20s at 9.26 GiB. |
| 13 | 147 | **Completed.** Two four-root pieces, full catalogue proof; fresh 97-file build in 43m38s at 11.84 GiB. |
| 14 | 168 | **Completed.** Two four-root pieces, full catalogue proof; fresh 97-file build in 44m34s at 11.84 GiB. |
| 15 | 151 | **Completed.** Two four-root pieces, full catalogue proof; fresh 97-file build in 46m04s at 11.83 GiB. |
| 16 | 188 | **Completed.** Three interval bounds, full catalogue proof; fresh 98-file build in 40m55s at 11.90 GiB. |
| 17 | 171 | **Completed.** Three interval bounds, full catalogue proof; fresh 98-file build in 42m16s at 11.88 GiB. |
| 18 | 153 | **Completed.** Three interval bounds, full catalogue proof; fresh 98-file build in 40m48s at 11.90 GiB. |
| 19 | 174 | **Completed.** Three interval bounds, full catalogue proof; fresh 98-file build in 40m52s at 11.91 GiB. |
| 20 | 127 | **Completed.** Two interval bounds, full catalogue proof; fresh 97-file build in 43m30s at 11.90 GiB. |
| 21 | 43 | Replace the retired 1,097-module `decide +kernel` chain with a compact rooted-SOS certificate on `[1/2,1]` in the `CompactS4` style (exact integer Gram data, sparse contractions, one shared checker). The house is the smallest S4 row, so the existing 118/122/124 pipeline should transfer directly; the rational certificate input `experiments/house_atlas43_rational.json` remains tracked. |
| 22 | 196 | Reattach the existing house-cone lift `Taeyoung.Methods.RootedSOS.Atlas196.satisfiesLowerBound_coneHouse` (20 small modules, `[2/3,1]`) to the compact Atlas 43 theorem; `Taeyoung.Examples.Graph196.iso` is already in place. No new certificate is needed. |

## Evidence and uncertainty

The ordering favors existing proof work, single-interval closures, reuse of
mathematical infrastructure, and then smaller certificate arithmetic. It is not
a measured ranking of Lean compilation times. Within a family, revise the order
when actual measurements or simpler proofs justify it.

For the 25 existing S4 certificates, source data inspection found:

- 118/122/124 have maximum correction-denominator lengths of 3,239/3,267/3,386
  decimal digits and the same factor dimensions.
- Single-certificate 181/157/169 have maximum lengths 3,323/3,378/3,585 digits.
- Single-certificate 194/185/199 have maximum lengths 4,300/4,340/4,381 digits.
- The upper certificates of 130/203 have maximum lengths 4,598/4,611 digits;
  their small new lower certificates do not eliminate this upper-range cost.
- The paired S4 data for 147, 168, and 151 total approximately 7.9, 8.8, and
  8.9 MiB respectively. File size is only a rough complexity indicator.

Primary local references:

- [Current example metadata](lean/Taeyoung/Examples/)
- [S4 campaign certificate manifest](experiments/s4_lean_campaign.json)
- [Existing S4 certificate intervals](notes/s4_exact_interval_sos_remaining_cases.tex)
- [Atlas 130/203 completion](notes/atlas130_atlas203_complete_bounds.tex)
- [Range-qualified implications](notes/open_conditional_implications.tex)
- [Self-amalgam low ranges](notes/four_self_amalgam_partial_ranges.tex)
- [Atlas 126 development](lean/Taeyoung/Methods/Atlas126/)
- [Atlas 127 certificate size and alternative routes](notes/smoothed_goodman_deflagged.tex)
