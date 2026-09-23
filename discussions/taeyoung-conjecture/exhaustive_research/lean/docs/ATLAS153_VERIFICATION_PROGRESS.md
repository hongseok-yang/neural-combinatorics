# Atlas153 compact verification record

Atlas153 is **verified** (2026-09-23). The fresh **98-file** build passed in **40m48s** (2447.782 seconds), at **11.90 GiB** peak process-tree private memory. The installed-source recheck brings combined verification to **40m56s** (2455.595 seconds).
All source hashes remained unchanged. The final theorem has only the three
standard axioms. Its catalogue example and classification are updated;
Atlas127 is next.

The fresh run includes all three interval bounds, chromatic counts, graph
identification, complete `SatisfiesLowerBound` theorem, and catalogue example.
Row artifacts were absent at the start. Compilation was sequential with
`LEAN_NUM_THREADS=1`, Lean `-M 12288 -j 1`, a 16 GiB process-tree watchdog,
and one 3,600-second deadline for all 98 row files.

- **Low** interval `[1/2,3/5]`: one hand-written file; the catalogue target is nonpositive there, so the bound is the nonnegativity of the homomorphism density. No certificate data.
- **Middle** interval `[3/5,2/3]`: 47 files; `p=(9+1*s)/15`, common denominator `6065280000000000000` and interpolation scale `759375`. The ten integer positive factors have orders `60, 102, 66, 60, 12, 32, 52, 34, 30, 6`.
- **Upper** interval `[2/3,1]`: 47 files; `p=(2+1*s)/3`, common denominator `11664000000000000` and interpolation scale `243`. The ten integer positive factors have orders `50, 98, 62, 60, 12, 23, 48, 30, 30, 6`.

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

- `verification_runs/atlas153/fresh_row_1/manifest.json` and `summary.json`.
- `verification_runs/atlas153/fresh_row_1/catalogue_compile.log`.
- `verification_runs/atlas153/installed_example_1.json` and `.log`.
- `verification_runs/atlas153/completed_row.json`.

Separate discovery and arithmetic audit records are `middle_face_discovery_1`, `upper_face_discovery_1`, `middle_independent_audit_1`, and `upper_independent_audit_1`.
Development runs and any unsuccessful fresh
attempts remain separate from the accepted measurement. The Lean development
runs are `low_module_1` (`Coloring` and the hand-written `Low.lean`, 33.5
seconds, of which `Low.lean` took 7.6) and `merged_block_pilot_1` (the heaviest
module `Middle.Block01` alone, 306.5 seconds at 11.85 GiB). The interval,
contraction and right modules were not piloted separately: they are within a
few hundred bytes of Atlas188's, measured earlier the same day.

## The middle interval was widened to `[3/5,2/3]`

The August certificate for this row covers `[37/60,2/3]`, and `37/60` is above
the point `0.60687…` where `Q₁₅₃` changes sign, so the elementary argument that
closes Atlas 188, 171 and 174 could not reach it. The plan therefore expected
Atlas 153 to need a self-amalgam and Fisher argument, several hundred lines of
new Lean. Instead the interval SOS was re-solved on the wider `[3/5,2/3]`,
where `Q₁₅₃(3/5) = -1/125 < 0` puts the whole remaining range inside the sign
lemma. No new Lean mathematics was needed, and this row has the same three
bounds and the same file count as the other three.

The discovery records for that widening are, in order: `middle35_sdp_search_1`
(43.9 seconds, feasible on the wider interval with no face reduction, residual
2e-10), `middle35_turan_faces_2` (the exact Turan faces, 2.3 seconds),
`middle35_sdp_faces_7` (901.7 seconds; CLARABEL fails on this face, so the
solution is SCS maximizing the smallest block eigenvalue, which reaches
2.06e-5) and `middle35_rationalize_5` (32.5 seconds, smallest exact
diagonal-dominance margin 0.9977). Earlier numbered attempts in the same
directory record the failures those settings were chosen against. The new
exact certificate is `experiments/atlas153_exact_middle35_interval_sos.json`;
the August `atlas153_exact_middle_interval_sos.json` on `[37/60,2/3]` is kept
but is not what this row proves.

See [the certificate explanation](../../notes/atlas153_compact_certificate.md).
