# Atlas118 compact verification progress

Atlas118 is **verified**, following Atlas126. Its complete fresh build passed
on 2026-09-22, and `Examples/Graph118.lean` and the Markdown classification
have been promoted. Atlas122 is the next active row.

The accepted run rebuilt 89 row files (8.55 MiB of source) sequentially in
1,533.218 seconds: **25 minutes 33 seconds**, with **9.09 GiB** peak process-tree
private memory. The final catalogue theorem reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. All sources were unchanged during the
run; previous row artifacts were moved to a retained backup before rebuilding.
The subsequent installed-source check passed in 7.859 seconds, giving
**25 minutes 41 seconds** combined verification time.

Records: `lean/verification_runs/atlas118/fresh_row_1/summary.json`, its
`manifest.json`, and `lean/verification_runs/atlas118/completed_row.json`.
The build used the prebuilt shared dependencies described below. Lean was
limited to a 12 GiB heap and one thread; the process-tree watchdog sampled
memory every 0.2 seconds and enforced the 16 GiB and 3,600-second limits.

## Completed matrix layers

All ten positivity blocks and all ten expansions from the reduced face to
the original Young slice have passed Lean's kernel:

- 40 row-specific source files, including their data modules;
- 912.124 seconds summed compilation time (15 minutes 12 seconds);
- 9.08 GiB peak process-tree private memory;
- strictly sequential Lean compilation;
- 20 printed theorem axiom reports, all exactly `propext`, `Classical.choice`,
  and `Quot.sound`;
- every source unchanged during its measured compilation.

These are component measurements across several runs, **not** a complete
fresh row build. Common prerequisites are not included in these numbers.
The retained combined record is `lean/verification_runs/atlas118/matrix_layers.json`.
Its component run directories are `packed_1`, `psd_remaining_1`,
`expansion_probe_2`, and `expansion_remaining_1`.

The new certificate has common denominator `5184000000000000` (16 digits),
compared with over 3,200 digits in the old correction denominators. Discovery
took approximately 11 seconds and 0.54 GiB. A separate exact audit passed all
407 coefficient equations and ten positivity witnesses in approximately
9.5 seconds and 0.28 GiB. Those external checks are not Lean proofs.

The mathematical change is explained in
`notes/atlas118_compact_certificate.md`. The original certificate is preserved.

## Checked reusable Lean infrastructure

- `CongruenceDiagonalDominance.lean`: positivity transferred through a
  nonsingular upper triangular integer congruence.
- `PackedMatrix.lean`: exact square and rectangular matrix multiplication
  inferred from bounded positional encodings.
- `MatrixGram.lean`: direct integer Gram matrices interpreted in the existing
  shared-Bernoulli flag framework, including positivity and expanded entries.
- `PackedCoefficients.lean`: bounded positional encoding and decoding of
  graph-group coefficients, including a uniform bound on decoded entries.
- `SparseFlagCoefficients.lean`: the finite-sum interpretation of sparse
  columns and their graph-group coefficients.
- `CompactS4/GroupsData.lean` and `Groups.lean`: balanced group lookup, checked
  against the existing graph-isomorphism witnesses, and the resulting
  graph-density identity. These two modules took about 38 seconds together.

## Existing generated sources need explicit discovery

Many old generated sources are ignored by Git and therefore hidden from
ordinary `rg --files`. There are about 100,000 existing `S4*.lean` files in
the RootedSOS directory, including 3,615 for the old Atlas118 route. They have
not been regenerated or removed.

In particular, the existing `S4ClassificationDensity.lean` and its compiled
artifact already prove `pair_density_classified`. Its classification
prerequisite closure has about 180 Taeyoung modules. This is shared graph
classification infrastructure; the cost of rebuilding it must be reported
separately. Do not import the enormous old Young-pullback or per-certificate
algebraic umbrellas into the new row.

## Compact coefficient route

The new shared Young pullback uses sparse columns as the actual definition of
the linear forms. No proof that they span an irreducible representation is
needed: every such linear combination is valid in a sum of squares.

For each column pair, pack its 143 graph-group coefficients into one integer.
All coefficients have absolute value at most 576; base 1153 therefore prevents
carries. `PackedCoefficients.lean` proves the decoding theorem. The generator
is `experiments/generate_compact_s4_young.py`.

Initial tests for the smallest block hit Lean's 12 GiB heap cap (15.45 GiB
process-tree private peak). Caching powers alone did not fix this. Splitting
each fixed row into its own theorem within the same source file did: all six
rows passed in 61.5 seconds at 7.95 GiB, without adding source files. The
record is `young1111_5`.

A probe of the largest-support row of the trivial Young block passed in
31.782 seconds at 10.97 GiB (`young4_worst_1`). The remaining four shared
blocks, plus the final density interpretation of the fifth, passed sequentially
in `young_remaining_1`: 1,982.078 seconds and 12.32 GiB peak private memory.
All five `pulled_exact` and `pair_basis_density` theorems printed only the
three standard axioms. The new shared Young route uses 29 files in total.
That run covers 24 modules; the other five prerequisites were checked in
earlier runs, so its time is not the total rebuild cost of all shared modules.

`CompactS4/Atlas118/Coloring.lean` passed in 29.5 seconds at 8.15 GiB in
`assembly_prerequisites_3`. It uses Atlas118's actual edges and proves the
coloring counts and catalogue conversion. Catalogue promotion followed the
complete fresh acceptance build.

The completed coefficient and assembly route is:

1. Check all 143 four-slot group totals from the expanded integer matrices.
   Flattening the five Young matrix sizes gives 5,820 input entries. A dense
   `143 x 5820` contraction wastes work: the common pulled matrices have only
   34,842 nonzero entries, with at most 1,004 in one group.
   The checked sparse transpose witness stores the nonzero entries by
   group and by matrix coordinate, with a proved bijection between the
   two dependent finite index types. The column lists are checked against the
   already checked positional Young encodings. This requires about 35,000
   terms instead of 832,000 large-integer digit decodings per row. The
   four scalar slots can then be packed and checked together.
2. Combine groups with equal cores, substituting `p = (1+s)/2`, and verify the
   six polynomial coefficients for each core. The target is
   `s*(s+1)^2*(3*s^2+1)/16`.
3. Assemble the shared-Bernoulli graphon identity, coloring target, and
   `SatisfiesLowerBound` theorem.
4. Run the complete fresh row build under the one-hour, 16 GiB, sequential
   limit, audit final axioms, and only then update Graph118 and classification.
   This acceptance step has passed.

The next catalogue row is Atlas122. Atlas118's acceptance requirements are
complete.

## Assembly checks

The compact row directory now contains 88 source files, including the 40
checked matrix modules. The new files cover four-slot contractions, the final
degree-five integer coefficient identity, coloring, and ten block-density
interpretations and final assembly. Together with the installed catalogue
example, this gives the accepted 89-file row build.

The sparse transpose witness has 34,842 entries. Its Lean construction checks
a left inverse from the column listing to the row listing and equality of the
two finite cardinalities. These imply bijectivity, so both coverage and
multiplicity are justified. Each sparse column is also checked against the
previously established packed Young coefficients. The generator is
`experiments/generate_compact_s4_sparse.py` (16 shared files).

Row generators are `generate_compact_s4_group_totals.py`,
`generate_compact_s4_interval.py`, and `generate_compact_s4_density.py` in
`experiments/`. The finite-sum reindexing generator is
`generate_compact_s4_flat.py`. Their Python syntax checks passed; their new
All row-specific output has now passed component compilation. `SparseContraction.lean` and
`MatrixFlagDensity.lean` passed in `assembly_prerequisites_3`. The additional
`IntervalCoefficients.lean` and `MatrixContraction.lean` passed there too;
replacing broad imports subsequently reduced them to 8.5/7.6 seconds and
4.84/4.81 GiB in `sparse_initial_1`.

The sparse row and column data passed in `sparse_initial_2` (128.1/117.0
seconds, 6.85/7.35 GiB), followed by `SparseBase` (100.8 seconds, 6.37 GiB).
An initial data compilation exceeded Lean's default internal heartbeat limit;
raising that limit while retaining the external time and memory caps fixed it.

Concrete finite-sum rewrites in `FlatBlocks` incurred excessive reduction.
The general theorem `sum_five_squares` and embeddings defined directly by
`Fin.castAdd`/`Fin.natAdd` avoid that reduction. The complete reindexing file
passed in 9.7 seconds at 5.45 GiB in `sparse_initial_7`, with only standard
axioms. All 12 sparse arithmetic chunks passed in that run, taking 20–36
seconds per chunk and peaking at 7.26 GiB. The final `Sparse.contraction`
theorem passed separately in `row_assembly_2` (8.7 seconds, 5.45 GiB), with
only standard axioms. Its final repair explicitly normalizes natural-number
casts before using the cached positional offset.

`row_assembly_3` completed the first two block-density interpretations,
`GroupData`, and all eight interval-identity files. The interval coefficient
chunks took 10–13 seconds each, peaking at 6.02 GiB. The final
`group_identity` theorem passed in 8.7 seconds with only standard axioms.
The shared contraction, complete polynomial identity, and core-graph
identifications are therefore established. `row_assembly_4` passed the
remaining eight block-density interpretations, all expanded-matrix checks,
and all 143 group-total arithmetic checks. Those group-total chunks took
10–20 seconds, peaking at 6.77 GiB. The final `groupTotal_exact` theorem passed
in `row_assembly_5`; all five paired-block bounds passed in `row_assembly_7`.

The complete `satisfiesLowerBound_118` theorem passed in `complete_theorem_5`
(9.3 seconds, 5.95 GiB), and the staged catalogue example passed in
`prepared_example_1` (7.86 seconds, 5.95 GiB). Both report exactly the three
standard axioms. These are component checks, before the full fresh build.

The shared work is recorded separately in
`lean/verification_runs/atlas118/shared_components.json`. All 57 new shared
modules have successful component measurements matching their current source
hashes: 2,884.982 seconds summed compilation (48 minutes 5 seconds), with a
12.32 GiB peak. This is **not** a single fresh rebuild of shared dependencies.
The full row closure uses 249 shared project modules, including 192 existing
ones whose rebuild cost is not measured here. Mathlib is also prebuilt.

The full dependency closure of the certificate contains 88 row
modules, plus one staged catalogue example, and 249 shared Taeyoung modules.
There are no unreferenced row files or explicit proof placeholders in that
closure. The staged example is
under `lean/verification_runs/atlas118/prepared/Graph118.lean`; its checked
bytes have now been installed as `Examples/Graph118.lean`. The fresh-build
driver `experiments/verify_compact_s4_fresh.py` completed in `fresh_row_1`.
