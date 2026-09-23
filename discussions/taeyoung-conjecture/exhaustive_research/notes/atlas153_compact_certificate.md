# Compact Atlas153 certificate

Status (2026-09-23): **verified**. The fresh **98-file** build passed in **40m48s** (2447.782 seconds), at **11.90 GiB** peak process-tree private memory. The installed-source recheck brings combined verification to **40m56s** (2455.595 seconds).
The complete catalogue theorem has only `propext`, `Classical.choice`, and
`Quot.sound`. Its example and classification are updated.

The full admissible interval is covered by two exact four-root SOS certificates, above the elementary range proved in `Low.lean`:

- **Low** interval `[1/2,3/5]`: one hand-written file; the catalogue target is nonpositive there, so the bound is the nonnegativity of the homomorphism density. No certificate data.
- **Middle** interval `[3/5,2/3]`: 47 files; `p=(9+1*s)/15`, common denominator `6065280000000000000` and interpolation scale `759375`. The ten integer positive factors have orders `60, 102, 66, 60, 12, 32, 52, 34, 30, 6`.
- **Upper** interval `[2/3,1]`: 47 files; `p=(2+1*s)/3`, common denominator `11664000000000000` and interpolation scale `243`. The ten integer positive factors have orders `50, 98, 62, 60, 12, 23, 48, 30, 30, 6`.

Each of the twenty Gram blocks retains its integer data, triangular-congruence
positivity proof, and exact basis-expansion proof in a single Lean module.
Ten density interpretation modules per piece are included verbatim in their
five corresponding block sums. Every proof is still checked. Sparse integer
contractions and affine coefficient identities assemble the graphon inequality;
the three interval bounds then prove the full catalogue `SatisfiesLowerBound` theorem.
Numerical certificate discovery and independent Python audits are not premises
of the Lean theorem.

The row has 21,606,176 source bytes. All interval data, coloring,
assembly, and the catalogue example are counted in the fresh run. See
[the verification record](../lean/docs/ATLAS153_VERIFICATION_PROGRESS.md).
