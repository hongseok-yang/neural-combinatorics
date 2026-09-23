# Compact Atlas171 certificate

Status (2026-09-23): **verified**. The fresh **98-file** build passed in **42m16s** (2536.266 seconds), at **11.88 GiB** peak process-tree private memory. The installed-source recheck brings combined verification to **42m24s** (2544.079 seconds).
The complete catalogue theorem has only `propext`, `Classical.choice`, and
`Quot.sound`. Its example and classification are updated.

The full admissible interval is covered by two exact four-root SOS certificates, above the elementary range proved in `Low.lean`:

- **Low** interval `[1/2,5/8]`: one hand-written file; the catalogue target is nonpositive there, so the bound is the nonnegativity of the homomorphism density. No certificate data.
- **Middle** interval `[5/8,2/3]`: 47 files; `p=(15+1*s)/24`, common denominator `2566080000000000000000` and interpolation scale `7962624`. The ten integer positive factors have orders `60, 102, 66, 60, 12, 32, 52, 34, 30, 6`.
- **Upper** interval `[2/3,1]`: 47 files; `p=(2+1*s)/3`, common denominator `11664000000000000` and interpolation scale `243`. The ten integer positive factors have orders `50, 98, 62, 60, 12, 23, 48, 30, 30, 6`.

Each of the twenty Gram blocks retains its integer data, triangular-congruence
positivity proof, and exact basis-expansion proof in a single Lean module.
Ten density interpretation modules per piece are included verbatim in their
five corresponding block sums. Every proof is still checked. Sparse integer
contractions and affine coefficient identities assemble the graphon inequality;
the three interval bounds then prove the full catalogue `SatisfiesLowerBound` theorem.
Numerical certificate discovery and independent Python audits are not premises
of the Lean theorem.

The row has 22,376,556 source bytes. All interval data, coloring,
assembly, and the catalogue example are counted in the fresh run. See
[the verification record](../lean/docs/ATLAS171_VERIFICATION_PROGRESS.md).
