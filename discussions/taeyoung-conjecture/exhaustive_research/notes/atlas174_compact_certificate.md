# Compact Atlas174 certificate

Status (2026-09-23): **verified**. The fresh **98-file** build passed in **40m52s** (2451.969 seconds), at **11.91 GiB** peak process-tree private memory. The installed-source recheck brings combined verification to **41m00s** (2459.782 seconds).
The complete catalogue theorem has only `propext`, `Classical.choice`, and
`Quot.sound`. Its example and classification are updated.

The full admissible interval is covered by two exact four-root SOS certificates, above the elementary range proved in `Low.lean`:

- **Low** interval `[1/2,7/12]`: one hand-written file; the catalogue target is nonpositive there, so the bound is the nonnegativity of the homomorphism density. No certificate data.
- **Middle** interval `[7/12,2/3]`: 47 files; `p=(7+1*s)/12`, common denominator `33094220544000000000000` and interpolation scale `248832`. The ten integer positive factors have orders `60, 102, 66, 60, 12, 32, 52, 34, 30, 6`.
- **Upper** interval `[2/3,1]`: 47 files; `p=(2+1*s)/3`, common denominator `23328000000000000` and interpolation scale `243`. The ten integer positive factors have orders `50, 98, 62, 60, 12, 23, 48, 30, 30, 6`.

Each of the twenty Gram blocks retains its integer data, triangular-congruence
positivity proof, and exact basis-expansion proof in a single Lean module.
Ten density interpretation modules per piece are included verbatim in their
five corresponding block sums. Every proof is still checked. Sparse integer
contractions and affine coefficient identities assemble the graphon inequality;
the three interval bounds then prove the full catalogue `SatisfiesLowerBound` theorem.
Numerical certificate discovery and independent Python audits are not premises
of the Lean theorem.

The row has 22,791,716 source bytes. All interval data, coloring,
assembly, and the catalogue example are counted in the fresh run. See
[the verification record](../lean/docs/ATLAS174_VERIFICATION_PROGRESS.md).
