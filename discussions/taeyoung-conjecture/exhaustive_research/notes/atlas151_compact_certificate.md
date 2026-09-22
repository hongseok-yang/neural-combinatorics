# Compact Atlas151 certificate

Status (2026-09-22): **verified**. The fresh **97-file** build passed in **46m04s** (2764.453 seconds), at **11.83 GiB** peak process-tree private memory. The installed-source recheck brings combined verification to **46m13s** (2773.140 seconds).
The complete catalogue theorem has only `propext`, `Classical.choice`, and
`Quot.sound`. Its example and classification are updated.

The full admissible interval is covered by two exact four-root SOS certificates:

- **Lower** interval `[1/2,2/3]`: 47 files; `p=(3+1*s)/6`, common denominator `186624000000000000` and interpolation scale `7776`. The ten integer positive factors have orders `57, 101, 65, 60, 12, 32, 52, 34, 30, 6`.
- **Upper** interval `[2/3,1]`: 47 files; `p=(2+1*s)/3`, common denominator `23328000000000000` and interpolation scale `243`. The ten integer positive factors have orders `50, 98, 62, 60, 12, 23, 48, 30, 30, 6`.

Each of the twenty Gram blocks retains its integer data, triangular-congruence
positivity proof, and exact basis-expansion proof in a single Lean module.
Ten density interpretation modules per piece are included verbatim in their
five corresponding block sums. Every proof is still checked. Sparse integer
contractions and affine coefficient identities assemble the graphon inequality;
the two interval bounds then prove the full catalogue `SatisfiesLowerBound` theorem.
Numerical certificate discovery and independent Python audits are not premises
of the Lean theorem.

The row has 21,011,900 source bytes. All interval data, coloring,
assembly, and the catalogue example are counted in the fresh run. See
[the verification record](../lean/docs/ATLAS151_VERIFICATION_PROGRESS.md).
