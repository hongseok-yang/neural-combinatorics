# Compact Atlas130 certificate

Status (2026-09-22): **verified**. The fresh **100-file** build passed in **34m30s** (2069.860 seconds), with **9.21 GiB** peak process-tree private memory. The installed-source recheck brings combined verification to **34m38s** (2078.110 seconds).
The complete catalogue theorem uses only `propext`, `Classical.choice`, and
`Quot.sound`. The example and classification are updated.

Atlas130 is two triangles joined by an edge. Its catalogue target is
`p^3*(2*p-1)^2`, and the full admissible interval is `[1/2,1]`. The proof
joins an induced certificate on `[1/2,2/3]` with a four-root certificate on
`[2/3,1]`. Both pieces are included in the measured row build.

## Lower interval

Let `s=6*p-3` and `D=272160000000000000`. The checked identity is

```
D*(t(H130,W)-p^3*(2*p-1)^2)
  = sum of 14 nonnegative induced flag Gram expressions
    + sum of nonnegative Bernstein residuals times induced densities.
```

The underlying 28 positive integer Gram factors have exact rectangular
pullbacks. For each flag family the interval matrix is a positive Gram
pullback plus `s*(1-s)` times another positive matrix. All 936 Bernstein
coefficient equations are checked over integers. Eleven fixed-density
constraints cancel using `t(F disjoint-union K2,W)=p*t(F,W)`.

The shared interpretation uses explicit sums of labelled branch patterns.
Summing over unspecified cross edges gives products of conditional flag
densities. There are 71,168 flag-pair completions, 3,632 matrix coordinates,
and 15,336 nonzero counting coefficients. Every labelled six-vertex graph
has a checked relabeling to one of 156 representatives. The proof uses
labelled induced densities, so it does not need a separate flag-orbit
classification theorem.

Finite arithmetic is compressed into bounded positional encodings and
checked by Lean's kernel. The Python exporters and numerical discovery
are not premises of the theorem. The original rational certificate also
passed an independent exact audit based on ordered host permutations.

## Upper interval and file budget

On `[2/3,1]`, the upper piece uses the same compact four-root machinery as
[Atlas118](atlas118_compact_certificate.md), with common Gram denominator
`23328000000000000`. Its 407 coefficient equations and ten positive matrices
passed the external audit and the corresponding kernel checks. The degree-five
target requires interpolation scale 243.

Ten density modules were inlined verbatim into five block-sum modules. This
preserves their proofs and leaves 78 upper-piece files. The lower piece uses
20 files; the complete assembly and catalogue example bring the total to 100.
The row contains 15,717,794 source bytes and imports
387 prebuilt shared project modules.

See [the verification record](../lean/docs/ATLAS130_VERIFICATION_PROGRESS.md)
for source hashes, timing, memory measurements, and shared-cost accounting.
