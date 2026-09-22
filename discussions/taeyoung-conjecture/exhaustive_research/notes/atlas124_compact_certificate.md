# Compact Atlas124 certificate

Status (2026-09-22): **verified**. The complete fresh build passed in
1,541.437 seconds (25 minutes 41 seconds), with 89 row files and 9.09 GiB
peak process-tree private memory. The installed-source recheck passed in
8.265 seconds, bringing combined verification to 25 minutes 50 seconds.
The final catalogue theorem uses only `propext`, `Classical.choice`, and
`Quot.sound`. The catalogue example and classification are updated.

Atlas124 uses the compact integer construction explained for
[Atlas118](atlas118_compact_certificate.md), with its own matrices and exact
catalogue edge list. The common Gram denominator is `10368000000000000`.
All 407 coefficient equations and ten integer positivity witnesses passed
the independent external audit; numerical discovery is not a Lean premise.

The checked identity gives, with `p=(1+s)/2`,

```
sum of positive flag-density blocks
  = 10368000000000000 *
      (t(H124,W) - s*(s+1)^2*(3*s^2+1)/16).
```

The block sum is nonnegative for `0 <= s <= 1`. The target equals
`p^2*(2*p-1)*(p^3+(1-p)^3)`. A separate Lean module checks the coloring counts
for Atlas124 and proves the conversion to its catalogue proposition.

The ten reduced matrix orders are 46, 93, 58, 59, 12, 20, 44, 27, 29, and 6.
Integer triangular congruences prove positivity; bounded positional encodings
check matrix products. The shared sparse flag map has 34,842 entries and its
source hashes agree with the accepted Atlas118 and Atlas122 builds. Neither
of those graphs' row-specific proofs is imported.

The row closure has 88 method modules plus one catalogue example, totaling
9,174,205 source bytes. It uses 249 prebuilt shared project modules, whose
accounting is recorded separately with Atlas118. The fresh acceptance driver
is `experiments/verify_compact_s4_fresh.py`; measurements and manifests are
under `lean/verification_runs/atlas124/`.
