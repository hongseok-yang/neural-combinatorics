# Compact Atlas122 certificate

Status (2026-09-22): **verified**. The complete fresh build passed in
1,543.829 seconds (25 minutes 44 seconds), using 89 row files and a 9.09 GiB
peak of process-tree private memory. The installed-source recheck passed in
8.047 seconds, bringing combined verification to 25 minutes 52 seconds.
The catalogue theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`; the live example and classification entry are updated.

Atlas122 uses the same compact integer construction as
[Atlas118](atlas118_compact_certificate.md), with new row-specific data and
the exact catalogue edge list. Its common Gram denominator is

```
D = 10368000000000000
```

The ten reduced matrix orders are 46, 93, 58, 59, 12, 20, 44, 27, 29, and 6.
Their integer face bases expand to orders 64, 104, 68, 60, 12, 32, 52, 34, 30,
and 6. Integer triangular congruences certify positivity; bounded positional
encodings certify matrix products. The shared sparse flag contraction has
34,842 entries. None of the numerical discovery steps are proof assumptions.

Writing `p=(1+s)/2`, the certificate proves the identity

```
sum of positive flag-density blocks
  = D * (t(H122,W) - s*(s+1)^2*(3*s^2+1)/16).
```

Five blocks use constant and linear flag combinations, and five carry the
nonnegative multiplier `s*(1-s)`. Thus the identity gives the required bound
throughout `1/2 <= p <= 1`. The target polynomial equals
`p^2*(2*p-1)*(p^3+(1-p)^3)`; the Lean coloring module checks the surjective
counts `0,0,0,36,360,960,720` and proves the catalogue conversion.

The shared machinery and its source hashes are identical to those used for
Atlas118. No Atlas118 row-specific theorem is imported. Atlas122's checked
closure contains 88 method modules and one catalogue example, totaling
9,083,136 source bytes. The 249 prebuilt shared project modules are accounted
for separately in the Atlas118 verification record.

Reproduction uses `experiments/compact_s4_face_certificate.py`,
`verify_compact_s4_face.py`, the compact matrix and contraction generators,
and `generate_compact_s4_half_assembly.py`. That last generator uses the
accepted Atlas118 source as a template and inserts Atlas122's actual edges;
Lean rechecks all coloring counts and graph identifications for Atlas122.

Records are under `lean/verification_runs/atlas122/`. The fresh acceptance
driver is `experiments/verify_compact_s4_fresh.py`; it rebuilds all row files
sequentially, audits the final axioms, and installs the prepared catalogue
example only after the whole row passes within 3,600 seconds and 16 GiB.
