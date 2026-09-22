# Compact Atlas181 certificate

Status (2026-09-22): **verified**. The complete fresh build passed in
1,606.671 seconds (26 minutes 47 seconds), with 89 row files and 9.23 GiB
peak process-tree private memory. The installed-source recheck passed in
8.047 seconds, giving 26 minutes 55 seconds combined. The final catalogue
theorem uses only `propext`, `Classical.choice`, and `Quot.sound`; its example
and classification are updated.

Atlas181 has chromatic number four. Its catalogue target is
`p*(2*p-1)^3*(3*p-2)`, and its full required interval is `2/3 <= p <= 1`.
Writing `p=(2+s)/3` gives the target `s*(s+2)*(2*s+1)^3/81`.

The compact construction from [Atlas118](atlas118_compact_certificate.md)
gives integer Gram matrices with common denominator `7776000000000000`.
The ten reduced matrix orders are 50, 98, 62, 60, 12, 23, 48, 30, 30, and 6.
Integer triangular congruences certify positivity, bounded positional
encodings check the matrix products, and the shared sparse flag map supplies
the graphon interpretation.

The exact block identity is

```
sum of positive flag-density blocks
  = 7776000000000000 * (t(H181,W) - s*(s+2)*(2*s+1)^3/81).
```

Five blocks use constant and linear flag combinations and five carry the
nonnegative factor `s*(1-s)`. The coefficient check clears denominators by
81 and uses the shared lemma `thirdIntervalCoefficient_eval`. Thus the same
sparse map applies at this new interval without changing any accepted row.

The independent audit passed all 407 coefficient equations and ten positivity
witnesses. Lean separately checks the coloring counts
`0,0,0,0,96,600,720`, identifies the catalogue target, and checks every
integer witness. The numerical discovery tools are not proof assumptions.

The fresh closure contains 89 row files, totaling 9,753,714 source bytes,
and 250 prebuilt common project modules. The sole added shared module,
`ThirdIntervalCoefficients.lean`, compiled in 8.672 seconds. Full records are
under `lean/verification_runs/atlas181/`.
