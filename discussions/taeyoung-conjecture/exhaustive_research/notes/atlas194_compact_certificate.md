# Compact Atlas194 certificate

Status (2026-09-22): **verified**. The fresh 89-file build passed in **26m40s** (1600.063 seconds), with **9.21 GiB** peak process-tree private memory. The installed-source recheck passed too, bringing combined verification to **26m48s** (1608.126 seconds).
The catalogue example and classification are updated. The final theorem
reports only `propext`, `Classical.choice`, and `Quot.sound`.

The full required interval is `[2/3,1]`. The catalogue target is
`p*(2*p - 1)*(3*p - 2)*(7*p**2 - 9*p + 3)`. With `p=2/3+(1/3)*s`, the checked identity is

```
sum of positive flag-density blocks
  = 7776000000000000 * (t(H194,W) - (s*(s + 2)*(2*s + 1)*(7*s**2 + s + 1)/81)).
```

Five blocks use constant and linear flag combinations; five have the
nonnegative multiplier `s*(1-s)`. The reduced integer matrix orders are
50, 98, 62, 60, 12, 23, 48, 30, 30, 6. Integer triangular congruences prove positivity, bounded positional
encodings prove the matrix products, and the shared sparse flag map supplies
the graphon interpretation. The method is explained in more detail in
[the Atlas118 note](atlas118_compact_certificate.md).

The external audit passed all 407 coefficient equations and ten positivity
witnesses. Lean independently checks the integer witnesses, graph
identifications, coloring counts, target polynomial, and full catalogue
conversion. Numerical discovery is not a premise of the theorem.

The row has 89 source files, totaling 9,972,220 bytes. It uses 250
prebuilt shared project modules. Source closure, hashes, measured build
costs, and the axiom audit are retained under
`lean/verification_runs/atlas194/`. See
[the verification record](../lean/docs/ATLAS194_VERIFICATION_PROGRESS.md).
