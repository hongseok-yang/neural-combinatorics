# Compact Atlas203 certificate

Status (2026-09-22): **verified**. The fresh **100-file** build passed in **37m20s** (2239.532 seconds), at **9.26 GiB** peak process-tree private memory. The installed-source recheck brings combined verification to **37m28s** (2247.782 seconds).
The complete catalogue theorem has only `propext`, `Classical.choice`, and
`Quot.sound`. Its example and classification are updated.

Atlas203 is `K6` with edges `04`, `25`, and `35` removed. Its target is
`p*(2*p-1)*(3*p-2)*(10*p^2-14*p+5)`. The full admissible interval `[2/3,1]`
is covered by an induced certificate on `[2/3,3/4]` and a four-root
certificate on `[3/4,1]`.

The lower proof uses the [Atlas130 induced interpretation](atlas130_compact_certificate.md).
With `s=12*p-8` and `D=3181190920704000000000000`, the exact identity expresses
`D*(t(H203,W)-target(p))` as 14 nonnegative induced flag Gram expressions
plus nonnegative Bernstein residuals times induced densities. Its 28 reduced
positive integer Gram factors have order at most 38. All 936 coefficient
equations and their nonnegative residuals are checked in Lean. Eleven
fixed-density multipliers cancel by the disjoint-union density identity.

The upper proof has ten positive factors and common denominator
`2592000000000000`. The substitution `p=(3+s)/4` uses scale 256. Both pieces
use bounded integer encodings, exact matrix products, and generic positivity
lemmas; numerical discovery and the Python audits are not premises of the
Lean theorem.

The row uses 78 upper files, 20 lower files, one complete assembly, and one
catalogue example: 100 files and 17,757,402 source bytes.
Both intervals and every row-specific data module are included in the fresh
measurement. See [the verification record](../lean/docs/ATLAS203_VERIFICATION_PROGRESS.md).
