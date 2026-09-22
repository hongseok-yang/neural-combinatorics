# Compact Atlas118 certificate

Status (2026-09-22): **verified**. The fresh 89-file build passed in 25 minutes
33 seconds at 9.09 GiB peak private memory, sequentially, against prebuilt
shared dependencies. The complete catalogue theorem reports only the three
standard axioms. The catalogue example and classification entry are updated.

The original certificate used rounded Cholesky coordinates. Solving the final
coefficient residual in those coordinates produced correction denominators
with more than 3,200 decimal digits. The coordinates, rather than the desired
graphon inequality, caused much of this arithmetic growth.

For each original integer factor `L`, rational row reduction of `L.transpose`
gives a basis `N` for its column space. Clearing the very small column
denominators gives integer bases with entries of absolute value at most 12.
Write the desired Gram block as `N R N.transpose`, and round and correct `R`
in these coordinates. Selecting independent coefficient columns in increasing
support size and coefficient magnitude is crucial: ordinary floating QR
pivots still gave a 427-digit common denominator; sparse modular pivot
selection followed by an exact rational solve gives

```
D = 5184000000000000
R = G / D
```

All ten `G` matrices have integer entries. The independent exact checker
reconstructs the graph-density coefficient equations and verifies all 407.
Modular rank selection and floating point are only witness-discovery tools.
Their correctness is not a premise of the Lean theorem.

To prove positivity without large rational inverses or principal minors,
choose an integer upper triangular matrix `P` near a scaled inverse Cholesky
factor. The exact witnesses are

```
K = G P
B = P.transpose K
```

Every diagonal entry of `P` is nonzero; `B` is symmetric and strictly
diagonally dominant with positive diagonal. Thus `P` is invertible, `B` is
positive semidefinite, and so is `G`. This argument is now proved in
`lean/Taeyoung/Methods/RootedSOS/CongruenceDiagonalDominance.lean`.

Lean checks the products using bounded positional integer encodings. Separate
digit bounds exclude carries, so a row encoding equality proves every entry
of that row. The same checker verifies `N G` and `(N G) N.transpose`.

The complete graphon interpretation uses the shared Bernoulli
label-edge evaluation. Ordinary products of graphon label-edge factors would
incorrectly square repeated edges. `MatrixGram.lean` proves that the direct
matrix certificate fits this Bernoulli interpretation and retains positivity.

The common Young columns define integer linear combinations of the 352 raw
flags. Their use in a sum of squares requires no irreducibility, rank, or
completeness theorem. The checked pullback groups each pair product by its
six-vertex core and number of isolated edges. Coefficients are bounded by 576,
so base 1153 packs all 143 groups without carries.

There are 5,820 Young matrix coordinates but only 34,842 nonzero group
coefficients. A checked bijection between the row and column listings permits
each row's contractions to visit only these entries. Lean verifies a left
inverse and equal finite cardinalities, then checks each column against the
packed Young coefficients. Thus the sparse listing cannot silently omit or
duplicate contributions.

For `p = (1+s)/2`, the ten positive Gram blocks give a nonnegative density sum
when `0 <= s <= 1`. Five blocks use constant and linear flag combinations;
the other five use constant combinations and carry the nonnegative multiplier
`s*(1-s)`. Their four integer
coefficient slots are combined into 143 group totals. The checked final
polynomial identity makes this sum equal to

```
D * (t(H118, W) - s*(s+1)^2*(3*s^2+1)/16).
```

The expression subtracted from the graph density equals
`p^2*(2*p-1)*(p^3+(1-p)^3)`. Checked coloring counts identify this with the
catalogue target. The complete theorem is
`CompactS4.Atlas118.satisfiesLowerBound_118`.

Files and reproduction:

- Discovery: `experiments/compact_s4_face_certificate.py`.
- Candidate: `experiments/atlas118_compact_face_candidate.json`.
- Separate exact arithmetic audit: `experiments/verify_compact_s4_face.py`.
- Lean matrix generators: `experiments/generate_compact_s4_psd.py` and
  `experiments/generate_compact_s4_expansion.py`.
- Shared sparse checker generator: `experiments/generate_compact_s4_sparse.py`.
- Row coefficient and assembly generators: `generate_compact_s4_group_totals.py`,
  `generate_compact_s4_interval.py`, `generate_compact_s4_density.py`, and
  `generate_compact_s4_block_sums.py` in `experiments/`.
- Fresh acceptance driver: `experiments/verify_compact_s4_fresh.py`.
- Measurements and remaining work:
  `lean/docs/ATLAS118_VERIFICATION_PROGRESS.md`.

The original certificate is preserved. The new certificate stands on its
checked positivity, coefficient identity, and graphon interpretation. Lean
need not verify how the numerical search found it or how its face basis
relates to the original factor.
