# Region II Lean Formalization Blueprint

Status legend: `[ ]` pending, `[-]` in progress, `[x]` complete.

This file is the authoritative implementation blueprint for the Region II
formalization. During development, only milestone statuses, verification
results, and source hashes should be updated. Mathematical or architectural
changes require an explicit revision note.

Revision note (2026-07-16): at the user's direction, `OddCycleBound/Main.lean`
is now the sole theorem-facing facade. Public names distinguish unconditional,
partial-range, conditional, and partial-range conditional results. The
foundational theorems `RegionII.regionII_large_odd_bound` and
`RegionII.C13_frontier_bound` remain in their implementation modules, while
the uniform public results are named `odd_cycle_regionII_large_bound` and
`odd_cycle_regionII_conditional_bound`.

## Source of truth and provenance

The mathematical source of truth is the corrected July 12b package at
`C:\Users\mekty\main\discussions\goodman-style-bound\gptpro_jul12b`.
In particular, use `regionII_corrected_solution.tex`, not the earlier Region II
manuscripts. The corrected package records the reversed Zone-B maximization
comparison, the additional Zone-C inequality `f >= d + delta`, corrected
directions for rational decimal bounds, the analytic Turan-corner proof, and
the expanded `K = 0` Huber case.

Observed SHA-256 hashes of the current Windows files (2026-07-15):

| File | SHA-256 |
| --- | --- |
| `regionII_corrected_solution.tex` | `7141cb23858c08900abb2b320543e2842876ff63d5c41bfe3226865be5e25b17` |
| `zoneB_certifier.py` | `869f72a758be4681dfacf29bb939c0333d30f338fb3c5701e1fd40d0fc092eaa` |
| `zoneC_certifier.py` | `0bde721927c9ef9048d895d0e85acc243a425eb16aace379ad3d040e543800cd` |
| `AUDIT_NOTES.md` | `85603a92cecb6b40ca48d63f13708d8a14cd651887da30fffa6aae1e5dcc38e5` |

The package's `SHA256SUMS` contains hashes of the LF-normalized distribution,
while the observed files have Windows line endings. Vendored files must record
the hashes of the bytes actually copied and retain the upstream manifest for
comparison.

The exact certifiers currently reproduce these summaries:

```text
boxes verified: 23, skipped (outside domain): 3, max depth: 8
ZONE-B BATTLE CERTIFIED (exact rational arithmetic)

boxes verified: 2997 (bottom-out: 5), skipped: 87, max depth: 28, max battle m: 1716
ZONE-C-MODERATE CERTIFIED on e <= 1/3 - 1/1000 (exact rational arithmetic)
```

The five additional C13 frontier Bernstein checks each certify their complete
rational box without subdivision.

## Intended public theorem signatures

The public statements use the existing arbitrary probability-space graphon
interface and the existing `trace`/`compPow` presentation.

```lean
theorem odd_cycle_regionII_large_bound
    (hW : IsGraphon W mu)
    (hm : Odd m) (hm15 : 15 <= m)
    (hp_lo : 1 / 2 < edgeDensity W mu)
    (hp_hi : edgeDensity W mu < 2 / 3) :
    trace mu (compPow mu W (m - 1)) >=
      edgeDensity W mu ^ m -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1)

theorem C13_path_bound
    (hW : IsGraphon W mu)
    (hp : 51 / 100 <= edgeDensity W mu) :
    trace mu (compPow mu W 12) >=
      edgeDensity W mu ^ 13 -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ 12

theorem odd_cycle_regionII_conditional_bound
    (hW : IsGraphon W mu)
    (htri : TriangleDensityLowerBoundUpTo (103 / 200))
    (hm : Odd m) (hm3 : 3 <= m)
    (hp_lo : 1 / 2 < edgeDensity W mu)
    (hp_hi : edgeDensity W mu < 2 / 3) :
    trace mu (compPow mu W (m - 1)) >=
      edgeDensity W mu ^ m -
        edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1)
```

Names or binder order may change only when required by existing Lean namespace
or universe conventions; the assumptions and conclusions must not be weakened.

## Milestone checklist

### 0. Blueprint and provenance

- [x] Create this authoritative blueprint before implementation.
- [x] Vendor the corrected July 12b proof sources, certifiers, audit notes, and
  upstream checksum manifest.
- [x] Add deterministic certificate-data emitters without treating Python
  acceptance as part of the Lean proof.

### 1. Centered spectral foundation

- [x] Define the centered kernel and identify its integral operator with the
  copied `centeredGraphonOp`.
- [x] Prove compactness by composing the canonical compact graphon operator
  with `centerProjection`.
- [x] Prove the Hilbert--Schmidt budget
  `Tr(A^2) + 2 * ||g||^2 <= p*q`.
- [x] Extract reusable compact self-adjoint spectral and trace-power results
  from the C9 development.
- [x] Continue to use finite Krylov compression for vector moments
  `inner g (A^j g)`.

### 2. One-sided spectral shift

- [x] Define the finite moment polynomial `oneSidedShift` using the existing
  moment-convolution infrastructure.
- [x] Prove the finite matrix one-sided shift identity from the copied
  block-power recurrences.
- [x] Lift the identity to arbitrary graphons using symmetric finite-rank
  Hilbert--Schmidt approximation.
- [x] Prove shift nonnegativity and the required linear-term lower bound using
  Krylov atoms and spectral support bounds.

This milestone is the first major acceptance checkpoint. Scalar-zone work must
not be used to claim progress on the graphon theorem until it compiles.

### 3. Frontier and Huber reductions

- [x] Prove the no-frontier case.
- [x] Prove uniqueness of a centered eigenvalue `alpha > q`.
- [x] Prove forced variance and `alpha^2 + q*alpha - q <= 0`.
- [x] Prove the master defect estimate and construct a bounded measurable
  representative of the frontier eigenfunction.
- [x] Prove the direct and safe coupling inequalities.
- [x] Define `AdmissibleParams` and `p`, `L`, `k_m`, `A_m`, `B_m`, `R_m`,
  `C_m`, `xi`, and `rho`.
- [x] Define `psi` as the minimum of the Huber objective on `[0,1]` and prove
  its piecewise and dual formulas.
- [x] Formalize exact Huber elimination, including the corrected `K = 0` case.

### 4. Scalar zones

- [x] Formalize the `(e,kappa)` chart and its inverse/domain lemmas.
- [x] Prove Zone A.
- [x] Prove the corrected Zone-B maximization reduction.
- [x] Prove small-`e` Zone C.
- [x] Prove the three-geometric defect, secant gate, and `f >= d + delta` used
  by moderate Zone C.
- [x] Prove the analytic Turan corner.
- [x] Assemble the scalar Huber inequality for every admissible odd `m >= 15`.

### 5. Verified certificates

- [x] Implement sound rational intervals, subdivision coverage, square-root
  enclosures, exponential bounds, directed powers, skips, and bottom-out
  leaves.
- [x] Check the Zone-B certificate tree with `decide +kernel` and reproduce
  `23/3/depth 8`.
- [x] Check the Zone-C certificate as bounded `decide +kernel` subtrees and
  reproduce `2997/5/87/depth 28/max m 1716`.
- [x] Implement a sound exact rational multivariate Bernstein checker.
- [x] Check the C13 frontier and full-support kernel certificates.

### 6. C13 frontier

- [x] Refactor the existing C13 path-defect identity into a density-range
  independent lemma.
- [x] Split spectral moments into the frontier atom and Krylov atoms for its
  orthogonal complement.
- [x] Prove safe-atom support in `[-1/2, 7/50]`.
- [x] Prove `C13_frontier_bound` on
  `51/100 <= p <= 519/1000` without triangle assumptions.

### 7. Public assembly

- [x] Prove the foundational `regionII_large_odd_bound` and public
  `odd_cycle_regionII_large_bound` for odd `m >= 15`.
- [x] Restrict `TriangleDensityLowerBoundUpTo (103/200)` to each smaller
  cutoff needed by C9 and C13.
- [x] Dispatch `m = 3,5,7,9,11,13` to the existing short-cycle results and
  the new C13 frontier theorem.
- [x] Prove `odd_cycle_regionII_conditional_bound`.
- [x] Export the new public results from the library root.

## Acceptance criteria

- [x] Every milestone module compiles with Lean 4.31.0 and the pinned Mathlib.
- [x] Zone boundaries and overlaps are checked explicitly: `xi = 1`,
  `e = 1/60`, the admissible frontier ceiling, `K = 0`, the Turan boundary,
  and certificate bottom-out cases.
- [x] Corrected Python certifiers pass as independent regression checks.
- [x] Lean, not Python, proves every certificate soundness implication.
- [x] `#print axioms` is recorded for the scalar theorem, large-odd graphon
  theorem, C13 frontier theorem, and final conditional theorem.
- [x] No `sorry`, `admit`, custom mathematical axiom, or opaque imported
  certificate assertion occurs in the implementation.
- [x] Existing unrelated work and the separate high-density project remain
  unchanged.

## Scope assumptions

- Preserve the arbitrary probability-space graphon interface.
- Formalizing the Razborov--Reiher triangle theorem itself is out of scope.
- The all-odd Region II theorem therefore exposes the existing conditional
  triangle-density hypothesis.
- Densities outside `1/2 < p < 2/3` are out of scope.
- `regionII_corrected_solution.tex` supersedes the earlier manuscripts.
