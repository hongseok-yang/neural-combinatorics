# Archive: the `lean/` and `new_lean/` odd-cycle projects

`goodman-style-bound/` used to hold four Lake projects. Two of them were removed on
**2026-08-18** because `complete_lean` proves a strictly stronger theorem:

| removed | proved | superseded by |
|---|---|---|
| `lean/` | `C3/C5/C7` at all `p`; `C9/C11/C13` on path-certificate bands; odd `m ≥ 15` on `1/2 < p < 2/3`; conditional all-density results | `complete_lean` — `odd_cycle_bound`, all `p`, all odd `m ≥ 3`, unconditional |
| `new_lean/` | `p ≥ 2/3`, all odd `m` (split at `m ≤ 61` / `m ≥ 63`) | `complete_lean` — `dense_cycle_bound` |

**The theorems were subsumed. The techniques were not.** `complete_lean` deliberately re-proves
the dense region *analytically* and contains **zero** `decide +kernel` (against 26 uses in `lean/`
and 199 in `new_lean/`), so the entire computational-certificate toolchain died with those two
projects. That toolchain is what this directory preserves.

## Provenance

Full contents of both projects — including every generated certificate file — remain in git:

```
commit 4adc70b9d60bb017137dcee63f8eaf5890eef993   (2026-08-18, "Verify alternating cycle semiinducibility")
git show 4adc70b:discussions/goodman-style-bound/new_lean/OddCycleBound/HighDensity/Hfin/M009.lean
git checkout 4adc70b -- discussions/goodman-style-bound/lean      # resurrect a whole tree
```

Nothing here is buildable as-is: these are loose modules whose imports point at packages that no
longer exist. Treat them as reference and as transplant donors.

## `cert-toolkit/` — the Python that produced the certificates

The part you would least want to write again. None of it is reachable from `complete_lean`.

- `regionII/` — the Region-II / C11 / C13 pipeline, verbatim from `lean/cert_scripts/`.
  `certgen.py`, `gen_linear.py`, `gen_bivar.py`, `gen_trivar.py`, `gen_engine.py`,
  `gen_assembly.py`, `gen_paths.py`, SDP feasibility (`feas_c11.py`, `sos_feas_c11.py`),
  moment extraction (`phi11_moments.py`, `phi13_moments.py`, the `phi*_L.pkl` Gram factors),
  the emitters under `regionII/`, and the solved certificates themselves
  (`cert11_L*.txt`, `cert13_L2.txt` — 4.1 MB of SDP output, `c11_assembly.txt`, `sos*var*.txt`).
  Read `RATIONAL_ROUNDING.md` and `LOWRANK_FINDINGS.md` first — they record *why* the rounding
  works and why low-rank SDP cannot shrink the certificates (Peyrl–Parrilo).
- `hfin/` — the high-density pipeline from `new_lean/`: `hfin_certs.py` (68 KB; emits the 196
  residual-strip Bernstein/Handelman certificates), `hfin_pipeline.py` (driver),
  `app_constants_finite_sweep.py` (the `eq:constant-A` finite sweep for `m ≥ 63`).
- `moments/` — the small standalone numeric checkers (`verify_c5_moments.py`, `verify_c7.py`,
  `verify_c7_moments.py`, `verify_necklace.py`).

### ⚠️ `pp_round.py` was already lost

`pp_round.py` — the Peyrl–Parrilo rational-rounding step that closed both the C11
(`p ≥ 103/200`) and C13 (`p ≥ 519/1000`) certificates — **was never committed to git** and its
source is gone. It survives only as stale CPython 3.12 bytecode, preserved here as
`regionII/pp_round.LOST-SOURCE.cpython-312.pyc`, with `regionII/pp_round.RECOVERY.txt` holding
what could be reconstructed: the full module docstring, the five function signatures
(`is_psd`, `_build_affine`, `_round_babai`, `_round_indep`, `rationalize`), their string/numeric
literals, and a complete disassembly.

Its docstring records the design rationale, which is the load-bearing part: the naive
"round-to-D then poke single Gram entries" scheme shared by `gen_linear`/`gen_bivar`/`gen_trivar`
dumps the whole rounding residual into individual entries, destroying PSD near the SDP margin,
and so **fails below `ρ ≈ 12/25`**. `pp_round` replaces it with a Babai-style rounding on the
affine space of coefficient-matching Gram matrices. Rewriting it from the disassembly is
feasible; rediscovering the rationale would not have been.

## `lean-technique/` — the reusable Lean modules

Generic machinery, separated from the problem-specific assembly it happened to serve. Sizes are
small; the multi-megabyte siblings left behind were all generated data.

- `reflection/` — the `decide +kernel` computational-reflection layer, the single most
  transplantable idea in either project.
  - `HfinPolyReflect.lean` (458 lines) — dense bivariate ℤ-polynomial reflection: `BP = List (List ℤ)`,
    an evaluation homomorphism into ℝ, and per-pair identities discharged as *data equality*
    `lhsBP = rhsBP` by `decide`, replacing a `ring` call that blows up in memory at degree ~112.
    No `native_decide`, no `sorry`.
  - `KernelReflect.lean`, `M6Reflection.lean` — the same trick specialised to the kernel and
    `M6`-strip obligations.
- `bernstein/` — the rational interval / Bernstein certificate framework.
  `Bernstein.lean`, `BernsteinCube.lean` (staged degree-8 tensors in 3 variables — three checked
  1-D transforms instead of expanding 729 basis products in one `ring`), `Intervals.lean`,
  `ChartIntervals.lean`, `Soundness.lean` (the trusted bridge from executable ℚ comparisons to
  real `sqrt`/`exp`/`pow`), `Tree.lean` (the preorder token stream Python emits; the checker
  re-derives every box, so split coverage is untrusted data), `Coverage.lean`.
  **Note:** `complete_lean/OddCycleBound/IntermediateRegion/Bernstein.lean` is a *diverged*
  130-line descendant of the 116-line `Bernstein.lean` here — compare before transplanting.
- `sos/` — the sum-of-squares engines.
  `Certificate.lean` (integral-form Φ₅/Φ₇ positivity certificates over `specMoment`; byte-identical
  in both dead projects), `C13Engine.lean`, `C13Engine4.lean` (the four-fold
  `∫⁴(Σ C·hhhh)²` moment identity — the L₄ engine), `C13Hankel.lean` (L₅/L₆ Hankel blocks).
- `audit/` — the axiom-audit pattern: `CheckGraphon.lean`, `CheckRegionII.lean`,
  `CheckAxioms.new_lean.lean`. The last was **untracked in git** and would have been destroyed
  outright rather than merely removed.

## `generated-samples/` — format records only

One or two examples of each emitted certificate format, so a future regeneration can be checked
against what the Lean side used to accept. Whole small files (`Hfin.Aggregate.lean`,
`Hfin.M009.lean`, the ZoneB/ZoneC boxes, a `Sweep` sample); `*.excerpt.lean` for the rest, cut to
40 lines and 300 columns because the originals run to 7 MB on single lines.

Not archived, by choice — regenerable from `cert-toolkit/`, and intact in git:
the 224 `Hfin/` and 221 `Sweep/` files (29 MB), `C13/{Bivar,Trivar,Quad,Linear}.lean` (11.6 MB),
`C11/{Bivar,Trivar,Linear}.lean` (1.5 MB), `RegionII/Certificate/{Generated,C13Generated}.lean`
and the ZoneB/ZoneC boxes and 22 `ZoneCChunks/`.

Also not archived: the superseded region assemblies, whose mathematics `complete_lean` carries in
better form — `lean/`'s `RegionII/{C13Frontier*,C13MomentPositivity,C13PathIdentity,CouplingChannels,`
`ForcedVariance,Frontier,FrontierTrace,HilbertSchmidtBudget,HuberGraphon,LargeOdd,MasterDefect,`
`OneSidedShift,SafeFrontier}`, `RegionII/Scalar/{Assembly,FrontierAlgebra,Huber,Payments,TuranCorner,`
`ZoneA,ZoneBMax,ZoneBReduction,ZoneCSmall}`, `LowBand/C1{1,3}{Scalar,Spectral}`, `C9/C11/C13.lean`,
`Conditional.lean`; and `new_lean/`'s `HighDensity/{AppConstants*,FinalAssembly,HighDensityGE63,`
`HighDensityLE61,KernelIBP,KernelR1,M6*,StripAssembly}`.

## `docs/` — the written record

`lean-README.md` (30 KB; the per-theorem range table for every band result),
`new_lean-README.md` (21 KB), `FORMALIZATION_NOTES.md`, `REGION_II_LEAN_BLUEPRINT.md`,
`REGION_II_PROGRESS.md`, `REGION_II_AXIOM_REPORT.md`, `HIGH_DENSITY_FORMALIZATION_PLAN.md` (25 KB),
`HFIN_HANDOFF.md`, `HFIN_REFLECTION_HANDOFF.md`, `HFIN_KICKOFF_PROMPT.md`.

## Build environment note

Both dead projects shipped their own fully-built 6.4 GB mathlib at rev `fabf563a`. Those were
consolidated into `discussions/.lake-shared/packages`, which is now junctioned into
`complete_lean`, `fisher_lean`, and both `schur_decomposition` projects. Toolchain
`leanprover/lean4:v4.31.0` throughout.
