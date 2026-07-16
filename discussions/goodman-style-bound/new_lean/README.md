# High-density odd-cycle bound — standalone Lean project

A **fresh, single-purpose** Lean 4 + Mathlib project for one theorem:

> **High-density odd-cycle bound** (`paper_new.tex` §`sec:high-density-theorem`).
> For every graphon `W` with `p = t(K₂,W) ≥ 2/3` and every odd `m ≥ 3`,
> `t(C_m, W) ≥ p^m − p(1−p)^{m-1}`.

At `p ≥ 2/3` this single theorem subsumes `C5`–`C13` (they are just `m = 5,7,9,11,13`), so this
project intentionally drops the entire per-cycle certificate/spectral-closure machinery of the sibling
`../lean` project and keeps only what the high-density proof reuses. Rationale, milestones, hardness
map, and route choice are in **`HIGH_DENSITY_FORMALIZATION_PLAN.md`** (the source of truth — read and
keep it updated as proofs land).

## What is here (copied, byte-exact, from `../lean`)

Reusable foundation only (plan §2). These are unmodified and already compiled clean in `../lean`:

| Module | Role |
|--------|------|
| `OddCycleBound/Graphon.lean` | `IsGraphon`, `edgeDensity`, `degree`, `degCentered` (= `g`), `compress` (= `A`), `specMoment j = ⟨g,Aʲg⟩`, `kernelOp` |
| `OddCycleBound/PathDensity.lean` | path densities `x_j = t(P_j,U)` (Lemma 2.4) |
| `OddCycleBound/Kernel.lean` | kernel-composition algebra: `comp`, `compPow`, `trace`, `trace_comp_comm`, `onesKernel` |
| `OddCycleBound/Certificate.lean` | Φ₅/Φ₇ positivity certificates (dependency of `Cycle`) |
| `OddCycleBound/Cycle.lean` | `cycleDensity`, the edge-deletion bound `edge_deletion_general` (`t(C_m,U) ≤ x_{m-1}`) |
| `OddCycleBound/Necklace.lean` | necklace recursions |
| `OddCycleBound/General/Necklace.lean` | `complTrace_necklace` — the general-`m` cyclic-trace identity (**precedent** for the from-scratch two-sided identity) |
| `OddCycleBound/General/PathRecurrence.lean` | general-`m` path recurrence `pathDensity_succ` |
| `OddCycleBound/General/SumOfSquares.lean` | general moment SOS engine `∫(Σ c·h)² ≥ 0` |
| `OddCycleBound/LowBand/GraphonL2Operator.lean` | canonical graphon `L²` operator foundations |
| `OddCycleBound/LowBand/CompactGraphonOperator.lean` | compact self-adjoint spectral theorem wiring + finite-rank HS approximation (moment-route base) |

Plus build config copied verbatim: `lakefile.toml`, `lean-toolchain` (`leanprover/lean4:v4.31.0`),
`lake-manifest.json` (pins Mathlib `v4.31.0`), `.gitignore`.

The Lean library name is still `OddCycleBound` and module paths are unchanged, so the copied files
compile as-is (no namespace rewrite). Only the root `OddCycleBound.lean` is new — it imports the
subset above.

## Important: what is *not* here

- **The high-density proof itself** — milestones M0–M7 are unwritten. This is the work.
- **The assembled trace-moment identity** `trace(Wᵏ) = Σλᵏ`. In `../lean` it lives inside the
  C9-specific `LowBand/C9Spectral.lean` (not copied). Only the *general* compact-operator base
  (`CompactGraphonOperator.lean`) came over. The moment route (plan M0) must build the compression
  `A`'s eigen-expansion + trace-moment identity **from scratch** on top of this base — that is expected
  (plan §2, "what is not reused — the proof itself").
- `C9`/`C11`/`C13`, `BoundsC5C7`, `Main`, `Conditional`, the `LowBand` C9/C11/C13 scalar+spectral
  closures — dropped on purpose (subsumed at `p ≥ 2/3`).

## Build

```
lake exe cache get     # fetch prebuilt Mathlib v4.31.0 oleans
lake build             # compiles the foundation (this project has no heavy certs yet)
```

The foundation here is light (no 18 GB SOS blocks — those were the dropped C13 certs), so a clean
build is fast relative to `../lean`.

## Where to start

Follow `HIGH_DENSITY_FORMALIZATION_PLAN.md`. First milestone is **M0a** — the *finite-rank* two-sided
identity (pure block-matrix algebra, no limit), which cheaply validates the moment route before any
heavy investment. New proof files go under `OddCycleBound/HighDensity/`; extend the imports in
`OddCycleBound.lean` as you add them.
