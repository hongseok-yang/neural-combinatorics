# Verifying the catalogue

`verify_catalogue.py` rebuilds the Lean development from source and checks every one of the 117 catalogue rows. It is meant both for the authors and for anyone who wants to confirm the result independently.

## What is checked

**Fresh compilation.** Every project module that a row depends on is compiled from source into a new build directory. Nothing previously built in this project is reused. Only Mathlib and its dependency packages (Batteries, Aesop, Qq, …) are taken prebuilt from the Lake environment. Exactly one `lean` process runs at a time, with one thread, under a process-tree memory cap (default 32 GiB).

**Units.** The work is split into independently measured units:

- **117 row units**, one per catalogue row: the modules that only this row imports, followed by the row's audit;
- **34 shared units**, one per library imported by more than one row: `Foundation`, `PureChordal`, `Fisher`, `Link`, … The large `RootedSOS` library is split into its parts: the Atlas 43 chain (used by Atlas 43 and 196), `CompactS4`, `Induced`, and its core.

Rows are processed in increasing Atlas order, **one at a time**. Before a row, each shared unit it needs that has not been compiled yet is compiled completely, as its own unit. Then the row unit runs:

1. the row's own modules are compiled;
2. **audit**: a generated file `audit/AuditGraphNNN.lean` is compiled against the fresh build. It checks, inside Lean:
   - `GraphNNN.status : SatisfiesLowerBound graph` for a positive row, or `ViolatesLowerBound graph` for a negative row, where `ViolatesLowerBound H` is by definition `¬ SatisfiesLowerBound H`;
   - the row's metadata (`atlasId`, `status`, `formalization = .verified`) agrees with that statement;
   - `#print axioms GraphNNN.status`. The row passes only if the theorem depends on no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. In particular it must not depend on `sorryAx` (a `sorry`) or `Lean.ofReduceBool` (`native_decide`).

Before compiling, the script runs independent Python checks (with NetworkX):

- the 117 row files are exactly the Atlas graphs with at most six vertices that are non-bipartite and have no isolated vertex and no isolated edge;
- each row's Lean edge list is isomorphic to its Atlas graph;
- the stated vertex count, edge count and chromatic number are correct;
- each row's statement matches its status;
- the Lean metadata agrees with `GRAPH_CLASSIFICATION_UP_TO_6_VERTICES.md`.

After the first verified row, two **negative controls** show that the audit can fail:
- the same audit, stated with the opposite statement (`ViolatesLowerBound` for a positive row), must be rejected by Lean;
- a theorem proved by `sorry` must be caught by the axiom check.

If either control does not fail as expected, the run is reported as not verified.

After the rows, `Taeyoung.Catalogue.Counts` is compiled. It checks in the kernel that the catalogue has 117 rows: 94 positive, 23 negative, 0 open, all verified.

## What you must still read yourself

A machine check proves the statements as written. A reader should confirm that the statements say what the paper claims. The trusted definitions are short:

| Definition | File |
|---|---|
| graphons on an arbitrary probability space; homomorphism density `homDensity`; edge density | `Taeyoung/Foundation/Graphon.lean` |
| chromatic polynomial and chromatic number, by their defining properties | `Taeyoung/Foundation/ChromaticPolynomial.lean` |
| the target $(1-p)^{v(H)}\chi_H(1/(1-p))$ and the admissible range $p \ge 1 - 1/(\chi(H)-1)$ | `Taeyoung/Foundation/ChromaticTarget.lean`, `Taeyoung/Foundation/Status.lean` |
| `SatisfiesLowerBound`, `ViolatesLowerBound` | `Taeyoung/Foundation/Status.lean` |
| each row's graph (an explicit edge list on `Fin n`) | `Taeyoung/Examples/GraphNNN.lean` |

The Lean kernel, the toolchain and the prebuilt Mathlib are also trusted.

## Requirements

- The Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.31.0`), installed with [elan](https://github.com/leanprover/elan).
- A resolved Lake environment with Mathlib built (see below).
- Python ≥ 3.11 with `psutil` and `networkx` (`pip install psutil networkx`).
- Memory: at least the cap (default 32 GiB) of physical RAM. The largest single module needs about 16 GiB.
- Disk: about 20 GB for the fresh build directory.

### Setting up Mathlib

In the authors' checkout, `lakefile.toml` points to a Mathlib that is shared between several local projects (`path = "../../../.lake-shared/packages/mathlib"`). In a fresh clone, replace the nine `[[require]]` blocks with a single one at the same Mathlib commit:

```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
```

Then fetch the prebuilt Mathlib:

```sh
lake update mathlib
lake exe cache get
```

The script finds Mathlib through `lake env`, so either layout works without further changes.

## Running

From the `lean/` directory:

```sh
python tools/verify_catalogue.py --plan            # show what will be compiled; compiles nothing
python tools/verify_catalogue.py                   # full verification (32 GiB cap, no time limit)
python tools/verify_catalogue.py --resume verification_runs/full-YYYYMMDD-HHMMSS
python tools/verify_catalogue.py --rows 17,43,127  # selected rows only (for testing)
```

Options:

| Option | Default | Meaning |
|---|---|---|
| `--memory-gib` | 32 | Process-tree memory cap for each Lean process. A process that exceeds it is stopped, and the module counts as failed. |
| `--lean-heap-mib` | cap − 2 GiB | Lean's own `-M` limit. |
| `--require-free-gib` | the cap | Before starting each Lean process, wait until this much memory is available. This avoids competing with other programs. |
| `--out` / `--resume` | `verification_runs/full-<timestamp>` | Run directory, or an interrupted run to continue. |
| `--skip-static-checks`, `--skip-counts` | off | Skip the Python checks or the catalogue-count module. |

Only one verification can run at a time; a lock file in `verification_runs/` enforces this. Interrupting with Ctrl-C stops the current Lean process cleanly. `--resume` continues where the run stopped: a module is reused only if its source and all of its dependencies are unchanged and its compiled file is present.

A failed module does not stop the run. Rows that depend on it are marked **blocked**, and every other row is still verified.

**Do not run `lake build` on this project to verify it.** Lake starts one worker per core, and several certificate modules need 13–16 GiB each. A parallel build therefore exhausts memory, and it crashed the authors' 64 GiB workstation on 2026-09-22.

## Output

Everything goes into the run directory:

| File | Content |
|---|---|
| `progress.log` | The console output: one line per module with `(k/n)`, time, peak memory and elapsed run time, and a closing line per unit. |
| `REPORT.md` | Summary, the negative controls, a table of shared units and a table of rows. |
| `units.json` | Every shared unit, row unit and the catalogue-count unit, with all measurements (see below). `shared.jsonl` and `rows.jsonl` hold the same records, written as each unit finishes. |
| `modules.jsonl` | One record per compiled module: its unit, time, CPU time, peak resident and private memory, memory available before start, source and `.olean` sizes, exit status. |
| `summary.json`, `config.json` | Overall result, and the environment: toolchain, Mathlib commit, git commit, limits, machine, the unit layout. |
| `logs/`, `audit/` | Compiler output of every module, audit and control, and the generated audit files. |
| `build/` | The fresh `.olean` files. They can be deleted afterwards. |

### Measurements

Each unit, shared or row, records:
- **time:** `wall_seconds`, `compile_seconds`, `cpu_seconds`;
- **memory:** `peak_private_gib`, `peak_rss_gib`, over its compiles and, for a row, its audit;
- **size:** module count, `source_bytes`, `source_lines`, `olean_bytes`;
- **extremes:** `slowest_module` and `most_memory_module`;
- **machine at its start:** available memory, CPU load, and other Lean processes (e.g. an editor) with their memory.

A shared unit also lists `used_by_rows` and `depends_on`. A row unit also records:
- `row_modules`, `closure_modules` and `shared_units`;
- `audit_seconds` and `audit_peak_private_gib`;
- `closure_source_bytes` and `closure_olean_bytes`, the compiled files its audit loads;
- the audit's `axioms`.

A row unit covers only the row's own modules and its audit, so it does not depend on the order in which rows run. Two further views include the shared units the row needs. They are computed after the last unit from the per-module measurements:

| View | Time | Peak memory |
|---|---|---|
| **standalone** (`standalone_seconds`, `standalone_peak_private_gib`) | verifying this row alone from scratch: every module of its import closure, own and shared, plus its audit | largest over the closure and the audit |
| **amortized** (`amortized_seconds`) | the row unit plus each shared module's time divided equally among the rows importing it; the amortized times of all rows add up to the catalogue's total compile time | — |

The audit of a row loads the compiled files of its entire closure at once, so its memory reflects the whole closure (`closure_olean_bytes`) even though the shared modules were compiled in their own units. Any other attribution can be computed from `modules.jsonl`.

## Expected cost

Measured on the authors' machine (Windows 11, 64 GiB RAM) with the same sequential setup:

- **The Atlas 43 chain** (shared unit `RootedSOS: Atlas 43 chain`, 1,076 modules, used by Atlas 43 and 196): about 6 hours, peak 15.4 GiB. It is the largest unit.
- **The twenty compact-certificate rows** (118 … 203): 25–46 minutes each including their certificate modules, peak 9–12 GiB.
- **Everything else:** most modules take 5–15 seconds and 2–5 GiB; the rows of this group take a few seconds to a few minutes each.

A complete run takes on the order of 20 hours.
