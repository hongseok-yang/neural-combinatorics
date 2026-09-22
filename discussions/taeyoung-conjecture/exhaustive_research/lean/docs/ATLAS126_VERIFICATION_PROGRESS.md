# Atlas126 verification completed

Atlas126 is verified. Its full `SatisfiesLowerBound` theorem, catalogue
isomorphism, and axiom audit passed on 2026-09-21. `Examples/Graph126.lean`
and the classification entry now mark it verified. Atlas118 is the next row.

## Fresh full-row measurement

| Item | Result |
|---|---:|
| Source files checked | 100 (99 row-specific, one shared checker) |
| Numerical certificate modules within that total | 61 |
| Source payload | 22.4 MiB |
| Fresh verification elapsed | 2705.406 seconds (45 minutes 5 seconds) |
| Peak sampled process-tree private memory | 9.73 GiB |
| Peak sampled process-tree resident memory | 5.82 GiB |
| Compilation | Sequential, one Lean process at a time |
| Axiom reports | Only propext, Classical.choice, Quot.sound |
| Source hashes | Unchanged throughout the check |

The selected old artifacts were moved into a retained backup before the run.
Every source in the final method dependency closure was rebuilt against the
already built common library; no selected module was skipped because of a
cached artifact. The changed shared integer checker was also rebuilt and is
included in the figures above.

The final catalogue source was checked under its actual module name in a
staging directory. Only after its proof and axiom audit passed within the
shared deadline were its source and compiled artifact installed. A separate
12.594-second check then imported the installed artifact and again audited
`Taeyoung.Examples.Graph126.status`. The fresh run and that additional import
check together took 2718.000 seconds of measured checking, still below one
hour. The extra import check is a temporary diagnostic, not an additional
source in the production proof dependency closure.

## Evidence and reproduction

- `lean/verification_runs/atlas126/completed_row.json`: compact completion record.
- `lean/verification_runs/atlas126/fresh_row_1/summary.json`: complete fresh result.
- `fresh_row_1/manifest.json`: ordered source list and SHA256 hashes.
- `fresh_row_1/build/`: per-module compiler logs, times and memory samples.
- `fresh_row_1/catalogue_compile.log`: final catalogue axiom report.
- `installed_import.log`: audit after importing the installed catalogue artifact.
- `fresh_row_1/previous_artifacts/`: retained artifacts from before the fresh build.
- `fresh_row_1/verify_atlas126_fresh.used.py`: exact driver used for the first run.

From the repository workspace, use a new output directory:

```powershell
python -u experiments/verify_atlas126_fresh.py --lake C:/Users/mekty/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lake.exe --output lean/verification_runs/atlas126/fresh_row_2 --seconds 3600 --gib 16
```

The driver now takes the installed example as its canonical source. It stages
and checks that same source before reinstalling it. The first run used the
prepared `Graph126.ready.lean`; its bytes match the installed example exactly.
Lean receives `-j 1 -M 12288`. The watchdog samples verification-process-tree
memory at 0.2-second intervals; it is not a Windows Job Object hard cap. The
unrelated editor server was left untouched.

## Main reductions

See `notes/atlas126_compact_verification.md` for formulas and proof connections.

- A, C and the corrected J plane cover the low-density interval. The original
  C plane fails near x=1; its obsolete junction certificates are not used.
- A strong interior estimate eliminates all three lower-boundary certificate
  families. Only two upper faces and an interior slack polynomial are needed.
- For A, gammaA is a polynomial square. Scaling by its square root lowers the
  certificate degree from (18,3,7) to (12,3,7), reducing 23 chunks to 11.
- Junction slack coordinates reduce the interior to six numerical boxes.
  A constant change of coordinates replaces a slow local determinant with a
  weighted sum of squares.
- The high-density right/high branch uses two quadratic-form regions and ten
  numerical boxes, replacing the original 5,785-box subdivision. The complete
  high-density interior uses four scaled-slack boxes.
- Integer coefficients, balanced lookup, staged transforms, and shared input
  tables avoid repeated rational normalization. Every numerical obligation is
  checked with `decide +kernel`; no external solver or native oracle is an axiom.
- Coloring counts are separated from the graphon imports and check the seven
  graph edges directly. Lean proves equivalence with the original coloring
  predicate before evaluating the counts.

The final coloring computation took 28.7 seconds at 8.11 GiB in the fresh run.
The earlier combined graphon/coloring file crossed 16 GiB, and the first split
still exceeded Lean's heap limit. Those failed diagnostics remain recorded;
they are not included as successful verifications. The direct-edge count
resolved the memory issue before the fresh acceptance run.

The remaining older generated certificates and partial attempts are historical
artifacts. The measured 100-file set is the complete dependency closure of the
verified result plus its audits and the rebuilt shared checker.
