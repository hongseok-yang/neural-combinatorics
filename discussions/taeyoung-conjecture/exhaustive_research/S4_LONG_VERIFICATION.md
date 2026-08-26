# Unattended S4 Lean verification

The campaign is prepared in this checkout. It contains **25 exact interval
certificates** in distinct namespaces and **99,539 independent Lean targets**.
Preparation found zero failed generators, zero missing target lists, and zero
missing Lean modules.

The generated JSON sidecars, target lists, and Lean leaf modules are
intentionally ignored by Git. A fresh clone must run the preparation command
in [Regeneration](#regeneration) once before starting the campaign.

## Before leaving

1. Keep the computer on AC power and set Windows sleep/hibernate to **Never**.
   A screen timeout is harmless; system sleep stops the build.
2. Leave at least 50 GB free on `C:`. At preparation time `dir C:\` reported
   about 159 GB free. The existing Lake build cache is about 7.6 GB; the full
   campaign will add many `.olean` files and logs.
3. Close memory-heavy programs. The measured dense certificate-group target
   used about 14.3 GiB private memory. The launcher intentionally runs one
   Lean process at a time.

## Start or resume

From PowerShell in this repository, run:

```powershell
.\run_s4_long_verification.ps1
```

The same command resumes after an interruption. It uses the repository's
pinned Lean 4.31 toolchain directly, so Elan does not need a network self-update.
Do not run a second copy concurrently.

The default limit is two hours per target. If a target exceeds it, its process
tree is terminated, the timeout is recorded, and the next target starts. To
change the limit or run directory:

```powershell
.\run_s4_long_verification.ps1 -TimeoutHours 4 -RunDirectory lean/verification_runs/s4_long_campaign
```

Stopping with Ctrl+C records the current target as interrupted and terminates
its Lean process tree. Rerun the same command to continue.

## What the campaign does

Targets are ordered as follows:

| Stage | Targets | Meaning |
|---|---:|---|
| certificate smoke | 150 | six representative modules per certificate |
| certificate data | 26,081 | bounded JSON decoders and shape checks |
| shared classification | 200 | exhaustive S4 glued-flag classification |
| shared Young pullback | 2,417 | sparse Young-basis/pullback identities |
| common arithmetic | 40,038 | exact staged Gram products |
| exceptional PSD | 12,953 | full corrections are symmetric and diagonally dominant |
| common group totals | 3,600 | common Gram entries reconstruct all 143 group totals |
| target coefficients | 10,175 | group totals give every interval-polynomial target coefficient |
| exceptional group totals | 3,600 | sparse corrections reconstruct common-to-full group differences |
| exact interfaces/bundles | 325 | theorem interfaces and final algebraic bundles |

Within a certificate-specific stage, targets are round-robin interleaved among
the 25 certificates. A difficult Atlas 118 row therefore cannot prevent all
other certificates from being reached.

Each target is a separate `lake build +Module:olean` process. A compile error,
kernel failure, launch error, or timeout is written to its own log; it does not
stop the queue. State is atomically saved after every target. Successful
targets are skipped on resume when the campaign fingerprint is unchanged.

## Results

During the run, inspect:

- `lean/verification_runs/s4_long_campaign/SUMMARY.txt` — live concise counts and failures;
- `progress.json` — live machine-readable counts and last result;
- `summary.csv` — one row per target, checkpointed every 10,000 attempts and at exit;
- `summary.json` — the corresponding full checkpoint;
- `events.jsonl` — append-only history;
- `logs/` — one Lake log per attempted target;
- `state.json` — durable resume state.

For a quick live view in another PowerShell window:

```powershell
.\show_s4_verification_status.ps1
```

Failures and timeouts are retried by default when the launcher is rerun;
successes are not. To resume while retaining earlier failures without retrying
them, invoke the Python runner directly with `--skip-previous-failures`.

## Exact scope of a successful run

For every certificate, the generated theorem
`S4<Tag>AlgebraicCertificate.algebraic_certificate_verified` bundles:

- exact common Gram construction;
- positivity of the full correction matrix;
- the shared S4 classification and Young pullback;
- common and exceptional fixed-density group reconstruction; and
- all exact target coefficient equations.

This is the finite algebraic certificate, not yet the final arbitrary-graphon
theorem. The generic S4 analytic interpretation (turning the four-label flag
algebra identity into the catalogue's graphon inequality) remains separate and
unimplemented. Therefore even a completely green campaign must not
automatically relabel the corresponding Atlas catalogue rows as `verified`.
Atlas 130 and Atlas 203 also currently have only partial-interval certificates.

The 25 certificates cover these namespaces:

`Atlas118`, `Atlas122`, `Atlas124`, `Atlas130Upper`, `Atlas147Lower`,
`Atlas147Upper`, `Atlas151Lower`, `Atlas151Upper`, `Atlas153Middle`,
`Atlas153Upper`, `Atlas157`, `Atlas168Lower`, `Atlas168Upper`, `Atlas169`,
`Atlas171Middle`, `Atlas171Upper`, `Atlas174Middle`, `Atlas174Upper`,
`Atlas181`, `Atlas185`, `Atlas188Middle`, `Atlas188Upper`, `Atlas194`,
`Atlas199`, and `Atlas203Upper34`.

## Regeneration

The campaign is already generated in this checkout. Regenerate after a fresh
clone, or whenever a certificate or generator is intentionally changed:

```powershell
python experiments/prepare_all_s4_lean.py
```

This rebuilds `experiments/s4_lean_campaign.json` and changes its fingerprint
when an input changes. Use a new run directory, or expect the runner to recheck
targets under the new fingerprint.
