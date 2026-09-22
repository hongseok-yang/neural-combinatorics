# Atlas 43 chain: full sequential verification (2026-09-22)

Question: is the existing Lean proof of the Atlas 43 house bound
(`Taeyoung.Methods.RootedSOS.Atlas43*`, reached through `Atlas196`) correct,
and what does it cost against the one-hour, 16 GiB verification envelope?

## Setup

- `order.py` computes the import closure of `Taeyoung.Examples.Graph043` and
  `Graph196` in dependency order: 1,122 modules, of which 1,097 belong to the
  chain (`modules.txt`, no Mathlib); all shared prerequisites already had
  `.olean`s.
- `sequential_1/`: `experiments/verify_lean_modules.py` over that list
  (`lake env lean -M 12288 -j 1` per module, 16 GiB tree cap, 3,600 s budget).
  39 modules passed; `Atlas43CoresRows56` failed under the 12 GiB Lean heap
  at a 15.0 GiB tree peak, and the run stopped after 52m34s.
- `coresrows56_32gib/` and `coresrows56_16gib/`: that module alone with a
  30 GiB and then a 16 GiB Lean heap. It passes both times (67–69 s,
  15.4 GiB), so the failure was the heap cap, not the proof.
- `sequential_full/` and `run_chain.py`: the remaining 1,057 modules, one at a
  time, `-M 16384` under a 16 GiB tree cap, no time budget. `progress.txt` is
  the per-module log; `sequential_full/results.jsonl` the measurements;
  `sequential_full/<module>/compile.{log,json}` the details.
- `checkatlas43_audit.log`: `Taeyoung/CheckAtlas43.lean` elaborated against
  the resulting `.olean`s.

## Result

- All 1,097 modules compile. None needed the 32 GiB retry; every source is
  unchanged since it was compiled; every module has an `.olean`.
- The four chain theorems (`Atlas43Coefficients.certificate_identity`,
  `Atlas43.certificateIdentity`, `Atlas43.satisfiesLowerBound_house`,
  `Atlas196.satisfiesLowerBound_coneHouse`) depend only on
  `propext`, `Classical.choice`, `Quot.sound`.
- Cost: 6.0 hours sequentially in total (0.88 h for the first 40 modules,
  5.14 h for the remaining 1,057; per module 2.9–212 s, mean 20 s).
  Peak 15.4 GiB on `Atlas43CoresRows56`; 56 further modules exceed 12 GiB
  (`CoresRows*` 13.4–15.4 GiB, `CommonBlock0Row*` about 13.2 GiB).

## Consequence

The proof is correct and fits the 16 GiB cap, but it needs six times the
one-hour budget and a Lean heap above the 12 GiB that
`experiments/verify_lean_modules.py` sets. On this evidence Atlas 43 and 196
were restored to verified rows the same day (their example theorems are the
real proofs, `CheckVerified.lean` prints their axioms, and the classification
table records the cost). The chain enters the default build only through
`Taeyoung.Examples.Graph043`; `Taeyoung/CheckAtlas43.lean` audits it on its
own. A compact certificate (plan rows 21 and 22) remains optional.

Do not build this chain with a parallel `lake build`: eight workers at
13–15 GiB each exhausted 64 GiB of RAM and crashed the machine earlier the
same day.
