# OddCycleBound

A Lean 4 / Mathlib formalization of the **odd-cycle Goodman bound**: for every graphon `W`
with edge density `p`, and every odd `m ≥ 3`, the `m`-cycle homomorphism density satisfies

```
t(C_m, W)  ≥  p^m − p·(1 − p)^(m − 1).
```

The proof is complete and `sorry`-free.

## Notation

For a probability space `(Ω, μ)` and a symmetric measurable `W : Ω → Ω → ℝ` with values in `[0,1]`:

- `IsGraphon W μ` — `W` is a graphon (measurable, symmetric, `0 ≤ W ≤ 1`).
- `edgeDensity W μ` — the edge density `p = ∫∫ W`.
- `cycleDensity μ W m` — the `m`-cycle homomorphism density `t(C_m, W) = ∫ (W^{m−1})(x,x) dμ`
  (the trace of the `(m−1)`-st kernel power).

## Theorems in `OddCycleBound/Main.lean`

The headline theorem is `odd_cycle_bound`; the other four are the regime lemmas it is assembled from.
Every one is proven (no `sorry`).

- **`odd_cycle_bound`** — the complete result. For any graphon `W` and any odd `m ≥ 3`,
  ```
  cycleDensity μ W m ≥ edgeDensity W μ ^ m − edgeDensity W μ * (1 − edgeDensity W μ) ^ (m − 1).
  ```
  Assembled by dispatching on `m` and on `p = edgeDensity W μ`:
  `m ≤ 9` → `small_cycle_bound`; else `p ≥ 2/3` → `dense_cycle_bound`, `p < 2/3` → `intermediate_cycle_bound`.

- **`dense_cycle_bound`** — the dense regime `p ≥ 2/3`, for every odd `m ≥ 3`. The analytic heart of
  the proof (beta-integral formula → gamma smoothing → the gamma moment inequality); fully unconditional.

- **`intermediate_cycle_bound`** — the intermediate regime `p < 2/3`, for odd `m ≥ 11`. For `p ≤ 1/2`
  the right-hand side is `≤ 0` and the bound is trivial; for `1/2 < p < 2/3` it is the operator/scalar
  envelope argument (`IntermediateRegion.intermediateRegion_odd_cycle_bound`): a spectral master-defect
  inequality combined with the scalar target `R ≤ C·ψ`.

- **`small_cycle_bound`** — the short cycles `3 ≤ m ≤ 9`, for every `p`. Cases `m = 3, 5, 7` are the
  Goodman/sum-of-squares short-cycle bounds; `m = 9` splits on `p` (`p ≥ 2/3` dense, `p ≤ 1/2` trivial,
  `1/2 < p < 2/3` via the intermediate-region bound).

## How to verify the proof

The claim is: `odd_cycle_bound` is proven from the Lean/Mathlib logical foundations alone, with no
`sorry` and no extra axioms.

1. **It compiles.** From this directory (`complete_lean/`):
   ```
   lake build
   ```
   This type-checks every module (using the pinned Mathlib `v4.31.0`). A successful build means the
   Lean kernel has verified every proof term. If any proof were incomplete the build would fail.

2. **It uses only the standard axioms.** `OddCycleBound/CheckComplete.lean` imports the main theorem
   and runs `#print axioms OddCycleBound.odd_cycle_bound`. Build it and read the emitted line:
   ```
   lake build OddCycleBound.CheckComplete
   ```
   A correct, `sorry`-free proof reports **exactly**:
   ```
   'OddCycleBound.odd_cycle_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```
   These are the three standard axioms of Lean/Mathlib classical mathematics. The absence of `sorryAx`
   is the machine-checked guarantee that nothing is assumed or left unproven.

There are no `decide +kernel` / `native_decide` shortcuts and no computational certificates trusted
outside the kernel.

## Benchmarks

The compilation of the complete proof takes about 40 minutes on a Windows 11 Laptop with 16GB RAM and an Intel i7-1165G7 CPU (2.80GHz), and maximum memory usage is about 6.2GB.