# OddCycleBound — Lean 4 formalization of the odd-cycle Goodman-type bound

This project formalizes, in Lean 4 + Mathlib, the odd-cycle homomorphism-density inequality of
`../paper.tex`,

```
t(C_{2k+1}, W) ≥ p^{2k+1} − p(1−p)^{2k},   p = t(K₂, W),
```

for the **complement path-certificate** cases, built so that the **only trusted input is the
integral definition of homomorphism density**. There is no operator model, no Hilbert space, no
analytic facts taken as hypotheses: the graphon is a measurable symmetric `[0,1]`-valued kernel
`W : Ω → Ω → ℝ` over an abstract probability space `(Ω, μ)`, and every density is a nested integral.

## Build

```
lake exe cache get        # download prebuilt Mathlib oleans (already done once)
lake build                # compiles the whole library
lake env lean CheckGraphon.lean   # prints the axiom trail of the main results
```

Toolchain: Lean `v4.31.0`, Mathlib `v4.31.0` (pinned in `lean-toolchain` / `lakefile.toml`).

## Build performance and memory

A clean rebuild of *only* the project modules (`lake clean OddCycleBound; lake build`, with
Mathlib oleans already fetched via `lake exe cache get`, so Mathlib itself is not recompiled)
took **293 s wall** in the run below. `lake build` fans **independent** files out across all
cores (up to the core count — 20 here), so the wall time is far below the sum of per-module
times; the **SOS certificate files dominate**.

Per-module times (this clean run, parallel; descending):

| Module | Time | | Module | Time |
|--------|-----:|-|--------|-----:|
| `C11/Bivar` | **145 s** | | `General.PathRecurrence` | 20 s |
| `C9` | **115 s** | | `Certificate` / `BoundsC5C7` / `General.Necklace` | 13 s |
| `C11/Trivar` | **115 s** | | `Graphon` / `Kernel` / `PathDensity` | 12 s |
| `C11/Linear` | **95 s** | | `Main` / `Necklace` / `Cycle` | 11 s |
| `General.SumOfSquares` | 58 s | | `OddCycleBound` (root) | 10 s |
| `C11` (assembly) | 38 s | | **total wall** | **293 s** |

Notes:
* The four heavy files — `C11/Bivar`, `C11/Trivar`, `C11/Linear`, `C9` — are the SOS certificates
  and run **concurrently**, which is why the total wall (293 s) is well under their sum (~470 s).
* These per-module times are wall-clock under 20-way contention, so they vary with machine load.
  Also, the **first** clean build after boot can inflate the earliest modules by tens of seconds
  while Mathlib's oleans are read cold from disk (warm OS file cache → the ~12 s seen here);
  an older benchmark recorded `Graphon` at 194 s for exactly this cold-cache reason.
* The `C9`/`C11` certificate files are dominated by **elaboration of giant proof-term `Expr`
  trees** (300-digit rational coefficients), *not* by parsing or kernel typechecking — measured:
  isolating a heavy block, parsing+statement-elaboration ≈ 2 s, kernel checking ≈ 0
  (`skipKernelTC` made no difference), proof elaboration ≈ 62 s. `count_heartbeats` reports tiny
  counts here because it counts `whnf`/`isDefEq` steps, not `Expr` construction — so it *under*counts
  this regime.
* **Memory:** the largest spikes come from building **many heavy files concurrently** (each `lean.exe`
  loads Mathlib plus its own large terms). To bound peak memory, throttle the build's concurrency
  via the Lean task pool, e.g. `LEAN_NUM_THREADS=4 lake build` (slower wall-clock, far smaller peak).
  The `C11` certificate is **split into per-block files** (`C11/Linear`, `C11/Bivar`, `C11/Trivar` +
  the `C11` assembly) so each is a separate ~120–580 KB compilation unit instead of one 1.2 MB file —
  this caps per-file peak memory and lets the editor elaborate one block at a time.

**Benchmark machine:** Intel Core i5-14600K (14C/20T), 64 GB RAM, Windows 11 Pro (build 26200),
Lean/Mathlib `v4.31.0`. Times are wall-clock and will scale with single-thread performance.

## Headline results

The paper-facing statements live in `OddCycleBound/Main.lean`, namespace `OddCycleBound`, for a
graphon `W` with the single hypothesis `hW : IsGraphon W μ` and edge density
`p = edgeDensity W μ = ∫∫W`:

| Theorem | Statement | Range |
|---------|-----------|-------|
| `C5_bound` | `t(C₅, W) ≥ p⁵ − p(1−p)⁴` | all densities |
| `C7_bound` | `t(C₇, W) ≥ p⁷ − p(1−p)⁶` | all densities |
| `C9_path_bound` | `t(C₉, W) ≥ p⁹ − p(1−p)⁸` | `p ≥ 1003/2000` (path-certificate range) |
| `C11_path_bound` | `t(C₁₁, W) ≥ p¹¹ − p(1−p)¹⁰` | `p ≥ 2/3` (high-density range) |

The `C₁₁` bound is proved on `p ≥ 2/3` (complement density `q = 1−p ≤ 1/3`), the natural
meeting point with Razborov's triangle-density theorem (valid on `[1/2, 2/3]`), which a future
spectral-closure development can use to cover the remaining band `1/2 < p < 2/3`.

Here `t(C_m, W)` is `trace μ (compPow μ W (m−1))` — the cyclic trace of the powers of the kernel
`W` — written out purely as nested integrals.

These are the `W`-facing restatements of the complement-form lemmas (phrased for `U = compl W =
1 − W`, where the inclusion–exclusion is natural), via `compl (compl W) = W` and
`edgeDensity (compl W) = 1 − edgeDensity W`:

| Lemma | Statement (`q = edgeDensity U μ = ∫∫U`) | Range |
|-------|------------------------------------------|-------|
| `C5_integral` | `t(C₅, 1−U) ≥ (1−q)⁵ − (1−q)q⁴` | all densities |
| `C7_integral` | `t(C₇, 1−U) ≥ (1−q)⁷ − (1−q)q⁶` | nontrivial regime `q ≤ ½` |
| `C7_integral_all` | the same `C₇` bound for all densities (`q > ½` is `g₇ ≤ 0 ≤ t`) | all densities |
| `C9_path_integral` | `t(C₉, 1−U) ≥ (1−q)⁹ − (1−q)q⁸` | `q ≤ 997/2000` |

## Module layout

```
Graphon → PathDensity → { Kernel, Certificate } → Cycle → Necklace → BoundsC5C7 → Main
                                                                   ↘ General/* → C9
                                                                              ↘ C11
C11 (assembly) ← { C11/Linear, C11/Bivar, C11/Trivar }
```

| Module | Content |
|--------|---------|
| `Graphon` | Integral foundations: `IsGraphon`, the integral operator `kernelOp`, `edgeDensity`, `degree`, the mean-zero degree part `compress`/`compressIter`, the moments `specMoment j = ∫ hᵢ·hⱼ`, and `sos1`. |
| `PathDensity` | **Lemma 2.4** (`pathDensity_two … _six`): the path densities `xⱼ` as polynomials in `q` and the moments `specMoment`, proved from the integral definitions. |
| `Kernel` | The reusable **kernel-composition algebra**: `comp`, the all-ones kernel `onesKernel`, `doubleMean`, the `GoodK` closure, the cut lemma, `comp_assoc`, the powers `compPow`, the trace `trace`, and its cyclic invariance `trace_comp_comm`. |
| `Certificate` | The Φ₅/Φ₇ **positivity certificates** (`sos2`, `cert5_specMoment`, `cert7_specMoment`) in the integral moments `specMoment`. |
| `Cycle` | The cycle density `cycleDensity`, `compPow_nonneg`, and the **edge-deletion bound** `edge_deletion_general : c_{k+2} ≤ x_{k+1}`. |
| `Necklace` | All necklace machinery (see below): the recursions `mixedTrace_succ`/`_zero`, `pairing_complIter_succ`, `complMean_succ`; the telescoped **general necklace identity** `complTrace_necklace`; the **closed form for the pairings** `pairing_pathIter_complIter_closed`; and `pathDensity_zero`/`_one`. |
| `BoundsC5C7` | Assembles the necklace + certificate + edge deletion into `C5_integral` / `C7_integral` / `C7_integral_all`. |
| `C9` | The Φ₉ certificate (`cert9_specMoment`, via the degree-3 and bivariate SOS engines on the path-certificate range `q ≤ 997/2000`) and the assembled `C9_path_integral`. |
| `C11` | **Assembly** for the Φ₁₁ bound: `cert11_L4`/`L5` (Hankel `nlinarith`), `cert11_specMoment` (combines `L1 … L5`), and `C11_path_integral`. Imports the three block files below. Split out of a former 1.2 MB monolith to bound per-file memory. |
| `C11/Linear` | The Φ₁₁ `L₁` block — linear in the moments, certified by `sos4` (`cert11_L10 … L13`, `cert11_L1`). |
| `C11/Bivar` | The Φ₁₁ `L₂` block — bivariate, certified by `sos2var4` (`cert11_L20 … L23` chunks, `cert11_L2`). |
| `C11/Trivar` | The Φ₁₁ `L₃` block — trivariate, certified by `sos3var3` (`cert11_L30 … L33` chunks, `cert11_L3`). |
| `Main` | The `W`-facing headline theorems `C5_bound`, `C7_bound`, `C9_path_bound`, `C11_path_bound` and the complement translation. |
| `General/PathRecurrence` | The **general path-density recurrence** `pathDensity_succ : x_{n+1} = q·xₙ + Σ sᵢ·x_{n−1−i}`, and `pathDensity_seven`/`_eight`. |
| `General/SumOfSquares` | The general Hankel sum-of-squares engine: `sos_sq_expand`, `sos_sq_expand_2var`, and the fixed-degree `sos2var3`/`sos3`. |
| `General/Necklace` | Regression `example`s checking that `complTrace_necklace` specialises to the explicit four-term (`C₅`) and six-term (`C₇`) inner-product forms. |

### The necklace identity and the uniform assembly

The cyclic inclusion–exclusion sum was feared to be `O(2ᵐ)`, but it **telescopes** to an
`O(m)`-term identity (verified numerically in `verify_necklace.py`). In `Necklace.lean`:

* `mixedTrace a b = trace(Uᵒ⁽ᵃ⁺¹⁾ ∘ (complᵒᵇ))` satisfies the recursion `mixedTrace_succ` and base
  `mixedTrace_zero : mixedTrace a 0 = x_{a+1} − c_{a+1}`;
* telescoping it (`mixedTrace_telescope`) and peeling (`complTrace_peel`) gives the
  **general-`m` necklace identity**

  ```
  complTrace_necklace : trace(complᵒ⁽ⁿ⁺¹⁾)
      = Σ_{j=0}^{n} (−1)ʲ ⟨pathIter j, complIter (n+1−j)⟩  +  (−1)ⁿ⁺¹ (x_{n+1} − c_{n+1}),
  ```

  with `x_{n+1} = pathDensity (n+1)` and `c_{n+1} = trace (Uᵒ⁽ⁿ⁺¹⁾)` the cycle density.

The inner products `⟨pathIter j, complIter k⟩` then collapse to path densities by the **single
closed-form lemma**

```
pairing_pathIter_complIter_closed :
    ⟨pathIter j, complIter k⟩ = Σ_{i<k} (−1)ⁱ · mean(complIter (k−1−i)) · x_{j+i}  +  (−1)ᵏ · x_{j+k},
```

proved once by induction via `pairing_complIter_succ`. Consequently every `Cₘ` assembly
(`C5_integral`, `C7_integral`, `C9_path_integral`) reduces the necklace to a pure polynomial in the
path densities by the **same** uniform step

```lean
rw [complTrace_necklace hU (m-1)]
simp only [pairing_pathIter_complIter_closed hU, complMean_succ hU, complMean_zero,
           pathDensity_zero, pairing_pathIter_zero, Finset.sum_range_succ, Finset.sum_range_zero, …]
rw [hx1, …, hxₘ₋₁]; ring
```

after which `Φₘ ≥ 0` (the certificate) and `x_{m−1} − cₘ ≥ 0` (`edge_deletion_general`) finish by
linear arithmetic. The only per-cycle inputs are the cycle length, the path-density formulas `hxᵢ`,
and the SOS certificate. The exact polynomial identities are double-checked symbolically before
being committed to Lean: `verify_c5_moments.py`, `verify_c7_moments.py`, `verify_c7.py`,
`verify_necklace.py`.

## Axioms

`lake build` succeeds with **zero `sorry`**, and all results — including `C5_integral`,
`C7_integral`, `C7_integral_all`, `C9_path_integral` and the `W`-facing theorems — depend on **only**
Lean's three standard axioms `propext, Classical.choice, Quot.sound` (no extra axioms).
`CheckGraphon.lean` prints the full axiom trail.

## Not (yet) formalized

* **`C₉` for all densities.** The middle band `1/2 < p < 1003/2000` needs the spectral closure of
  `paper.tex` §6.2 (the sharp Razborov–Reiher triangle-density bound plus a spectral decomposition
  `t(Cₘ,W) = Σ λᵢᵐ`). The latter requires an operator/Hilbert–Schmidt layer — Mathlib has the
  compact self-adjoint spectral theorem but not the trace/moment identity — and is out of scope of
  the current integral-only design.
* **`C₁₁` is done on the high-density range `p ≥ 2/3`** (`OddCycleBound/C11.lean`): the complement
  defect `Φ₁₁ = L₁ + L₂ + L₃ + L₄ + 10 s₀⁵` is certified piecewise via the joint `(q, λ, …)`
  **Positivstellensatz** `K = σ₀ + q σ₁ + (1−3q)/3·… ` with `{1, q, 1/3−q, q(1/3−q)}` multipliers —
  `L₁` linear (`sos4`), `L₂` bivariate (`sos2var4`), `L₃` trivariate (`sos3var3` /
  `sos_sq_expand_3var`), `L₄`/`L₅` by Hankel `nlinarith`. The certificates are machine-generated
  by the exact-rational pipeline in `cert_scripts/` (CLARABEL SDP → rational LDL → `ring`-verified
  Lean), chunked to fit Lean's `ring`. The path-density recurrence is extended with
  `pathDensity_nine … _twelve`.
* **`C₁₃`.** Its decomposition `Φ₁₃ = L₁ + … + L₅ + 12 s₀⁶` is computed and `L₁` (degree-10 `P_q`,
  `sos5`) is certified, but the higher pieces need degree-8/6 kernels (`sos2var5`, a degree-3
  `sos3var`) whose expanded SOS forms × the square count overflow Lean's `ring` budget. **Low-rank
  rationalization is a confirmed dead end** (`cert_scripts/LOWRANK_FINDINGS.md`): rank-minimizing
  solves cut `C₁₃ L₂` from 95 to 14 squares *numerically*, but the low-rank face is on the PSD-cone
  boundary and fails rational rounding at every denominator (the Peyrl–Parrilo obstruction), so the
  rational certificate stays ~95 squares. The productive levers are **smaller coefficients**
  (kernel-aware rounding — the 300-digit integers are an artifact of LDL denominator accumulation +
  integer-clearing, not of the inequality's tightness) and **bespoke Hankel certificates** (few
  squares, tiny coefficients, like `cert11_L4`/`L5`).
* The all-densities versions (closing `1/2 < p < 2/3` for `C₁₁`, the analogous band for `C₁₃`, and
  the `C₉` middle band) additionally need the spectral/Razborov-triangle closure of the paper.
* The conditional results (regularity, the operator-theoretic universal bound, the variational
  structure) — explicitly out of scope.
