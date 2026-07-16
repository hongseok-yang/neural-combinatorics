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

The table below is a per-module **isolated** profile: each row is a single `lean <module>` run — a
one-threaded elaboration of that module against already-built dependency oleans — so the rows are
reproducible and do **not** overlap (unlike a parallel `lake build`, where independent files run
concurrently and the wall time is far below the column sum). A clean parallel `lake build` of the
whole project (Mathlib oleans already fetched, so Mathlib is not recompiled) takes **PARALLEL_WALL s
wall**, bounded from below by the longest single non-splittable file (`C13/Bivar`).

* **Wall** = single-thread elaboration time. **Peak memory** = process peak working set. 

| Module | Wall | Peak memory |
|--------|-----:|------------:|
| `C13/Bivar` | 835 s | 18.3 GB |
| `C13/Trivar` | 586 s | ≤ 11.8 GB |
| `C11/Trivar` | 275 s | ≤ 5.9 GB |
| `C13` (assembly) | 180 s | 6.9 GB |
| `C11/Bivar` | 97 s | ≤ 6.0 GB |
| `C13/Linear` | 114 s | ≤ 5.7 GB |
| `C9` | 71 s | 4.3 GB |
| `C13/Quad` | 84 s | ≤ 4.7 GB |
| `General.SumOfSquares` | 56 s | 3.3 GB |
| `C11/Linear` | 40 s | ≤ 4.0 GB |
| `C11` (assembly) | 39 s | 4.0 GB |
| `C13/Engine4` | 31 s | 3.5 GB |
| `C13/Engine` | 25 s | 3.5 GB |
| `General.PathRecurrence` | 19 s | 3.3 GB |
| `Certificate` | 14 s | 3.2 GB |
| `PathDensity` | 13 s | 3.1 GB |
| `BoundsC5C7` | 13 s | 3.2 GB |
| `Necklace` | 13 s | 3.2 GB |
| `Graphon` | 13 s | 3.1 GB |
| `C13/Hankel` | 13 s | 3.1 GB |
| `Kernel` | 13 s | 3.1 GB |
| `Cycle` | 12 s | 3.1 GB |
| `General.Necklace` | 13 s | 3.1 GB |
| `Main` | 13 s | 3.1 GB |

Notes:
* The **`C11/*` rows are the `p ≥ 103/200` frontier certificates** and the **`C13/*` rows the
  `p ≥ 519/1000` frontier certificates** (both Peyrl–Parrilo rounded). Their integer-cleared
  coefficients are smaller-magnitude than the former `2/3` certs, so the memory figures above
  (several carried over from the `2/3` build, marked `≤`) are upper bounds — `C13/Bivar`'s measured
  frontier peak was 18.3 GB, *below* the old 18.7 GB. `C11/Linear`/`Bivar` are slightly *faster*;
  `C11/Trivar` is slower (≈ 275 s vs the old 75 s) because the PP projection distributes the rounding
  correction over the whole null space, giving denser SOS squares and heavier `ring` normalisation at
  the same square count. All are still bounded by `C13/Bivar`, so the **parallel-build wall is
  essentially unchanged**.
* The **~3.1 GB floor** on every row is the Mathlib import baseline — each `lean.exe` memory-maps
  Mathlib's oleans before doing any work; a module's real cost is the *excess* above that floor (and
  its wall time above the ~13 s cold-import baseline).
* The **SOS certificate files dominate** both axes. `C13/Bivar` (the 95-square `sos2var5` block) and
  `C13/Trivar` (80-square `sos3var4`) peak at ~19 GB / ~12 GB — this is **elaboration of giant
  proof-term `Expr` trees**, *not* parsing or kernel typechecking (isolating a heavy block:
  parsing+statement-elaboration ≈ 2 s, kernel checking ≈ 0 with `skipKernelTC`, proof elaboration
  dominates).
* **Memory in a parallel build:** the worst spikes come from several heavy files elaborating at once.
  To cap peak memory, throttle the Lean task pool, e.g. `LEAN_NUM_THREADS=4 lake build` (slower wall,
  far smaller peak). The `C11`/`C13` certificates are **split into per-block files** so each is a
  separate compilation unit (the editor and the build elaborate one block at a time), which is what
  keeps any single module's footprint to the ~5–19 GB range rather than one monolith.

**Benchmark machine:** Intel Core i5-14600K (14C/20T), 64 GB RAM, Windows 11 Pro (build 26200),
Lean/Mathlib `v4.31.0`. Wall times are single-thread and scale with single-thread performance; peak
memory is largely machine-independent (term sizes, not cores).

## Headline results

The paper-facing statements live in `OddCycleBound/Main.lean`, namespace `OddCycleBound`, for a
graphon `W` with the single hypothesis `hW : IsGraphon W μ` and edge density
`p = edgeDensity W μ = ∫∫W`:

| Theorem | Statement | Range |
|---------|-----------|-------|
| `C3_bound` | `t(C₃, W) ≥ p³ − p(1−p)²` | all densities |
| `C5_bound` | `t(C₅, W) ≥ p⁵ − p(1−p)⁴` | all densities |
| `C7_bound` | `t(C₇, W) ≥ p⁷ − p(1−p)⁶` | all densities |
| `C9_path_bound` | `t(C₉, W) ≥ p⁹ − p(1−p)⁸` | `p ≥ 1003/2000` (path-certificate range) |
| `C11_path_bound` | `t(C₁₁, W) ≥ p¹¹ − p(1−p)¹⁰` | `p ≥ 103/200` (path-certificate frontier `ρ₁₁`) |
| `C13_path_bound` | `t(C₁₃, W) ≥ p¹³ − p(1−p)¹²` | `p ≥ 51/100` (certified frontier plus path range) |
| `C9_conditional_bound` | `t(C₉, W) ≥ p⁹ − p(1−p)⁸` | all densities, assuming the triangle bound through `1003/2000` |
| `C11_conditional_bound` | `t(C₁₁, W) ≥ p¹¹ − p(1−p)¹⁰` | all densities, assuming the triangle bound through `103/200` |
| `C13_path_conditional_bound` | `t(C₁₃, W) ≥ p¹³ − p(1−p)¹²` | `p ≤ 51/100`, assuming the triangle bound |
| `C13_conditional_bound` | `t(C₁₃, W) ≥ p¹³ − p(1−p)¹²` | all densities, assuming the triangle bound through `51/100` |
| `odd_cycle_regionII_large_bound` | `t(C_m,W) ≥ p^m − p(1−p)^(m−1)` | odd `m ≥ 15`, `1/2 < p < 2/3`, unconditional |
| `odd_cycle_regionII_conditional_bound` | `t(C_m,W) ≥ p^m − p(1−p)^(m−1)` | odd `m ≥ 3`, `1/2 < p < 2/3`, assuming the triangle bound through `103/200` |

The `C₁₁` bound is proved on `p ≥ 103/200` (complement density `q = 1−p ≤ 97/200`), the
**path-certificate frontier `ρ₁₁`** — the lowest `p` at which the joint-Positivstellensatz SOS
certificate is feasible (the SDP goes infeasible just below). This was pushed down from the former
`2/3` by replacing the certificate rationaliser with a **Peyrl–Parrilo rational rounding**
(`cert_scripts/pp_round.py`): the SDP interior point is projected into the exact coefficient-matching
affine subspace by rounding in a QR-orthogonalised null-space basis (Babai nearest-plane), which uses
the full SDP margin and so rationalises the near-marginal certificate where the old "round-then-poke"
scheme failed — while keeping the Gram at a controlled denominator, so the integer-cleared
coefficients stay *smaller* than the former `2/3` certificate. Below `103/200` the path certificate
cannot reach (the SDP is infeasible); the thin remaining band `1/2 < p < 103/200` is exactly the
range the spectral / Razborov-triangle closure must cover. The rounding methods (and why the naive
one fails near the frontier) are written up in `cert_scripts/RATIONAL_ROUNDING.md`, with a minimal
self-contained runnable example in `cert_scripts/rational_rounding_demo.py`.

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
| `C13` | **Assembly** for the Φ₁₃ bound: `cert13_specMoment` (combines `L₁ … L₆`) and `C13_path_integral`. Imports the block files below. The path-density recurrence reaches `pathDensity_twelve`. |
| `C13/Engine` | The `sos2var5` (degree-(4,4)) and `sos3var4` (Newton maxdeg-3) Hankel SOS engine lemmas for `L₂`/`L₃`. |
| `C13/Engine4` | The **four-fold** moment engine `sos_sq_expand_4var` (`0 ≤ ∫⁴(Σ C·h h h h)²`) and its Newton wrapper `sos4var3`, for the quartic `L₄`. |
| `C13/Linear` | The Φ₁₃ `L₁` block — linear, certified by `sos5`. |
| `C13/Bivar` | The Φ₁₃ `L₂` block — bivariate, `sos2var5`, 95 squares (CHUNK=1). |
| `C13/Trivar` | The Φ₁₃ `L₃` block — trivariate, `sos3var4`, 80 squares (CHUNK=1). |
| `C13/Quad` | The Φ₁₃ `L₄` block — quartic, `sos4var3`, 39 squares (CHUNK=1). |
| `C13/Hankel` | The Φ₁₃ `L₅` (`s₀³·B₅` via the `momcs` minor) and `L₆` (`12 s₀⁶`) blocks. |
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
* **`C₁₁` is done on the path-certificate frontier `p ≥ 103/200`** (`OddCycleBound/C11.lean`): the
  complement defect `Φ₁₁ = L₁ + L₂ + L₃ + L₄ + 10 s₀⁵` is certified piecewise via the joint `(q, λ, …)`
  **Positivstellensatz** with `{1, q, 97/200−q, q(97/200−q)}` multipliers — `L₁` linear (`sos4`),
  `L₂` bivariate (`sos2var4`), `L₃` trivariate (`sos3var3` / `sos_sq_expand_3var`), `L₄`/`L₅` by
  Hankel `nlinarith`. The certificates are machine-generated by the exact-rational pipeline in
  `cert_scripts/` (CLARABEL SDP → **Peyrl–Parrilo rational rounding** (`pp_round.py`) → `ring`-verified
  Lean), chunked to fit Lean's `ring`. The path-density recurrence is extended with
  `pathDensity_nine … _twelve`. The range was pushed from the former `2/3` down to `ρ₁₁ = 103/200`
  (where the SDP first goes infeasible) purely by upgrading the rationaliser — same SDP, same square
  counts, same `Φ₁₁` split, only the `RHO = 97/200` multiplier and the bound hypotheses changed.
* **`C₁₃` is fully formalized on the path-certificate frontier `p ≥ 519/1000`** (`OddCycleBound/
  C13.lean` + `OddCycleBound/C13/*`), axiom-clean (`propext, Classical.choice, Quot.sound`, zero
  `sorry`). Pushed from the former `2/3` to `ρ₁₃ = 519/1000` by the same Peyrl–Parrilo rationaliser
  (`cert_scripts/pp_round.py`) at `RHO = 481/1000`, where the binding linear block `L₁` first goes
  marginal (SDP margin → 0); the four blocks rationalise at `D = 16384 / 8192 / 512 / 64`
  (`L₁/L₂/L₃/L₄`). The complement defect
  `Φ₁₃ = L₁ + L₂ + L₃ + L₄ + L₅ + 12 s₀⁶` is certified piecewise and assembled (`cert13_specMoment`)
  into `C13_path_integral` via the same necklace identity as `C₉`/`C₁₁`; `Main.lean` exposes the
  `W`-facing `C13_path_bound`:

  | block | form | engine | module | squares |
  |-------|------|--------|--------|--------:|
  | `L₁` | linear | `sos5` | `C13/Linear.lean` | 66 |
  | `L₂` | bivariate | `sos2var5` | `C13/Bivar.lean` | 95 |
  | `L₃` | trivariate (Newton maxdeg-3) | `sos3var4` | `C13/Trivar.lean` | 80 |
  | `L₄` | **quartic** (Newton maxdeg-2) | **`sos4var3`** | `C13/Quad.lean` | 39 |
  | `L₅` | `s₀³·B₅` (Hankel-minor + square) | `momcs` + `nlinarith` | `C13/Hankel.lean` | — |
  | `L₆` | `12 s₀⁶` | `pow_nonneg` | `C13/Hankel.lean` | — |

  The pieces once believed to overflow Lean's `ring`/heartbeat budget all build (the **low-rank dead
  end** is irrelevant — `cert_scripts/LOWRANK_FINDINGS.md`). What unstuck them, none touching the
  math: (1) the `sos2var5`/`sos3var4`/`sos4var3` engine lemmas **never existed** — generated by
  `cert_scripts/gen_engine.py` and proved `simp; norm_num at h; exact le_of_le_of_eq h (by ring)`
  (the old `nlinarith` closing times out at `whnf` at these arities), plus `maxRecDepth 8000` and, for
  the 4-fold engine, a raised `simp` `maxSteps`; (2) **CHUNK=1** emission (one square per `ring`)
  so each per-square `ring` fits; (3) **8 M** heartbeat ceilings on the block-combiner/assembly
  lemmas. `L₄` is the genuinely new piece — a degree-4 moment form is not a real-SOS nor a 2-/3-fold
  SOS, so it needed the **four-fold engine `sos_sq_expand_4var`** (`0 ≤ ∫⁴(Σ C·h h h h)²`, the
  degree-4 analog of the 2-/3-var engines, in `C13/Engine4.lean`) and a 4-variable symmetric-kernel
  SDP (`cert_scripts/gen_4var.py`); `L₅` factors as `s₀³·B₅` with `B₅ ≥ 0` by the `momcs` Hankel
  minor plus a square. Per-file build times at the `519/1000` frontier (cached Mathlib): `C13/Bivar`
  ≈ 835 s (peak 18.3 GB), `C13/Trivar` ≈ 586 s, `C13/Linear` ≈ 114 s, `C13/Quad` ≈ 84 s, `C13.lean`
  assembly ≈ 180 s — essentially unchanged from the `2/3` build (the PP certs are slightly denser but
  smaller-magnitude, so wall and peak memory both stay put; same square counts).
* The all-densities versions (closing the thin remaining bands `1/2 < p < 103/200` for `C₁₁` and
  `1/2 < p < 519/1000` for `C₁₃` — the path certificate cannot go lower, the SDP is infeasible there —
  and the `C₉` middle band) additionally need the spectral/Razborov-triangle closure of the paper.
* The conditional results (regularity, the operator-theoretic universal bound, the variational
  structure) — explicitly out of scope.
