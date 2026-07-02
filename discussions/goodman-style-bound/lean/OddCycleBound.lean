import OddCycleBound.Main
import OddCycleBound.BoundsC5C7
import OddCycleBound.General.Necklace
import OddCycleBound.General.PathRecurrence
import OddCycleBound.General.SumOfSquares
import OddCycleBound.C9
import OddCycleBound.C11
import OddCycleBound.C13
import OddCycleBound.LowBand.CompactSpectral
import OddCycleBound.LowBand.L2Kernel
import OddCycleBound.LowBand.InfiniteSpectral
import OddCycleBound.LowBand.C9
import OddCycleBound.Conditional

/-!
# OddCycleBound — the odd-cycle Goodman-type bound, integral-grounded

The headline results, for a graphon `W` over a probability space with edge density `p = ∫∫W`
(`OddCycleBound/Main.lean`):

* `OddCycleBound.C5_bound` : `t(C₅, W) ≥ p⁵ − p(1−p)⁴`,
* `OddCycleBound.C7_bound` : `t(C₇, W) ≥ p⁷ − p(1−p)⁶`,
* `OddCycleBound.C9_path_bound` : `t(C₉, W) ≥ p⁹ − p(1−p)⁸` for `p ≥ 1003/2000`.

The first two hold for all densities, for any graphon `W` defined as an integral kernel over an
abstract probability space (`IsGraphon W μ`).  The *only* trusted item is the integral definition
of homomorphism density; Lemma 2.4, the cyclic inclusion–exclusion (necklace) identity, the
edge-deletion bound, and the SOS positivity certificates are all proved inside Lean.

## Module layout

Foundations and the complement-path `C₅`/`C₇`/`C₉` cases:

```
Graphon  →  PathDensity  →  { Kernel, Certificate }  →  Cycle  →  Necklace  →  BoundsC5C7  →  Main
```

* `Graphon`      — the graphon `IsGraphon`, the integral operator `kernelOp`, and the spectral
                   moments (`degCentered`, `compress`, `compressIter`, `specMoment`).
* `PathDensity`  — Lemma 2.4: the explicit path densities `pathDensity 2 … 6`.
* `Kernel`       — kernel-composition algebra: `comp`, `onesKernel`, `compPow`, `trace`, the cut
                   lemma, associativity, cyclic trace invariance.
* `Certificate`  — the Φ₅/Φ₇ positivity certificates in the spectral moments.
* `Cycle`        — the cycle density `cycleDensity` and the edge-deletion bound.
* `Necklace`     — the necklace identity (cyclic inclusion–exclusion) and its recursions.
* `BoundsC5C7`   — assembles the necklace + certificate into `C5_integral` / `C7_integral`.
* `Main`         — the `W`-facing headline theorems.

General-`m` machinery (reused for `C₉` and future cases), under `General/`:

* `General.Necklace`      — the telescoped general-`m` necklace identity.
* `General.PathRecurrence`— the general path-density recurrence (and `pathDensity 7, 8`).
* `General.SumOfSquares`  — the general Hankel sum-of-squares engine.

`C9` then builds the Φ₉ certificate and `C9_path_integral` on top of these.

The file `LowBand.FiniteSpectral` is deliberately not imported here.  It is a
finite-dimensional sanity check for spectral algebra only; the graphon-facing
low-band C9 interface in `LowBand.InfiniteSpectral` is countable/compact-action
based and does not assume finitely many non-zero eigenvalues.
-/
