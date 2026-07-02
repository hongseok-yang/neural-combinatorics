import OddCycleBound.BoundsC5C7
import OddCycleBound.General.Necklace
import OddCycleBound.General.PathRecurrence
import OddCycleBound.General.SumOfSquares
import OddCycleBound.C9
import OddCycleBound.C11
import OddCycleBound.C13
import OddCycleBound.LowBand.CompactGraphonOperator
import OddCycleBound.LowBand.GraphonL2Operator
import OddCycleBound.LowBand.C9Spectral
import OddCycleBound.LowBand.C9Scalar
import OddCycleBound.LowBand.C11Scalar
import OddCycleBound.LowBand.C13Scalar
import OddCycleBound.Conditional

/-!
# OddCycleBound ??the odd-cycle Goodman-type bound, integral-grounded

The headline results, for a graphon `W` over a probability space with edge density `p = ?モ닽W`
(`OddCycleBound/Main.lean`):

* `OddCycleBound.C5_bound` : `t(C?? W) ??p????p(1?뭦)??,
* `OddCycleBound.C7_bound` : `t(C?? W) ??p????p(1?뭦)??,
* `OddCycleBound.C9_path_bound` : `t(C?? W) ??p????p(1?뭦)?? for `p ??1003/2000`.

The first two hold for all densities, for any graphon `W` defined as an integral kernel over an
abstract probability space (`IsGraphon W 關`).  The *only* trusted item is the integral definition
of homomorphism density; Lemma 2.4, the cyclic inclusion?밻xclusion (necklace) identity, the
edge-deletion bound, and the SOS positivity certificates are all proved inside Lean.

## Module layout

Foundations and the complement-path `C??/`C??/`C?? cases:

```
Graphon  ?? PathDensity  ?? { Kernel, Certificate }  ?? Cycle  ?? Necklace  ?? BoundsC5C7  ?? Main
```

* `Graphon`      ??the graphon `IsGraphon`, the integral operator `kernelOp`, and the spectral
                   moments (`degCentered`, `compress`, `compressIter`, `specMoment`).
* `PathDensity`  ??Lemma 2.4: the explicit path densities `pathDensity 2 ??6`.
* `Kernel`       ??kernel-composition algebra: `comp`, `onesKernel`, `compPow`, `trace`, the cut
                   lemma, associativity, cyclic trace invariance.
* `Certificate`  ??the 過??過??positivity certificates in the spectral moments.
* `Cycle`        ??the cycle density `cycleDensity` and the edge-deletion bound.
* `Necklace`     ??the necklace identity (cyclic inclusion?밻xclusion) and its recursions.
* `BoundsC5C7`   ??assembles the necklace + certificate into `C5_integral` / `C7_integral`.
* `Main`         ??the `W`-facing headline theorems.

General-`m` machinery (reused for `C?? and future cases), under `General/`:

* `General.Necklace`      ??the telescoped general-`m` necklace identity.
* `General.PathRecurrence`??the general path-density recurrence (and `pathDensity 7, 8`).
* `General.SumOfSquares`  ??the general Hankel sum-of-squares engine.

`C9` then builds the 過??certificate and `C9_path_integral` on top of these.

Low-band C9 lives under `LowBand/`:
* `LowBand.GraphonL2Operator` formalizes the canonical graphon `L²` operator.
* `LowBand.CompactGraphonOperator` records the compact self-adjoint spectral
  interfaces used by the graphon operator.
* `LowBand.C9Scalar` contains the scalar C9 low-band inequalities.
* `LowBand.C9Spectral` assembles the countable/compact-action C9 spectral data;
  it does not assume finitely many non-zero graphon eigenvalues.
-/
