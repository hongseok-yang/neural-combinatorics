/-
# OddCycleBound (high-density project) — root aggregator

This is the **high-density-only** formalization project: the target is the single theorem

> for every graphon `W` with `p = t(K₂,W) ≥ 2/3` and every odd `m ≥ 3`,
> `t(C_m, W) ≥ p^m − p(1−p)^{m-1}`     (`paper_new.tex` §`sec:high-density-theorem`).

It deliberately does **not** carry the per-cycle certificate machinery (`C9`/`C11`/`C13`,
`BoundsC5C7`, the `LowBand` spectral closures, `Conditional`, `Main`) from the sibling `../lean`
project: at `p ≥ 2/3` the high-density theorem subsumes `C5`–`C13` as instances, so that whole
certificate zoo is dead weight here.

What is imported below is the **reusable foundation only** (see `HIGH_DENSITY_FORMALIZATION_PLAN.md`
§2): the integral graphon definitions, the kernel/trace algebra, path densities and their general
recurrence, the necklace identity (the general-`m` cyclic-trace *precedent* for the from-scratch
two-sided identity), and the compact self-adjoint `L²` operator layer that the moment route builds on.

The high-density argument itself (milestones M0–M7 in the plan) is **not yet written** — that is the
work. Add it under a new `OddCycleBound/HighDensity/` subtree and extend the imports here.
-/

-- Integral foundations and kernel/trace algebra.
import OddCycleBound.Graphon
import OddCycleBound.PathDensity
import OddCycleBound.Kernel
import OddCycleBound.Certificate
import OddCycleBound.Cycle
import OddCycleBound.Necklace

-- General-`m` machinery: path recurrence, necklace identity, moment SOS engine.
import OddCycleBound.General.Necklace
import OddCycleBound.General.PathRecurrence
import OddCycleBound.General.SumOfSquares

-- Compact self-adjoint graphon `L²` operator + eigen-expansion (moment-route base).
import OddCycleBound.LowBand.GraphonL2Operator
import OddCycleBound.LowBand.CompactGraphonOperator

-- High-density theorem (milestones M0–M7). M0a: finite-rank two-sided identity (length 3) — done.
import OddCycleBound.HighDensity.FiniteRank
-- General-`m` block-power recursion (toward the necklace decomposition of Tr(blockOp^m)).
import OddCycleBound.HighDensity.BlockPower
-- M0c (direct): graphon reduction of the target to `Φ_m ≥ 0` (necklace-sum positivity).
import OddCycleBound.HighDensity.GraphonReduction
-- M1 (Thm expansion), step 0: moment-friendly rewrite of neckSum (B_{1-W}=T_W).
import OddCycleBound.HighDensity.MomentExpansion
-- M1 foundation: complete homogeneous symmetric polynomial layer (h_d, convolution identity).
import OddCycleBound.HighDensity.SymmetricPoly
-- M3 foundation: sign structure of ρ (reflection nonnegativity, left window).
import OddCycleBound.HighDensity.RhoLemma
-- M1 Stage 2a: the natural Beta integral (foundation for the Dirichlet mixture positivity transfer).
import OddCycleBound.HighDensity.MixtureIntegral
-- M2/M3: eq:G-form (finite Beta(r,r) form of diagKernel) + thm:pointwise (regimes 2r≥n and ℓ≤0).
import OddCycleBound.HighDensity.KernelForm
-- M5/M6 gateway: prop:kernel, the improper ∫₀^∞ kernel form (via x=ℓ/(ℓ+s) substitution).
import OddCycleBound.HighDensity.KernelImproper
-- M5: thm:r1 (r=1 diagonal positivity) — base case m=5 + the prop:kernel reduction scaffold.
import OddCycleBound.HighDensity.KernelR1
-- M5/M6 shared machinery (A): integrability of the kernel integrand on (0,∞).
import OddCycleBound.HighDensity.KernelIntegrable
-- M5/M6 shared machinery (D core): the abstract weighted-reflection inequality.
import OddCycleBound.HighDensity.KernelReflect
-- M3/M5: thm:ibp (r=1) + full thm:r1 assembly (all lengths, r=1 diagonal positivity).
import OddCycleBound.HighDensity.KernelIBP
-- M6: residual strip (m≥63 tail) — lem:threshold (H(b) ≤ 2/5).
import OddCycleBound.HighDensity.M6Strip
-- M6: residual strip (m≥63 tail) — lem:right-reflection (θ≥1/6, ℓ>2/5) assembly.
import OddCycleBound.HighDensity.M6Reflection
-- M6: residual strip — lem:left-estimate machinery (tail-D/tail-S) + reduction to app:constants.
import OddCycleBound.HighDensity.M6LeftEstimate
-- Stage C/D: diagonal-kernel case assembly (prop:remaining / thm:main case split).
import OddCycleBound.HighDensity.StripAssembly
-- Stage D: app:constants m≥500 tail arithmetic (eq:constant-A), isolating the B₀ rpow bound.
import OddCycleBound.HighDensity.AppConstants
-- Stage D: app:constants eq:constant-A rpow factor bound B₀(θ) ≥ 201/200 (derivative/monotone route).
import OddCycleBound.HighDensity.AppConstantsB0
-- Stage D: app:constants eq:constant-A m≥500 uniform tail (P·B₀ glue: constA_m500).
import OddCycleBound.HighDensity.AppConstantsTail
-- M6: residual-strip eq:tail-ratio scalar factor bounds (eq:tail-A/B, rpow-free building blocks).
import OddCycleBound.HighDensity.M6TailFactors
-- M6: residual-strip eq:tail-ratio bridge — c_n bound + power-lifted factor bounds (rpow).
import OddCycleBound.HighDensity.M6TailRatio
