/-
# The odd-cycle Goodman bound — certificate-free consolidation

Target theorem: for every graphon `W` with edge density `p` and every odd `m ≥ 3`,
`t(C_m, W) ≥ p^m − p(1−p)^{m−1}`.

Source of mathematical truth: `../paper_new_region2_v2.tex`. Consolidation plan and
provenance: `../COMPLETE_LEAN_PLAN.md`, `RENAMING.md`.

Layout:
* foundations — `Graphon`, `PathDensity`, `Kernel`, `MomentSOS`, `Cycle`, `Necklace`
* `General/` — general-`m` necklace, path recurrence, sum-of-squares engine
* short cycles `m = 3, 5, 7` — `BasicBounds`, `BoundsC5C7` (paper §2)
* `Spectral/` — the graphon `L²` operator layer (compact self-adjoint theory)
* `DenseRegion/` — the region `p ≥ 2/3`, all odd `m` (paper §4); the analytic
  endgame `DenseRegion/Diagonal/` (beta formula → gamma smoothing → gamma moment
  inequality) is Phase D of the plan and is not yet present
* `IntermediateRegion/` — the region `1/2 < p < 2/3`, odd `m ≥ 9` (paper §5–§9);
  the scalar endgame (`Chart`, `QuadraticBranch`, `LinearBranch`, `Bernstein`) is
  Phase R of the plan and is not yet present
* `Fisher/` — Fisher's triangle-density lower bound and its graphon bridge, ending
  in `triangleDensityLowerBound_twoThirds : TriangleDensityLowerBoundUpTo (2/3)`.
  Insurance for unconditionality: if the intermediate-region floor `m ≥ 9` stalls,
  this discharges the triangle-density hypothesis of the archived conditional route.
  (The optional `TraceMonoid` branch of the original `fisher_lean`, which contains a
  `sorry`, is deliberately NOT transferred.)
-/

-- Foundations
import OddCycleBound.Graphon
import OddCycleBound.PathDensity
import OddCycleBound.Kernel
import OddCycleBound.MomentSOS
import OddCycleBound.Cycle
import OddCycleBound.Necklace
import OddCycleBound.BasicBounds
import OddCycleBound.BoundsC5C7
import OddCycleBound.ShortCycles

-- General-m engine
import OddCycleBound.General.Necklace
import OddCycleBound.General.PathRecurrence
import OddCycleBound.General.SumOfSquares

-- Spectral operator layer
import OddCycleBound.Spectral.GraphonL2Operator
import OddCycleBound.Spectral.CompactGraphonOperator
import OddCycleBound.Spectral.C9Scalar
import OddCycleBound.Spectral.C9Spectral

-- Dense region (p ≥ 2/3), paper §4
import OddCycleBound.DenseRegion.SymmetricPoly
import OddCycleBound.DenseRegion.MixtureIntegral
import OddCycleBound.DenseRegion.Expansion
import OddCycleBound.DenseRegion.GraphonReduction
import OddCycleBound.DenseRegion.MomentExpansion
import OddCycleBound.DenseRegion.DefectIdentity
import OddCycleBound.DenseRegion.DefectPowerSeries
import OddCycleBound.DenseRegion.FiniteRank
import OddCycleBound.DenseRegion.BlockPower
import OddCycleBound.DenseRegion.AtomicMomentRepresentation
import OddCycleBound.DenseRegion.AtomicSpectral
import OddCycleBound.DenseRegion.KrylovCompression
import OddCycleBound.DenseRegion.GraphonKrylovBridge
import OddCycleBound.DenseRegion.ExpansionAssembly
import OddCycleBound.DenseRegion.RhoLemma
import OddCycleBound.DenseRegion.KernelForm
import OddCycleBound.DenseRegion.KernelImproper
import OddCycleBound.DenseRegion.KernelIntegrable
-- Dense region, Phase D analytic endgame (paper §4 beta/gamma route)
import OddCycleBound.DenseRegion.Diagonal.RhoIdentities
import OddCycleBound.DenseRegion.Diagonal.GammaMoment
import OddCycleBound.DenseRegion.Diagonal.ShiftedGammaPositive
import OddCycleBound.DenseRegion.Diagonal.Positivity
import OddCycleBound.DenseRegion.Diagonal.GammaSmoothing
import OddCycleBound.DenseRegion.Diagonal.LogRatioBound
import OddCycleBound.DenseRegion.Diagonal.GammaMomentProof
import OddCycleBound.DenseRegion.Diagonal.DenseRegionEndgame

-- Intermediate region (1/2 < p < 2/3), paper §5–§6 operator side
import OddCycleBound.IntermediateRegion.OneSidedPolynomial
import OddCycleBound.IntermediateRegion.CenteredOperator
import OddCycleBound.IntermediateRegion.CenteredKernel
import OddCycleBound.IntermediateRegion.BoundedKernelL2
import OddCycleBound.IntermediateRegion.HilbertSchmidtBound
import OddCycleBound.IntermediateRegion.SpectralFoundation
import OddCycleBound.IntermediateRegion.TracePowers
import OddCycleBound.IntermediateRegion.KernelBlockDecomposition
import OddCycleBound.IntermediateRegion.FormalShift
import OddCycleBound.IntermediateRegion.GraphonShiftIdentity
import OddCycleBound.IntermediateRegion.LeadingEigenvalue
import OddCycleBound.IntermediateRegion.VarianceLowerBound
import OddCycleBound.IntermediateRegion.SafeSubspace
import OddCycleBound.IntermediateRegion.CouplingBounds
import OddCycleBound.IntermediateRegion.LeadingEigenvalueTrace
import OddCycleBound.IntermediateRegion.DirectedKernel
import OddCycleBound.IntermediateRegion.ShiftSpectral
import OddCycleBound.IntermediateRegion.DefectLowerBound
import OddCycleBound.IntermediateRegion.EnvelopeBound

-- Fisher's triangle bound (unconditionality insurance)
import OddCycleBound.Fisher.Interface
import OddCycleBound.Fisher.CliqueCounts
import OddCycleBound.Fisher.DependencePolynomial
import OddCycleBound.Fisher.SmallestRoot
import OddCycleBound.Fisher.ThirdTruncation
import OddCycleBound.Fisher.Spectral
import OddCycleBound.Fisher.CubicOpt
import OddCycleBound.Fisher.FiniteTheorem
import OddCycleBound.Fisher.GraphonContinuity
import OddCycleBound.Fisher.FiniteGraphon
import OddCycleBound.Fisher.GraphonRounding
import OddCycleBound.Fisher.GraphonSampling
import OddCycleBound.Fisher.GraphonScaling
import OddCycleBound.Fisher.GraphonBridge

-- Intermediate region, scalar infrastructure
import OddCycleBound.IntermediateRegion.Scalar.Definitions
import OddCycleBound.IntermediateRegion.Scalar.EigenvalueAlgebra
import OddCycleBound.IntermediateRegion.Scalar.Envelope
import OddCycleBound.IntermediateRegion.Scalar.ShapeElimination
import OddCycleBound.IntermediateRegion.Scalar.ParameterFacts
import OddCycleBound.IntermediateRegion.Scalar.Coordinates
import OddCycleBound.IntermediateRegion.Scalar.Elementary
import OddCycleBound.IntermediateRegion.Scalar.ThreeGeometric
import OddCycleBound.IntermediateRegion.Scalar.EnvelopeEstimates
import OddCycleBound.IntermediateRegion.Scalar.Chart
import OddCycleBound.IntermediateRegion.Bernstein
import OddCycleBound.IntermediateRegion.QuadraticBranch
import OddCycleBound.IntermediateRegion.LinearBranch
import OddCycleBound.IntermediateRegion.LinearCore
import OddCycleBound.IntermediateRegion.LinearBroad
import OddCycleBound.IntermediateRegion.LinearHighZeta
import OddCycleBound.IntermediateRegion.LinearN7
import OddCycleBound.IntermediateRegion.LinearN7Mid
import OddCycleBound.IntermediateRegion.JGrowth
import OddCycleBound.IntermediateRegion.LinearLowZeta
import OddCycleBound.IntermediateRegion.ScalarTarget
import OddCycleBound.IntermediateRegion.IntermediateAssembly
