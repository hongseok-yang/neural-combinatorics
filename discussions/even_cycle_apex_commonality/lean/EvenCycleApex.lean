-- Foundation: copied from `cycle_commonality` (plan D7), with provenance headers.
import EvenCycleApex.Foundation.Graphon
import EvenCycleApex.Foundation.Kernel
import EvenCycleApex.Foundation.GraphonL2Operator
import EvenCycleApex.Foundation.Defs
import EvenCycleApex.Foundation.Fubini
import EvenCycleApex.Foundation.Continuity
import EvenCycleApex.Foundation.StepApprox
import EvenCycleApex.Foundation.Factored
import EvenCycleApex.Foundation.Spectral.EigenSystem
import EvenCycleApex.Foundation.Model.StepModel
import EvenCycleApex.Foundation.FiniteBridge
-- M1: graph densities on an arbitrary probability space.
import EvenCycleApex.Graph.Apex
import EvenCycleApex.Graph.HomDensity
import EvenCycleApex.Graph.PairMarginal
import EvenCycleApex.Graph.Lipschitz
import EvenCycleApex.Graph.DensityAlgebra
-- M2: the weighted finite host.
import EvenCycleApex.Host.Defs
import EvenCycleApex.Host.Bridge
import EvenCycleApex.Host.EdgeDensity
import EvenCycleApex.Host.Matrix
import EvenCycleApex.Host.Spectral
import EvenCycleApex.Host.Scalars
import EvenCycleApex.Host.ScalarBounds
import EvenCycleApex.Host.EvenCycle
import EvenCycleApex.Host.Regression
-- M3: conditional second spectral moments.
import EvenCycleApex.Graph.ApexEdges
import EvenCycleApex.Conditional.Defs
import EvenCycleApex.Conditional.Trace
import EvenCycleApex.Conditional.Diamond
-- M4: moment inequalities, and one apex end to end.
import EvenCycleApex.Moments.Basic
import EvenCycleApex.Moments.ApexLifting
import EvenCycleApex.Finite.OneApex
-- M5: two apices, certificate-free (plan D10).
import EvenCycleApex.Finite.TwoApex
import EvenCycleApex.Transfer
-- M6: certificate language and soundness (encoding of DEVIATIONS X3).
import EvenCycleApex.Certificate.Mask
import EvenCycleApex.Certificate.Rooted
import EvenCycleApex.Certificate.Accum
import EvenCycleApex.Certificate.LDL
import EvenCycleApex.Certificate.Checker
import EvenCycleApex.Certificate.Targets
import EvenCycleApex.Certificate.Schema
import EvenCycleApex.Certificate.Sound
-- M7: kernel-checked certificates (decide +kernel).
import EvenCycleApex.Certificate.Groups
import EvenCycleApex.Certificate.Checks.Witness
import EvenCycleApex.Certificate.Checks.MeanThree
import EvenCycleApex.Certificate.Checks.Neg
import EvenCycleApex.Certificate.Checks.Pos
import EvenCycleApex.Certificate.Main
-- M8: three apices.
import EvenCycleApex.Finite.ThreeApexGraphs
import EvenCycleApex.Finite.ThreeApexMoments
import EvenCycleApex.Finite.ThreeApexScalars
import EvenCycleApex.Finite.ThreeApex
-- M9: every apex number; headlines H1 and H3.
import EvenCycleApex.Finite.AllApices
import EvenCycleApex.Main
-- M10: equality; headline H2.
import EvenCycleApex.Equality.Spectral
import EvenCycleApex.Equality.Functionals
import EvenCycleApex.Equality.CZero
import EvenCycleApex.Equality.Main
-- M11: the blueprint's declaration names (plan §6).
import EvenCycleApex.BlueprintNames
