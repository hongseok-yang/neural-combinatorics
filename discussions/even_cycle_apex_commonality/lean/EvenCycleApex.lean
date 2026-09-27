-- Foundation: copied from `cycle_commonality` (plan D7), with provenance headers.
import EvenCycleApex.Foundation.Graphon
import EvenCycleApex.Foundation.PathDensity
import EvenCycleApex.Foundation.Kernel
import EvenCycleApex.Foundation.GraphonL2Operator
import EvenCycleApex.Foundation.Defs
import EvenCycleApex.Foundation.Fubini
import EvenCycleApex.Foundation.Continuity
import EvenCycleApex.Foundation.StepApprox
import EvenCycleApex.Foundation.Factored
import EvenCycleApex.Foundation.StepDensity
import EvenCycleApex.Foundation.Spectral.Rayleigh
import EvenCycleApex.Foundation.Spectral.EigenSystem
import EvenCycleApex.Foundation.Spectral.Interlace
import EvenCycleApex.Foundation.Spectral.RankOneTrace
import EvenCycleApex.Foundation.Majorization.Karamata
import EvenCycleApex.Foundation.Majorization.Bump
import EvenCycleApex.Foundation.Majorization.RankOne
import EvenCycleApex.Foundation.Model.StepModel
import EvenCycleApex.Foundation.FiniteBridge
import EvenCycleApex.Smoke
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
