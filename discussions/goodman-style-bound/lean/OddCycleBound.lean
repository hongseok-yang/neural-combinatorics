import OddCycleBound.Main
import OddCycleBound.NecklaceGen
import OddCycleBound.PathMoment
import OddCycleBound.MomentSOS
import OddCycleBound.C9

/-!
# OddCycleBound — the odd-cycle Goodman-type bound, integral-grounded

The headline results, for a graphon `W` over a probability space with edge density `p = ∫∫W`
(`OddCycleBound/Main.lean`):

* `OddCycleBound.Graphon.C5_bound` : `t(C₅, W) ≥ p⁵ − p(1−p)⁴`,
* `OddCycleBound.Graphon.C7_bound` : `t(C₇, W) ≥ p⁷ − p(1−p)⁶`,

both for all densities, for any graphon `W` defined as an integral kernel over an abstract
probability space (`IsGraphon W μ`).  The *only* trusted item is the integral definition of
homomorphism density; Lemma 2.4, the cyclic inclusion–exclusion (necklace) identity, the
edge-deletion bound, and the SOS positivity certificates are all proved inside Lean.

Importing `Main` transitively pulls in the whole development
(`Graphon → PathDensity → {Kernel, IntegralCert} → Cycle → Necklace → Main`).
-/
