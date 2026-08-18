import Taeyoung.Foundation
import Taeyoung.Methods.PureChordal.Main
import Taeyoung.Methods.OddCycleC5.Main
import Taeyoung.Catalogue.Counts
-- The negative rows' machinery.  `Catalogue.Counts` reaches it through the 19
-- generated Atlas modules that consume it, but it is imported here as well so
-- that a change breaking only the unconsumed parts still fails the build.
import Taeyoung.Methods.Negative.ProperCount
import Taeyoung.Methods.Negative.Chromatic
import Taeyoung.Methods.Negative.Tensor
import Taeyoung.Methods.Negative.LocalTuran
import Taeyoung.Methods.Negative.Atlas152
-- The odd-walk development for Atlas 102: the graphon-native Blekherman--Raymond
-- proof of `t(P5,W)^3 >= t(P3,W)^5`.  Still in progress -- the pieces below are
-- complete and `sorry`-free, but they do not yet reach a catalogue row.
import Taeyoung.Methods.OddWalk.Row102
-- Reusable machinery that no catalogue row consumes *yet*: the ported Bernstein
-- certificate format.  Imported here so that it cannot rot.
import Taeyoung.Methods.Certificate.Bernstein
-- Fisher's sharp triangle-density theorem on `1/2 < p <= 2/3`, vendored from
-- `discussions/goodman-style-bound/fisher_lean`, and its bridge to this
-- project's bundled graphons.  Atlas 148 is the row that needs it; see
-- `Taeyoung/Fisher.lean` for why the copy exists and what was left behind.
import Taeyoung.Methods.TriangleDensity
-- The Atlas 148 development.  The high-density interval `[3/5,1]` is complete
-- and `sorry`-free, from the scalar supporting line through the density
-- identity: `homDensity_graph148_high`.  The low interval's scalar layer is
-- complete too; its analytic layer, which consumes the vendored Fisher bound,
-- is still to come, so no catalogue row is reached yet.
import Taeyoung.Methods.Atlas148
-- Atlas 145: Atlas 148 with the second triangle page moved onto the first
-- page's cycle edge, by one pointwise Cauchy--Schwarz on the cycle arm.
import Taeyoung.Methods.Atlas145
import Taeyoung.Methods.Atlas160.Rows

/-!
# Taeyoung-conjecture verification project

The foundation and method modules are reusable mathematics.  The catalogue
imports exactly 117 Atlas modules and audits their current status counts.
-/
