-- Trees with independent apices (TREES_VERIFICATION_PLAN.md).  One import group per milestone.
-- T0: scaffold.
import TreeApex.Smoke
-- T1: apex graphs, recursive trees, the IsTree bridge.
import TreeApex.Graph.Apex
import TreeApex.Graph.RecTree
-- T2: weighted hosts, their scalars, the doubled host, Goodman, regression hosts.
import TreeApex.Host.ProbHost
import TreeApex.Host.Double
import TreeApex.Host.Goodman
import TreeApex.Host.Regression
-- T3: finite relative entropy; generic extension along a tree.
import TreeApex.Entropy.RelEnt
import TreeApex.Entropy.TreeLaw
-- T4: the triangle and the book.
import TreeApex.Entropy.Triangle
import TreeApex.Entropy.Book
-- T5: the finite counting inequality.
import TreeApex.Finite.OneColour
-- T6: two colours and commonness on hosts.
import TreeApex.Finite.TwoColour
-- T7: transfer to graphons; headlines P1–P4.
import TreeApex.Transfer
import TreeApex.Main
-- T8 (optional): appendix A, trees themselves.
import TreeApex.Appendix.Sidorenko
-- T9: the plan's declaration names (§6).
import TreeApex.PaperNames
