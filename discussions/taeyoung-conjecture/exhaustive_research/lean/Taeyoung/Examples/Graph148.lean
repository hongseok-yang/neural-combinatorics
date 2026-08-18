import Taeyoung.Foundation
import Taeyoung.Methods.Atlas148.Chromatic

/-!
# Atlas 148: verified paw-bias projection example

graph6: `EyUG`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Two triangles sharing a vertex, plus a two-edge path joining one
outer vertex of each.  Peeling the three degree-two vertices gives
`t = int int int K(x,a)K(x,b)S(a,b)` with `K = W*S`, which is the
squared norm of `T_W F_x` fibrewise.  On `p >= 3/5` a linearized
two-term Bessel projection onto `1` and the centred row `W(x,.)-d(x)`
gives `T >= G^2 + 2L*Delta - L^2*V` for every multiplier `L`; taking
`L = -cq` and feeding in the supporting-line estimate
`p^2 G - q Delta >= pcf` collapses the target to `(G - cp^2)^2 >= 0`.
That estimate integrates a scalar inequality certified by two
Bernstein boxes in `z = sqrt(d(x)d(y))`, and uses the edge geometric
mean `int int W*z >= p^2`.  On `p <= 3/5` the density is bounded below
by `G^2` and `G` by the sharp paw value `p*g(p)`: symmetrizing the paw
leaf, tilting by `d^(1/3)`, and applying Fisher's triangle theorem
below tilted density `2/3` and Goodman above it.  The chromatic
polynomial `r(r-1)(r-2)^2(r^2-3r+3)` does not split, so it comes from
surjective counts rather than an attachment tower.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph148

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (1, 4), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 148
  vertexCount := 6
  edgeCount := 8
  chromaticNumber := 3
  graph6 := "EyUG"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![1, 0, 4, 2, 3, 5]
  invFun := ![1, 0, 3, 4, 2, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Atlas148.graph148).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.Atlas148.graph148) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.Atlas148.satisfiesLowerBound_148)

end Taeyoung.Examples.Graph148
