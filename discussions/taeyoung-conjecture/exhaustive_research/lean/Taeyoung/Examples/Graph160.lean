import Taeyoung.Foundation
import Taeyoung.Methods.Atlas160.Rows

/-!
# Atlas 160: verified weighted-K4 supporting-plane example

graph6: `E~@g`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

A `K4` carrying a triangle page on one clique edge, with a leaf on
the page.  Integrating the leaf and then the page leaves
`B(x,y) = int W(x,z)W(y,z)d(z)`, and `rs >= r+s-1` gives
`B(x,y) >= A(x)+A(y)-p`.  Integrated against the `K4` weight that is
the page reduction `t(H) >= 2 t(K4 two-edge tail) - p t(K4)`, which
in rooted form is `int (2A-p)*kappa4`.  The signed combination must
be kept intact: the two-edge-tail bound alone is not enough.
Conditioning at a clique vertex and applying Goodman in the link
gives a piecewise scalar function of `(d, A)`, and a supporting
plane in the coordinates `(d, A-d^2)` integrates to the target
exactly, because `int d = p` and `int A = int d^2`.  Its active
region is one explicit cubic factorization; its negative region
needs only the two faces `a = p/2` and `a = d+p-1`.  The chromatic
polynomial `r(r-1)^2(r-2)^2(r-3)` comes from the attachment tower
`K4`, then the page on a clique edge, then the leaf on the page.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph160

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 5), (2, 3), (2, 5), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 160
  vertexCount := 6
  edgeCount := 9
  chromaticNumber := 4
  graph6 := "E~@g"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![1, 2, 0, 3, 5, 4]
  invFun := ![2, 0, 1, 3, 5, 4]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Atlas160.graph160).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.Atlas160.graph160) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.Atlas160.satisfiesLowerBound_160)

end Taeyoung.Examples.Graph160
