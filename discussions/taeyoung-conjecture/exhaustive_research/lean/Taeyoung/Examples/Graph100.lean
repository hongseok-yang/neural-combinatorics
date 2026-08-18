import Taeyoung.Foundation
import Taeyoung.Methods.Broom

/-!
# Atlas 100: verified triangle two-leaf-broom example

graph6: `EsCW`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Peeling gives `int tau(x) C(x)` for `C = T_W(d^2)`.  Two pointwise
facts reduce it to the scalar pair `(d, a) = (d(x), A(x))`:
`C >= A^2/d`, Cauchy-Schwarz in the row measure, and `tau >=
(2A-p)_+`, Goodman.  The supporting plane `L_p(d,a) = 2p^4(1-4p) +
p^3(10p-3)d + 2p^2(3p-1)(a-d^2)` integrates to `p^4(2p-1)` exactly,
because `int d = p` and `int A = int d^2`.  In the coordinates
`alpha = a - p^2`, `delta = d - p` the cleared inequality is a ring
identity whose two cubic terms are absorbed by `a >= p/2` and
`d >= p/2`; what remains is positive definite via
`16p^2 Q = (8p^2 alpha - 2p^2(3p-1) delta)^2 + 4p^4(11p^2-2p-1) delta^2`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph100

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (3, 4), (3, 5), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 100
  vertexCount := 6
  edgeCount := 6
  chromaticNumber := 3
  graph6 := "EsCW"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Broom.broom).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.Broom.broom) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.Broom.satisfiesLowerBound_100)

end Taeyoung.Examples.Graph100
