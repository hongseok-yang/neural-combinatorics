import Taeyoung.Foundation
import Taeyoung.Methods.OddLeaf.Rows

/-!
# Atlas 104: verified odd-cycle-with-one-leaf example

graph6: `Ehd?`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Peeling the leaf gives `int F(y) d(y_0)` for the five-cycle weight
`F`, which is invariant under the cyclic rotation of the five
coordinates, so the degree may sit at any of them.  Averaging the
five and applying the arithmetic-geometric mean inequality gives
`int F(y) prod_i d(y_i)^{1/5} = M^5 t(C5,W;nu)` for the biased
probability measure `dnu = (d^{1/5}/M)dmu`.  The already verified
analytic `C5` theorem applies verbatim there, and the row closes
with `M^5 <= p` (Jensen), `p^7 <= (M^5)^2 s^5` (three-factor
Holder at `(5/7,1/7,1/7)`, because the fractionally weighted edge
integral is `M^2 s`), and the rescaling `s^3 h(p)^2 <= p^3 h(s)^2`
for `h(u) = (2u-1)(2u^2-2u+1)`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph104

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 4), (1, 2), (1, 5), (2, 3), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 104
  vertexCount := 6
  edgeCount := 6
  chromaticNumber := 3
  graph6 := "Ehd?"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![1, 0, 4, 3, 2, 5]
  invFun := ![1, 0, 4, 3, 2, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.OddLeaf.c5plus).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.OddLeaf.c5plus) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.OddLeaf.satisfiesLowerBound_104)

end Taeyoung.Examples.Graph104
