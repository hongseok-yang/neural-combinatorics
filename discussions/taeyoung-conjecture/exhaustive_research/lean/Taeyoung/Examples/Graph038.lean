import Taeyoung.Foundation
import Taeyoung.Methods.OddCycleC5.Chromatic

/-!
# Atlas 38: verified odd-cycle example

graph6: `Dhc`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The bound is the analytic `C₅` inequality of `Methods/OddCycleC5`,
carried to the shared density layer by `cycleDensity_bridge` and
`edgeDensity_bridge`, and combined with the five-cycle chromatic
polynomial `(X-1)^5 - (X-1)` proved in `Chromatic.lean`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph038

open Taeyoung

def graph : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (0, 4), (1, 2), (2, 3), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 38
  vertexCount := 5
  edgeCount := 5
  chromaticNumber := 3
  graph6 := "Dhc"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 5 ≃ Fin 5 where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 5) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.OddCycleC5.c5).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.OddCycleC5.c5) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.OddCycleC5.c5_satisfiesLowerBound)

end Taeyoung.Examples.Graph038
