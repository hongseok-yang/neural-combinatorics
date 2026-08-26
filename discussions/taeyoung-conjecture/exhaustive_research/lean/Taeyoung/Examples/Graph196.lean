import Taeyoung.Foundation
import Taeyoung.Methods.RootedSOS.Atlas196

/-!
# Atlas 196: verified normalized-link consequence of Atlas 43

graph6: `ER~g`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph196

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 196
  vertexCount := 6
  edgeCount := 11
  chromaticNumber := 4
  graph6 := "ER~g"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the cone-over-house representative to this
Atlas graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![4, 2, 3, 1, 5, 0]
  invFun := ![5, 3, 1, 2, 0, 4]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling preserves adjacency, checked by kernel computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Link.coneGraph
        Taeyoung.Methods.RootedSOS.House.houseGraph).Adj a b := by
  revert a b
  decide

/-- The certificate representative is Atlas 196 up to relabelling. -/
def iso :
    (Taeyoung.Methods.Link.coneGraph
      Taeyoung.Methods.RootedSOS.House.houseGraph) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    Taeyoung.Methods.RootedSOS.Atlas196.satisfiesLowerBound_coneHouse

end Taeyoung.Examples.Graph196
