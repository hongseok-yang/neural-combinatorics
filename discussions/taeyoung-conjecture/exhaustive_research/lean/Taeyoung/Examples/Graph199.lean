import Taeyoung.Foundation

/-!
# Atlas 199

graph6: `El^g`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph199

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 3), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 199
  vertexCount := 6
  edgeCount := 11
  chromaticNumber := 4
  graph6 := "El^g"
  status := .open
  formalization := .unresolved

/-- This row is mathematically open.  It asserts no sign: only `P ∨ ¬P`. -/
theorem statusAlternative :
    SatisfiesLowerBound graph ∨ ViolatesLowerBound graph :=
  status_excludedMiddle graph

end Taeyoung.Examples.Graph199
