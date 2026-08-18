import Taeyoung.Foundation

/-!
# Atlas 157

graph6: `E~`_`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph157

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 5), (2, 3), (2, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 157
  vertexCount := 6
  edgeCount := 9
  chromaticNumber := 4
  graph6 := "E~`_"
  status := .open
  formalization := .unresolved

/-- This row is mathematically open.  It asserts no sign: only `P ∨ ¬P`. -/
theorem statusAlternative :
    SatisfiesLowerBound graph ∨ ViolatesLowerBound graph :=
  status_excludedMiddle graph

end Taeyoung.Examples.Graph157
