import Taeyoung.Foundation

/-!
# Atlas 169

graph6: `Exf_`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph169

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (2, 5), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 169
  vertexCount := 6
  edgeCount := 9
  chromaticNumber := 4
  graph6 := "Exf_"
  status := .open
  formalization := .unresolved

/-- This row is mathematically open.  It asserts no sign: only `P ∨ ¬P`. -/
theorem statusAlternative :
    SatisfiesLowerBound graph ∨ ViolatesLowerBound graph :=
  status_excludedMiddle graph

end Taeyoung.Examples.Graph169
