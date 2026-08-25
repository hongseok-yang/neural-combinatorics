import Taeyoung.Foundation

/-!
# Atlas 127

graph6: `EZEG`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph127

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (0, 5), (1, 2), (1, 3), (2, 3), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 127
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "EZEG"
  status := .positive
  formalization := .believed

/-- Accepted mathematical result: the accepted smoothed Goodman theorem recorded in the classification catalogue.

The method-specific Lean bridge for this row remains to be formalized. -/
theorem status : SatisfiesLowerBound graph := by
  sorry

end Taeyoung.Examples.Graph127
