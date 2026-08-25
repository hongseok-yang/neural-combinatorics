import Taeyoung.Foundation

/-!
# Atlas 196

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
  formalization := .believed

/-- Accepted mathematical result: the exact Atlas 43 theorem followed by the normalized-link house-cone theorem.

The method-specific Lean bridge for this row remains to be formalized. -/
theorem status : SatisfiesLowerBound graph := by
  sorry

end Taeyoung.Examples.Graph196
