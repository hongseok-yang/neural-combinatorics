import Taeyoung.Foundation

/-!
# Atlas 126

graph6: `ERUO`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph126

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (0, 5), (1, 3), (1, 4), (2, 3), (3, 4), (3, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 126
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "ERUO"
  status := .positive
  formalization := .believed

/-- Accepted mathematical result: [Atlas 126 triangle--$C_4$ vertex supporting-plane theorem](notes/atlas126_triangle_c4_vertex_supporting_plane.tex): a rooted $C_4$ projection, the sharp triangle profile, and exact Bernstein certificates

The method-specific Lean bridge for this row remains to be formalized. -/
theorem status : SatisfiesLowerBound graph := by
  sorry

end Taeyoung.Examples.Graph126
