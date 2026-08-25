import Taeyoung.Foundation

/-!
# Atlas 43

graph6: `Dlc`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph043

open Taeyoung

def graph : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (0, 3), (0, 4), (1, 2), (2, 3), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 43
  vertexCount := 5
  edgeCount := 6
  chromaticNumber := 3
  graph6 := "Dlc"
  status := .positive
  formalization := .believed

/-- Accepted mathematical result: the exact rooted interval-SOS certificate in notes/atlas43_exact_rooted_sos.tex.

The method-specific Lean bridge for this row remains to be formalized. -/
theorem status : SatisfiesLowerBound graph := by
  sorry

end Taeyoung.Examples.Graph043
