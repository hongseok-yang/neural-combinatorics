import Taeyoung.Foundation

/-!
# Atlas 174

graph6: `EtTg`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph174

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 174
  vertexCount := 6
  edgeCount := 9
  chromaticNumber := 3
  graph6 := "EtTg"
  status := .positive
  formalization := .believed

/-- Accepted mathematical result: the exact four-root interval-SOS proof in notes/s4_exact_interval_sos_remaining_cases.tex.

The method-specific Lean bridge for this row remains to be formalized. -/
theorem status : SatisfiesLowerBound graph := by
  sorry

end Taeyoung.Examples.Graph174
