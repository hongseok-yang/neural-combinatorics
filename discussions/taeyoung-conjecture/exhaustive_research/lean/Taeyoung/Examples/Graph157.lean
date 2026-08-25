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
  status := .positive
  formalization := .believed

/-- Accepted mathematical result: the exact four-root interval-SOS proof in notes/s4_exact_interval_sos_remaining_cases.tex.

The method-specific Lean bridge for this row remains to be formalized. -/
theorem status : SatisfiesLowerBound graph := by
  sorry

end Taeyoung.Examples.Graph157
