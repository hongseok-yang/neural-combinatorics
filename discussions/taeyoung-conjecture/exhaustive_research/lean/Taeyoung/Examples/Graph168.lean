import Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Certificate

/-!
# Atlas 168

graph6: `E^MG`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph168

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (2, 3), (2, 4), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 168
  vertexCount := 6
  edgeCount := 9
  chromaticNumber := 3
  graph6 := "E^MG"
  status := .positive
  formalization := .verified

/-- Complete compact SOS proof across all admissible intervals. -/
theorem status : SatisfiesLowerBound graph :=
  Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.satisfiesLowerBound_168

end Taeyoung.Examples.Graph168

#print axioms Taeyoung.Examples.Graph168.status
