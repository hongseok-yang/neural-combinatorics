import Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Certificate

/-!
# Atlas 147

graph6: `EhMg`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph147

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 5), (1, 2), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 147
  vertexCount := 6
  edgeCount := 8
  chromaticNumber := 3
  graph6 := "EhMg"
  status := .positive
  formalization := .verified

/-- Complete compact SOS proof across all admissible intervals. -/
theorem status : SatisfiesLowerBound graph :=
  Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.satisfiesLowerBound_147

end Taeyoung.Examples.Graph147

#print axioms Taeyoung.Examples.Graph147.status
