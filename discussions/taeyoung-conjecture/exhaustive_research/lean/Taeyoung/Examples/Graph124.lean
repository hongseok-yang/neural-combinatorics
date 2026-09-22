import Taeyoung.Methods.RootedSOS.CompactS4.Atlas124.Certificate

/-!
# Atlas 124

graph6: `Exd?`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph124

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 4), (1, 2), (1, 5), (2, 3), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 124
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "Exd?"
  status := .positive
  formalization := .verified

/-- Complete compact integer SOS proof, including the graphon interpretation. -/
theorem status : SatisfiesLowerBound graph :=
  Taeyoung.Methods.RootedSOS.CompactS4.Atlas124.satisfiesLowerBound_124

end Taeyoung.Examples.Graph124

#print axioms Taeyoung.Examples.Graph124.status
