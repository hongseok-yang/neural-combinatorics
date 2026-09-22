import Taeyoung.Methods.RootedSOS.CompactS4.Atlas122.Certificate

/-!
# Atlas 122

graph6: `Eld?`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph122

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 3), (0, 4), (1, 2), (1, 5), (2, 3), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 122
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "Eld?"
  status := .positive
  formalization := .verified

/-- Complete compact integer SOS proof, including the graphon interpretation. -/
theorem status : SatisfiesLowerBound graph :=
  Taeyoung.Methods.RootedSOS.CompactS4.Atlas122.satisfiesLowerBound_122

end Taeyoung.Examples.Graph122

#print axioms Taeyoung.Examples.Graph122.status
