import Taeyoung.Methods.RootedSOS.CompactS4.Atlas181.Certificate

/-!
# Atlas 181

graph6: `E^mG`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph181

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (2, 3), (2, 4), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 181
  vertexCount := 6
  edgeCount := 10
  chromaticNumber := 4
  graph6 := "E^mG"
  status := .positive
  formalization := .verified

/-- Complete compact integer SOS proof, including the graphon interpretation. -/
theorem status : SatisfiesLowerBound graph :=
  Taeyoung.Methods.RootedSOS.CompactS4.Atlas181.satisfiesLowerBound_181

end Taeyoung.Examples.Graph181

#print axioms Taeyoung.Examples.Graph181.status
