import Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Certificate

/-!
# Atlas 194

graph6: `E~wW`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph194

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 5), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 194
  vertexCount := 6
  edgeCount := 11
  chromaticNumber := 4
  graph6 := "E~wW"
  status := .positive
  formalization := .verified

/-- Complete compact integer SOS proof, including the graphon interpretation. -/
theorem status : SatisfiesLowerBound graph :=
  Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.satisfiesLowerBound_194

end Taeyoung.Examples.Graph194

#print axioms Taeyoung.Examples.Graph194.status
