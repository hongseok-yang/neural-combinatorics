import Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Certificate

/-!
# Atlas 151

graph6: `EhdW`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph151

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 4), (1, 2), (1, 5), (2, 3), (3, 4), (3, 5), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 151
  vertexCount := 6
  edgeCount := 8
  chromaticNumber := 3
  graph6 := "EhdW"
  status := .positive
  formalization := .verified

/-- Complete compact SOS proof across all admissible intervals. -/
theorem status : SatisfiesLowerBound graph :=
  Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.satisfiesLowerBound_151

end Taeyoung.Examples.Graph151

#print axioms Taeyoung.Examples.Graph151.status
