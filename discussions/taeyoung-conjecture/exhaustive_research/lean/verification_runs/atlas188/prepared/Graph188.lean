import Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Certificate

/-!
# Atlas 188

graph6: `EzNG`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph188

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 188
  vertexCount := 6
  edgeCount := 10
  chromaticNumber := 3
  graph6 := "EzNG"
  status := .positive
  formalization := .verified

/-- Complete compact SOS proof across all admissible intervals. -/
theorem status : SatisfiesLowerBound graph :=
  Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.satisfiesLowerBound_188

end Taeyoung.Examples.Graph188

#print axioms Taeyoung.Examples.Graph188.status
