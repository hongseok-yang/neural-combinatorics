import Taeyoung.Methods.RootedSOS.CompactS4.Atlas185.Certificate

/-!
# Atlas 185

graph6: `Exv_`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph185

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 185
  vertexCount := 6
  edgeCount := 10
  chromaticNumber := 4
  graph6 := "Exv_"
  status := .positive
  formalization := .verified

/-- Complete compact integer SOS proof, including the graphon interpretation. -/
theorem status : SatisfiesLowerBound graph :=
  Taeyoung.Methods.RootedSOS.CompactS4.Atlas185.satisfiesLowerBound_185

end Taeyoung.Examples.Graph185

#print axioms Taeyoung.Examples.Graph185.status
