import Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.Certificate

/-!
# Atlas 169

graph6: `Exf_`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph169

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (2, 5), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 169
  vertexCount := 6
  edgeCount := 9
  chromaticNumber := 4
  graph6 := "Exf_"
  status := .positive
  formalization := .verified

/-- Complete compact integer SOS proof, including the graphon interpretation. -/
theorem status : SatisfiesLowerBound graph :=
  Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.satisfiesLowerBound_169

end Taeyoung.Examples.Graph169

#print axioms Taeyoung.Examples.Graph169.status
