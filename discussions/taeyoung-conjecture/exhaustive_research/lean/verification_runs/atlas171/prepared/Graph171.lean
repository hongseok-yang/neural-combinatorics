import Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Certificate

/-!
# Atlas 171

graph6: `Ehew`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph171

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 4), (0, 5), (1, 2), (2, 3), (2, 5), (3, 4), (3, 5), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 171
  vertexCount := 6
  edgeCount := 9
  chromaticNumber := 3
  graph6 := "Ehew"
  status := .positive
  formalization := .verified

/-- Complete compact SOS proof across all admissible intervals. -/
theorem status : SatisfiesLowerBound graph :=
  Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.satisfiesLowerBound_171

end Taeyoung.Examples.Graph171

#print axioms Taeyoung.Examples.Graph171.status
