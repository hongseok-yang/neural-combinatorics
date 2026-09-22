import Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Certificate

/-!
# Atlas 153

graph6: `Ehf_`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph153

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (2, 5), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 153
  vertexCount := 6
  edgeCount := 8
  chromaticNumber := 3
  graph6 := "Ehf_"
  status := .positive
  formalization := .verified

/-- Complete compact SOS proof across all admissible intervals. -/
theorem status : SatisfiesLowerBound graph :=
  Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.satisfiesLowerBound_153

end Taeyoung.Examples.Graph153

#print axioms Taeyoung.Examples.Graph153.status
