import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Certificate

/-!
# Atlas 203

graph6: `E~^G`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph203

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 203
  vertexCount := 6
  edgeCount := 12
  chromaticNumber := 4
  graph6 := "E~^G"
  status := .positive
  formalization := .verified

/-- Complete catalogue bound, with both density intervals checked in Lean. -/
theorem status : SatisfiesLowerBound graph :=
  Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.satisfiesLowerBound_203

#print axioms status

end Taeyoung.Examples.Graph203
