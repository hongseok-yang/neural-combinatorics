import Taeyoung.Methods.RootedSOS.Atlas43

/-!
# Atlas 43: verified exact rooted-SOS certificate

graph6: `Dlc`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.
-/

namespace Taeyoung.Examples.Graph043

open Taeyoung

def graph : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (0, 3), (0, 4), (1, 2), (2, 3), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 43
  vertexCount := 5
  edgeCount := 6
  chromaticNumber := 3
  graph6 := "Dlc"
  status := .positive
  formalization := .verified

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph := by
  simpa [graph, Taeyoung.Methods.RootedSOS.House.houseGraph] using
    Taeyoung.Methods.RootedSOS.Atlas43.satisfiesLowerBound_house

end Taeyoung.Examples.Graph043
