import Taeyoung.Methods.Atlas126.Verified

/-!
# Atlas 126

graph6: `ERUO`. A triangle and a four-cycle share one vertex.
The supporting planes, their complete domain coverage, the exact arithmetic
certificates, the graphon integration and coloring counts are checked in Lean.
The explicit isomorphism below transports the method representative to the
catalogue's edge list.
-/

namespace Taeyoung.Examples.Graph126

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (0, 5), (1, 3), (1, 4), (2, 3), (3, 4), (3, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 126
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "ERUO"
  status := .positive
  formalization := .verified

def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![3, 1, 4, 0, 2, 5]
  invFun := ![3, 1, 4, 0, 2, 5]
  left_inv := by decide
  right_inv := by decide

theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Atlas126.graph126).Adj a b := by
  revert a b
  decide

def iso : (Taeyoung.Methods.Atlas126.graph126) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    Taeyoung.Methods.Atlas126.satisfiesLowerBound_126

end Taeyoung.Examples.Graph126

#print axioms Taeyoung.Examples.Graph126.status
