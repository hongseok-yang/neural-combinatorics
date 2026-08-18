import Taeyoung.Foundation
import Taeyoung.Methods.Components.Atlas84

/-!
# Atlas 84: verified component-multiplicativity example

graph6: `ECd_`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The graph is a disjoint union, and both sides of the catalogue
proposition are multiplicative over it: the density by the product
splitting of the assignment measure, the chromatic polynomial by the
product splitting of proper assignments.  The triangle factor is the
pure-chordal clique bound; the path factor is `t(P3,W) = ∫d² ≥ p²`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph084

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 3), (0, 4), (1, 5), (2, 5), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 84
  vertexCount := 6
  edgeCount := 5
  chromaticNumber := 3
  graph6 := "ECd_"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![0, 3, 4, 5, 1, 2]
  invFun := ![0, 4, 5, 1, 2, 3]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Components.atlas84).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.Components.atlas84) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.Components.atlas84_satisfiesLowerBound)

end Taeyoung.Examples.Graph084
