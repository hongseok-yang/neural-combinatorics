import Taeyoung.Foundation
import Taeyoung.Methods.PawCone.Rows

/-!
# Atlas 156: verified paw / triangle–edge cone example

graph6: `E~H_`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The base graph — the paw, or `K₃ ⊔ K₂`, with isolated vertices —
dominates `φ(z) = z²(2z-1)` above `z = 1/2`, by the rooted
triangle–tree bound and by multiplicativity with the Goodman
triangle bound respectively.  `φ` is a cubic, so its tangent at
`c = 2 - 1/p` lies under it; the conditional cone lemma then
integrates that tangent over the links, and the weighted
rooted-triangle inequality kills the correction term, leaving
`p^m(2p-1)²(3p-2)`.  The chromatic polynomial comes from two
clique-attachments over the `K₄` spanned by the apex.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph156

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (2, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 156
  vertexCount := 6
  edgeCount := 9
  chromaticNumber := 4
  graph6 := "E~H_"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![2, 1, 0, 3, 5, 4]
  invFun := ![2, 1, 0, 3, 5, 4]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Link.coneGraph Taeyoung.Methods.PawCone.pawIsolated).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.Link.coneGraph Taeyoung.Methods.PawCone.pawIsolated) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.PawCone.satisfiesLowerBound_156)

end Taeyoung.Examples.Graph156
