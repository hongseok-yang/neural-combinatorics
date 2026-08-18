import Taeyoung.Foundation
import Taeyoung.Methods.SelfAmalgam

/-!
# Atlas 115: verified edge self-amalgamation example

graph6: `E`Xg`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The graph is two paws glued along the triangle edge opposite the
leaf-bearing vertex, i.e. the two-fold edge self-amalgam of the paw.
Conditioning on the images of the two glued roots, the rooted factor
`g(x,y) = int W(x,z)W(y,z)d(z)` is the project's `Link.pageOp W 1`,
so `t(paw,W) = int int W g` is `integral_edge_pageOp` at `s = 1` and
one peeling gives `t = int int W g^2`.  Cauchy-Schwarz in the weight
`W dmu^2` yields `t(paw,W)^2 <= p*t`, and the paw bound
`t(paw,W) >= p^2(2p-1)` is the rooted triangle-tree family bound at
`r = 1`.  Then `(p^2(2p-1))^2/p = p^3(2p-1)^2`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph115

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 115
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "E`Xg"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![4, 5, 1, 0, 2, 3]
  invFun := ![3, 2, 4, 5, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.SelfAmalgam.amalgam).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.SelfAmalgam.amalgam) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.SelfAmalgam.satisfiesLowerBound_115)

end Taeyoung.Examples.Graph115
