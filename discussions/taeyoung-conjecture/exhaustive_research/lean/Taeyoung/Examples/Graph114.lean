import Taeyoung.Foundation
import Taeyoung.Methods.PageBook.Atlas114

/-!
# Atlas 114: verified page-rooted book-leaf example

graph6: `EJwG`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Deleting the spine edge's two endpoints leaves two pages; the
density factors as an integral over the spine of the two page
operators `H_s(x,y) = int W(x,z)W(y,z)d(z)^s`.  One weighted
Cauchy-Schwarz compresses the two pages to `H_1^2`, a second one
on the product measure turns that into `(int W H_1)^2/p`, and
`int int W H_1 = int d*tau` is Tonelli.  The weighted
rooted-triangle inequality and Jensen finish it.  The chromatic
polynomial comes from a triangle with one page and its two leaves
attached in turn.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph114

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 114
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "EJwG"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![1, 2, 3, 4, 0, 5]
  invFun := ![4, 0, 1, 2, 3, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.PageBook.book114).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.PageBook.book114) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.PageBook.satisfiesLowerBound_114)

end Taeyoung.Examples.Graph114
