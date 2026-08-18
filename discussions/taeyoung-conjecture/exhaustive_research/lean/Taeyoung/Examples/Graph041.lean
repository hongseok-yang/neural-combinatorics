import Taeyoung.Foundation
import Taeyoung.Methods.PageBook.Atlas41

/-!
# Atlas 41: verified page-rooted book-leaf example

graph6: `Db[`.  The edge-list definition below is the Lean graph;
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

namespace Taeyoung.Examples.Graph041

open Taeyoung

def graph : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 41
  vertexCount := 5
  edgeCount := 6
  chromaticNumber := 3
  graph6 := "Db["
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 5 ≃ Fin 5 where
  toFun := ![3, 4, 2, 1, 0]
  invFun := ![4, 3, 2, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 5) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.PageBook.book41).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.PageBook.book41) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.PageBook.satisfiesLowerBound_41')

end Taeyoung.Examples.Graph041
