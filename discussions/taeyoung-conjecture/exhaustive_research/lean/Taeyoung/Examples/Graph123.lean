import Taeyoung.Foundation
import Taeyoung.Methods.PageTail.Rows

/-!
# Atlas 123: verified page-rooted two-edge-tail example

graph6: `EJy?`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

With the two-edge tail on a page rather than on the spine, the
weight `A = T_W d` sits inside one page: the density is
`int int W(x,y) G(x,y) S(x,y)` with `G = int W(x,z)W(y,z)A(z)dz`.
A weighted Cauchy-Schwarz inside the page splits `A` into two
square roots, `R^2 <= S G` for `R = int W(x,z)W(y,z)sqrt(A(z))dz`;
this is the m = 2 case of the note's average over the page orbit.
A second Cauchy-Schwarz on the product measure, with weight `W` of
total mass `p`, gives `int int W R^2 >= (int int W R)^2/p`, and
Fubini identifies `int int W R = int sqrt(A) tau`.  That last
quantity is at least `p^2(2p-1)` by the affine minorant of
`a -> sqrt(a) max(2a-p,0)` at `a = p^2`, whose two cases factor as
`2(s-p)^2(s + p/2 + 1/4)` and `-p(p-1/2)^2` after `a = s^2`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph123

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 123
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "EJy?"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![1, 2, 4, 3, 0, 5]
  invFun := ![4, 0, 1, 3, 2, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.PageTail.book123).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.PageTail.book123) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.PageTail.satisfiesLowerBound_123)

end Taeyoung.Examples.Graph123
