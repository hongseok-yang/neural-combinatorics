import Taeyoung.Foundation
import Taeyoung.Methods.BookTail.Rows

/-!
# Atlas 120: verified triangle-book two-edge-tail example

graph6: `EB}?`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Peeling the pages and the two-edge tail turns the density into
`int int W(x,y) A(x) S(x,y)^m` with `A = T_W d` and `S = H_0`.  One
weighted Cauchy-Schwarz on the product measure, with weight
`W(x,y)A(x)` of total mass `B = int A d = t(P4,W)`, bounds it below
by `F^2/B` for `F = int A tau`.  Two lower bounds on `F` finish it:
`F >= (2p-1)B`, which on `p >= 1/2` follows from the Cauchy-Schwarz
chain `B^2 <= N M`, `N >= M^2`, `M >= p^2` through the factorization
`(2N-pM)^2 - (2p-1)^2 N M = (4N-M)(N-p^2 M)`; and `F >= p^3(2p-1)`,
the sharp first-page bound.  Both start from the pointwise Goodman
estimate `tau >= 2A - p`, and `int A = int d^2` is self-adjointness.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph120

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 4), (0, 5), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 120
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "EB}?"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![4, 3, 1, 2, 0, 5]
  invFun := ![4, 2, 3, 1, 0, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.BookTail.book120).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.BookTail.book120) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.BookTail.satisfiesLowerBound_120)

end Taeyoung.Examples.Graph120
