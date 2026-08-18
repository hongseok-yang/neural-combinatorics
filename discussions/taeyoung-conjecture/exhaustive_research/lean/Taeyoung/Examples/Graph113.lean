import Taeyoung.Foundation
import Taeyoung.Methods.CliqueDist.Diamond

/-!
# Atlas 113: verified orbit-balanced diamond-leaf example

graph6: `E^_O`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The diamond `K_4 - e` has two vertex orbits of size two, and one
leaf sits in each.  Peeling both gives `int F(x) d(x_0)d(x_2)` over
the four diamond variables.  Swapping the two orbits at once is an
automorphism carrying the leaves from `{0,2}` to `{1,3}`, so twice
the density is `int F (d_0 d_2 + d_1 d_3)` and the two-term AM-GM
`a + b >= 2 sqrt(ab)` gives `2 int F prod sqrt(d_i)`.  Changing to
the `sqrt(d)`-biased probability measure turns that into
`M^4 t(D, W_nu)`, where the already-verified diamond bound
`t(D,V) >= z(2z-1)^2` applies.  `M^2 <= p` is Cauchy-Schwarz against
the constant `1`, `M^2 t(K_2,W_nu) >= p^2` is the geometric-mean
estimate, and the rescaling is the identity
`p(2s-1)^2 - s(2p-1)^2 = (s-p)(4ps-1)`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph113

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3), (3, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 113
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "E^_O"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![3, 2, 0, 1, 5, 4]
  invFun := ![2, 3, 1, 0, 5, 4]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.CliqueDist.diamondLeaf02).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.CliqueDist.diamondLeaf02) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.CliqueDist.satisfiesLowerBound_113)

end Taeyoung.Examples.Graph113
