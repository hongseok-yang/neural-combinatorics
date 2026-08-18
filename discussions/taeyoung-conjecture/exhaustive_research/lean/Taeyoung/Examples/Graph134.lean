import Taeyoung.Foundation
import Taeyoung.Methods.CliqueDist.Rows

/-!
# Atlas 134: verified clique distributed-leaf example

graph6: `E~_O`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Peeling the two leaves gives `int F(x) d(x_0)d(x_1)` over the four
clique variables.  The graph with its leaves on `{0,1}` is
isomorphic to the one with leaves on `{2,3}`, so twice the density
is `int F (d_0 d_1 + d_2 d_3)`, and the two-term AM-GM
`a + b >= 2 sqrt(ab)` bounds that below by `2 int F prod sqrt(d_i)`
-- the `h/r = 1/2` weight, obtained from one exchange rather than
an `r!`-fold average.  Changing to the `sqrt(d)`-biased probability
measure turns that into `M^4 t(K_4, W_nu)`, and the accepted clique
bound applies there.  Two facts close it: `M^2 <= p`, Cauchy-Schwarz
against the constant `1`; and `M^2 t(K_2,W_nu) = int int W
sqrt(d(x)d(y)) >= p^2`, the geometric-mean estimate.  The rescaling
is the factorization `p(2s-1)(3s-2) - s(2p-1)(3p-2) = (s-p)(6ps-2)`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph134

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3), (3, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 134
  vertexCount := 6
  edgeCount := 8
  chromaticNumber := 4
  graph6 := "E~_O"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.CliqueDist.cliqueDist01).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.CliqueDist.cliqueDist01) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.CliqueDist.satisfiesLowerBound_134)

end Taeyoung.Examples.Graph134
