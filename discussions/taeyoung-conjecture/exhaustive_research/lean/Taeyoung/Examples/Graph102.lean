import Taeyoung.Foundation
import Taeyoung.Methods.OddWalk.Row102

/-!
# Atlas 102: verified odd-walk example

graph6: `EJe?`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Rooting the triangle and peeling the tail from its free end gives
`t(R3,W) = int tau * B` with `B = T_W^3 1`.  The pointwise Goodman
bound `tau >= 2A - p` is integrated against `B >= 0` directly -- no
Jensen and no convexity -- leaving `2a5 - p*a3`, and the odd-walk
inequality `a5^3 >= a3^5` with Blakley-Roy `a3 >= p^3` gives
`a5 >= p^2 a3`, whence `p^4(2p-1)`.  The odd-walk inequality itself
is proved in `Methods/OddWalk` by the graphon-native form of the
Blekherman-Raymond entropy argument: three folds of P5 onto P3, a
chain of Gibbs steps, and no finite host graph.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph102

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 4), (0, 5), (1, 2), (1, 3), (2, 3), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 102
  vertexCount := 6
  edgeCount := 6
  chromaticNumber := 3
  graph6 := "EJe?"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![3, 1, 2, 4, 0, 5]
  invFun := ![4, 1, 2, 0, 3, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.OddWalk.r3).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.OddWalk.r3) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.OddWalk.satisfiesLowerBound_102)

end Taeyoung.Examples.Graph102
