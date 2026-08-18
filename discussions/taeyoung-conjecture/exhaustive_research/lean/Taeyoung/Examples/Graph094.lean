import Taeyoung.Foundation
import Taeyoung.Methods.Whisker94

/-!
# Atlas 94: verified whiskering example

graph6: `E@dW`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Attaching a pendant leaf to every vertex is a change of the vertex
measure: integrating each whisker out multiplies by the degree of
the vertex it hangs from, and `d*mu/p` is again a probability
measure, so `t(Wh(F),W) = p^v(F) * t(F,W_nu)`.  The biased edge
density is `t(P4,W)/p^2 >= p` by path Sidorenko, so the base is
evaluated at a density no smaller than the one we started from;
Goodman for the triangle and monotonicity finish it.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph094

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 4), (1, 5), (2, 3), (3, 4), (3, 5), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 94
  vertexCount := 6
  edgeCount := 6
  chromaticNumber := 3
  graph6 := "E@dW"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![4, 3, 5, 0, 2, 1]
  invFun := ![3, 5, 4, 1, 0, 2]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Whisker.whisker3).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.Whisker.whisker3) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.Whisker.satisfiesLowerBound_94)

end Taeyoung.Examples.Graph094
