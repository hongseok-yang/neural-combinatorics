import Taeyoung.Foundation
import Taeyoung.Methods.ForestCone.Rows

/-!
# Atlas 135: verified forest-cone example

graph6: `EzW_`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Deleting the universal vertex leaves a forest whose components are
stars and single edges, so its Sidorenko bound `t(F,V) >= z^e(F)`
is Jensen for the degree moments together with disjoint-union
multiplicativity -- no forest Sidorenko theorem is used.  The cone
bound is then the affine-product tangent at `c = 2 - 1/p` plus the
weighted rooted-triangle inequality, and coning shifts every root
of the chromatic polynomial by one, which is why the result is the
cone's own target.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph135

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (2, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 135
  vertexCount := 6
  edgeCount := 8
  chromaticNumber := 3
  graph6 := "EzW_"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![2, 1, 0, 3, 4, 5]
  invFun := ![2, 1, 0, 3, 4, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Link.coneGraph Taeyoung.Methods.ForestCone.star3Isolate).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.Link.coneGraph Taeyoung.Methods.ForestCone.star3Isolate) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.ForestCone.satisfiesLowerBound_135)

end Taeyoung.Examples.Graph135
