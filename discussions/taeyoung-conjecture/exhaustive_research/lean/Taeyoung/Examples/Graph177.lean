import Taeyoung.Foundation
import Taeyoung.Methods.BaseCone.Rows

/-!
# Atlas 177: verified base-cone example

graph6: `En{G`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The base already has a checked graphon bound, and its target is a
product of affine factors `1 - k(1-z)` over the roots of its
chromatic polynomial.  Such a product is nonnegative with a
nonnegative slope above `1 - 1/kmax`, so its tangent at
`c = 2 - 1/p` is an affine minorant there; the conditional cone
lemma integrates that minorant over the links, and the weighted
rooted-triangle inequality cancels the correction term.  Coning
shifts every root by one and absorbs one power of `p` per root,
so `p^v(B)·Φ_B(2 - 1/p)` is exactly the cone's own target.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph177

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 177
  vertexCount := 6
  edgeCount := 10
  chromaticNumber := 4
  graph6 := "En{G"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![4, 1, 3, 0, 2, 5]
  invFun := ![3, 1, 4, 2, 0, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Link.coneGraph Taeyoung.Methods.BaseCone.diamondIsolated).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.Link.coneGraph Taeyoung.Methods.BaseCone.diamondIsolated) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.BaseCone.satisfiesLowerBound_177)

end Taeyoung.Examples.Graph177
