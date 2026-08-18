import Taeyoung.Foundation
import Taeyoung.Methods.RootedTriangleTree.Paw

/-!
# Atlas 15: verified rooted triangle-tree example

graph6: `CN`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Conditioning on the root factors the density as `∫ dʳ·τ`, which the
weighted rooted-triangle inequality of `Methods/Link` and Jensen turn into
the family target `p^(r+1)(2p-1)`.  The chromatic polynomial comes from
iterated clique-attachment over `K₃`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph015

open Taeyoung

def graph : SimpleGraph (Fin 4) :=
  graphFromEdges 4 [(0, 3), (1, 2), (1, 3), (2, 3)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 15
  vertexCount := 4
  edgeCount := 4
  chromaticNumber := 3
  graph6 := "CN"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 4 ≃ Fin 4 where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 4) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Chromatic.pawGraph).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.Chromatic.pawGraph) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.RootedTriangleTree.paw_satisfiesLowerBound)

end Taeyoung.Examples.Graph015
