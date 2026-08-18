import Taeyoung.Foundation
import Taeyoung.Methods.CliqueLeaf.Rows

/-!
# Atlas 133: verified clique common-leaf example

graph6: `E~a?`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

`H_{r,k}` is the cone over `K_{r-1}` together with `k` isolated
vertices.  Conditioning on the apex gives
`t(H,W) = ∫ dⁿ·t(K_{r-1},W_x)`; the tangent line of the clique
polynomial at `2 - 1/p` and the weighted rooted-triangle inequality
turn that into the target `pᵏA_r(p)`.  The chromatic polynomial
comes from `k` clique-attachments at one vertex of `K_r`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph133

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (2, 3)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 133
  vertexCount := 6
  edgeCount := 8
  chromaticNumber := 4
  graph6 := "E~a?"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.CliqueLeaf.cliqueLeafGraph 1 2).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.CliqueLeaf.cliqueLeafGraph 1 2) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.CliqueLeaf.satisfiesLowerBound_42)

end Taeyoung.Examples.Graph133
