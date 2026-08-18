import Taeyoung.Foundation
import Taeyoung.Methods.CliqueLeaf.Rows

/-!
# Atlas 45: verified clique common-leaf example

graph6: `DJ{`.  The edge-list definition below is the Lean graph;
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

namespace Taeyoung.Examples.Graph045

open Taeyoung

def graph : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 45
  vertexCount := 5
  edgeCount := 7
  chromaticNumber := 4
  graph6 := "DJ{"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 5 ≃ Fin 5 where
  toFun := ![4, 1, 2, 3, 0]
  invFun := ![4, 1, 2, 3, 0]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 5) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.CliqueLeaf.cliqueLeafGraph 1 1).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.CliqueLeaf.cliqueLeafGraph 1 1) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.CliqueLeaf.satisfiesLowerBound_41)

end Taeyoung.Examples.Graph045
