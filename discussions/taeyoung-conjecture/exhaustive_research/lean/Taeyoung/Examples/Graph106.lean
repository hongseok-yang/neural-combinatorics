import Taeyoung.Foundation
import Taeyoung.Methods.PureChordal.Main
import Taeyoung.Methods.PureChordal.Certificates.N6

/-!
# Atlas 106: verified pure-chordal example

graph6: `EJaG`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The bound comes from the checked clique-tree certificate
`Certificates.G6_1`: 2 bags, every maximal clique of size 3.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph106

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 4), (0, 5), (1, 2), (1, 3), (2, 3), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 106
  vertexCount := 6
  edgeCount := 6
  chromaticNumber := 3
  graph6 := "EJaG"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.PureChordal.Certificates.G6_1.graph).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.PureChordal.Certificates.G6_1.graph) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.PureChordal.Certificates.G6_1.decomp.satisfiesLowerBound
      (by norm_num))

end Taeyoung.Examples.Graph106
