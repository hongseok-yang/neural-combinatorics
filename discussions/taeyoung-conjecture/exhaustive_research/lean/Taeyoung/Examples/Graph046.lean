import Taeyoung.Foundation
import Taeyoung.Methods.PureChordal.Main
import Taeyoung.Methods.PureChordal.Certificates.N5

/-!
# Atlas 46: verified pure-chordal example

graph6: `DF{`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The bound comes from the checked clique-tree certificate
`Certificates.G5_2`: 3 bags, every maximal clique of size 3.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph046

open Taeyoung

def graph : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 3), (0, 4), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 46
  vertexCount := 5
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "DF{"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 5 ≃ Fin 5 where
  toFun := ![3, 4, 0, 1, 2]
  invFun := ![2, 3, 4, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 5) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.PureChordal.Certificates.G5_2.graph).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.PureChordal.Certificates.G5_2.graph) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.PureChordal.Certificates.G5_2.decomp.satisfiesLowerBound
      (by norm_num))

end Taeyoung.Examples.Graph046
