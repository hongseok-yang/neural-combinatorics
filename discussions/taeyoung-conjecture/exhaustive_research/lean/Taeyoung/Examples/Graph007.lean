import Taeyoung.Foundation
import Taeyoung.Methods.PureChordal.Main
import Taeyoung.Methods.PureChordal.Certificates.Cliques

/-!
# Atlas 7: verified pure-chordal clique example

graph6: `Bw`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

`K3` is its own unique maximal clique, so the one-bag certificate
`Certificates.cliqueDecomp` applies.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph007

open Taeyoung

def graph : SimpleGraph (Fin 3) :=
  graphFromEdges 3 [(0, 1), (0, 2), (1, 2)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 7
  vertexCount := 3
  edgeCount := 3
  chromaticNumber := 3
  graph6 := "Bw"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 3 ≃ Fin 3 where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 3) :
    graph.Adj (relabel a) (relabel b) ↔
      ((⊤ : SimpleGraph (Fin 3))).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : ((⊤ : SimpleGraph (Fin 3))) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    ((Taeyoung.Methods.PureChordal.Certificates.cliqueDecomp 3).satisfiesLowerBound
      (by norm_num))

end Taeyoung.Examples.Graph007
