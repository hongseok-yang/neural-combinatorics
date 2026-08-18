import Taeyoung.Foundation
import Taeyoung.Methods.PureChordal.Main
import Taeyoung.Methods.PureChordal.Certificates.Cliques

/-!
# Atlas 18: verified pure-chordal clique example

graph6: `C~`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

`K4` is its own unique maximal clique, so the one-bag certificate
`Certificates.cliqueDecomp` applies.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph018

open Taeyoung

def graph : SimpleGraph (Fin 4) :=
  graphFromEdges 4 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 18
  vertexCount := 4
  edgeCount := 6
  chromaticNumber := 4
  graph6 := "C~"
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
      ((⊤ : SimpleGraph (Fin 4))).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : ((⊤ : SimpleGraph (Fin 4))) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    ((Taeyoung.Methods.PureChordal.Certificates.cliqueDecomp 4).satisfiesLowerBound
      (by norm_num))

end Taeyoung.Examples.Graph018
