import Taeyoung.Foundation
import Taeyoung.Methods.PureChordal.Main
import Taeyoung.Methods.PureChordal.Certificates.Cliques

/-!
# Atlas 52: verified pure-chordal clique example

graph6: `D~{`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

`K5` is its own unique maximal clique, so the one-bag certificate
`Certificates.cliqueDecomp` applies.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph052

open Taeyoung

def graph : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 52
  vertexCount := 5
  edgeCount := 10
  chromaticNumber := 5
  graph6 := "D~{"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 5 ≃ Fin 5 where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 5) :
    graph.Adj (relabel a) (relabel b) ↔
      ((⊤ : SimpleGraph (Fin 5))).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : ((⊤ : SimpleGraph (Fin 5))) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    ((Taeyoung.Methods.PureChordal.Certificates.cliqueDecomp 5).satisfiesLowerBound
      (by norm_num))

end Taeyoung.Examples.Graph052
