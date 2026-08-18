import Taeyoung.Foundation
import Taeyoung.Methods.PagePawBranch.Rows

/-!
# Atlas 139: verified page-paw branch example

graph6: `Eju?`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

A two-page triangle book on the spine `0,1` with a triangle glued
along the page edge `0-2` at a new vertex `4`, and one leaf: at the
glued vertex for Atlas 139, at the exceptional page for Atlas 137.
Peeling the leaf and the glued vertex gives the exact identity
`t = int int W*H0*L_h`, where `L_h(x,y) = int W(x,z)W(y,z)h(x,z)` is
the branch operator and `h = H1` (Atlas 139) or `h(x,z) = d(z)H0(x,z)`
(Atlas 137).  Cauchy-Schwarz on the page variable gives
`L_sqrt(h)^2 <= H0*L_h`, which replaces the note's page-orbit
symmetrization; edge Cauchy-Schwarz and edge Jensen at exponent 3/2
then reduce everything to `int d^(1/3)*tau >= p^(4/3)(2p-1)`, from the
weighted rooted-triangle inequality and Jensen.  The chromatic
polynomial `x(x-1)^2(x-2)^3` comes from a three-step clique
attachment tower over `K3`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph139

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (2, 3), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 139
  vertexCount := 6
  edgeCount := 8
  chromaticNumber := 3
  graph6 := "Eju?"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![1, 3, 4, 2, 0, 5]
  invFun := ![4, 0, 3, 1, 2, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.PagePawBranch.bookNew).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.PagePawBranch.bookNew) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.PagePawBranch.satisfiesLowerBound_bookNew)

end Taeyoung.Examples.Graph139
