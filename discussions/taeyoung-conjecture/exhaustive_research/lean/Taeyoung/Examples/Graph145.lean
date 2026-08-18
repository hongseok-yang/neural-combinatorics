import Taeyoung.Foundation
import Taeyoung.Methods.Atlas145

/-!
# Atlas 145: verified page-concentration example

graph6: `Exe_`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

A 4-cycle with two triangle pages on one cycle edge.  Moving one
page to the adjacent cycle edge gives Atlas 148, whose
full-interval theorem is proved in `Methods/Atlas148`.  Labelling
the cycle so that its two opposite corners are the outer
integration variables makes the other two cycle vertices
integrate independently, and for fixed corners the three arm
integrals `P = int W W`, `Q = int W W S`, `R = int W W S^2`
satisfy `t(148) = int int Q^2` and `t(145) = int int P*R`.  So
the note's square identity, which needs a reflection of a
four-fold integral, becomes the pointwise weighted
Cauchy-Schwarz `Q^2 <= P*R`.  The frame copy of Atlas 148 is
carried to its own labelling by `homDensity_iso`.  The chromatic
polynomial `r(r-1)(r-2)^2(r^2-3r+3)` is the same as Atlas 148's
and comes from surjective counts.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph145

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (2, 3), (2, 5), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 145
  vertexCount := 6
  edgeCount := 8
  chromaticNumber := 3
  graph6 := "Exe_"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![0, 3, 2, 4, 1, 5]
  invFun := ![0, 4, 2, 1, 3, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Atlas145.frame145).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.Atlas145.frame145) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.Atlas145.satisfiesLowerBound_145)

end Taeyoung.Examples.Graph145
