import Taeyoung.Foundation
import Taeyoung.Methods.OddCycleCone

/-!
# Atlas 187: verified clique--odd-cycle join example

graph6: `Ehfw`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The base bound is the analytic `C5` inequality of
`Methods/OddCycleC5`, which assumes nothing about the edge density.
Its target factors as `z(2z-1)(z^2 + (1-z)^2)`, so it vanishes at
`1/2` and is nonnegative above it, and the quartic remainder of its
tangent at `c` factors as `(w-c)^2` times a polynomial with
nonnegative coefficients in `w - 1/2` and `c - 1/2`.  The cone has
no simplicial vertex, so its chromatic polynomial comes from the
general cone identity `chi_{K1 v F}(x) = x*chi_F(x-1)` rather than
from an attachment tower.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph187

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (2, 5), (3, 4), (3, 5), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 187
  vertexCount := 6
  edgeCount := 10
  chromaticNumber := 4
  graph6 := "Ehfw"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Link.coneGraph Taeyoung.Methods.OddCycleC5.c5).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.Link.coneGraph Taeyoung.Methods.OddCycleC5.c5) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.OddCycleCone.satisfiesLowerBound_187)

end Taeyoung.Examples.Graph187
