import Taeyoung.Foundation
import Taeyoung.Methods.MixedBranch

/-!
# Atlas 95: verified mixed rooted-triangle-branch example

graph6: `EG}?`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Peeling every branch at the root gives `int tau(x) A(x) d(x)` for
`A = T_W d`.  The pointwise Goodman bound `tau >= 2A - p`, weighted
by `A d >= 0`, turns that into `2 int d A^2 - p int d A`.  The
weighted Cauchy-Schwarz `(int d A)^2 <= (int d)(int d A^2)` and path
Sidorenko `int d A >= p^3` then close it, through the factorization
`p(2C - pB) - p(2p^5 - p^4) >= (B - p^3)(2(B + p^3) - p^2) >= 0`
with `B = int d A` and `C = int d A^2`.  No symmetrization is used.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph095

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 4), (0, 5), (1, 2), (1, 4), (2, 4), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 95
  vertexCount := 6
  edgeCount := 6
  chromaticNumber := 3
  graph6 := "EG}?"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![4, 1, 2, 3, 0, 5]
  invFun := ![4, 1, 2, 3, 0, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.MixedBranch.r11).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.MixedBranch.r11) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.MixedBranch.satisfiesLowerBound_95)

end Taeyoung.Examples.Graph095
