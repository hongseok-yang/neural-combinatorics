import Taeyoung.Foundation
import Taeyoung.Methods.TwoRoot.Rows

/-!
# Atlas 93: verified two-root book-leaf example

graph6: `EC{O`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Peeling every leaf and every page turns the density into
`int int W(x,y) d(x)^a d(y)^b H_0(x,y)^m`, with `H_0` the page
operator at exponent `0`.  Two inputs bound it: `H_0 >= d(x)+d(y)-1`
and, by AM-GM, `d(x)+d(y) >= 2Z` for `Z = sqrt(d(x)d(y))`, so the
integrand dominates `W Z^n max(2Z-1,0)^m` with `n = a+b`.  Two
Cauchy-Schwarz steps in `ENNReal` give the geometric-mean estimate
`int int W Z >= p^2`, and the affine minorant of `z^n(2z-1)^m`
through `p` -- the tangent-line form of Jensen, valid below `1/2`
as well because the line has already crossed zero there --
integrates to `p^{n+1}(2p-1)^m`, the target.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph093

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 3), (0, 4), (1, 4), (2, 4), (3, 4), (3, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 93
  vertexCount := 6
  edgeCount := 6
  chromaticNumber := 3
  graph6 := "EC{O"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![3, 4, 0, 5, 1, 2]
  invFun := ![2, 4, 5, 0, 1, 3]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.TwoRoot.book93).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.TwoRoot.book93) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.TwoRoot.satisfiesLowerBound_93)

end Taeyoung.Examples.Graph093
