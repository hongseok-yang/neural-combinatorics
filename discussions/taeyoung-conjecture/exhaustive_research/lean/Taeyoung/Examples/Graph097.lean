import Taeyoung.Foundation
import Taeyoung.Methods.AdjTail

/-!
# Atlas 97: verified adjacent-root leaf and two-edge-tail example

graph6: `EYWO`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The leaf and the two-edge tail sit at different triangle roots, so
peeling gives `int A(x) E(x)` for `E(x) = int int W(x,y)W(x,z)W(y,z)
d(y)`.  A two-edge inclusion-exclusion inside the triangle gives
`E >= C - (1-d)A` with `C = T_W(d^2)`, and `A^2 <= d C` is
Cauchy-Schwarz in the row measure, so the row reduces to the scalar
pair `(d, a) = (d(x), A(x))`.  The supporting plane `L_p(d,a) =
p^4(3-8p) + 2p^3(5p-2)d + p^2(5p-2)(a-d^2)` integrates to
`p^4(2p-1)` exactly, because `int d = p` and `int A = int d^2`.
Cleared of `d`, the active case is the ring identity
`a^2(a+d^2-d) - d L_p = (a-p^2)^2 (a+d^2-d) + p^2 (2X^2 + (2d+p)XY
+ (7p-2)dY^2)` at `X = a-pd`, `Y = d-p`, whose bracket is
nonnegative on `0 <= a <= d <= 1` by a split at `d = p/3`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph097

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 2), (1, 2), (1, 3), (1, 4), (2, 4), (3, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 97
  vertexCount := 6
  edgeCount := 6
  chromaticNumber := 3
  graph6 := "EYWO"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![1, 2, 4, 3, 5, 0]
  invFun := ![5, 0, 1, 3, 2, 4]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.AdjTail.adjTail).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.AdjTail.adjTail) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.AdjTail.satisfiesLowerBound_97)

end Taeyoung.Examples.Graph097
