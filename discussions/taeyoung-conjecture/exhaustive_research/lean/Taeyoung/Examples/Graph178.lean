import Taeyoung.Foundation
import Taeyoung.Methods.Atlas178.Rows

/-!
# Atlas 178: verified half-degree weighted-K4 example

graph6: `En}?`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Two `K4`s sharing a triangle, with a pendant leaf on one of the
two page vertices.  Integrating the leaf gives the exact identity
`t(H) = int A*K_1*K_0`, where `A` is the spine triangle weight and
`K_f(x) = int f(z)W(z,x0)W(z,x1)W(z,x2)`.  Cauchy-Schwarz in the
page variable gives `K_{1/2}^2 <= K_0*K_1`, and a second
Cauchy-Schwarz on the spine against the weight `A` gives
`t(H) >= I4^2/T` with `I4 = int sqrt(d)*kappa4` and `T = t(K3,W)`.
Two sharp supporting planes in the rooted coordinates `(d,A,tau)`,
written in `D = sqrt(d)` and `r = sqrt(p)` so that both are
polynomial, then give `I4 >= (3p-2)*I` and `I^2 >= p^2(2p-1)T` for
`I = int sqrt(d)*tau`.  Multiplying and cancelling the single
factor `T >= p(2p-1) >= 2/9 > 0` leaves the target.  Both planes
are exact nonnegative combinations of the feasibility slacks: no
box subdivision is used.  The chromatic polynomial
`r(r-1)^2(r-2)(r-3)^2` comes from the attachment tower spine
triangle, page, second page, leaf on the first page.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph178

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 178
  vertexCount := 6
  edgeCount := 10
  chromaticNumber := 4
  graph6 := "En}?"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![1, 3, 4, 0, 2, 5]
  invFun := ![3, 0, 4, 1, 2, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.Atlas178.graph178).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.Atlas178.graph178) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.Atlas178.satisfiesLowerBound_178)

end Taeyoung.Examples.Graph178
