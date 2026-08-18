import Taeyoung.Foundation
import Taeyoung.Methods.K4Tail.Rows

/-!
# Atlas 142: verified K4 two-edge-tail example

graph6: `E~AG`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Conditioning the three non-tail clique vertices through the link at
`x` turns the rooted `K_4` density into `d(x)^3 t(K_3, W_x)`, and
Goodman inside the link, together with `tau >= 2A - p` and the
monotonicity of `z -> z(2z-1)_+`, gives the pointwise bound
`d(x) kappa_4(x) >= u (2u - d(x)^2)_+` for `u = (2A(x)-p)_+`.  A
supporting plane `L_p(d,a) = T_p + beta(d-p) + gamma(a-d^2)` lies
under `a` times that bound on the whole feasible region, and
integrates to `T_p` exactly because `int d = p` and `int A = int
d^2`.  The plane's slopes are forced by tangency at `(p,p^2)`; the
certificate is an explicit cubic factorization in `w = 4a-2p-d^2`,
whose two remainder coefficients reduce to one-variable polynomial
positivity on `[2/3,1]`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph142

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (2, 3), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 142
  vertexCount := 6
  edgeCount := 8
  chromaticNumber := 4
  graph6 := "E~AG"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.K4Tail.k4tail).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.K4Tail.k4tail) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.K4Tail.satisfiesLowerBound_142)

end Taeyoung.Examples.Graph142
