import Taeyoung.Foundation
import Taeyoung.Methods.BowtieLeaf

/-!
# Atlas 119: verified bowtie-outer-leaf example

graph6: `EtoO`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

Peeling the leaf gives `int F(y) d(y_1)` for the bowtie weight `F`.
The four outer vertices are one orbit of the bowtie's automorphism
group, so the degree may sit at any of them; averaging and applying
the arithmetic-geometric mean inequality puts exponent `1/4` at all
four.  The two triangles then use disjoint variables, so the result
factors as `int R(x)^2` for `R(x) = int int W(x,y)W(x,z)W(y,z)
d(y)^{1/4}d(z)^{1/4}`, and Cauchy-Schwarz drops it to `(int R)^2`.
Averaging the three rotations of `int R` and applying the
arithmetic-geometric mean inequality again reaches exponent `1/6` at
every triangle vertex, which is `M^3 t(K3,W;nu)` for the
`d^{1/6}`-biased measure.  Goodman there, `M^6 <= p` (Jensen) and
`p^8 <= (M^6)^2 s^6` (three-factor Holder at `(3/4,1/8,1/8)`) close
it, the rescaling reducing to `(s-p)(4ps-1) >= 0`.
It is transported to this graph along the explicit relabelling `relabel`, whose
adjacency correspondence `iso_adj` is checked by kernel computation.
-/

namespace Taeyoung.Examples.Graph119

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 4), (2, 3), (3, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 119
  vertexCount := 6
  edgeCount := 7
  chromaticNumber := 3
  graph6 := "EtoO"
  status := .positive
  formalization := .verified

/-- Vertex relabelling carrying the certificate representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![0, 3, 2, 1, 4, 5]
  invFun := ![0, 3, 2, 1, 4, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔
      (Taeyoung.Methods.BowtieLeaf.bowtieLeaf).Adj a b := by
  revert a b
  decide

/-- The certificate representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.BowtieLeaf.bowtieLeaf) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked instance of the common catalogue proposition. -/
theorem status : SatisfiesLowerBound graph :=
  SatisfiesLowerBound.of_iso iso
    (Taeyoung.Methods.BowtieLeaf.satisfiesLowerBound_119)

end Taeyoung.Examples.Graph119
