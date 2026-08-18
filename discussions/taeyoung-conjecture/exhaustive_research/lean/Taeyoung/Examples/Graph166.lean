import Taeyoung.Foundation
import Taeyoung.Methods.Negative.LocalTuran

/-!
# Atlas 166: verified Turán-local counterexample

graph6: `ElfO`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The witness is the two-scale perturbation of `T2`, a rational step
graphon on a uniform finite space.  Its density and edge density are single
kernel evaluations of sums of natural numbers, by
`Methods/Negative/StepGraphon.lean`; the chromatic data comes from the
surjective counts of `Methods/Negative/Chromatic.lean`.  See
`notes/turan_local_and_high_density_negative_tests.tex`.
-/

namespace Taeyoung.Examples.Graph166

open Taeyoung

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 3), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (3, 4), (3, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 166
  vertexCount := 6
  edgeCount := 9
  chromaticNumber := 3
  graph6 := "ElfO"
  status := .negative
  formalization := .verified

/-- Vertex relabelling carrying the method representative to this graph. -/
def relabel : Fin 6 ≃ Fin 6 where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide
  right_inv := by decide

/-- The relabelling is an adjacency correspondence, checked by computation. -/
theorem iso_adj (a b : Fin 6) :
    graph.Adj (relabel a) (relabel b) ↔ (Taeyoung.Methods.Negative.graph166).Adj a b := by
  revert a b
  decide

/-- The method representative is this Atlas graph, up to relabelling. -/
def iso : (Taeyoung.Methods.Negative.graph166) ≃g graph where
  toEquiv := relabel
  map_rel_iff' := by intro a b; exact iso_adj a b

/-- Fully checked refutation of the common catalogue proposition. -/
theorem status : ViolatesLowerBound graph :=
  ViolatesLowerBound.of_iso iso (Taeyoung.Methods.Negative.violatesLowerBound_166)

end Taeyoung.Examples.Graph166
