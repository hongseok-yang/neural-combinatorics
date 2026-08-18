import Taeyoung.Foundation
import Taeyoung.Methods.Negative.Tensor
import Taeyoung.Methods.Negative.Chromatic

/-!
# Atlas 50: verified tensor-Turán counterexample

graph6: `Dl{`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The witness is `tensorTuran 3 5`, the categorical product of two balanced
complete multipartite graphons, of edge density
`p = (1 - 1/3)(1 - 1/5) = 8/15`.  The chromatic number is
3, so admissibility asks only `p ≥ 1/2`.  The two sides are

```
t = χ_H(3)·χ_H(5) / 15^5 = 56/16875,
Φ = (1 - p)^5·χ_H(1/(1-p))   = 344/50625,
```

and `t < Φ`, so this graph refutes the catalogue proposition.

**Where the values of `χ_H` come from.**  Not from `decide`: `χ_H(5)` alone
would be `5^5 = 3125` functions.  Only the surjective counts are
evaluated by kernel reduction — and only up to `j = 4`, since `j = 5` is
`surjCount_card`.  Every value of the chromatic polynomial is then read off
`properAssignmentCount_eq_sum`.
-/

open Finset Polynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Taeyoung.Examples.Graph050

open Taeyoung Taeyoung.Methods.Negative

def graph : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (0, 3), (0, 4), (1, 2), (1, 4), (2, 3), (2, 4), (3, 4)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 50
  vertexCount := 5
  edgeCount := 8
  chromaticNumber := 3
  graph6 := "Dl{"
  status := .negative
  formalization := .verified

/-! ### The surjective colouring counts -/

theorem surj_0 : surjCount graph 0 = 0 := by decide +kernel
theorem surj_1 : surjCount graph 1 = 0 := by decide +kernel
theorem surj_2 : surjCount graph 2 = 0 := by decide +kernel
theorem surj_3 : surjCount graph 3 = 6 := by decide +kernel
theorem surj_4 : surjCount graph 4 = 48 := by decide +kernel

/-- The top count is `5!` for *every* graph on 5 vertices: a
surjection between equal finite cardinalities is a bijection, and an
injective assignment separates every pair. -/
theorem surj_5 : surjCount graph 5 = 120 := by
  rw [surjCount_card graph]
  decide

/-! ### The chromatic data -/

/-- Every colouring count of this graph, from the surjective counts above. -/
theorem count (k : ℕ) :
    properAssignmentCount graph k = 6 * k.choose 3 + 48 * k.choose 4 + 120 * k.choose 5 := by
  rw [properAssignmentCount_eq_sum graph k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    surj_0, surj_1, surj_2, surj_3, surj_4, surj_5]
  ring

/-- `χ_H(3) = 6`, the first tensor factor. -/
theorem count_3 : properAssignmentCount graph 3 = 6 := by
  rw [count]
  decide

/-- `χ_H(5) = 420`, the second tensor factor. -/
theorem count_5 : properAssignmentCount graph 5 = 420 := by
  rw [count]
  decide

theorem chromNum : IsChromaticNumber graph 3 where
  positive := by rw [count]; decide
  zero_below k hk := by
    rw [count]
    interval_cases k <;> decide

theorem chromPoly : IsChromaticPolynomial graph
    (∑ j ∈ range (Fintype.card (Fin 5) + 1),
      C ((surjCount graph j : ℝ) / (j).factorial) * ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph

/-! ### The witness -/

/-- Fully checked refutation of the common catalogue proposition. -/
theorem status : ViolatesLowerBound graph := by
  have hp : (1 - 1 / ((3 : ℕ) : ℝ)) * (1 - 1 / ((5 : ℕ) : ℝ)) =
      8 / 15 := by
    norm_num
  refine violatesLowerBound_of_tensor graph chromPoly chromNum 3 5 ?_ ?_
  · rw [admissibleDensity, hp]; norm_num
  · rw [homDensity_tensorTuran, hp,
      chromaticTarget_of_ne_one _
        (by norm_num : (8 : ℝ) / 15 ≠ 1)]
    rw [count_3, count_5]
    simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero,
      surj_0, surj_1, surj_2, surj_3, surj_4, surj_5,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
    norm_num

end Taeyoung.Examples.Graph050
