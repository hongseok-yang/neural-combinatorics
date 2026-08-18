import Taeyoung.Foundation
import Taeyoung.Methods.Negative.Tensor
import Taeyoung.Methods.Negative.Chromatic

/-!
# Atlas 197: verified tensor-Turán counterexample

graph6: `E}^G`.  The edge-list definition below is the Lean graph;
the graph6 string is stable external metadata until a verified decoder exists.

The witness is `tensorTuran 4 6`, the categorical product of two balanced
complete multipartite graphons, of edge density
`p = (1 - 1/4)(1 - 1/6) = 5/8`.  The chromatic number is
3, so admissibility asks only `p ≥ 1/2`.  The two sides are

```
t = χ_H(4)·χ_H(6) / 24^6 = 1075/331776,
Φ = (1 - p)^6·χ_H(1/(1-p))   = 55/16384,
```

and `t < Φ`, so this graph refutes the catalogue proposition.

**Where the values of `χ_H` come from.**  Not from `decide`: `χ_H(6)` alone
would be `6^6 = 46656` functions.  Only the surjective counts are
evaluated by kernel reduction — and only up to `j = 5`, since `j = 6` is
`surjCount_card`.  Every value of the chromatic polynomial is then read off
`properAssignmentCount_eq_sum`.
-/

open Finset Polynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Taeyoung.Examples.Graph197

open Taeyoung Taeyoung.Methods.Negative

def graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (3, 4), (4, 5)]

instance : DecidableRel graph.Adj := graphFromEdges_decidableAdj _ _

def metadata : CatalogueRow where
  atlasId := 197
  vertexCount := 6
  edgeCount := 11
  chromaticNumber := 3
  graph6 := "E}^G"
  status := .negative
  formalization := .verified

/-! ### The surjective colouring counts -/

theorem surj_0 : surjCount graph 0 = 0 := by decide +kernel
theorem surj_1 : surjCount graph 1 = 0 := by decide +kernel
theorem surj_2 : surjCount graph 2 = 0 := by decide +kernel
theorem surj_3 : surjCount graph 3 = 6 := by decide +kernel
theorem surj_4 : surjCount graph 4 = 96 := by decide +kernel
theorem surj_5 : surjCount graph 5 = 480 := by decide +kernel

/-- The top count is `6!` for *every* graph on 6 vertices: a
surjection between equal finite cardinalities is a bijection, and an
injective assignment separates every pair. -/
theorem surj_6 : surjCount graph 6 = 720 := by
  rw [surjCount_card graph]
  decide

/-! ### The chromatic data -/

/-- Every colouring count of this graph, from the surjective counts above. -/
theorem count (k : ℕ) :
    properAssignmentCount graph k = 6 * k.choose 3 + 96 * k.choose 4 + 480 * k.choose 5 + 720 * k.choose 6 := by
  rw [properAssignmentCount_eq_sum graph k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    surj_0, surj_1, surj_2, surj_3, surj_4, surj_5, surj_6]
  ring

/-- `χ_H(4) = 120`, the first tensor factor. -/
theorem count_4 : properAssignmentCount graph 4 = 120 := by
  rw [count]
  decide

/-- `χ_H(6) = 5160`, the second tensor factor. -/
theorem count_6 : properAssignmentCount graph 6 = 5160 := by
  rw [count]
  decide

theorem chromNum : IsChromaticNumber graph 3 where
  positive := by rw [count]; decide
  zero_below k hk := by
    rw [count]
    interval_cases k <;> decide

theorem chromPoly : IsChromaticPolynomial graph
    (∑ j ∈ range (Fintype.card (Fin 6) + 1),
      C ((surjCount graph j : ℝ) / (j).factorial) * ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount graph

/-! ### The witness -/

/-- Fully checked refutation of the common catalogue proposition. -/
theorem status : ViolatesLowerBound graph := by
  have hp : (1 - 1 / ((4 : ℕ) : ℝ)) * (1 - 1 / ((6 : ℕ) : ℝ)) =
      5 / 8 := by
    norm_num
  refine violatesLowerBound_of_tensor graph chromPoly chromNum 4 6 ?_ ?_
  · rw [admissibleDensity, hp]; norm_num
  · rw [homDensity_tensorTuran, hp,
      chromaticTarget_of_ne_one _
        (by norm_num : (5 : ℝ) / 8 ≠ 1)]
    rw [count_4, count_6]
    simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero,
      surj_0, surj_1, surj_2, surj_3, surj_4, surj_5, surj_6,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero]
    norm_num

end Taeyoung.Examples.Graph197
