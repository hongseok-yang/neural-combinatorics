import Taeyoung.Foundation
import Taeyoung.Methods.Negative.Chromatic
import Taeyoung.Methods.RootedSOS.Gram
import Taeyoung.Methods.RootedSOS.Interval

/-!
# Atlas 43 (the house graph): finite and chromatic reduction

This is the graph-specific shell around the exact rooted-SOS certificate from
`notes/atlas43_exact_rooted_sos.tex`.  The analytic certificate will prove
`house_bound`; this file discharges the remaining finite graph and chromatic
work and turns that inequality into the catalogue proposition.

The graph is a four-cycle `0-1-2-3-0` with a roof vertex `4` on the edge
`0-3`.  Its chromatic polynomial is

```
r (r - 1) (r - 2) (r^2 - 3r + 3),
```

so the catalogue target is

```
p (2p - 1) (3p^2 - 3p + 1).
```
-/

open MeasureTheory Finset Polynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Taeyoung.Methods.RootedSOS.House

open Taeyoung Taeyoung.Methods.Negative

/-- Atlas 43, in the same labelling as the catalogue row. -/
def houseGraph : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (0, 3), (0, 4), (1, 2), (2, 3), (3, 4)]

instance : DecidableRel houseGraph.Adj := graphFromEdges_decidableAdj _ _

/-! ## Chromatic data -/

theorem surj_house_0 : surjCount houseGraph 0 = 0 := by decide +kernel
theorem surj_house_1 : surjCount houseGraph 1 = 0 := by decide +kernel
theorem surj_house_2 : surjCount houseGraph 2 = 0 := by decide +kernel
theorem surj_house_3 : surjCount houseGraph 3 = 18 := by decide +kernel
theorem surj_house_4 : surjCount houseGraph 4 = 96 := by decide +kernel

theorem surj_house_5 : surjCount houseGraph 5 = 120 := by
  rw [surjCount_card houseGraph]
  decide

/-- Every proper-colouring count, reconstructed from the six finite
surjective-colouring counts above. -/
theorem properAssignmentCount_house (k : ℕ) :
    properAssignmentCount houseGraph k =
      18 * k.choose 3 + 96 * k.choose 4 + 120 * k.choose 5 := by
  rw [properAssignmentCount_eq_sum houseGraph k]
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
    surj_house_0, surj_house_1, surj_house_2, surj_house_3, surj_house_4,
    surj_house_5]
  ring

theorem houseChromaticNumber : IsChromaticNumber houseGraph 3 where
  positive := by rw [properAssignmentCount_house]; decide
  zero_below k hk := by
    rw [properAssignmentCount_house]
    interval_cases k <;> decide

theorem houseChromaticPolynomial : IsChromaticPolynomial houseGraph
    (∑ j ∈ range (Fintype.card (Fin 5) + 1),
      C ((surjCount houseGraph j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_surjCount houseGraph

/-! ## The catalogue bridge -/

/-- The closed form of the Atlas 43 chromatic target. -/
noncomputable def houseTarget (p : ℝ) : ℝ :=
  p * (2 * p - 1) * (3 * p ^ 2 - 3 * p + 1)

/-- **A graphon proof of the exact house inequality implies the Atlas 43
catalogue proposition.**

This is the interface consumed by the rooted-SOS certificate: its analytic
side only has to establish `houseTarget p ≤ t(houseGraph,W)` on `p ≥ 1/2`.
The chromatic polynomial, chromatic number, admissibility conversion, and the
endpoint `p = 1` are all handled here. -/
theorem satisfiesLowerBound_house_of_bound
    (house_bound : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] (W : Graphon Ω μ),
        (1 : ℝ) / 2 ≤ cliqueDensity 2 W →
          houseTarget (cliqueDensity 2 W) ≤ homDensity houseGraph W) :
    SatisfiesLowerBound houseGraph := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = ∑ j ∈ range (Fintype.card (Fin 5) + 1),
      C ((surjCount houseGraph j : ℝ) / (j).factorial) *
        ∏ i ∈ range j, (X - C (i : ℝ)) :=
    IsChromaticPolynomial.unique (H := houseGraph) hP houseChromaticPolynomial
  have hreq : r = 3 :=
    IsChromaticNumber.unique (H := houseGraph) hr houseChromaticNumber
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := house_bound W hp
  change chromaticTarget (V := Fin 5) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num [houseTarget] at hkey
    exact hkey
  · rw [chromaticTarget_of_ne_one _ hone]
    have hcalc : (1 - cliqueDensity 2 W) ^ Fintype.card (Fin 5) *
        Polynomial.eval (1 / (1 - cliqueDensity 2 W))
          (∑ j ∈ range (Fintype.card (Fin 5) + 1),
            C ((surjCount houseGraph j : ℝ) / (j).factorial) *
              ∏ i ∈ range j, (X - C (i : ℝ))) =
        houseTarget (cliqueDensity 2 W) := by
      simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.prod_range_succ, Finset.prod_range_zero,
        surj_house_0, surj_house_1, surj_house_2, surj_house_3, surj_house_4,
        surj_house_5, houseTarget, eval_add, eval_mul, eval_sub, eval_C, eval_X,
        eval_one, eval_zero]
      field_simp
      ring
    rw [hcalc]
    exact hkey

end Taeyoung.Methods.RootedSOS.House
