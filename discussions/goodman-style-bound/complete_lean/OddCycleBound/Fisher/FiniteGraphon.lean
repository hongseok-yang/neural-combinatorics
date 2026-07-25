import OddCycleBound.Fisher.FiniteTheorem
import OddCycleBound.Fisher.GraphonContinuity
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite graphs as uniform graphons

This file records the exact normalization dictionary between Fisher's finite
clique counts and the graphon interface.
-/

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound

universe u

variable {V : Type u} [Fintype V] [Nonempty V] [DecidableEq V]
variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- Uniform probability measure on a nonempty finite type. -/
noncomputable def finiteUniformMeasure : Measure V :=
  (PMF.uniformOfFintype V).toMeasure

instance : IsProbabilityMeasure (finiteUniformMeasure (V := V)) := by
  unfold finiteUniformMeasure
  infer_instance

theorem finiteUniform_integral (f : V → ℝ) :
    ∫ x, f x ∂(finiteUniformMeasure (V := V)) =
      (∑ x, f x) / (Fintype.card V : ℝ) := by
  rw [finiteUniformMeasure, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [smul_eq_mul]
  change (Finset.univ.sum fun x : V =>
    (Fintype.card V : ℝ)⁻¹ * f x) = _
  rw [← Finset.mul_sum]
  rw [div_eq_mul_inv]
  ring

/-- The `0/1` adjacency kernel of a finite simple graph. -/
def finiteGraphKernel (G : SimpleGraph V) [DecidableRel G.Adj] : V → V → ℝ :=
  fun x y => if G.Adj x y then 1 else 0

theorem finiteGraphKernel_isGraphon
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsGraphon (finiteGraphKernel G) (finiteUniformMeasure (V := V)) := by
  refine ⟨measurable_of_finite _, ?_, ?_, ?_⟩
  · intro x y
    by_cases h : G.Adj x y <;> simp [finiteGraphKernel, h]
  · intro x y
    by_cases h : G.Adj x y <;> simp [finiteGraphKernel, h]
  · intro x y
    simp only [finiteGraphKernel]
    by_cases h : G.Adj x y
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hyx => h hyx.symm)]

theorem edgeDensity_finiteGraphKernel
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeDensity (finiteGraphKernel G) (finiteUniformMeasure (V := V)) =
      2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ 2 := by
  simp only [edgeDensity, mean, degree]
  simp_rw [finiteUniform_integral]
  have hsum :
      (∑ x : V, ∑ y : V, finiteGraphKernel G x y) =
        2 * (G.edgeFinset.card : ℝ) := by
    have hreal := congrArg (fun n : ℕ => (n : ℝ))
      G.sum_degrees_eq_twice_card_edges
    push_cast at hreal
    simp only [finiteGraphKernel]
    simp_rw [Finset.sum_boole]
    simp_rw [← SimpleGraph.neighborFinset_eq_filter,
      SimpleGraph.card_neighborFinset_eq_degree]
    exact hreal
  simp only [div_eq_mul_inv]
  change (Finset.univ.sum (fun x : V =>
    (Finset.univ.sum fun y : V => finiteGraphKernel G x y) *
      (Fintype.card V : ℝ)⁻¹)) * (Fintype.card V : ℝ)⁻¹ = _
  rw [← Finset.sum_mul, hsum]
  ring

private theorem finiteGraphKernel_triangle_row
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (∑ y : V, ∑ z : V,
      finiteGraphKernel G x y * finiteGraphKernel G y z * finiteGraphKernel G z x) =
      2 * (Fisher.cliqueCount
        (G.induce (↑(G.neighborFinset x) : Set V)) 2 : ℝ) := by
  have hsum :
      (∑ y : V, ∑ z : V,
        finiteGraphKernel G x y * finiteGraphKernel G y z * finiteGraphKernel G z x) =
      ∑ y ∈ G.neighborFinset x, ∑ z ∈ G.neighborFinset x,
        if G.Adj y z then (1 : ℝ) else 0 := by
    simp [finiteGraphKernel, SimpleGraph.neighborFinset_eq_filter,
      ← Finset.sum_filter, SimpleGraph.adj_comm]
  rw [hsum]
  have hsub :
      (∑ y ∈ G.neighborFinset x, ∑ z ∈ G.neighborFinset x,
        if G.Adj y z then (1 : ℝ) else 0) =
      ∑ y : (↑(G.neighborFinset x) : Set V),
        ((G.induce (↑(G.neighborFinset x) : Set V)).degree y : ℝ) := by
    rw [Finset.sum_subtype (p := fun y : V =>
      y ∈ (↑(G.neighborFinset x) : Set V)) (G.neighborFinset x) (by simp)]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.sum_boole]
    norm_cast
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun z hz =>
      (⟨z, (Finset.mem_filter.mp hz).1⟩ :
        (↑(G.neighborFinset x) : Set V)))
    · intro z hz
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]
      exact (Finset.mem_filter.mp hz).2
    · intro a ha b hb hab
      exact congrArg Subtype.val hab
    · intro z hz
      refine ⟨z, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨z.property, by simpa only [SimpleGraph.mem_neighborFinset,
        SimpleGraph.induce_adj] using hz⟩
  rw [hsub]
  have hdeg :=
    (G.induce (↑(G.neighborFinset x) : Set V)).sum_degrees_eq_twice_card_edges
  have hdegR :
      (∑ y : (↑(G.neighborFinset x) : Set V),
        ((G.induce (↑(G.neighborFinset x) : Set V)).degree y : ℝ)) =
      2 * ((G.induce (↑(G.neighborFinset x) : Set V)).edgeFinset.card : ℝ) := by
    exact_mod_cast hdeg
  rw [hdegR]
  change 2 * (_ : ℝ) = 2 * (_ : ℝ)
  congr 1
  norm_cast
  exact Fisher.cliqueCount_two _ |>.symm

private theorem finiteGraphKernel_triangle_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ x : V, ∑ y : V, ∑ z : V,
      finiteGraphKernel G x y * finiteGraphKernel G y z * finiteGraphKernel G z x) =
      6 * (Fisher.cliqueCount G 3 : ℝ) := by
  simp_rw [finiteGraphKernel_triangle_row G]
  rw [← Finset.mul_sum]
  have h := Fisher.sum_cliqueCount_neighbor G 2
  have hR :
      (∑ x : V, (Fisher.cliqueCount
        (G.induce (↑(G.neighborFinset x) : Set V)) 2 : ℝ)) =
      3 * (Fisher.cliqueCount G 3 : ℝ) := by
    exact_mod_cast h
  rw [hR]
  ring

theorem triangleDensity_finiteGraphKernel
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    trace (finiteUniformMeasure (V := V))
        (compPow (finiteUniformMeasure (V := V)) (finiteGraphKernel G) 2) =
      6 * (Fisher.cliqueCount G 3 : ℝ) / (Fintype.card V : ℝ) ^ 3 := by
  rw [trace_compPow_two_eq_triangleIntegral (finiteGraphKernel_isGraphon G)]
  simp_rw [finiteUniform_integral]
  simp_rw [← Finset.sum_div]
  rw [finiteGraphKernel_triangle_sum G]
  ring

/-- Fisher's finite density inequality, expressed directly in the graphon
normalization of a finite simple graph. -/
theorem fisher_density_form_finiteGraphKernel
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hplo : 1 / 2 ≤ edgeDensity (finiteGraphKernel G)
      (finiteUniformMeasure (V := V)))
    (hphi : edgeDensity (finiteGraphKernel G)
      (finiteUniformMeasure (V := V)) ≤ 2 / 3) :
    edgeDensity (finiteGraphKernel G) (finiteUniformMeasure (V := V)) - 4 / 9 -
        (4 / 9) * (1 - 3 * edgeDensity (finiteGraphKernel G)
          (finiteUniformMeasure (V := V)) / 2) ^ ((3 : ℝ) / 2) ≤
      trace (finiteUniformMeasure (V := V))
        (compPow (finiteUniformMeasure (V := V)) (finiteGraphKernel G) 2) := by
  have hn : 0 < Fisher.nR G := by
    simp [Fisher.nR, Fisher.cliqueCount_one, Fintype.card_pos]
  apply Fisher.fisher_density_form G hn
      (edgeDensity (finiteGraphKernel G) (finiteUniformMeasure (V := V)))
      (trace (finiteUniformMeasure (V := V))
        (compPow (finiteUniformMeasure (V := V)) (finiteGraphKernel G) 2))
  · rw [edgeDensity_finiteGraphKernel]
    simp [Fisher.eR, Fisher.nR, Fisher.cliqueCount_one,
      Fisher.cliqueCount_two]
  · rw [triangleDensity_finiteGraphKernel]
    simp [Fisher.TR, Fisher.nR, Fisher.cliqueCount_one]
  · exact hplo
  · exact hphi

end OddCycleBound
