import Taeyoung.Foundation.ChromaticExtension
import Taeyoung.Foundation.HomDensity
import Taeyoung.Foundation.ChromaticPolynomial
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# The balanced complete multipartite graphon

On the uniform probability space `Fin k`, put weight `0` inside a part and
weight `1` between distinct parts.  Homomorphisms into this graphon are exactly
proper `k`-colourings.
-/

namespace Taeyoung.Methods.PureChordal

open MeasureTheory
open scoped ENNReal BigOperators

/-- Uniform probability measure on a nonempty finite type. -/
noncomputable def finiteUniformMeasure (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] : Measure α :=
  (PMF.uniformOfFintype α).toMeasure

instance finiteUniformMeasure_isProbability
    (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] :
    IsProbabilityMeasure (finiteUniformMeasure α) := by
  unfold finiteUniformMeasure
  infer_instance

theorem finiteUniform_integral
    {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → ℝ) :
    ∫ x, f x ∂finiteUniformMeasure α =
      (∑ x, f x) / (Fintype.card α : ℝ) := by
  rw [finiteUniformMeasure, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  change (Finset.univ.sum fun x : α =>
    (Fintype.card α : ℝ)⁻¹ * f x) = _
  rw [← Finset.mul_sum, div_eq_mul_inv]
  ring

/-- The balanced complete `k`-partite graphon.  Each point of `Fin k`
represents one part of mass `1/k`. -/
def balancedMultipartiteGraphon (k : ℕ) [NeZero k] :
    Graphon (Fin k) (finiteUniformMeasure (Fin k)) where
  toFun x y := if x = y then 0 else 1
  measurable := measurable_of_finite _
  nonneg := by intro x y; split <;> positivity
  le_one := by intro x y; split <;> norm_num
  symm := by
    intro x y
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]

@[simp] lemma balancedMultipartiteGraphon_apply
    (k : ℕ) [NeZero k] (x y : Fin k) :
    balancedMultipartiteGraphon k x y = if x = y then 0 else 1 := rfl

theorem assignmentMeasure_finiteUniform
    {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] :
    assignmentMeasure V (finiteUniformMeasure α) =
      finiteUniformMeasure (V → α) := by
  apply Measure.ext_of_singleton
  intro x
  rw [assignmentMeasure, Measure.pi_singleton]
  unfold finiteUniformMeasure
  simp_rw [PMF.toMeasure_uniformOfFintype_apply _
    (MeasurableSet.singleton _)]
  simp
  exact ENNReal.inv_pow.symm

section ColoringDensity

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

noncomputable local instance instDecidableIsProperAssignment
    {k : ℕ} (x : V → Fin k) :
    Decidable (IsProperAssignment H x) :=
  Classical.propDecidable _

lemma graphWeight_balancedMultipartite
    (k : ℕ) [NeZero k] (x : V → Fin k) :
    graphWeight H (balancedMultipartiteGraphon k) x =
      if IsProperAssignment H x then 1 else 0 := by
  classical
  by_cases hx : IsProperAssignment H x
  · rw [if_pos hx]
    apply Finset.prod_eq_one
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have huv : H.Adj u v := by
          simpa [SimpleGraph.mem_edgeFinset] using he
        simp [edgeValue, Sym2.lift_mk, hx huv]
  · rw [if_neg hx]
    simp only [IsProperAssignment, not_forall] at hx
    rcases hx with ⟨u, v, huv, hsame⟩
    apply Finset.prod_eq_zero (i := s(u, v))
    · simpa [SimpleGraph.mem_edgeFinset] using huv
    · have hsame' : x u = x v := not_ne_iff.mp hsame
      simp [edgeValue, Sym2.lift_mk, hsame']

/-- On a uniform finite space, homomorphism density is the proportion of
proper colour assignments. -/
theorem homDensity_balancedMultipartite
    (k : ℕ) [NeZero k] :
    homDensity H (balancedMultipartiteGraphon k) =
      (properAssignmentCount H k : ℝ) /
        (k : ℝ) ^ Fintype.card V := by
  classical
  rw [homDensity, assignmentMeasure_finiteUniform,
    finiteUniform_integral]
  simp_rw [graphWeight_balancedMultipartite H k]
  rw [show (∑ x : V → Fin k,
      if IsProperAssignment H x then (1 : ℝ) else 0) =
      properAssignmentCount H k by
        simp [properAssignmentCount]]
  simp


theorem cliqueDensity_balancedMultipartite
    (s k : ℕ) [NeZero k] :
    cliqueDensity s (balancedMultipartiteGraphon k) =
      (k.descFactorial s : ℝ) / (k : ℝ) ^ s := by
  rw [cliqueDensity, homDensity_balancedMultipartite,
    properAssignmentCount_top]
  simp

/-- The edge density of the balanced complete `k`-partite graphon is
`1 - 1/k`. -/
theorem edgeDensity_balancedMultipartite
    (k : ℕ) [NeZero k] :
    cliqueDensity 2 (balancedMultipartiteGraphon k) =
      1 - 1 / (k : ℝ) := by
  rw [cliqueDensity_balancedMultipartite]
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  rw [Nat.descFactorial]
  simp only [Nat.descFactorial_one, Nat.cast_mul, Nat.cast_sub
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)), Nat.cast_one]
  field_simp

end ColoringDensity

end Taeyoung.Methods.PureChordal
