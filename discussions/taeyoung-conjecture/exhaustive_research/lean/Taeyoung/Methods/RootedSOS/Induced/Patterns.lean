import Taeyoung.Foundation.ProductIntegral
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Finite independent edge patterns. Bits are `Fin 2`, so their complete enumeration
has the explicit base-two equivalence `finFunctionFinEquiv`. Unspecified edges
are summed out; no graphon edge is assumed to be Boolean.
-/

open Finset MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Induced

variable {E : Type*} [Fintype E] [DecidableEq E]

def bitWeight (w : Real) (b : Fin 2) : Real := if b = 1 then w else 1 - w

def patternWeight (w : E → Real) (b : E → Fin 2) : Real :=
  ∏ e, bitWeight (w e) (b e)

theorem bitWeight_nonneg {w : Real} (h0 : 0 ≤ w) (h1 : w ≤ 1) (b : Fin 2) :
    0 ≤ bitWeight w b := by
  unfold bitWeight
  split_ifs <;> linarith

theorem bitWeight_le_one {w : Real} (h0 : 0 ≤ w) (h1 : w ≤ 1) (b : Fin 2) :
    bitWeight w b ≤ 1 := by
  unfold bitWeight
  split_ifs <;> linarith

theorem patternWeight_nonneg {w : E → Real}
    (h0 : ∀ e, 0 ≤ w e) (h1 : ∀ e, w e ≤ 1) (b : E → Fin 2) :
    0 ≤ patternWeight w b :=
  Finset.prod_nonneg fun e _ => bitWeight_nonneg (h0 e) (h1 e) _

theorem patternWeight_le_one {w : E → Real}
    (h0 : ∀ e, 0 ≤ w e) (h1 : ∀ e, w e ≤ 1) (b : E → Fin 2) :
    patternWeight w b ≤ 1 :=
  Finset.prod_le_one (fun e _ => bitWeight_nonneg (h0 e) (h1 e) _)
    (fun e _ => bitWeight_le_one (h0 e) (h1 e) _)

theorem sum_patternWeight (w : E → Real) : ∑ b, patternWeight w b = 1 := by
  simp only [patternWeight]
  rw [← Fintype.prod_sum]
  simp [Fin.sum_univ_two, bitWeight]

/-- The marginal of a specified set of independent edge bits. -/
theorem patternWeight_marginal (w : E → Real) (S : Finset E) (p : E → Fin 2) :
    (∑ b : E → Fin 2, patternWeight w b *
      if ∀ e ∈ S, b e = p e then 1 else 0) =
      ∏ e ∈ S, bitWeight (w e) (p e) := by
  classical
  let v (e : E) (t : Fin 2) : Real :=
    if e ∈ S ∧ t ≠ p e then 0 else bitWeight (w e) t
  have hterm (b : E → Fin 2) :
      patternWeight w b * (if ∀ e ∈ S, b e = p e then 1 else 0) =
        ∏ e, v e (b e) := by
    by_cases hb : ∀ e ∈ S, b e = p e
    · rw [if_pos hb, mul_one]
      unfold patternWeight
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : e ∈ S
      · simp [v, he, hb e he]
      · simp [v, he]
    · rw [if_neg hb, mul_zero]
      push Not at hb
      obtain ⟨e, he, hne⟩ := hb
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [v, he, hne])
  simp_rw [hterm]
  rw [← Fintype.prod_sum]
  have hv (e : E) : (∑ t, v e t) =
      if e ∈ S then bitWeight (w e) (p e) else 1 := by
    by_cases he : e ∈ S
    · have hp : p e = 0 ∨ p e = 1 := by omega
      rcases hp with hp | hp <;> simp [Fin.sum_univ_two, v, he, hp, bitWeight]
    · simp [Fin.sum_univ_two, v, he, bitWeight]
  simp_rw [hv]
  rw [← Finset.prod_subset (Finset.subset_univ S) (by
    intro e _ he
    simp [he])]
  exact Finset.prod_congr rfl fun e he => by simp [he]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A complete induced pattern on an explicitly indexed collection of pairs. -/
def inducedWeight (pairs : E → V × V) (p : E → Fin 2)
    (W : Taeyoung.Graphon Ω μ) (z : V → Ω) : Real :=
  patternWeight (fun e => W (z (pairs e).1) (z (pairs e).2)) p

theorem measurable_inducedWeight (pairs : E → V × V) (p : E → Fin 2)
    (W : Taeyoung.Graphon Ω μ) : Measurable (inducedWeight pairs p W) := by
  apply Finset.measurable_fun_prod
  intro e _
  have hw : Measurable fun z : V → Ω => W (z (pairs e).1) (z (pairs e).2) := by
    have hp : Measurable fun z : V → Ω => (z (pairs e).1, z (pairs e).2) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    simpa only [Function.comp_def, Function.uncurry] using
      W.measurable.comp hp
  dsimp [bitWeight]
  split_ifs
  · exact hw
  · exact measurable_const.sub hw

theorem inducedWeight_nonneg (pairs : E → V × V) (p : E → Fin 2)
    (W : Taeyoung.Graphon Ω μ) (z : V → Ω) : 0 ≤ inducedWeight pairs p W z :=
  patternWeight_nonneg (fun _ => W.nonneg _ _) (fun _ => W.le_one _ _) p

theorem inducedWeight_le_one (pairs : E → V × V) (p : E → Fin 2)
    (W : Taeyoung.Graphon Ω μ) (z : V → Ω) : inducedWeight pairs p W z ≤ 1 :=
  patternWeight_le_one (fun _ => W.nonneg _ _) (fun _ => W.le_one _ _) p

theorem integrable_inducedWeight (pairs : E → V × V) (p : E → Fin 2)
    (W : Taeyoung.Graphon Ω μ) :
    Integrable (inducedWeight pairs p W) (Taeyoung.assignmentMeasure V μ) :=
  Taeyoung.integrable_of_bounded (measurable_inducedWeight pairs p W)
    (fun z => by
      rw [abs_of_nonneg (inducedWeight_nonneg pairs p W z)]
      exact inducedWeight_le_one pairs p W z)

noncomputable def inducedDensity (pairs : E → V × V) (p : E → Fin 2)
    (W : Taeyoung.Graphon Ω μ) : Real :=
  ∫ z, inducedWeight pairs p W z ∂Taeyoung.assignmentMeasure V μ

theorem inducedDensity_nonneg (pairs : E → V × V) (p : E → Fin 2)
    (W : Taeyoung.Graphon Ω μ) : 0 ≤ inducedDensity pairs p W :=
  integral_nonneg fun z => inducedWeight_nonneg pairs p W z

theorem sum_inducedDensity (pairs : E → V × V) (W : Taeyoung.Graphon Ω μ) :
    ∑ p, inducedDensity pairs p W = 1 := by
  simp only [inducedDensity]
  rw [← integral_finset_sum _ (fun p _ => integrable_inducedWeight pairs p W)]
  simp only [inducedWeight, sum_patternWeight]
  simp

end Taeyoung.Methods.RootedSOS.Induced
