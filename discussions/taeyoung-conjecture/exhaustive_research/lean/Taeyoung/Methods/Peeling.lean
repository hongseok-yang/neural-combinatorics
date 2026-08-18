import Taeyoung.Foundation

/-!
# Coordinate peeling, once and for all

Every row so far has re-run the same ladder of `integral_assignmentMeasure_succ`
calls inline, carrying its own `Fin.cons` bookkeeping.  That is fine when the
intermediate expressions are what the proof wants to look at, but when the goal
is simply *"turn the assignment integral into an iterated one"* the ladder is
pure noise.

This file does it once, for the arities the six-vertex catalogue needs: a
function of `n` explicit coordinates integrates over `assignmentMeasure (Fin n)`
to the `n`-fold iterated integral.  The bound is fixed at `1` because every
integrand in the project is a product of graphon values and degrees.
-/

open MeasureTheory

namespace Taeyoung.Methods

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Two coordinates of an assignment, paired through the kernel. -/
lemma measurable_coord_pair {n : ℕ} (W : Graphon Ω μ) (i j : Fin n) :
    Measurable fun y : Fin n → Ω ↦ W (y i) (y j) :=
  Measurable.comp (f := fun y : Fin n → Ω ↦ (y i, y j)) W.measurable
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j))

lemma integral_assignment_fin_two {g : Ω → Ω → ℝ}
    (hm : Measurable fun y : Fin 2 → Ω ↦ g (y 0) (y 1))
    (hb : ∀ y : Fin 2 → Ω, |g (y 0) (y 1)| ≤ 1) :
    (∫ y : Fin 2 → Ω, g (y 0) (y 1) ∂assignmentMeasure (Fin 2) μ) =
      ∫ a0, ∫ a1, g a0 a1 ∂μ ∂μ := by
  rw [integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 1 → Ω ↦ g ((Fin.cons a0 y : Fin 2 → Ω) 0)
      ((Fin.cons a0 y : Fin 2 → Ω) 1))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [show (∫ _y : Fin 0 → Ω,
      g ((Fin.cons a0 (Fin.cons a1 (_ : Fin 0 → Ω)) : Fin 2 → Ω) 0)
        ((Fin.cons a0 (Fin.cons a1 (_ : Fin 0 → Ω)) : Fin 2 → Ω) 1)
      ∂assignmentMeasure (Fin 0) μ) = g a0 a1 by simp]

lemma integral_assignment_fin_three {g : Ω → Ω → Ω → ℝ}
    (hm : Measurable fun y : Fin 3 → Ω ↦ g (y 0) (y 1) (y 2))
    (hb : ∀ y : Fin 3 → Ω, |g (y 0) (y 1) (y 2)| ≤ 1) :
    (∫ y : Fin 3 → Ω, g (y 0) (y 1) (y 2) ∂assignmentMeasure (Fin 3) μ) =
      ∫ a0, ∫ a1, ∫ a2, g a0 a1 a2 ∂μ ∂μ ∂μ := by
  rw [integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 2 → Ω ↦ g ((Fin.cons a0 y : Fin 3 → Ω) 0)
      ((Fin.cons a0 y : Fin 3 → Ω) 1) ((Fin.cons a0 y : Fin 3 → Ω) 2))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 1 → Ω ↦ g
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 3 → Ω) 0)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 3 → Ω) 1)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 3 → Ω) 2))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  show (∫ _y : Fin 0 → Ω, g a0 a1 a2 ∂assignmentMeasure (Fin 0) μ) = g a0 a1 a2
  simp

lemma integral_assignment_fin_four {g : Ω → Ω → Ω → Ω → ℝ}
    (hm : Measurable fun y : Fin 4 → Ω ↦ g (y 0) (y 1) (y 2) (y 3))
    (hb : ∀ y : Fin 4 → Ω, |g (y 0) (y 1) (y 2) (y 3)| ≤ 1) :
    (∫ y : Fin 4 → Ω, g (y 0) (y 1) (y 2) (y 3)
        ∂assignmentMeasure (Fin 4) μ) =
      ∫ a0, ∫ a1, ∫ a2, ∫ a3, g a0 a1 a2 a3 ∂μ ∂μ ∂μ ∂μ := by
  rw [integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 3 → Ω ↦ g ((Fin.cons a0 y : Fin 4 → Ω) 0)
      ((Fin.cons a0 y : Fin 4 → Ω) 1) ((Fin.cons a0 y : Fin 4 → Ω) 2)
      ((Fin.cons a0 y : Fin 4 → Ω) 3))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 2 → Ω ↦ g
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 4 → Ω) 0)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 4 → Ω) 1)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 4 → Ω) 2)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 4 → Ω) 3))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 1 → Ω ↦ g
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 4 → Ω) 0)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 4 → Ω) 1)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 4 → Ω) 2)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 4 → Ω) 3))
    (hm.comp ((measurable_fin_cons a0).comp
      ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
  simp only []
  show (∫ _y : Fin 0 → Ω, g a0 a1 a2 a3 ∂assignmentMeasure (Fin 0) μ) =
    g a0 a1 a2 a3
  simp

lemma integral_assignment_fin_five {g : Ω → Ω → Ω → Ω → Ω → ℝ}
    (hm : Measurable fun y : Fin 5 → Ω ↦ g (y 0) (y 1) (y 2) (y 3) (y 4))
    (hb : ∀ y : Fin 5 → Ω, |g (y 0) (y 1) (y 2) (y 3) (y 4)| ≤ 1) :
    (∫ y : Fin 5 → Ω, g (y 0) (y 1) (y 2) (y 3) (y 4)
        ∂assignmentMeasure (Fin 5) μ) =
      ∫ a0, ∫ a1, ∫ a2, ∫ a3, ∫ a4, g a0 a1 a2 a3 a4 ∂μ ∂μ ∂μ ∂μ ∂μ := by
  rw [integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ g ((Fin.cons a0 y : Fin 5 → Ω) 0)
      ((Fin.cons a0 y : Fin 5 → Ω) 1) ((Fin.cons a0 y : Fin 5 → Ω) 2)
      ((Fin.cons a0 y : Fin 5 → Ω) 3) ((Fin.cons a0 y : Fin 5 → Ω) 4))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 3 → Ω ↦ g
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 5 → Ω) 0)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 5 → Ω) 1)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 5 → Ω) 2)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 5 → Ω) 3)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 5 → Ω) 4))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 2 → Ω ↦ g
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 5 → Ω) 0)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 5 → Ω) 1)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 5 → Ω) 2)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 5 → Ω) 3)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 5 → Ω) 4))
    (hm.comp ((measurable_fin_cons a0).comp
      ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 1 → Ω ↦ g
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))) : Fin 5 → Ω) 0)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))) : Fin 5 → Ω) 1)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))) : Fin 5 → Ω) 2)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))) : Fin 5 → Ω) 3)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))) : Fin 5 → Ω) 4))
    (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
      ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a4 ↦ ?_)
  simp only []
  show (∫ _y : Fin 0 → Ω, g a0 a1 a2 a3 a4 ∂assignmentMeasure (Fin 0) μ) =
    g a0 a1 a2 a3 a4
  simp

/-- **Coordinate permutations preserve the assignment integral.**  This is the
measure-preserving half of `homDensity_iso`, exposed on its own so that a proof
can symmetrise an integrand that is *not* a graph weight — a graph weight
multiplied by a degree at one coordinate, say. -/
lemma integral_assignment_perm {n : ℕ} (e : Fin n ≃ Fin n)
    (g : (Fin n → Ω) → ℝ) :
    (∫ y, g y ∂assignmentMeasure (Fin n) μ) =
      ∫ y, g (fun v ↦ y (e v)) ∂assignmentMeasure (Fin n) μ := by
  let q : (Fin n → Ω) ≃ᵐ (Fin n → Ω) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ Ω) e.symm
  have hq : MeasurePreserving q (assignmentMeasure (Fin n) μ)
      (assignmentMeasure (Fin n) μ) := by
    simpa [q, assignmentMeasure] using
      (measurePreserving_piCongrLeft
        (α := fun _ : Fin n ↦ Ω) (fun _ : Fin n ↦ μ) e.symm)
  rw [← hq.integral_comp' (g := g)]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  show g (q y) = g fun v ↦ y (e v)
  have hqy : q y = fun v ↦ y (e v) := by
    funext v
    simp [q, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [hqy]

lemma integral_assignment_fin_six {g : Ω → Ω → Ω → Ω → Ω → Ω → ℝ}
    (hm : Measurable fun y : Fin 6 → Ω ↦ g (y 0) (y 1) (y 2) (y 3) (y 4) (y 5))
    (hb : ∀ y : Fin 6 → Ω, |g (y 0) (y 1) (y 2) (y 3) (y 4) (y 5)| ≤ 1) :
    (∫ y : Fin 6 → Ω, g (y 0) (y 1) (y 2) (y 3) (y 4) (y 5)
        ∂assignmentMeasure (Fin 6) μ) =
      ∫ a0, ∫ a1, ∫ a2, ∫ a3, ∫ a4, ∫ a5,
        g a0 a1 a2 a3 a4 a5 ∂μ ∂μ ∂μ ∂μ ∂μ ∂μ := by
  rw [integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ g ((Fin.cons a0 y : Fin 6 → Ω) 0)
      ((Fin.cons a0 y : Fin 6 → Ω) 1) ((Fin.cons a0 y : Fin 6 → Ω) 2)
      ((Fin.cons a0 y : Fin 6 → Ω) 3) ((Fin.cons a0 y : Fin 6 → Ω) 4)
      ((Fin.cons a0 y : Fin 6 → Ω) 5))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ g
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 6 → Ω) 0)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 6 → Ω) 1)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 6 → Ω) 2)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 6 → Ω) 3)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 6 → Ω) 4)
      ((Fin.cons a0 (Fin.cons a1 y) : Fin 6 → Ω) 5))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 3 → Ω ↦ g
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 6 → Ω) 0)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 6 → Ω) 1)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 6 → Ω) 2)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 6 → Ω) 3)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 6 → Ω) 4)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 6 → Ω) 5))
    (hm.comp ((measurable_fin_cons a0).comp
      ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 2 → Ω ↦ g
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))) : Fin 6 → Ω) 0)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))) : Fin 6 → Ω) 1)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))) : Fin 6 → Ω) 2)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))) : Fin 6 → Ω) 3)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))) : Fin 6 → Ω) 4)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))) : Fin 6 → Ω) 5))
    (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
      ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a4 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 1 → Ω ↦ g
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y)))) :
        Fin 6 → Ω) 0)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y)))) :
        Fin 6 → Ω) 1)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y)))) :
        Fin 6 → Ω) 2)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y)))) :
        Fin 6 → Ω) 3)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y)))) :
        Fin 6 → Ω) 4)
      ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y)))) :
        Fin 6 → Ω) 5))
    (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
      ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
        (measurable_fin_cons a4))))))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a5 ↦ ?_)
  simp only []
  show (∫ _y : Fin 0 → Ω, g a0 a1 a2 a3 a4 a5 ∂assignmentMeasure (Fin 0) μ) =
    g a0 a1 a2 a3 a4 a5
  simp

end Taeyoung.Methods
