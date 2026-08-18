import Taeyoung.Foundation.HomDensity
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Peeling one coordinate off an assignment integral

`homDensity` integrates over the finite product measure `assignmentMeasure V μ`.
Every method that reasons *vertex by vertex* — conditioning on a root, reading a
cycle density as an iterated kernel — needs to turn that single product integral
into an iterated one.  This file provides the one lemma that does it.

The statement is restricted to bounded measurable integrands, which is the only
case that occurs here (`graphWeight` is bounded by `1`), and which lets every
integrability side condition be discharged internally.
-/

open MeasureTheory

namespace Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A bounded measurable function is integrable for the assignment measure. -/
lemma integrable_of_bounded {V : Type*} [Fintype V] [DecidableEq V]
    {f : (V → Ω) → ℝ} (hmeas : Measurable f) {C : ℝ} (hbdd : ∀ x, |f x| ≤ C) :
    Integrable f (assignmentMeasure V μ) :=
  (integrable_const (μ := assignmentMeasure V μ) C).mono'
    hmeas.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hbdd x)

/-- Prepending a fixed point is measurable in the remaining coordinates. -/
lemma measurable_fin_cons {n : ℕ} (a : Ω) :
    Measurable fun y : Fin n → Ω ↦ (Fin.cons a y : Fin (n + 1) → Ω) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  refine Fin.cases ?_ ?_ i
  · simpa using measurable_const
  · intro j
    simpa using measurable_pi_apply j

/-- The measurable equivalence `(Fin (n+1) → Ω) ≃ᵐ Ω × (Fin n → Ω)` splitting off
the coordinate `0`, together with the fact that it preserves the product
measure. -/
lemma measurePreserving_assignment_succ (n : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Ω) 0)
      (assignmentMeasure (Fin (n + 1)) μ)
      (μ.prod (assignmentMeasure (Fin n) μ)) := by
  simpa [assignmentMeasure] using
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ μ) 0

@[simp] lemma piFinSuccAbove_symm_apply (n : ℕ) (a : Ω) (y : Fin n → Ω) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Ω) 0).symm (a, y) =
      Fin.cons a y := by
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']

/-- **Peel the first coordinate.**  A bounded measurable integrand over
`Fin (n+1)` assignments integrates as an outer integral in the coordinate `0`
and an inner assignment integral over the remaining `n` coordinates. -/
theorem integral_assignmentMeasure_succ {n : ℕ} (f : (Fin (n + 1) → Ω) → ℝ)
    (hmeas : Measurable f) {C : ℝ} (hbdd : ∀ x, |f x| ≤ C) :
    ∫ x, f x ∂assignmentMeasure (Fin (n + 1)) μ =
      ∫ a, (∫ y, f (Fin.cons a y) ∂assignmentMeasure (Fin n) μ) ∂μ := by
  classical
  have hmp := measurePreserving_assignment_succ (μ := μ) n
  have hcomp : ∫ x, f x ∂assignmentMeasure (Fin (n + 1)) μ =
      ∫ p, f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Ω) 0).symm p)
        ∂(μ.prod (assignmentMeasure (Fin n) μ)) := by
    rw [← hmp.integral_comp'
      (g := fun p ↦ f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ Ω) 0).symm p))]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by simp)
  rw [hcomp]
  have hmeas' : Measurable fun p : Ω × (Fin n → Ω) ↦
      f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Ω) 0).symm p) :=
    hmeas.comp (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ Ω) 0).symm.measurable
  have hint : Integrable (fun p : Ω × (Fin n → Ω) ↦
      f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Ω) 0).symm p))
      (μ.prod (assignmentMeasure (Fin n) μ)) := by
    refine (integrable_const
      (μ := μ.prod (assignmentMeasure (Fin n) μ)) C).mono'
      hmeas'.aestronglyMeasurable (ae_of_all _ fun p ↦ ?_)
    rw [Real.norm_eq_abs]
    exact hbdd _
  rw [MeasureTheory.integral_prod _ hint]
  simp

/-! ### Peeling the last coordinate, and dropping unused ones

A graph with isolated vertices has a weight that ignores the coordinates those
vertices are assigned.  Removing them from the integral is the content of
`integral_assignmentMeasure_castAdd`: an integrand that only looks at the first
`m` of `m + k` coordinates integrates to the same value over `Fin m`.  The route
is the same peel as above, taken at `Fin.last` instead of `0`, so that the
discarded coordinate is the outer one. -/

lemma measurePreserving_assignment_last (n : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Ω) (Fin.last n))
      (assignmentMeasure (Fin (n + 1)) μ)
      (μ.prod (assignmentMeasure (Fin n) μ)) := by
  simpa [assignmentMeasure] using
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ μ) (Fin.last n)

@[simp] lemma piFinSuccAbove_last_symm_apply (n : ℕ) (a : Ω) (y : Fin n → Ω) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Ω) (Fin.last n)).symm (a, y) =
      Fin.snoc y a := by
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_last']

/-- **Peel the last coordinate.** -/
theorem integral_assignmentMeasure_last {n : ℕ} (f : (Fin (n + 1) → Ω) → ℝ)
    (hmeas : Measurable f) {C : ℝ} (hbdd : ∀ x, |f x| ≤ C) :
    ∫ x, f x ∂assignmentMeasure (Fin (n + 1)) μ =
      ∫ a, (∫ y, f (Fin.snoc y a) ∂assignmentMeasure (Fin n) μ) ∂μ := by
  classical
  have hmp := measurePreserving_assignment_last (μ := μ) n
  have hcomp : ∫ x, f x ∂assignmentMeasure (Fin (n + 1)) μ =
      ∫ p, f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Ω)
          (Fin.last n)).symm p)
        ∂(μ.prod (assignmentMeasure (Fin n) μ)) := by
    rw [← hmp.integral_comp'
      (g := fun p ↦ f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ Ω) (Fin.last n)).symm p))]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by simp)
  rw [hcomp]
  have hmeas' : Measurable fun p : Ω × (Fin n → Ω) ↦
      f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Ω)
        (Fin.last n)).symm p) :=
    hmeas.comp (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ Ω) (Fin.last n)).symm.measurable
  have hint : Integrable (fun p : Ω × (Fin n → Ω) ↦
      f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Ω)
        (Fin.last n)).symm p))
      (μ.prod (assignmentMeasure (Fin n) μ)) := by
    refine (integrable_const
      (μ := μ.prod (assignmentMeasure (Fin n) μ)) C).mono'
      hmeas'.aestronglyMeasurable (ae_of_all _ fun p ↦ ?_)
    rw [Real.norm_eq_abs]
    exact hbdd _
  rw [MeasureTheory.integral_prod _ hint]
  simp

/-- Dropping the last coordinate, when the integrand ignores it. -/
theorem integral_assignmentMeasure_castSucc {n : ℕ} (g : (Fin n → Ω) → ℝ)
    (hmeas : Measurable g) {C : ℝ} (hbdd : ∀ z, |g z| ≤ C) :
    ∫ x, g (fun i ↦ x i.castSucc) ∂assignmentMeasure (Fin (n + 1)) μ =
      ∫ z, g z ∂assignmentMeasure (Fin n) μ := by
  have hmeas' : Measurable fun x : Fin (n + 1) → Ω ↦ g (fun i ↦ x i.castSucc) :=
    hmeas.comp (measurable_pi_lambda _ fun i ↦ measurable_pi_apply _)
  rw [integral_assignmentMeasure_last _ hmeas' (fun x ↦ hbdd _)]
  simp only [Fin.snoc_castSucc]
  simp

/-- **Isolated coordinates drop out.**  An integrand that only looks at the first
`m` of `m + k` coordinates has the same integral over `Fin m`. -/
theorem integral_assignmentMeasure_castAdd {m : ℕ} (g : (Fin m → Ω) → ℝ)
    (hmeas : Measurable g) {C : ℝ} (hbdd : ∀ z, |g z| ≤ C) (k : ℕ) :
    ∫ x, g (fun i ↦ x (Fin.castAdd k i)) ∂assignmentMeasure (Fin (m + k)) μ =
      ∫ z, g z ∂assignmentMeasure (Fin m) μ := by
  induction k with
  | zero =>
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      congr 1
  | succ k ih =>
      calc ∫ x, g (fun i ↦ x (Fin.castAdd (k + 1) i))
            ∂assignmentMeasure (Fin (m + (k + 1))) μ
          = ∫ x : Fin (m + k + 1) → Ω,
              (fun z : Fin (m + k) → Ω ↦ g fun i ↦ z (Fin.castAdd k i))
                (fun j ↦ x j.castSucc) ∂assignmentMeasure (Fin (m + k + 1)) μ := by
            refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
            simp only []
            congr 1
        _ = ∫ z, g (fun i ↦ z (Fin.castAdd k i)) ∂assignmentMeasure (Fin (m + k)) μ :=
            integral_assignmentMeasure_castSucc _
              (hmeas.comp (measurable_pi_lambda _ fun i ↦ measurable_pi_apply _))
              (fun z ↦ hbdd _)
        _ = ∫ z, g z ∂assignmentMeasure (Fin m) μ := ih

end Taeyoung
