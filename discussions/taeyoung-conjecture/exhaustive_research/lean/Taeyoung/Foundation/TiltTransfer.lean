import Taeyoung.Foundation.ProductIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Assignment integrals against a tilted measure

Every *cone* methodology conditions on the image `x` of a distinguished vertex
and then invokes a theorem valid for **arbitrary** graphons, applied to the link
graphon on the tilted measure `g dμ`.  Carrying that out needs one identity: an
assignment integral against `g dμ` equals the assignment integral against `μ` of
the integrand weighted by `∏ v, g (y v)`.

At the level of measures this is `Measure.pi (fun _ ↦ μ.withDensity g) =
(Measure.pi fun _ ↦ μ).withDensity (fun y ↦ ∏ v, g (y v))`, which Mathlib does
not have; proving it through `Measure.pi_eq` would first need the product
factorisation of a lower integral over `Measure.pi`, which Mathlib does not have
either.  The integral form proved here needs neither.  It follows by induction on
the number of coordinates from two facts already available:

* `integral_assignmentMeasure_succ`, which peels one coordinate, and
* `integral_withDensity_eq_integral_toReal_smul`, the one-coordinate case.

As throughout, the statement is confined to bounded measurable integrands, which
lets every integrability side condition be discharged internally.
-/

open MeasureTheory

namespace Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The tilted measure -/

omit [IsProbabilityMeasure μ] in
/-- A nonnegative density of total mass one tilts a probability measure to a
probability measure. -/
lemma isProbabilityMeasure_withDensity_ofReal {g : Ω → ℝ}
    (hint : Integrable g μ) (hg0 : ∀ y, 0 ≤ g y) (hgone : ∫ y, g y ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity fun y ↦ ENNReal.ofReal (g y)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hg0), hgone,
    ENNReal.ofReal_one]

/-- A bounded nonnegative measurable function is integrable for a probability
measure. -/
lemma integrable_of_nonneg_le {g : Ω → ℝ} (hg : Measurable g)
    (hg0 : ∀ y, 0 ≤ g y) {C : ℝ} (hC : ∀ y, g y ≤ C) : Integrable g μ := by
  refine (integrable_const (μ := μ) C).mono' hg.aestronglyMeasurable
    (ae_of_all _ fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hg0 y)]
  exact hC y

/-! ### The transfer identity -/

/-- The coordinatewise product of a density is measurable. -/
lemma measurable_coord_prod {g : Ω → ℝ} (hg : Measurable g) (n : ℕ) :
    Measurable fun y : Fin n → Ω ↦ ∏ i, g (y i) :=
  Finset.univ.measurable_fun_prod fun i _ ↦ hg.comp (measurable_pi_apply i)

omit [MeasurableSpace Ω] in
lemma coord_prod_nonneg {g : Ω → ℝ} (hg0 : ∀ y, 0 ≤ g y) {n : ℕ}
    (y : Fin n → Ω) : 0 ≤ ∏ i, g (y i) :=
  Finset.prod_nonneg fun i _ ↦ hg0 (y i)

omit [MeasurableSpace Ω] in
lemma coord_prod_le {g : Ω → ℝ} (hg0 : ∀ y, 0 ≤ g y) {C : ℝ} (hC : ∀ y, g y ≤ C)
    {n : ℕ} (y : Fin n → Ω) : (∏ i, g (y i)) ≤ C ^ n := by
  calc ∏ i, g (y i) ≤ ∏ _i : Fin n, C :=
        Finset.prod_le_prod (fun i _ ↦ hg0 (y i)) (fun i _ ↦ hC (y i))
    _ = C ^ n := by simp

/-- Auxiliary `∀`-form of the transfer identity, so that the induction on the
number of coordinates can vary the integrand. -/
theorem integral_assignmentMeasure_withDensity_forall {g : Ω → ℝ}
    (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y) {Cg : ℝ} (hCg : ∀ y, g y ≤ Cg)
    (hgone : ∫ y, g y ∂μ = 1) (n : ℕ) :
    ∀ (f : (Fin n → Ω) → ℝ), Measurable f → ∀ B : ℝ, 0 ≤ B → (∀ z, |f z| ≤ B) →
      ∫ y, f y ∂assignmentMeasure (Fin n)
          (μ.withDensity fun y ↦ ENNReal.ofReal (g y)) =
        ∫ y, (∏ i, g (y i)) * f y ∂assignmentMeasure (Fin n) μ := by
  haveI hne : Nonempty Ω := by
    rcases isEmpty_or_nonempty Ω with h | h
    · have h1 : μ Set.univ = 1 := measure_univ
      rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
      exact absurd h1 (by simp)
    · exact h
  have hCg0 : 0 ≤ Cg :=
    (hg0 (Classical.arbitrary Ω)).trans (hCg (Classical.arbitrary Ω))
  have hgint : Integrable g μ := integrable_of_nonneg_le hg hg0 hCg
  haveI hprob : IsProbabilityMeasure (μ.withDensity fun y ↦ ENNReal.ofReal (g y)) :=
    isProbabilityMeasure_withDensity_ofReal hgint hg0 hgone
  induction n with
  | zero =>
      intro f _ B _ _
      have key : ∀ (ν : Measure (Fin 0 → Ω)) (_ : IsProbabilityMeasure ν),
          ∫ y, f y ∂ν = f default := by
        intro ν hν
        rw [integral_unique]
        simp [measureReal_def, hν.measure_univ]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
      rw [key _ inferInstance, key _ inferInstance]
  | succ n ih =>
      intro f hf B hB0 hB
      have hprodf : Measurable fun z : Fin (n + 1) → Ω ↦ (∏ i, g (z i)) * f z :=
        (measurable_coord_prod hg _).mul hf
      have hprodB : ∀ z : Fin (n + 1) → Ω,
          |(∏ i, g (z i)) * f z| ≤ Cg ^ (n + 1) * B := by
        intro z
        rw [abs_mul, abs_of_nonneg (coord_prod_nonneg hg0 z)]
        exact mul_le_mul (coord_prod_le hg0 hCg z) (hB z) (abs_nonneg _)
          (pow_nonneg hCg0 _)
      rw [integral_assignmentMeasure_succ
          (μ := μ.withDensity fun y ↦ ENNReal.ofReal (g y)) f hf hB,
        integral_assignmentMeasure_succ (μ := μ)
          (fun z ↦ (∏ i, g (z i)) * f z) hprodf hprodB]
      -- Rewrite each inner integral by the induction hypothesis.
      have hinner : ∀ a : Ω,
          ∫ y, f (Fin.cons a y) ∂assignmentMeasure (Fin n)
              (μ.withDensity fun y ↦ ENNReal.ofReal (g y)) =
            ∫ y, (∏ i, g (y i)) * f (Fin.cons a y)
              ∂assignmentMeasure (Fin n) μ := fun a ↦
        ih _ (hf.comp (measurable_fin_cons a)) B hB0 fun y ↦ hB _
      simp only [hinner]
      -- Untilt the remaining outer integral.
      rw [integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
        (ae_of_all _ fun a ↦ ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
      simp only [smul_eq_mul, ENNReal.toReal_ofReal (hg0 a)]
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      simp only []
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring

/-- **Transfer of an assignment integral along a tilt.**  Integrating a bounded
measurable `f` against the assignment measure of the tilted measure `g dμ` is the
same as integrating `(∏ i, g (y i)) * f y` against the assignment measure of `μ`.

This is the integral form of `Measure.pi_withDensity`, and is what lets a theorem
about arbitrary graphons be applied to a link. -/
theorem integral_assignmentMeasure_withDensity {g : Ω → ℝ}
    (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y) {Cg : ℝ} (hCg : ∀ y, g y ≤ Cg)
    (hgone : ∫ y, g y ∂μ = 1) {n : ℕ} (f : (Fin n → Ω) → ℝ) (hf : Measurable f)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, |f z| ≤ B) :
    ∫ y, f y ∂assignmentMeasure (Fin n)
        (μ.withDensity fun y ↦ ENNReal.ofReal (g y)) =
      ∫ y, (∏ i, g (y i)) * f y ∂assignmentMeasure (Fin n) μ :=
  integral_assignmentMeasure_withDensity_forall hg hg0 hCg hgone n f hf B hB0 hB

end Taeyoung
