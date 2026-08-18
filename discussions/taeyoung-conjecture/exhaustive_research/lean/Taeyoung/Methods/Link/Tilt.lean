import Taeyoung.Methods.Link.WeightedGoodman
import Taeyoung.Foundation.TiltTransfer

/-!
# The tilted link measure, and the global tangent lemma

Five of the catalogue's methodologies condition on the image `x` of a
distinguished vertex and then apply a *known bound for arbitrary graphons* to
the link.  Two ingredients are needed for that, and both are supplied here.

* `linkMeasure W x` is `W(x,·) dμ / d(x)`, a probability measure whenever
  `d(x) > 0`.  Because `Graphon` asks nothing of the measure beyond its being a
  probability measure — measurability, the bounds and symmetry are conditions on
  the kernel alone — the same `W` is a graphon on the link with no re-proving:
  that is `linkGraphon`.

* `tangent_of_convex` is the observation that a bound known only above a
  threshold `a` still yields its tangent line as a bound *everywhere*, provided
  the bounding function vanishes at `a` and is nondecreasing.  Below `a` the
  tangent is nonpositive, and homomorphism densities are nonnegative.

The lemma is stated with an explicit slope rather than `deriv`, so a caller
supplies the tangent inequality for its concrete polynomial (for the clique
polynomials `A_m` that is an `nlinarith` away) and never has to differentiate.
-/

open MeasureTheory

namespace Taeyoung.Methods.Link

open Taeyoung

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The tilted measure -/

/-- The link measure at `x`: `W(x,·) dμ` normalised by the degree. -/
noncomputable def linkMeasure (W : Graphon Ω μ) (x : Ω) : Measure Ω :=
  μ.withDensity fun y ↦ ENNReal.ofReal (W x y / degree W x)

lemma integrable_link_density (W : Graphon Ω μ) (x : Ω) :
    Integrable (fun y ↦ W x y / degree W x) μ := by
  have hrow : Measurable fun y ↦ W x y := measurable_row W.measurable x
  by_cases hx : degree W x = 0
  · simp [hx]
  · refine integrable_of_bdd (hrow.div_const _) (C := 1 / degree W x) fun y ↦ ?_
    rw [abs_div, abs_of_nonneg (W.nonneg x y), abs_of_nonneg (degree_nonneg W x)]
    gcongr <;> first
      | exact degree_nonneg W x
      | exact W.le_one x y

/-- At a point of positive degree, the link measure is a probability measure. -/
lemma linkMeasure_univ (W : Graphon Ω μ) {x : Ω} (hx : 0 < degree W x) :
    linkMeasure W x Set.univ = 1 := by
  have hrow : Measurable fun y ↦ W x y := measurable_row W.measurable x
  rw [linkMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_link_density W x)
    (ae_of_all _ fun y ↦ div_nonneg (W.nonneg x y) (degree_nonneg W x))]
  rw [integral_div]
  show ENNReal.ofReal (degree W x / degree W x) = 1
  rw [div_self (ne_of_gt hx)]
  simp

lemma isProbabilityMeasure_linkMeasure (W : Graphon Ω μ) {x : Ω}
    (hx : 0 < degree W x) : IsProbabilityMeasure (linkMeasure W x) :=
  ⟨linkMeasure_univ W hx⟩

/-- **The same kernel is a graphon on the link.**  `Graphon` constrains only the
kernel, so nothing has to be re-proved. -/
def linkGraphon (W : Graphon Ω μ) (x : Ω) : Graphon Ω (linkMeasure W x) where
  toFun := W.toFun
  measurable := W.measurable
  nonneg := W.nonneg
  le_one := W.le_one
  symm := W.symm

/-! ### Assignment integrals over the link -/

/-- **Untilting an assignment integral.**  Integrating a bounded measurable `f`
over assignments drawn from the link at `x` is the same as integrating it over
assignments drawn from `μ`, weighted by `∏ i, W x (y i)` and normalised by
`d(x) ^ n`.

This is what converts a statement about `linkGraphon W x` — obtained by applying
a theorem valid for *arbitrary* graphons — back into an ordinary rooted integral
against `μ`, and so is the bridge every cone methodology crosses. -/
theorem integral_assignmentMeasure_linkMeasure (W : Graphon Ω μ) {x : Ω}
    (hx : 0 < degree W x) {n : ℕ} (f : (Fin n → Ω) → ℝ) (hf : Measurable f)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, |f z| ≤ B) :
    ∫ y, f y ∂assignmentMeasure (Fin n) (linkMeasure W x) =
      (degree W x)⁻¹ ^ n *
        ∫ y, (∏ i, W x (y i)) * f y ∂assignmentMeasure (Fin n) μ := by
  have hrow : Measurable fun y ↦ W x y := measurable_row W.measurable x
  have hg : Measurable fun y ↦ W x y / degree W x := hrow.div_const _
  have hg0 : ∀ y, 0 ≤ W x y / degree W x := fun y ↦
    div_nonneg (W.nonneg x y) (degree_nonneg W x)
  have hCg : ∀ y, W x y / degree W x ≤ (degree W x)⁻¹ := fun y ↦ by
    rw [div_eq_mul_inv]
    calc W x y * (degree W x)⁻¹ ≤ 1 * (degree W x)⁻¹ :=
          mul_le_mul_of_nonneg_right (W.le_one x y)
            (inv_nonneg.mpr (degree_nonneg W x))
      _ = (degree W x)⁻¹ := one_mul _
  have hgone : ∫ y, W x y / degree W x ∂μ = 1 := by
    rw [integral_div]
    exact div_self (ne_of_gt hx)
  have hden : (∏ _i : Fin n, degree W x) = degree W x ^ n := by simp
  rw [show linkMeasure W x =
      μ.withDensity fun y ↦ ENNReal.ofReal (W x y / degree W x) from rfl,
    integral_assignmentMeasure_withDensity hg hg0 hCg hgone f hf hB0 hB,
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only []
  rw [Finset.prod_div_distrib, hden, div_eq_mul_inv, inv_pow]
  ring

/-! ### The global tangent lemma -/

/-- **A bound known only above a threshold gives its tangent line everywhere.**

`φ` bounds the density above `a` and vanishes at `a`; `s` is a nonnegative slope
for which the tangent line at `c` lies under `φ` on `[a,1]`.  Then the tangent
line lies under the density at *every* admissible `z`, including `z < a`, where
it is nonpositive while the density is not. -/
theorem tangent_of_convex {φ : ℝ → ℝ} {a c s z t : ℝ}
    (hφa : φ a = 0) (hs : 0 ≤ s)
    (htangent : ∀ w, a ≤ w → w ≤ 1 → φ c + s * (w - c) ≤ φ w)
    (ha1 : a ≤ 1) (hz1 : z ≤ 1) (ht0 : 0 ≤ t)
    (hbound : a ≤ z → φ z ≤ t) :
    φ c + s * (z - c) ≤ t := by
  rcases le_or_gt a z with hz | hz
  · exact le_trans (htangent z hz hz1) (hbound hz)
  · have hat : φ c + s * (a - c) ≤ 0 := by
      have := htangent a le_rfl ha1
      rw [hφa] at this
      exact this
    have hmono : φ c + s * (z - c) ≤ φ c + s * (a - c) := by
      have : s * (z - c) ≤ s * (a - c) :=
        mul_le_mul_of_nonneg_left (by linarith) hs
      linarith
    linarith

end Taeyoung.Methods.Link
