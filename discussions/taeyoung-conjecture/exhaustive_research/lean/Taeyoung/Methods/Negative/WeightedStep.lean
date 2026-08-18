import Taeyoung.Methods.Negative.StepGraphon

/-!
# Rational step graphons with unequal masses

`Methods/Negative/StepGraphon.lean` covers step graphons on a *uniform* finite
space, which is enough for Atlas 166, 172 and 206.  Atlas 152 is different: its
witness has five parts of unequal mass, so the ground measure must be weighted.

Rather than build a weighted finite measure from scratch, this file obtains it
as a **tilt of the uniform one**, `w i / D = (1/k) · (k · w i / D)`, and reuses
`Foundation/TiltTransfer.lean`.  That is the same device the link measures use,
and it means no new measure theory: the assignment integral over the weighted
space is the assignment integral over the uniform space against the extra factor
`∏ᵥ (k · w(zᵥ) / D)`, and the `k`'s cancel against the uniform normalisation.

The upshot is the same shape as the uniform case — a natural-number numerator,

```
t(H, W) = (∑_z (∏ᵥ w(zᵥ)) · F z) / (D^{v(H)} · Dw),
```

so a row is still one `decide +kernel` on a sum of naturals.
-/

open Finset MeasureTheory

namespace Taeyoung.Methods.Negative

open Taeyoung Taeyoung.Methods.PureChordal

section Weighted

variable (k : ℕ) [NeZero k] (w : Fin k → ℕ) (D : ℕ)

/-- The tilt density of the mass vector `w/D` against the uniform measure. -/
noncomputable def massDensity (i : Fin k) : ℝ := (k : ℝ) * (w i : ℝ) / (D : ℝ)

lemma massDensity_nonneg (i : Fin k) : 0 ≤ massDensity k w D i := by
  unfold massDensity; positivity

lemma measurable_massDensity : Measurable (massDensity k w D) :=
  measurable_of_finite _

lemma integrable_massDensity :
    Integrable (massDensity k w D) (finiteUniformMeasure (Fin k)) :=
  Integrable.of_finite

lemma massDensity_le (hsum : ∑ i, w i = D) (i : Fin k) :
    massDensity k w D i ≤ (k : ℝ) := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · have : w i = 0 := by
      have := Finset.single_le_sum (f := w) (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      omega
    simp [massDensity, this]
  · have hwi : (w i : ℝ) ≤ (D : ℝ) := by
      have := Finset.single_le_sum (f := w) (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      exact_mod_cast this.trans_eq hsum
    have hD' : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    rw [massDensity, div_le_iff₀ hD']
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

lemma integral_massDensity (hsum : ∑ i, w i = D) (hD : D ≠ 0) :
    ∫ i, massDensity k w D i ∂finiteUniformMeasure (Fin k) = 1 := by
  have hk : (0 : ℝ) < (k : ℝ) := by
    have := NeZero.ne k
    positivity
  have hD' : (0 : ℝ) < (D : ℝ) := by
    have : 0 < D := Nat.pos_of_ne_zero hD
    exact_mod_cast this
  have hw : ∑ i, ((w i : ℝ)) = (D : ℝ) := by
    rw [← Nat.cast_sum, hsum]
  rw [finiteUniform_integral, Fintype.card_fin]
  have hsplit : ∑ i, massDensity k w D i = (k : ℝ) * (∑ i, (w i : ℝ)) / (D : ℝ) := by
    unfold massDensity
    rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [hsplit, hw]
  field_simp

/-- The finite measure with masses `w i / D`, as a tilt of the uniform one. -/
noncomputable def weightedMeasure : Measure (Fin k) :=
  (finiteUniformMeasure (Fin k)).withDensity fun i ↦
    ENNReal.ofReal (massDensity k w D i)

lemma weightedMeasure_univ (hsum : ∑ i, w i = D) (hD : D ≠ 0) :
    weightedMeasure k w D Set.univ = 1 := by
  rw [weightedMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_massDensity k w D)
      (ae_of_all _ (massDensity_nonneg k w D)),
    integral_massDensity k w D hsum hD]
  simp

lemma isProbabilityMeasure_weightedMeasure (hsum : ∑ i, w i = D) (hD : D ≠ 0) :
    IsProbabilityMeasure (weightedMeasure k w D) :=
  ⟨weightedMeasure_univ k w D hsum hD⟩

/-! ### The density -/

variable [IsProbabilityMeasure (weightedMeasure k w D)]

/-- **The density of a weighted step graphon.**  Same shape as the uniform case,
with the masses folded into the natural-number numerator. -/
theorem homDensity_weighted {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hsum : ∑ i, w i = D) (hD : D ≠ 0)
    (W : Graphon (Fin k) (weightedMeasure k w D))
    (F : (Fin n → Fin k) → ℕ) (Dw : ℝ)
    (hw : ∀ z, graphWeight H W z = (F z : ℝ) / Dw) :
    homDensity H W
      = ((∑ z : Fin n → Fin k, (∏ v, w (z v)) * F z : ℕ) : ℝ)
          / ((D : ℝ) ^ n * Dw) := by
  classical
  have hk : (0 : ℝ) < (k : ℝ) := by
    have := NeZero.ne k
    positivity
  have hD' : (0 : ℝ) < (D : ℝ) := by
    have : 0 < D := Nat.pos_of_ne_zero hD
    exact_mod_cast this
  -- `weightedMeasure` is *definitionally* a tilt of the uniform measure, so the
  -- transfer theorem applies once the statement is written out.
  have htrans :
      (∫ z, graphWeight H W z ∂assignmentMeasure (Fin n) (weightedMeasure k w D))
        = ∫ z, (∏ v, massDensity k w D (z v)) * graphWeight H W z
            ∂assignmentMeasure (Fin n) (finiteUniformMeasure (Fin k)) :=
    integral_assignmentMeasure_withDensity (measurable_massDensity k w D)
      (massDensity_nonneg k w D) (massDensity_le k w D hsum)
      (integral_massDensity k w D hsum hD) (graphWeight H W)
      (measurable_graphWeight H W) zero_le_one
      (fun z ↦ by
        rw [abs_of_nonneg (graphWeight_nonneg H W z)]
        exact graphWeight_le_one H W z)
  rw [homDensity, htrans]
  rw [assignmentMeasure_finiteUniform, finiteUniform_integral, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]
  -- pointwise: the `k`'s cancel against the uniform normalisation
  have hpt : ∀ z : Fin n → Fin k,
      (∏ v, massDensity k w D (z v)) * graphWeight H W z
        = (k : ℝ) ^ n * (((∏ v, w (z v)) * F z : ℕ) : ℝ) / ((D : ℝ) ^ n * Dw) := by
    intro z
    have hprod : (∏ v, massDensity k w D (z v))
        = (k : ℝ) ^ n * (∏ v, (w (z v) : ℝ)) / (D : ℝ) ^ n := by
      unfold massDensity
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
      simp [Finset.prod_const, div_div_eq_mul_div, mul_div_assoc]
    rw [hprod, hw z]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl fun z _ ↦ hpt z]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  push_cast
  field_simp

end Weighted

end Taeyoung.Methods.Negative
