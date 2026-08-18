import Taeyoung.Methods.PathSidorenko

/-!
# The degree-biased measure

`notes/whiskering.tex` observes that attaching one pendant leaf to *every*
vertex of `F` is exactly a change of the vertex measure: integrating each
whisker out multiplies the integrand by the degree of the vertex it hangs
from, and `d·μ/p` is again a probability measure.  So

```
t(Wh(F), W) = p^{v(F)} · t(F, W_ν),        dν = (d/p)dμ,
```

with `W` reread as a graphon on `(Ω,ν)` — nothing about `W` changes, only the
space it lives on.  The edge density moves to

```
t(K₂, W_ν) = t(P₄,W)/p² ≥ p,
```

the inequality being path Sidorenko, which is why every whiskered graph
inherits its base's bound at a *higher* density than `p`.

This file supplies the change of measure.  It is the whole analytic content of
the whiskering methodology; a particular row then needs only the peeling
identity for its own graph and the base bound for `F`.

The transfer is `Foundation/TiltTransfer.lean`'s
`integral_assignmentMeasure_withDensity`, which was built for the link measure
and applies verbatim here — the two constructions differ only in the density.
-/

open MeasureTheory Finset

namespace Taeyoung.Methods.DegreeBias

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.PathSidorenko

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The measure -/

/-- The degree-biased density `d/p`. -/
noncomputable def degreeDensity (W : Graphon Ω μ) (x : Ω) : ℝ :=
  degree W x / cliqueDensity 2 W

/-- `dν = (d/p)dμ`. -/
noncomputable def degreeMeasure (W : Graphon Ω μ) : Measure Ω :=
  μ.withDensity fun x ↦ ENNReal.ofReal (degreeDensity W x)

section Basic

variable (W : Graphon Ω μ)

lemma measurable_degreeDensity : Measurable (degreeDensity W) :=
  (measurable_degree W).div_const _

lemma degreeDensity_nonneg (hp : 0 < cliqueDensity 2 W) (x : Ω) :
    0 ≤ degreeDensity W x :=
  div_nonneg (degree_nonneg W x) hp.le

lemma degreeDensity_le (hp : 0 < cliqueDensity 2 W) (x : Ω) :
    degreeDensity W x ≤ 1 / cliqueDensity 2 W := by
  simp only [degreeDensity, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (degree_le_one W x) (inv_nonneg.mpr hp.le)

lemma integrable_degreeDensity : Integrable (degreeDensity W) μ :=
  (integrable_degree W).div_const _

lemma integral_degreeDensity (hp : 0 < cliqueDensity 2 W) :
    ∫ x, degreeDensity W x ∂μ = 1 := by
  simp only [degreeDensity]
  rw [integral_div, integral_degree]
  exact div_self (ne_of_gt hp)

lemma isProbabilityMeasure_degreeMeasure (hp : 0 < cliqueDensity 2 W) :
    IsProbabilityMeasure (degreeMeasure W) :=
  isProbabilityMeasure_withDensity_ofReal (integrable_degreeDensity W)
    (degreeDensity_nonneg W hp) (integral_degreeDensity W hp)

end Basic

/-- The same kernel, reread on the degree-biased measure. -/
def degreeGraphon (W : Graphon Ω μ) : Graphon Ω (degreeMeasure W) where
  toFun := W.toFun
  measurable := W.measurable
  nonneg := W.nonneg
  le_one := W.le_one
  symm := W.symm

/-! ### The transfer -/

/-- **Whiskering is a change of measure.**  The density of `F` on the
degree-biased space is the degree-weighted density on the original one. -/
theorem homDensity_degreeGraphon {n : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (W : Graphon Ω μ) (hp : 0 < cliqueDensity 2 W)
    [IsProbabilityMeasure (degreeMeasure W)] :
    homDensity F (degreeGraphon W) =
      ∫ y, (∏ i, degreeDensity W (y i)) * graphWeight F W y
        ∂assignmentMeasure (Fin n) μ := by
  have hb : ∀ z : Fin n → Ω, |graphWeight F W z| ≤ 1 := fun z ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg F W z)]
    exact graphWeight_le_one F W z
  exact integral_assignmentMeasure_withDensity (measurable_degreeDensity W)
    (degreeDensity_nonneg W hp) (degreeDensity_le W hp)
    (integral_degreeDensity W hp) (graphWeight F W)
    (measurable_graphWeight F W) zero_le_one hb

/-- The same identity with the normalisation pulled out: the whiskered density
is `p^{v(F)}` times the density of `F` on the biased space. -/
theorem integral_degree_prod (n : ℕ) (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (W : Graphon Ω μ) (hp : 0 < cliqueDensity 2 W)
    [IsProbabilityMeasure (degreeMeasure W)] :
    (∫ y, (∏ i, degree W (y i)) * graphWeight F W y
        ∂assignmentMeasure (Fin n) μ) =
      cliqueDensity 2 W ^ n * homDensity F (degreeGraphon W) := by
  rw [homDensity_degreeGraphon F W hp, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [degreeDensity]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  field_simp

/-! ### The edge density moves up -/

/-- **The biased edge density is `t(P₄,W)/p²`, hence at least `p`.**  This is
path Sidorenko, and it is what makes whiskering useful: the base graph is
evaluated at a density no smaller than the one we started from. -/
theorem le_cliqueDensity_degreeGraphon (W : Graphon Ω μ)
    (hp : 0 < cliqueDensity 2 W) [IsProbabilityMeasure (degreeMeasure W)] :
    cliqueDensity 2 W ≤ cliqueDensity 2 (degreeGraphon W) := by
  have hkey := integral_degree_prod 2 (⊤ : SimpleGraph (Fin 2)) W hp
  have htop : ∀ y : Fin 2 → Ω,
      (∏ i, degree W (y i)) * graphWeight (⊤ : SimpleGraph (Fin 2)) W y =
        degree W (y 0) * degree W (y 1) * W (y 0) (y 1) := by
    intro y
    rw [graphWeight_top_fin_two, Fin.prod_univ_two]
  rw [integral_congr_ae (ae_of_all _ htop)] at hkey
  -- the left side is `t(P₄,W)`, by the rooted factorization
  have hp4 : (∫ y : Fin 2 → Ω,
      degree W (y 0) * degree W (y 1) * W (y 0) (y 1)
        ∂assignmentMeasure (Fin 2) μ) =
      ∫ x, degree W x * pathOp W x ∂μ := by
    have hW2 : Measurable fun y : Fin 2 → Ω ↦ W (y 0) (y 1) :=
      Measurable.comp (f := fun y : Fin 2 → Ω ↦ (y 0, y 1)) W.measurable
        ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
    have hm : Measurable fun y : Fin 2 → Ω ↦
        degree W (y 0) * degree W (y 1) * W (y 0) (y 1) :=
      (((measurable_degree W).comp (measurable_pi_apply 0)).mul
        ((measurable_degree W).comp (measurable_pi_apply 1))).mul hW2
    have hbd : ∀ y : Fin 2 → Ω,
        |degree W (y 0) * degree W (y 1) * W (y 0) (y 1)| ≤ 1 := by
      intro y
      have h0 : 0 ≤ degree W (y 0) * degree W (y 1) * W (y 0) (y 1) :=
        mul_nonneg (mul_nonneg (degree_nonneg W _) (degree_nonneg W _))
          (W.nonneg _ _)
      rw [abs_of_nonneg h0]
      exact mul_le_one₀ (mul_le_one₀ (degree_le_one W _) (degree_nonneg W _)
        (degree_le_one W _)) (W.nonneg _ _) (W.le_one _ _)
    rw [integral_assignmentMeasure_succ _ hm hbd]
    refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
    simp only []
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 1 → Ω ↦ degree W ((Fin.cons a0 y : Fin 2 → Ω) 0) *
        degree W ((Fin.cons a0 y : Fin 2 → Ω) 1) *
        W ((Fin.cons a0 y : Fin 2 → Ω) 0) ((Fin.cons a0 y : Fin 2 → Ω) 1))
      (hm.comp (measurable_fin_cons a0)) fun y ↦ hbd _]
    have hval : ∀ a1 : Ω,
        (∫ y : Fin 0 → Ω,
            degree W ((Fin.cons a0 (Fin.cons a1 y) : Fin 2 → Ω) 0) *
              degree W ((Fin.cons a0 (Fin.cons a1 y) : Fin 2 → Ω) 1) *
              W ((Fin.cons a0 (Fin.cons a1 y) : Fin 2 → Ω) 0)
                ((Fin.cons a0 (Fin.cons a1 y) : Fin 2 → Ω) 1)
          ∂assignmentMeasure (Fin 0) μ) =
          degree W a0 * (W a0 a1 * degree W a1) := by
      intro a1
      rw [show (∫ y : Fin 0 → Ω,
          degree W ((Fin.cons a0 (Fin.cons a1 y) : Fin 2 → Ω) 0) *
            degree W ((Fin.cons a0 (Fin.cons a1 y) : Fin 2 → Ω) 1) *
            W ((Fin.cons a0 (Fin.cons a1 y) : Fin 2 → Ω) 0)
              ((Fin.cons a0 (Fin.cons a1 y) : Fin 2 → Ω) 1)
            ∂assignmentMeasure (Fin 0) μ) =
          degree W a0 * degree W a1 * W a0 a1 by simp]
      ring
    rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul]
    rfl
  rw [hp4] at hkey
  -- path Sidorenko, then divide by `p²`
  have hsid := pow_three_le_pathIntegral W
  have hden : cliqueDensity 2 W ^ 2 * cliqueDensity 2 W ≤
      cliqueDensity 2 W ^ 2 *
        homDensity (⊤ : SimpleGraph (Fin 2)) (degreeGraphon W) := by
    rw [← hkey]
    calc cliqueDensity 2 W ^ 2 * cliqueDensity 2 W = cliqueDensity 2 W ^ 3 := by ring
      _ ≤ ∫ x, degree W x * pathOp W x ∂μ := hsid
  exact le_of_mul_le_mul_left hden (by positivity)

end Taeyoung.Methods.DegreeBias
