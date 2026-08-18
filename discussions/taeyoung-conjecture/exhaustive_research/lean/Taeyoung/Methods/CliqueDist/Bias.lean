import Taeyoung.Methods.GeometricMean
import Taeyoung.Methods.BookTail.Core
import Taeyoung.Methods.CliqueLeaf.Density

/-!
# The `√d`-biased measure

`notes/clique_distributed_leaves.tex` §3.  Distributing `h` leaves over the
vertices of `K_r` and symmetrising turns the density into

```
t(H,W) ≥ ∫_{Ω^r} F(x)·∏ᵢ d(xᵢ)^{h/r} dμ^r,
```

and the right-hand side is a clique density on the biased probability space
`dν = (d^{h/r}/M)dμ`, `M = ∫ d^{h/r}`.  The only scoped instance is
`(r,h) = (4,2)`, where the exponent is `1/2`; this file therefore builds the
`√d`-bias rather than the general fractional one.

`Methods/DegreeBias.lean` is the same construction at exponent `1`, and both go
through `Foundation/TiltTransfer.lean`'s `integral_assignmentMeasure_withDensity`,
which takes the density as a parameter.

Two facts make `√d` the convenient exponent:

* `M² ≤ p` is Cauchy–Schwarz against the constant `1`, using the unweighted
  `BookTail.sq_integral_mul_le`; no concavity argument is needed;
* `M²·t(K₂,W_ν) = ∫∫ W(x,y)√(d(x)d(y))`, which is exactly the geometric-mean
  integral of `Methods/GeometricMean.lean`, already known to be `≥ p²`.
-/

open MeasureTheory Finset

namespace Taeyoung.Methods.CliqueDist

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.GeometricMean Taeyoung.Methods.BookTail

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### `√d` and its mean -/

/-- `√(d(x))`. -/
noncomputable def sqrtDegree (W : Graphon Ω μ) (x : Ω) : ℝ :=
  Real.sqrt (degree W x)

/-- `M = ∫ √d`. -/
noncomputable def sqrtMean (W : Graphon Ω μ) : ℝ := ∫ x, sqrtDegree W x ∂μ

section Basic

variable (W : Graphon Ω μ)

lemma measurable_sqrtDegree : Measurable (sqrtDegree W) :=
  Real.continuous_sqrt.measurable.comp (measurable_degree W)

lemma sqrtDegree_nonneg (x : Ω) : 0 ≤ sqrtDegree W x := Real.sqrt_nonneg _

lemma sqrtDegree_le_one (x : Ω) : sqrtDegree W x ≤ 1 := by
  rw [sqrtDegree, show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (degree_le_one W x)

lemma sq_sqrtDegree (x : Ω) : sqrtDegree W x ^ 2 = degree W x :=
  Real.sq_sqrt (degree_nonneg W x)

/-- On `[0,1]` the square root dominates: `d ≤ √d`. -/
lemma degree_le_sqrtDegree (x : Ω) : degree W x ≤ sqrtDegree W x := by
  have h0 := sqrtDegree_nonneg W x
  have h1 := sqrtDegree_le_one W x
  have hsq := sq_sqrtDegree W x
  nlinarith

lemma integrable_sqrtDegree : Integrable (sqrtDegree W) μ :=
  integrable_of_bdd (measurable_sqrtDegree W) (C := 1) fun x ↦ by
    rw [abs_of_nonneg (sqrtDegree_nonneg W x)]
    exact sqrtDegree_le_one W x

/-- `M > 0` whenever the edge density is. -/
lemma sqrtMean_pos (hp : 0 < cliqueDensity 2 W) : 0 < sqrtMean W := by
  have h : cliqueDensity 2 W ≤ sqrtMean W := by
    rw [← integral_degree W, sqrtMean]
    exact integral_mono (integrable_degree W) (integrable_sqrtDegree W)
      (degree_le_sqrtDegree W)
  linarith

/-- **`M² ≤ p`**, Cauchy–Schwarz against the constant `1`. -/
theorem sq_sqrtMean_le : sqrtMean W ^ 2 ≤ cliqueDensity 2 W := by
  have h := sq_integral_mul_le (ν := μ) (f := sqrtDegree W) (g := fun _ ↦ (1 : ℝ))
    (by
      refine Integrable.congr (integrable_degree W) (ae_of_all _ fun x ↦ ?_)
      show degree W x = sqrtDegree W x ^ 2
      exact (sq_sqrtDegree W x).symm)
    (by simpa using (integrable_const (1 : ℝ)))
    (by simpa using integrable_sqrtDegree W)
  simp only [mul_one, one_pow] at h
  have hsq : (∫ x, sqrtDegree W x ^ 2 ∂μ) = cliqueDensity 2 W := by
    rw [← integral_degree W]
    exact integral_congr_ae (ae_of_all _ fun x ↦ sq_sqrtDegree W x)
  rw [hsq] at h
  simpa [sqrtMean] using h

end Basic

/-! ### The measure -/

/-- The `√d`-biased density `√d/M`. -/
noncomputable def sqrtDensity (W : Graphon Ω μ) (x : Ω) : ℝ :=
  sqrtDegree W x / sqrtMean W

/-- `dν = (√d/M)dμ`. -/
noncomputable def sqrtMeasure (W : Graphon Ω μ) : Measure Ω :=
  μ.withDensity fun x ↦ ENNReal.ofReal (sqrtDensity W x)

section Density

variable (W : Graphon Ω μ)

lemma measurable_sqrtDensity : Measurable (sqrtDensity W) :=
  (measurable_sqrtDegree W).div_const _

lemma sqrtDensity_nonneg (hM : 0 < sqrtMean W) (x : Ω) : 0 ≤ sqrtDensity W x :=
  div_nonneg (sqrtDegree_nonneg W x) hM.le

lemma sqrtDensity_le (hM : 0 < sqrtMean W) (x : Ω) :
    sqrtDensity W x ≤ 1 / sqrtMean W := by
  simp only [sqrtDensity, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (sqrtDegree_le_one W x) (inv_nonneg.mpr hM.le)

lemma integrable_sqrtDensity : Integrable (sqrtDensity W) μ :=
  (integrable_sqrtDegree W).div_const _

lemma integral_sqrtDensity (hM : 0 < sqrtMean W) :
    ∫ x, sqrtDensity W x ∂μ = 1 := by
  simp only [sqrtDensity]
  rw [integral_div]
  exact div_self (ne_of_gt hM)

lemma isProbabilityMeasure_sqrtMeasure (hM : 0 < sqrtMean W) :
    IsProbabilityMeasure (sqrtMeasure W) :=
  isProbabilityMeasure_withDensity_ofReal (integrable_sqrtDensity W)
    (sqrtDensity_nonneg W hM) (integral_sqrtDensity W hM)

end Density

/-- The same kernel, reread on the `√d`-biased measure. -/
def sqrtGraphon (W : Graphon Ω μ) : Graphon Ω (sqrtMeasure W) where
  toFun := W.toFun
  measurable := W.measurable
  nonneg := W.nonneg
  le_one := W.le_one
  symm := W.symm

/-! ### The transfer -/

theorem homDensity_sqrtGraphon {n : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (W : Graphon Ω μ) (hM : 0 < sqrtMean W)
    [IsProbabilityMeasure (sqrtMeasure W)] :
    homDensity F (sqrtGraphon W) =
      ∫ y, (∏ i, sqrtDensity W (y i)) * graphWeight F W y
        ∂assignmentMeasure (Fin n) μ := by
  have hb : ∀ z : Fin n → Ω, |graphWeight F W z| ≤ 1 := fun z ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg F W z)]
    exact graphWeight_le_one F W z
  exact integral_assignmentMeasure_withDensity (measurable_sqrtDensity W)
    (sqrtDensity_nonneg W hM) (sqrtDensity_le W hM)
    (integral_sqrtDensity W hM) (graphWeight F W)
    (measurable_graphWeight F W) zero_le_one hb

/-- **The `√d`-weighted clique integral is `M^n` times a clique density on the
biased space.** -/
theorem integral_sqrtDegree_prod (n : ℕ) (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (W : Graphon Ω μ) (hM : 0 < sqrtMean W)
    [IsProbabilityMeasure (sqrtMeasure W)] :
    (∫ y, (∏ i, sqrtDegree W (y i)) * graphWeight F W y
        ∂assignmentMeasure (Fin n) μ) =
      sqrtMean W ^ n * homDensity F (sqrtGraphon W) := by
  rw [homDensity_sqrtGraphon F W hM, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [sqrtDensity]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  field_simp

/-! ### The biased edge density -/

/-- **`M²·t(K₂,W_ν) = ∫∫ W√(d(x)d(y))`**, hence at least `p²`. -/
theorem sq_le_sq_sqrtMean_mul_cliqueDensity (W : Graphon Ω μ)
    (hM : 0 < sqrtMean W) [IsProbabilityMeasure (sqrtMeasure W)] :
    cliqueDensity 2 W ^ 2 ≤
      sqrtMean W ^ 2 * cliqueDensity 2 (sqrtGraphon W) := by
  have hkey := integral_sqrtDegree_prod 2 (⊤ : SimpleGraph (Fin 2)) W hM
  have htop : ∀ y : Fin 2 → Ω,
      (∏ i, sqrtDegree W (y i)) * graphWeight (⊤ : SimpleGraph (Fin 2)) W y =
        W (y 0) (y 1) * Real.sqrt (degree W (y 0) * degree W (y 1)) := by
    intro y
    rw [graphWeight_top_fin_two, Fin.prod_univ_two, sqrtDegree, sqrtDegree,
      ← Real.sqrt_mul (degree_nonneg W (y 0))]
    ring
  rw [integral_congr_ae (ae_of_all _ htop)] at hkey
  -- the left side is the geometric-mean integral
  have hgeo : (∫ y : Fin 2 → Ω,
      W (y 0) (y 1) * Real.sqrt (degree W (y 0) * degree W (y 1))
        ∂assignmentMeasure (Fin 2) μ) =
      ∫ q, geoIntegrand W q ∂(μ.prod μ) := by
    have hm : Measurable fun y : Fin 2 → Ω ↦
        W (y 0) (y 1) * Real.sqrt (degree W (y 0) * degree W (y 1)) := by
      refine Measurable.mul ?_ ?_
      · exact Measurable.comp (f := fun y : Fin 2 → Ω ↦ (y 0, y 1)) W.measurable
          ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
      · exact Real.continuous_sqrt.measurable.comp
          (((measurable_degree W).comp (measurable_pi_apply 0)).mul
            ((measurable_degree W).comp (measurable_pi_apply 1)))
    have hbd : ∀ y : Fin 2 → Ω,
        |W (y 0) (y 1) * Real.sqrt (degree W (y 0) * degree W (y 1))| ≤ 1 := by
      intro y
      have h0 : 0 ≤ W (y 0) (y 1) * Real.sqrt (degree W (y 0) * degree W (y 1)) :=
        mul_nonneg (W.nonneg _ _) (Real.sqrt_nonneg _)
      rw [abs_of_nonneg h0]
      have hs : Real.sqrt (degree W (y 0) * degree W (y 1)) ≤ 1 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (mul_le_one₀ (degree_le_one W _)
          (degree_nonneg W _) (degree_le_one W _))
      exact mul_le_one₀ (W.le_one _ _) (Real.sqrt_nonneg _) hs
    rw [integral_assignmentMeasure_succ _ hm hbd]
    have hint : Integrable (geoIntegrand W) (μ.prod μ) := integrable_geoIntegrand W
    rw [← integral_integral (f := fun a b ↦ geoIntegrand W (a, b)) hint]
    refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
    simp only []
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 1 → Ω ↦ W ((Fin.cons a0 y : Fin 2 → Ω) 0)
          ((Fin.cons a0 y : Fin 2 → Ω) 1) *
        Real.sqrt (degree W ((Fin.cons a0 y : Fin 2 → Ω) 0) *
          degree W ((Fin.cons a0 y : Fin 2 → Ω) 1)))
      (hm.comp (measurable_fin_cons a0)) fun y ↦ hbd _]
    refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
    simp only []
    rw [show (∫ y : Fin 0 → Ω,
        W ((Fin.cons a0 (Fin.cons a1 y) : Fin 2 → Ω) 0)
            ((Fin.cons a0 (Fin.cons a1 y) : Fin 2 → Ω) 1) *
          Real.sqrt (degree W ((Fin.cons a0 (Fin.cons a1 y) : Fin 2 → Ω) 0) *
            degree W ((Fin.cons a0 (Fin.cons a1 y) : Fin 2 → Ω) 1))
        ∂assignmentMeasure (Fin 0) μ) =
        W a0 a1 * Real.sqrt (degree W a0 * degree W a1) by simp]
    rfl
  rw [hgeo] at hkey
  have hc : cliqueDensity 2 (sqrtGraphon W) =
      homDensity (⊤ : SimpleGraph (Fin 2)) (sqrtGraphon W) := rfl
  rw [hc, ← hkey]
  exact sq_le_integral_geoIntegrand W

end Taeyoung.Methods.CliqueDist
