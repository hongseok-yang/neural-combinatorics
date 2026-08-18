import Taeyoung.Methods.Link.WeightedGoodmanRpow
import Taeyoung.Methods.Peeling

/-!
# The `d^{1/m}`-biased measure

`notes/odd_cycle_one_leaf.tex` §4.  Averaging the pendant leaf of `C_m⁺` over
the `m` cycle vertices and applying the arithmetic–geometric mean inequality
turns the density into

```
t(C_m⁺,W) ≥ ∫_{Ω^m} F(x)·∏ᵢ d(xᵢ)^{1/m} dμ^m,
```

and the right-hand side is `M^m` times a cycle density on the biased
probability space `dν = (d^{1/m}/M)dμ`, `M = ∫ d^{1/m}`.

This is `Methods/CliqueDist/Bias.lean` with `√d` replaced by the `m`-th root,
and `Methods/DegreeBias.lean` is the same construction at exponent `1`.  All
three go through `Foundation/TiltTransfer.lean`'s
`integral_assignmentMeasure_withDensity`, which takes the density as a
parameter.

Fixing the exponent to a *reciprocal integer* keeps the two facts that matter
free of `Real.rpow` arithmetic: `(d^{1/m})^m = d` as an `ℕ`-power, and
`M^m ≤ p` as ordinary Jensen against the convex `t ↦ t^m`.
-/

open MeasureTheory Finset

namespace Taeyoung.Methods.OddLeaf

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### `d^{1/m}` and its mean -/

/-- `d(x)^{1/m}`. -/
noncomputable def rootDegree (W : Graphon Ω μ) (m : ℕ) (x : Ω) : ℝ :=
  degree W x ^ ((m : ℝ)⁻¹)

/-- `M = ∫ d^{1/m}`. -/
noncomputable def rootMean (W : Graphon Ω μ) (m : ℕ) : ℝ :=
  ∫ x, rootDegree W m x ∂μ

section Basic

variable (W : Graphon Ω μ) {m : ℕ}

lemma measurable_rootDegree : Measurable (rootDegree W m) :=
  measurable_degree_rpow W (by positivity)

lemma rootDegree_nonneg (x : Ω) : 0 ≤ rootDegree W m x :=
  degree_rpow_nonneg W _ x

lemma rootDegree_le_one (x : Ω) : rootDegree W m x ≤ 1 :=
  degree_rpow_le_one W (by positivity) x

/-- `(d^{1/m})^m = d`. -/
lemma pow_rootDegree (hm : m ≠ 0) (x : Ω) :
    rootDegree W m x ^ m = degree W x := by
  rw [rootDegree, ← Real.rpow_natCast (degree W x ^ ((m : ℝ)⁻¹)) m,
    ← Real.rpow_mul (degree_nonneg W x), inv_mul_cancel₀
      (by exact_mod_cast hm : (m : ℝ) ≠ 0), Real.rpow_one]

/-- On `[0,1]` a root dominates: `d ≤ d^{1/m}` for `m ≥ 1`. -/
lemma degree_le_rootDegree (hm : m ≠ 0) (x : Ω) :
    degree W x ≤ rootDegree W m x := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hinv : ((m : ℝ))⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_one (by linarith : (0 : ℝ) < (m : ℝ))]
    exact hm1
  rcases eq_or_lt_of_le (degree_nonneg W x) with h0 | hpos
  · rw [rootDegree, ← h0, Real.zero_rpow (by positivity)]
  · calc degree W x = degree W x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ degree W x ^ ((m : ℝ)⁻¹) :=
        Real.rpow_le_rpow_of_exponent_ge hpos (degree_le_one W x) hinv
      _ = rootDegree W m x := rfl

lemma integrable_rootDegree : Integrable (rootDegree W m) μ :=
  integrable_of_bdd (measurable_rootDegree W) (C := 1) fun x ↦ by
    rw [abs_of_nonneg (rootDegree_nonneg W x)]
    exact rootDegree_le_one W x

/-- `M > 0` whenever the edge density is. -/
lemma rootMean_pos (hm : m ≠ 0) (hp : 0 < cliqueDensity 2 W) :
    0 < rootMean W m := by
  have h : cliqueDensity 2 W ≤ rootMean W m := by
    rw [← integral_degree W, rootMean]
    exact integral_mono (integrable_degree W) (integrable_rootDegree W)
      (degree_le_rootDegree W hm)
  linarith

/-- **`M^m ≤ p`**, Jensen against the convex `t ↦ tᵐ`. -/
theorem pow_rootMean_le (hm : m ≠ 0) :
    rootMean W m ^ m ≤ cliqueDensity 2 W := by
  have hpow : Integrable (fun x ↦ rootDegree W m x ^ m) μ := by
    refine (integrable_degree W).congr (ae_of_all _ fun x ↦ ?_)
    exact (pow_rootDegree W hm x).symm
  have hj := ConvexOn.map_integral_le (μ := μ) (s := Set.Ici 0)
    (g := fun t : ℝ ↦ t ^ m) (f := rootDegree W m) (convexOn_pow m)
    ((continuous_pow m).continuousOn) isClosed_Ici
    (ae_of_all _ fun x ↦ rootDegree_nonneg W x)
    (integrable_rootDegree W) hpow
  have hval : (∫ x, rootDegree W m x ^ m ∂μ) = cliqueDensity 2 W := by
    rw [← integral_degree W]
    exact integral_congr_ae (ae_of_all _ fun x ↦ pow_rootDegree W hm x)
  rwa [hval] at hj

end Basic

/-! ### The measure -/

/-- The biased density `d^{1/m}/M`. -/
noncomputable def rootDensity (W : Graphon Ω μ) (m : ℕ) (x : Ω) : ℝ :=
  rootDegree W m x / rootMean W m

/-- `dν = (d^{1/m}/M)dμ`. -/
noncomputable def rootMeasure (W : Graphon Ω μ) (m : ℕ) : Measure Ω :=
  μ.withDensity fun x ↦ ENNReal.ofReal (rootDensity W m x)

section Density

variable (W : Graphon Ω μ) {m : ℕ}

lemma measurable_rootDensity : Measurable (rootDensity W m) :=
  (measurable_rootDegree W).div_const _

lemma rootDensity_nonneg (hM : 0 < rootMean W m) (x : Ω) :
    0 ≤ rootDensity W m x :=
  div_nonneg (rootDegree_nonneg W x) hM.le

lemma rootDensity_le (hM : 0 < rootMean W m) (x : Ω) :
    rootDensity W m x ≤ 1 / rootMean W m := by
  simp only [rootDensity, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (rootDegree_le_one W x) (inv_nonneg.mpr hM.le)

lemma integrable_rootDensity : Integrable (rootDensity W m) μ :=
  (integrable_rootDegree W).div_const _

omit [IsProbabilityMeasure μ] in
lemma integral_rootDensity (hM : 0 < rootMean W m) :
    ∫ x, rootDensity W m x ∂μ = 1 := by
  simp only [rootDensity]
  rw [integral_div]
  exact div_self (ne_of_gt hM)

lemma isProbabilityMeasure_rootMeasure (hM : 0 < rootMean W m) :
    IsProbabilityMeasure (rootMeasure W m) :=
  isProbabilityMeasure_withDensity_ofReal (integrable_rootDensity W)
    (rootDensity_nonneg W hM) (integral_rootDensity W hM)

end Density

/-- The same kernel, reread on the `d^{1/m}`-biased measure. -/
def rootGraphon (W : Graphon Ω μ) (m : ℕ) : Graphon Ω (rootMeasure W m) where
  toFun := W.toFun
  measurable := W.measurable
  nonneg := W.nonneg
  le_one := W.le_one
  symm := W.symm

/-! ### The transfer -/

theorem homDensity_rootGraphon {n m : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (W : Graphon Ω μ) (hM : 0 < rootMean W m)
    [IsProbabilityMeasure (rootMeasure W m)] :
    homDensity F (rootGraphon W m) =
      ∫ y, (∏ i, rootDensity W m (y i)) * graphWeight F W y
        ∂assignmentMeasure (Fin n) μ := by
  have hb : ∀ z : Fin n → Ω, |graphWeight F W z| ≤ 1 := fun z ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg F W z)]
    exact graphWeight_le_one F W z
  exact integral_assignmentMeasure_withDensity (measurable_rootDensity W)
    (rootDensity_nonneg W hM) (rootDensity_le W hM)
    (integral_rootDensity W hM) (graphWeight F W)
    (measurable_graphWeight F W) zero_le_one hb

/-- **The `d^{1/m}`-weighted graph integral is `M^n` times a density on the
biased space.** -/
theorem integral_rootDegree_prod (n m : ℕ) (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (W : Graphon Ω μ) (hM : 0 < rootMean W m)
    [IsProbabilityMeasure (rootMeasure W m)] :
    (∫ y, (∏ i, rootDegree W m (y i)) * graphWeight F W y
        ∂assignmentMeasure (Fin n) μ) =
      rootMean W m ^ n * homDensity F (rootGraphon W m) := by
  rw [homDensity_rootGraphon F W hM, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [rootDensity]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  field_simp

end Taeyoung.Methods.OddLeaf
