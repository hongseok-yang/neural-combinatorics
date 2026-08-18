import Taeyoung.Methods.DegreeBias
import Taeyoung.Methods.PageBook.Atlas41

/-!
# Atlas 94: the fully whiskered triangle

`Wh(K₃)` — a triangle with one pendant leaf at each of its three vertices.
By `Methods/DegreeBias.lean` this is a change of measure:

```
t(Wh(K₃),W) = p³·t(K₃, W_ν),        dν = (d/p)dμ,
```

and the biased edge density satisfies `z := t(K₂,W_ν) ≥ p` — that is path
Sidorenko, `t(K₂,W_ν) = t(P₄,W)/p² ≥ p`.  Goodman for the triangle on the
biased space then gives

```
t(Wh(K₃),W) = p³·t(K₃,W_ν) ≥ p³·z(2z-1) ≥ p³·p(2p-1) = p⁴(2p-1) = Φ,
```

the last step being monotonicity of `z ↦ z(2z-1)` on `[1/2,1]`.

All that is left to supply here is the peeling identity, which has to be run on
both sides: six coordinates on the left, three on the right.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.Whisker

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.DegreeBias Taeyoung.Methods.PawCone
  Taeyoung.Methods.ForestCone Taeyoung.Methods.BaseCone
  Taeyoung.Methods.PureChordal Taeyoung.Methods.CliqueLeaf

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The graph -/

/-- Triangle `0,1,2`; leaf `3` at `0`, leaf `4` at `1`, leaf `5` at `2`. -/
def whisker3 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)]

instance : DecidableRel whisker3.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_whisker3 :
    whisker3.edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 4), s(2, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_whisker3 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight whisker3 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 0) (x 3) * W (x 1) (x 2) *
        W (x 1) (x 4) * W (x 2) (x 5) := by
  rw [graphWeight, edgeFinset_whisker3]
  simp
  ring

lemma edgeFinset_top3 :
    (⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_top3 (W : Graphon Ω μ) (y : Fin 3 → Ω) :
    graphWeight (⊤ : SimpleGraph (Fin 3)) W y =
      W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) := by
  rw [graphWeight, edgeFinset_top3]
  simp
  ring

lemma graphWeight_whisker3_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight whisker3 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a4 * W a2 a5 := by
  rw [graphWeight_whisker3]
  rfl

/-- The common triple integrand both sides peel down to. -/
noncomputable def tri (W : Graphon Ω μ) (a0 a1 a2 : Ω) : ℝ :=
  degree W a0 * degree W a1 * degree W a2 *
    (W a0 a1 * W a0 a2 * W a1 a2)

/-! ### Peeling the whiskered graph -/

private lemma hb6 (W : Graphon Ω μ) :
    ∀ x, |graphWeight whisker3 W x| ≤ 1 := fun x ↦ by
  rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
  exact graphWeight_le_one _ W x

theorem homDensity_whisker3_iterated (W : Graphon Ω μ) :
    homDensity whisker3 W = ∫ a0, ∫ a1, ∫ a2, tri W a0 a1 a2 ∂μ ∂μ ∂μ := by
  have hm : Measurable (graphWeight whisker3 W) := measurable_graphWeight _ W
  have hb := hb6 W
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight whisker3 W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight whisker3 W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 3 → Ω ↦
      graphWeight whisker3 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
    (hm.comp ((measurable_fin_cons a0).comp
      ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
    fun y ↦ hb _]
  -- the three leaves, innermost first
  have hstep3 : ∀ a3 : Ω,
      (∫ y : Fin 2 → Ω, graphWeight whisker3 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
        ∂assignmentMeasure (Fin 2) μ) =
        (W a0 a1 * W a0 a2 * W a1 a2 * (degree W a1 * degree W a2)) *
          W a0 a3 := by
    intro a3
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 2 → Ω ↦ graphWeight whisker3 W
        (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
      (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
        ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
      fun y ↦ hb _]
    have hstep4 : ∀ a4 : Ω,
        (∫ y : Fin 1 → Ω, graphWeight whisker3 W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
              (Fin.cons a4 y)))))
          ∂assignmentMeasure (Fin 1) μ) =
          (W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * degree W a2) * W a1 a4 := by
      intro a4
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 1 → Ω ↦ graphWeight whisker3 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
            (Fin.cons a4 y))))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
            (measurable_fin_cons a4))))))
        fun y ↦ hb _]
      have hval : ∀ a5 : Ω,
          (∫ y : Fin 0 → Ω, graphWeight whisker3 W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 (Fin.cons a5 y))))))
            ∂assignmentMeasure (Fin 0) μ) =
            (W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a4) * W a2 a5 := by
        intro a5
        rw [show (∫ y : Fin 0 → Ω, graphWeight whisker3 W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
              (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
            W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a4 * W a2 a5 by
          simp [graphWeight_whisker3_cons]]
      rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul]
      show _ * degree W a2 = _
      ring
    rw [integral_congr_ae (ae_of_all _ hstep4)]
    have hre : ∀ a4 : Ω,
        (W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * degree W a2) * W a1 a4 =
          ((W a0 a1 * W a0 a2 * W a1 a2 * degree W a2) * W a0 a3) * W a1 a4 := by
      intro a4; ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
    show _ * degree W a1 = _
    ring
  rw [integral_congr_ae (ae_of_all _ hstep3), integral_const_mul]
  show _ * degree W a0 = _
  rw [tri]
  ring

lemma degTop3_cons (W : Graphon Ω μ) (a0 a1 a2 : Ω) (y : Fin 0 → Ω) :
    (∏ i, degree W ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) : Fin 3 → Ω) i)) *
        graphWeight (⊤ : SimpleGraph (Fin 3)) W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))) = tri W a0 a1 a2 := by
  rw [Fin.prod_univ_three, graphWeight_top3, tri]
  rfl

/-! ### Peeling the degree-weighted triangle -/

theorem integral_degree_top3_iterated (W : Graphon Ω μ) :
    (∫ y : Fin 3 → Ω, (∏ i, degree W (y i)) *
        graphWeight (⊤ : SimpleGraph (Fin 3)) W y
      ∂assignmentMeasure (Fin 3) μ) =
      ∫ a0, ∫ a1, ∫ a2, tri W a0 a1 a2 ∂μ ∂μ ∂μ := by
  have hm : Measurable fun y : Fin 3 → Ω ↦
      (∏ i, degree W (y i)) * graphWeight (⊤ : SimpleGraph (Fin 3)) W y :=
    (Finset.univ.measurable_fun_prod fun i _ ↦
      (measurable_degree W).comp (measurable_pi_apply i)).mul
      (measurable_graphWeight _ W)
  have hb : ∀ y : Fin 3 → Ω,
      |(∏ i, degree W (y i)) *
        graphWeight (⊤ : SimpleGraph (Fin 3)) W y| ≤ 1 := by
    intro y
    have hpn : 0 ≤ ∏ i, degree W (y i) :=
      Finset.prod_nonneg fun i _ ↦ degree_nonneg W _
    have hpo : (∏ i, degree W (y i)) ≤ 1 :=
      Finset.prod_le_one (fun i _ ↦ degree_nonneg W _)
        fun i _ ↦ degree_le_one W _
    rw [abs_of_nonneg (mul_nonneg hpn (graphWeight_nonneg _ W y))]
    exact mul_le_one₀ hpo (graphWeight_nonneg _ W y) (graphWeight_le_one _ W y)
  rw [integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 2 → Ω ↦
      (∏ i, degree W ((Fin.cons a0 y : Fin 3 → Ω) i)) *
        graphWeight (⊤ : SimpleGraph (Fin 3)) W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 1 → Ω ↦
      (∏ i, degree W ((Fin.cons a0 (Fin.cons a1 y) : Fin 3 → Ω) i)) *
        graphWeight (⊤ : SimpleGraph (Fin 3)) W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  rw [show (∫ y : Fin 0 → Ω,
      (∏ i, degree W ((Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)) :
          Fin 3 → Ω) i)) *
        graphWeight (⊤ : SimpleGraph (Fin 3)) W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y)))
      ∂assignmentMeasure (Fin 0) μ) = tri W a0 a1 a2 by
    simp [degTop3_cons]]

/-- **The whiskered density is the degree-weighted triangle density.** -/
theorem homDensity_whisker3 (W : Graphon Ω μ) :
    homDensity whisker3 W =
      ∫ y : Fin 3 → Ω, (∏ i, degree W (y i)) *
        graphWeight (⊤ : SimpleGraph (Fin 3)) W y
      ∂assignmentMeasure (Fin 3) μ := by
  rw [homDensity_whisker3_iterated, integral_degree_top3_iterated]

/-! ### The bound -/

/-- **Atlas 94 dominates its target.** -/
theorem whisker3_bound (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 4 * (2 * cliqueDensity 2 W - 1) ≤
      homDensity whisker3 W := by
  have hppos : (0 : ℝ) < cliqueDensity 2 W := by linarith
  haveI := isProbabilityMeasure_degreeMeasure W hppos
  rw [homDensity_whisker3,
    integral_degree_prod 3 (⊤ : SimpleGraph (Fin 3)) W hppos]
  set z := cliqueDensity 2 (degreeGraphon W) with hzdef
  have hzp : cliqueDensity 2 W ≤ z := le_cliqueDensity_degreeGraphon W hppos
  have hzhalf : (1 : ℝ) / 2 ≤ z := le_trans hp hzp
  have hgood : z * (2 * z - 1) ≤ cliqueDensity 3 (degreeGraphon W) := by
    have h := cliqueDensity_ge_cliquePoly' (degreeGraphon W) 1 (by
      simp only [cliqueThreshold]
      rw [← hzdef]
      norm_num
      linarith)
    rwa [show (1 : ℕ) + 2 = 3 from rfl, cliquePoly_three, ← hzdef] at h
  have hmono : cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1) ≤ z * (2 * z - 1) := by
    nlinarith
  have hfin : cliqueDensity 2 W ^ 3 *
      (cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1)) ≤
      cliqueDensity 2 W ^ 3 * cliqueDensity 3 (degreeGraphon W) :=
    mul_le_mul_of_nonneg_left (le_trans hmono hgood) (by positivity)
  calc cliqueDensity 2 W ^ 4 * (2 * cliqueDensity 2 W - 1)
      = cliqueDensity 2 W ^ 3 *
        (cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1)) := by ring
    _ ≤ cliqueDensity 2 W ^ 3 * cliqueDensity 3 (degreeGraphon W) := hfin

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_94 (z : ℝ) :
    affineProd [0, 1, 1, 1, 1, 2] z = z ^ 4 * (2 * z - 1) := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

def iso94 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0}) {some 1})
      {some (some 2)} ≃g whisker3 where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom94 : IsChromaticPolynomial whisker3
    ((([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := whisker3) iso94
    (isClique_singleton _ (some (some 2)))
    (isChromaticPolynomial_attachVertex (isClique_singleton _ (some 1))
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [Finset.card_singleton, Finset.card_singleton, Finset.card_singleton] at h
  have hpoly : ((([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((1 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count94 (k : ℕ) :
    properAssignmentCount whisker3 k =
      (k - 1) * ((k - 1) * ((k - 1) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := whisker3) iso94
      (isClique_singleton _ (some (some 2))) k,
    properAssignmentCount_attachVertex (isClique_singleton _ (some 1)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    Finset.card_singleton, Finset.card_singleton, Finset.card_singleton]

theorem num94 : IsChromaticNumber whisker3 3 where
  positive := by rw [count94]; decide
  zero_below k hk := by
    rw [count94, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-- **Atlas 94 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_94 : Taeyoung.SatisfiesLowerBound whisker3 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P = (([0, 1, 1, 1, 1, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := whisker3) hP chrom94
  have hreq : r = 3 := IsChromaticNumber.unique (H := whisker3) hr num94
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := whisker3_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 1, 2] (by norm_num) hone,
      affineProd_94]
    exact hkey

end Taeyoung.Methods.Whisker
