import Taeyoung.Methods.Atlas148.High
import Taeyoung.Methods.Peeling

/-!
# Atlas 148: the density identity

Atlas 148 is two triangles sharing a vertex, plus a two-edge path joining one
outer vertex of each.  Labelled for peeling — centre `0`, the two joined outer
vertices `1` and `2`, the two triangle apexes `3` and `4`, the path middle `5`
— its edge list is

```
01, 02, 03, 04, 13, 15, 24, 25.
```

Integrating the three degree-two vertices `3, 4, 5` produces one codegree
kernel each, and the note's identity

```
t(F₁₄₈, W) = ∫∫∫ K(x,a)K(x,b)S(a,b),      K = W·S,
```

falls out with no inequality used.  Two Fubini swaps then turn the triple
integral into the kernel form `T = ∫∫ (T_W F_x)(z)²` of `High.lean`: for fixed
`x`,

```
∫ (T_W F_x)(z)² dz = ∫ K(x,a)·(∫ W(a,z)(T_W F_x)(z) dz) da
                    = ∫∫ K(x,a)K(x,b)S(a,b) da db.
```

Composing with `Atlas148.high_bound` gives the note's high interval for the
homomorphism density itself.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas148

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The two Fubini swaps -/

/-- Pairing a row of `W` against `T_W F_x`. -/
theorem integral_row_mul_fibOp (W : Graphon Ω μ) (x a : Ω) :
    (∫ z, W a z * fibOp W x z ∂μ) = ∫ b, edgeK W x b * pageOp W 0 a b ∂μ := by
  have hi : Integrable
      (Function.uncurry fun z b ↦ W a z * (W z b * edgeK W x b)) (μ.prod μ) := by
    refine integrable_prod_of_bdd (((W.measurable.comp
      (measurable_const.prodMk measurable_fst))).mul (W.measurable.mul
        ((measurable_edgeK W).comp (measurable_const.prodMk measurable_snd))))
      (C := 1) fun q ↦ ?_
    have h0 : 0 ≤ W a q.1 * (W q.1 q.2 * edgeK W x q.2) :=
      mul_nonneg (W.nonneg _ _) (fibOp_integrand_nonneg W x q.1 q.2)
    show |W a q.1 * (W q.1 q.2 * edgeK W x q.2)| ≤ 1
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (W.le_one _ _) (fibOp_integrand_nonneg W x q.1 q.2)
      (fibOp_integrand_le_one W x q.1 q.2)
  have hstep : (∫ z, W a z * fibOp W x z ∂μ)
      = ∫ z, ∫ b, W a z * (W z b * edgeK W x b) ∂μ ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    show W a z * fibOp W x z = ∫ b, W a z * (W z b * edgeK W x b) ∂μ
    rw [fibOp, ← integral_const_mul]
  rw [hstep, integral_integral_swap hi]
  refine integral_congr_ae (ae_of_all _ fun b ↦ ?_)
  show (∫ z, W a z * (W z b * edgeK W x b) ∂μ) = edgeK W x b * pageOp W 0 a b
  have hre : ∀ z, W a z * (W z b * edgeK W x b) = edgeK W x b * (W a z * W b z) := by
    intro z
    rw [W.symm z b]
    ring
  rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul, ← pageOp_zero_eq]

/-- The fibre squared norm, as a double integral. -/
theorem fibNormSq_eq (W : Graphon Ω μ) (x : Ω) :
    fibNormSq W x = ∫ a, ∫ b, edgeK W x a * edgeK W x b * pageOp W 0 a b ∂μ ∂μ := by
  have hi : Integrable
      (Function.uncurry fun z a ↦ fibOp W x z * (W z a * edgeK W x a)) (μ.prod μ) := by
    refine integrable_prod_of_bdd (((measurable_fibOp W).comp
      (measurable_const.prodMk measurable_fst)).mul (W.measurable.mul
        ((measurable_edgeK W).comp (measurable_const.prodMk measurable_snd))))
      (C := 1) fun q ↦ ?_
    have h0 : 0 ≤ fibOp W x q.1 * (W q.1 q.2 * edgeK W x q.2) :=
      mul_nonneg (fibOp_nonneg W x q.1) (fibOp_integrand_nonneg W x q.1 q.2)
    show |fibOp W x q.1 * (W q.1 q.2 * edgeK W x q.2)| ≤ 1
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (fibOp_le_one W x q.1) (fibOp_integrand_nonneg W x q.1 q.2)
      (fibOp_integrand_le_one W x q.1 q.2)
  have hstep : fibNormSq W x = ∫ z, ∫ a, fibOp W x z * (W z a * edgeK W x a) ∂μ ∂μ := by
    rw [fibNormSq]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    show fibOp W x z ^ 2 = ∫ a, fibOp W x z * (W z a * edgeK W x a) ∂μ
    rw [integral_const_mul]
    show fibOp W x z ^ 2 = fibOp W x z * fibOp W x z
    ring
  rw [hstep, integral_integral_swap hi]
  refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
  show (∫ z, fibOp W x z * (W z a * edgeK W x a) ∂μ)
      = ∫ b, edgeK W x a * edgeK W x b * pageOp W 0 a b ∂μ
  have hre : ∀ z, fibOp W x z * (W z a * edgeK W x a)
      = edgeK W x a * (W a z * fibOp W x z) := by
    intro z
    rw [W.symm z a]
    ring
  rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul,
    integral_row_mul_fibOp W x a, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun b ↦ ?_)
  ring

/-- **`T` is the triple integral of the note.** -/
theorem bigT_eq (W : Graphon Ω μ) :
    bigT W = ∫ a0, ∫ a1, ∫ a2,
      edgeK W a0 a1 * edgeK W a0 a2 * pageOp W 0 a1 a2 ∂μ ∂μ ∂μ := by
  rw [bigT]
  exact integral_congr_ae (ae_of_all _ fun x ↦ fibNormSq_eq W x)

/-! ### The graph, and its peeled density -/

/-- Centre `0`; joined outer vertices `1, 2`; triangle apexes `3, 4`; the
two-edge path middle `5`. -/
def graph148 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 5), (2, 4), (2, 5)]

instance : DecidableRel graph148.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_graph148 :
    graph148.edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(1, 3), s(1, 5), s(2, 4), s(2, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_graph148 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight graph148 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 0) (x 3) * W (x 0) (x 4) *
        W (x 1) (x 3) * W (x 1) (x 5) * W (x 2) (x 4) * W (x 2) (x 5) := by
  rw [graphWeight, edgeFinset_graph148]
  simp
  ring

lemma graphWeight_graph148_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight graph148 W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a1 * W a0 a2 * W a0 a3 * W a0 a4 * W a1 a3 * W a1 a5 * W a2 a4 *
        W a2 a5 := by
  rw [graphWeight_graph148]
  rfl

/-- **The density identity.**  Peeling the three degree-two vertices. -/
theorem homDensity_graph148 (W : Graphon Ω μ) :
    homDensity graph148 W =
      ∫ a0, ∫ a1, ∫ a2,
        edgeK W a0 a1 * edgeK W a0 a2 * pageOp W 0 a1 a2 ∂μ ∂μ ∂μ := by
  have hm : Measurable (graphWeight graph148 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight graph148 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight graph148 W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω ↦ graphWeight graph148 W (Fin.cons a0 (Fin.cons a1 y)))
    (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 3 → Ω ↦ graphWeight graph148 W
      (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
    (hm.comp ((measurable_fin_cons a0).comp
      ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
    fun y ↦ hb _]
  have hstep3 : ∀ a3 : Ω,
      (∫ y : Fin 2 → Ω, graphWeight graph148 W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
        ∂assignmentMeasure (Fin 2) μ) =
        (W a0 a1 * W a0 a2 * pageOp W 0 a1 a2 * pageOp W 0 a0 a2) *
          (W a0 a3 * W a1 a3 * degree W a3 ^ (0 : ℝ)) := by
    intro a3
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 2 → Ω ↦ graphWeight graph148 W
        (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
      (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
        ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
      fun y ↦ hb _]
    have hstep4 : ∀ a4 : Ω,
        (∫ y : Fin 1 → Ω, graphWeight graph148 W (Fin.cons a0 (Fin.cons a1
            (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y)))))
          ∂assignmentMeasure (Fin 1) μ) =
          (W a0 a1 * W a0 a2 * W a0 a3 * W a1 a3 * pageOp W 0 a1 a2) *
            (W a0 a4 * W a2 a4 * degree W a4 ^ (0 : ℝ)) := by
      intro a4
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 1 → Ω ↦ graphWeight graph148 W (Fin.cons a0 (Fin.cons a1
          (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y))))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
            (measurable_fin_cons a4))))))
        fun y ↦ hb _]
      have hval : ∀ a5 : Ω,
          (∫ y : Fin 0 → Ω, graphWeight graph148 W (Fin.cons a0 (Fin.cons a1
              (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y))))))
            ∂assignmentMeasure (Fin 0) μ) =
            (W a0 a1 * W a0 a2 * W a0 a3 * W a0 a4 * W a1 a3 * W a2 a4) *
              (W a1 a5 * W a2 a5 * degree W a5 ^ (0 : ℝ)) := by
        intro a5
        rw [show (∫ y : Fin 0 → Ω, graphWeight graph148 W (Fin.cons a0 (Fin.cons a1
            (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
            W a0 a1 * W a0 a2 * W a0 a3 * W a0 a4 * W a1 a3 * W a1 a5 *
              W a2 a4 * W a2 a5 by simp [graphWeight_graph148_cons],
          Real.rpow_zero]
        ring
      rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul, ← pageOp,
        Real.rpow_zero]
      ring
    rw [integral_congr_ae (ae_of_all _ hstep4), integral_const_mul, ← pageOp,
      Real.rpow_zero]
    ring
  rw [integral_congr_ae (ae_of_all _ hstep3), integral_const_mul, ← pageOp]
  simp only [edgeK]
  ring

/-- **Atlas 148's density is the kernel form.** -/
theorem homDensity_graph148_eq_bigT (W : Graphon Ω μ) :
    homDensity graph148 W = bigT W := by
  rw [homDensity_graph148, bigT_eq]

/-- **The high interval for the density itself.** -/
theorem homDensity_graph148_high (W : Graphon Ω μ)
    (hp0 : 3 / 5 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W * (2 * cliqueDensity 2 W - 1) ^ 2 *
        (3 * cliqueDensity 2 W ^ 2 - 3 * cliqueDensity 2 W + 1)
      ≤ homDensity graph148 W := by
  rw [homDensity_graph148_eq_bigT]
  exact high_bound W hp0

end Taeyoung.Methods.Atlas148
