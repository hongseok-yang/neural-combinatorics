import Taeyoung.Methods.Atlas178.Moments
import Taeyoung.Methods.Peeling
import Taeyoung.Methods.TriangleDensity

/-!
# Atlas 178: the page compression

`notes/atlas178_half_degree_weighted_k4.tex` §4.  Integrating the pendant leaf
turns the density into

```
t(H₁₇₈,W) = ∫ A(x)·K₁(x)·K₀(x),        K_f(x) = ∫ f(z)·W(z,x₀)W(z,x₁)W(z,x₂),
```

with `A` the spine triangle weight.  Two Cauchy–Schwarz steps follow: one in the
page variable, `K_{1/2}² ≤ K₀K₁`, and one on the spine triple against the weight
`A`, which gives `∫A·K_{1/2}² ≥ (∫A·K_{1/2})²/∫A = I₄²/T`.

Both are the same lemma, `PureChordal.integral_mul_sq_le_integral_mul_integral_mul_sq`,
applied on `μ` and on `assignmentMeasure (Fin 3) μ` respectively.
-/

open MeasureTheory

namespace Taeyoung.Methods.Atlas178

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link Taeyoung.Methods.K4Tail
  Taeyoung.Methods.CliqueLeaf Taeyoung.Methods.PureChordal
  Taeyoung.Methods.TriangleDensity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The page operator -/

/-- `K_f(a,b,c) = ∫ f(z)·W(a,z)W(b,z)W(c,z)`. -/
noncomputable def pageK (W : Graphon Ω μ) (f : Ω → ℝ) (a b c : Ω) : ℝ :=
  ∫ z, f z * (W a z * W b z * W c z) ∂μ

/-- The spine triangle weight. -/
noncomputable def spineA (W : Graphon Ω μ) (a b c : Ω) : ℝ :=
  W a b * W a c * W b c

section Page

variable (W : Graphon Ω μ) {f : Ω → ℝ}

omit [IsProbabilityMeasure μ] in
lemma spineA_nonneg (a b c : Ω) : 0 ≤ spineA W a b c :=
  mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _)) (W.nonneg _ _)

omit [IsProbabilityMeasure μ] in
lemma spineA_le_one (a b c : Ω) : spineA W a b c ≤ 1 :=
  mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)

lemma measurable_spineA :
    Measurable fun y : Fin 3 → Ω ↦ spineA W (y 0) (y 1) (y 2) :=
  ((measurable_coord_pair W 0 1).mul (measurable_coord_pair W 0 2)).mul
    (measurable_coord_pair W 1 2)

omit [IsProbabilityMeasure μ] in
/-- The three page factors, as a jointly measurable kernel. -/
private lemma measurable_pageKernel (i : Fin 3) :
    Measurable fun q : (Fin 3 → Ω) × Ω ↦ W (q.1 i) q.2 := by
  have hp : Measurable fun q : (Fin 3 → Ω) × Ω ↦ (q.1 i, q.2) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
  have hc : Measurable
      (Function.uncurry W.toFun ∘ fun q : (Fin 3 → Ω) × Ω ↦ (q.1 i, q.2)) :=
    W.measurable.comp hp
  simpa [Function.comp_def, Function.uncurry] using hc

lemma measurable_pageK (hf : Measurable f) :
    Measurable fun y : Fin 3 → Ω ↦ pageK W f (y 0) (y 1) (y 2) := by
  have h : StronglyMeasurable (Function.uncurry
      fun (y : Fin 3 → Ω) (z : Ω) ↦ f z * (W (y 0) z * W (y 1) z * W (y 2) z)) := by
    refine Measurable.stronglyMeasurable ?_
    exact (hf.comp measurable_snd).mul
      (((measurable_pageKernel W 0).mul (measurable_pageKernel W 1)).mul
        (measurable_pageKernel W 2))
  exact (h.integral_prod_right' (ν := μ)).measurable

omit [IsProbabilityMeasure μ] in
lemma pageK_nonneg (hf : ∀ z, 0 ≤ f z) (a b c : Ω) : 0 ≤ pageK W f a b c :=
  integral_nonneg fun z ↦ mul_nonneg (hf z)
    (mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _)) (W.nonneg _ _))

lemma integrable_pageIntegrand (hf : Measurable f) (hf1 : ∀ z, |f z| ≤ 1)
    (a b c : Ω) : Integrable (fun z ↦ f z * (W a z * W b z * W c z)) μ := by
  refine integrable_of_bdd ((hf.mul (((measurable_row W.measurable a).mul
    (measurable_row W.measurable b)).mul (measurable_row W.measurable c))))
    (C := 1) fun z ↦ ?_
  rw [abs_mul, abs_of_nonneg (mul_nonneg (mul_nonneg (W.nonneg a z)
    (W.nonneg b z)) (W.nonneg c z))]
  exact mul_le_one₀ (hf1 z) (mul_nonneg (mul_nonneg (W.nonneg a z)
    (W.nonneg b z)) (W.nonneg c z))
    (mul_le_one₀ (mul_le_one₀ (W.le_one a z) (W.nonneg b z) (W.le_one b z))
      (W.nonneg c z) (W.le_one c z))

lemma pageK_le_one (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1)
    (a b c : Ω) : pageK W f a b c ≤ 1 := by
  have habs : ∀ z, |f z| ≤ 1 := fun z ↦ by
    rw [abs_of_nonneg (hf0 z)]; exact hf1 z
  calc pageK W f a b c ≤ ∫ _z : Ω, (1 : ℝ) ∂μ := by
        refine integral_mono (integrable_pageIntegrand W hf habs a b c)
          (integrable_const _) fun z ↦ ?_
        exact mul_le_one₀ (hf1 z) (mul_nonneg (mul_nonneg (W.nonneg a z)
          (W.nonneg b z)) (W.nonneg c z))
          (mul_le_one₀ (mul_le_one₀ (W.le_one a z) (W.nonneg b z)
            (W.le_one b z)) (W.nonneg c z) (W.le_one c z))
    _ = 1 := by simp

end Page

/-! ### Cauchy–Schwarz in the page variable -/

/-- `K_{1/2}² ≤ K₀·K₁`. -/
theorem sq_pageK_half_le (W : Graphon Ω μ) (a b c : Ω) :
    pageK W (sqrtDeg W) a b c ^ 2 ≤
      pageK W (fun _ ↦ 1) a b c * pageK W (degree W) a b c := by
  set A : Ω → ℝ := fun z ↦ W a z * W b z * W c z with hA
  have hA0 : ∀ z, 0 ≤ A z := fun z ↦
    mul_nonneg (mul_nonneg (W.nonneg a z) (W.nonneg b z)) (W.nonneg c z)
  have hAm : Measurable A :=
    ((measurable_row W.measurable a).mul (measurable_row W.measurable b)).mul
      (measurable_row W.measurable c)
  have hA1 : ∀ z, A z ≤ 1 := fun z ↦
    mul_le_one₀ (mul_le_one₀ (W.le_one a z) (W.nonneg b z) (W.le_one b z))
      (W.nonneg c z) (W.le_one c z)
  have hAi : Integrable A μ :=
    integrable_of_bdd hAm (C := 1) fun z ↦ by
      rw [abs_of_nonneg (hA0 z)]; exact hA1 z
  have hAη : Integrable (fun z ↦ A z * sqrtDeg W z) μ :=
    integrable_of_bdd (hAm.mul (measurable_sqrtDeg W)) (C := 1) fun z ↦ by
      rw [abs_of_nonneg (mul_nonneg (hA0 z) (sqrtDeg_nonneg W z))]
      exact mul_le_one₀ (hA1 z) (sqrtDeg_nonneg W z) (sqrtDeg_le_one W z)
  have hAη2 : Integrable (fun z ↦ A z * sqrtDeg W z ^ 2) μ :=
    integrable_of_bdd (hAm.mul ((measurable_sqrtDeg W).pow_const 2)) (C := 1)
      fun z ↦ by
        rw [abs_of_nonneg (mul_nonneg (hA0 z) (by positivity))]
        exact mul_le_one₀ (hA1 z) (by positivity)
          (by rw [sqrtDeg_sq]; exact degree_le_one W z)
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := μ) (A := A) (η := sqrtDeg W) hAi hAη hAη2 hA0
  have e1 : (∫ z, A z * sqrtDeg W z ∂μ) = pageK W (sqrtDeg W) a b c := by
    rw [pageK]; exact integral_congr_ae (ae_of_all _ fun z ↦ by rw [hA]; ring)
  have e2 : (∫ z, A z ∂μ) = pageK W (fun _ ↦ 1) a b c := by
    rw [pageK]; exact integral_congr_ae (ae_of_all _ fun z ↦ by rw [hA]; ring)
  have e3 : (∫ z, A z * sqrtDeg W z ^ 2 ∂μ) = pageK W (degree W) a b c := by
    rw [pageK]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only [hA]
    rw [sqrtDeg_sq]
    ring
  rw [e1, e2, e3] at hcs
  exact hcs

/-! ### The graph and its density -/

/-- Atlas 178: a spine triangle `0,1,2`, two page vertices `3,4` joined to all
three spine vertices, and a pendant leaf `5` on the page `3`. -/
def graph178 : SimpleGraph (Fin 6) :=
  graphFromEdges 6
    [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3), (0, 4), (1, 4), (2, 4),
      (3, 5)]

instance : DecidableRel graph178.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_graph178 :
    graph178.edgeFinset =
      {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(1, 3), s(2, 3), s(0, 4), s(1, 4),
        s(2, 4), s(3, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_graph178 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight graph178 W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) * W (x 0) (x 3) *
        W (x 1) (x 3) * W (x 2) (x 3) * W (x 0) (x 4) * W (x 1) (x 4) *
        W (x 2) (x 4) * W (x 3) (x 5) := by
  rw [graphWeight, edgeFinset_graph178]
  simp
  ring

set_option maxHeartbeats 1000000 in
/-- **The density of Atlas 178 is `∫ A·K₁·K₀`.** -/
theorem homDensity_graph178 (W : Graphon Ω μ) :
    homDensity graph178 W =
      ∫ y : Fin 3 → Ω, spineA W (y 0) (y 1) (y 2) *
        (pageK W (degree W) (y 0) (y 1) (y 2) *
          pageK W (fun _ ↦ 1) (y 0) (y 1) (y 2))
        ∂assignmentMeasure (Fin 3) μ := by
  have hm : Measurable (graphWeight graph178 W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight graph178 W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  have hm' : Measurable fun y : Fin 6 → Ω ↦
      W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
        W (y 1) (y 3) * W (y 2) (y 3) * W (y 0) (y 4) * W (y 1) (y 4) *
        W (y 2) (y 4) * W (y 3) (y 5) :=
    ((((((((((measurable_coord_pair W 0 1).mul
      (measurable_coord_pair W 0 2)).mul (measurable_coord_pair W 1 2)).mul
      (measurable_coord_pair W 0 3)).mul (measurable_coord_pair W 1 3)).mul
      (measurable_coord_pair W 2 3)).mul (measurable_coord_pair W 0 4)).mul
      (measurable_coord_pair W 1 4)).mul (measurable_coord_pair W 2 4)).mul
      (measurable_coord_pair W 3 5))
  have hb' : ∀ y : Fin 6 → Ω,
      |W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2) * W (y 0) (y 3) *
        W (y 1) (y 3) * W (y 2) (y 3) * W (y 0) (y 4) * W (y 1) (y 4) *
        W (y 2) (y 4) * W (y 3) (y 5)| ≤ 1 := by
    intro y
    rw [← graphWeight_graph178 W y]
    exact hb y
  rw [homDensity, integral_congr_ae (ae_of_all _ fun y ↦ graphWeight_graph178 W y),
    integral_assignment_fin_six (g := fun a0 a1 a2 a3 a4 a5 : Ω ↦
      W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a2 a3 * W a0 a4 *
        W a1 a4 * W a2 a4 * W a3 a5) hm' hb']
  -- collapse the three page coordinates
  have hstep : ∀ a0 a1 a2 : Ω,
      (∫ a3, ∫ a4, ∫ a5,
          W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a2 a3 *
            W a0 a4 * W a1 a4 * W a2 a4 * W a3 a5 ∂μ ∂μ ∂μ) =
        spineA W a0 a1 a2 *
          (pageK W (degree W) a0 a1 a2 * pageK W (fun _ ↦ 1) a0 a1 a2) := by
    intro a0 a1 a2
    have h5 : ∀ a3 a4 : Ω,
        (∫ a5, W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a2 a3 *
            W a0 a4 * W a1 a4 * W a2 a4 * W a3 a5 ∂μ) =
          (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a2 a3 *
            W a0 a4 * W a1 a4 * W a2 a4) * degree W a3 := by
      intro a3 a4
      rw [integral_const_mul]
      rfl
    rw [integral_congr_ae (ae_of_all _ fun a3 ↦
      integral_congr_ae (ae_of_all _ fun a4 ↦ h5 a3 a4))]
    have h4 : ∀ a3 : Ω,
        (∫ a4, (W a0 a1 * W a0 a2 * W a1 a2 * W a0 a3 * W a1 a3 * W a2 a3 *
            W a0 a4 * W a1 a4 * W a2 a4) * degree W a3 ∂μ) =
          (W a0 a1 * W a0 a2 * W a1 a2 * (W a0 a3 * W a1 a3 * W a2 a3 *
            degree W a3)) * pageK W (fun _ ↦ 1) a0 a1 a2 := by
      intro a3
      rw [pageK, ← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun a4 ↦ by simp only []; ring)
    rw [integral_congr_ae (ae_of_all _ h4)]
    have h3 : (∫ a3, (W a0 a1 * W a0 a2 * W a1 a2 * (W a0 a3 * W a1 a3 *
          W a2 a3 * degree W a3)) * pageK W (fun _ ↦ 1) a0 a1 a2 ∂μ) =
        (W a0 a1 * W a0 a2 * W a1 a2 * pageK W (fun _ ↦ 1) a0 a1 a2) *
          pageK W (degree W) a0 a1 a2 := by
      have hcong : ∀ a3 : Ω,
          (W a0 a1 * W a0 a2 * W a1 a2 * (W a0 a3 * W a1 a3 * W a2 a3 *
              degree W a3)) * pageK W (fun _ ↦ 1) a0 a1 a2
            = (W a0 a1 * W a0 a2 * W a1 a2 * pageK W (fun _ ↦ 1) a0 a1 a2) *
              (degree W a3 * (W a0 a3 * W a1 a3 * W a2 a3)) := fun a3 ↦ by ring
      rw [integral_congr_ae (ae_of_all _ hcong), integral_const_mul]
      rfl
    rw [h3, spineA]
    ring
  rw [integral_congr_ae (ae_of_all _ fun a0 ↦
    integral_congr_ae (ae_of_all _ fun a1 ↦
      integral_congr_ae (ae_of_all _ fun a2 ↦ hstep a0 a1 a2)))]
  refine (integral_assignment_fin_three (g := fun a0 a1 a2 : Ω ↦
    spineA W a0 a1 a2 *
      (pageK W (degree W) a0 a1 a2 * pageK W (fun _ ↦ 1) a0 a1 a2)) ?_ ?_).symm
  · exact (measurable_spineA W).mul
      ((measurable_pageK W (measurable_degree W)).mul
        (measurable_pageK W measurable_const))
  · intro y
    have h0 : 0 ≤ spineA W (y 0) (y 1) (y 2) *
        (pageK W (degree W) (y 0) (y 1) (y 2) *
          pageK W (fun _ ↦ 1) (y 0) (y 1) (y 2)) :=
      mul_nonneg (spineA_nonneg W _ _ _)
        (mul_nonneg (pageK_nonneg W (degree_nonneg W) _ _ _)
          (pageK_nonneg W (fun _ ↦ zero_le_one) _ _ _))
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ (spineA_le_one W _ _ _)
      (mul_nonneg (pageK_nonneg W (degree_nonneg W) _ _ _)
        (pageK_nonneg W (fun _ ↦ zero_le_one) _ _ _))
      (mul_le_one₀
        (pageK_le_one W (measurable_degree W) (degree_nonneg W)
          (degree_le_one W) _ _ _)
        (pageK_nonneg W (fun _ ↦ zero_le_one) _ _ _)
        (pageK_le_one W measurable_const (fun _ ↦ zero_le_one)
          (fun _ ↦ le_refl 1) _ _ _))

/-! ### The spine integral of the page operator -/

set_option maxHeartbeats 1000000 in
/-- Fubini between the spine triple and the page variable. -/
theorem integral_spineA_mul_pageK (W : Graphon Ω μ) {f : Ω → ℝ}
    (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1) :
    (∫ y : Fin 3 → Ω, spineA W (y 0) (y 1) (y 2) * pageK W f (y 0) (y 1) (y 2)
        ∂assignmentMeasure (Fin 3) μ) = ∫ z, f z * rootedK4 W z ∂μ := by
  set ν := assignmentMeasure (Fin 3) μ with hν
  set F : (Fin 3 → Ω) → Ω → ℝ := fun y z ↦
    spineA W (y 0) (y 1) (y 2) * (f z * (W (y 0) z * W (y 1) z * W (y 2) z))
    with hF
  have hmeas : Measurable (Function.uncurry F) := by
    refine Measurable.mul ?_ ?_
    · exact (measurable_spineA W).comp measurable_fst
    · exact (hf.comp measurable_snd).mul
        (((measurable_pageKernel W 0).mul (measurable_pageKernel W 1)).mul
          (measurable_pageKernel W 2))
  have hbd : ∀ q : (Fin 3 → Ω) × Ω, |Function.uncurry F q| ≤ 1 := by
    rintro ⟨y, z⟩
    have h0 : 0 ≤ spineA W (y 0) (y 1) (y 2) *
        (f z * (W (y 0) z * W (y 1) z * W (y 2) z)) :=
      mul_nonneg (spineA_nonneg W _ _ _) (mul_nonneg (hf0 z)
        (mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _)) (W.nonneg _ _)))
    show |spineA W (y 0) (y 1) (y 2) *
        (f z * (W (y 0) z * W (y 1) z * W (y 2) z))| ≤ 1
    rw [abs_of_nonneg h0]
    refine mul_le_one₀ (spineA_le_one W _ _ _) (mul_nonneg (hf0 z)
      (mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _)) (W.nonneg _ _))) ?_
    exact mul_le_one₀ (hf1 z)
      (mul_nonneg (mul_nonneg (W.nonneg _ _) (W.nonneg _ _)) (W.nonneg _ _))
      (mul_le_one₀ (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
        (W.nonneg _ _) (W.le_one _ _))
  have hint : Integrable (Function.uncurry F) (ν.prod μ) :=
    (integrable_const (μ := ν.prod μ) (1 : ℝ)).mono' hmeas.aestronglyMeasurable
      (ae_of_all _ fun q ↦ by rw [Real.norm_eq_abs]; exact hbd q)
  have hleft : ∀ y : Fin 3 → Ω,
      spineA W (y 0) (y 1) (y 2) * pageK W f (y 0) (y 1) (y 2)
        = ∫ z, F y z ∂μ := by
    intro y
    rw [hF, pageK, ← integral_const_mul]
  rw [integral_congr_ae (ae_of_all _ hleft), integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  simp only []
  have hrk : rootedK4 W z = ∫ y : Fin 3 → Ω, spineA W (y 0) (y 1) (y 2) *
      (W (y 0) z * W (y 1) z * W (y 2) z) ∂ν := by
    rw [rootedK4, rootedDensity]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    simp only []
    rw [Fin.prod_univ_three, graphWeight_top3, spineA, W.symm z (y 0),
      W.symm z (y 1), W.symm z (y 2)]
    ring
  rw [hrk, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  show spineA W (y 0) (y 1) (y 2) * (f z * (W (y 0) z * W (y 1) z * W (y 2) z))
      = f z * (spineA W (y 0) (y 1) (y 2) * (W (y 0) z * W (y 1) z * W (y 2) z))
  ring

/-! ### Cauchy–Schwarz on the spine -/

set_option maxHeartbeats 1000000 in
/-- **The page compression.**  `I₄² ≤ T·t(H₁₇₈,W)`. -/
theorem sq_halfK4_le (W : Graphon Ω μ) :
    halfK4 W ^ 2 ≤ cliqueDensity 3 W * homDensity graph178 W := by
  set ν := assignmentMeasure (Fin 3) μ with hν
  set A : (Fin 3 → Ω) → ℝ := fun y ↦ spineA W (y 0) (y 1) (y 2) with hA
  set η : (Fin 3 → Ω) → ℝ := fun y ↦ pageK W (sqrtDeg W) (y 0) (y 1) (y 2)
    with hη
  have hA0 : ∀ y, 0 ≤ A y := fun y ↦ spineA_nonneg W _ _ _
  have hA1 : ∀ y, A y ≤ 1 := fun y ↦ spineA_le_one W _ _ _
  have hAm : Measurable A := measurable_spineA W
  have hηm : Measurable η := measurable_pageK W (measurable_sqrtDeg W)
  have hη0 : ∀ y, 0 ≤ η y := fun y ↦ pageK_nonneg W (sqrtDeg_nonneg W) _ _ _
  have hη1 : ∀ y, η y ≤ 1 := fun y ↦
    pageK_le_one W (measurable_sqrtDeg W) (sqrtDeg_nonneg W) (sqrtDeg_le_one W)
      _ _ _
  have hAi : Integrable A ν :=
    integrable_of_bdd (μ := ν) hAm (C := 1) fun y ↦ by
      rw [abs_of_nonneg (hA0 y)]; exact hA1 y
  have hAη : Integrable (fun y ↦ A y * η y) ν :=
    integrable_of_bdd (μ := ν) (hAm.mul hηm) (C := 1) fun y ↦ by
      rw [abs_of_nonneg (mul_nonneg (hA0 y) (hη0 y))]
      exact mul_le_one₀ (hA1 y) (hη0 y) (hη1 y)
  have hAη2 : Integrable (fun y ↦ A y * η y ^ 2) ν :=
    integrable_of_bdd (μ := ν) (hAm.mul (hηm.pow_const 2)) (C := 1) fun y ↦ by
      rw [abs_of_nonneg (mul_nonneg (hA0 y) (by positivity))]
      exact mul_le_one₀ (hA1 y) (by positivity)
        (by nlinarith [hη0 y, hη1 y])
  have hcs := integral_mul_sq_le_integral_mul_integral_mul_sq
    (μ := ν) (A := A) (η := η) hAi hAη hAη2 hA0
  -- the three integrals
  have hT : (∫ y, A y ∂ν) = cliqueDensity 3 W := by
    rw [cliqueDensity_three_eq, hA]
    refine integral_assignment_fin_three (g := fun a0 a1 a2 : Ω ↦
      spineA W a0 a1 a2) hAm ?_
    intro y
    rw [abs_of_nonneg (hA0 y)]; exact hA1 y
  have hI4 : (∫ y, A y * η y ∂ν) = halfK4 W := by
    rw [hA, hη, halfK4]
    exact integral_spineA_mul_pageK W (measurable_sqrtDeg W) (sqrtDeg_nonneg W)
      (sqrtDeg_le_one W)
  have hbound : (∫ y, A y * η y ^ 2 ∂ν) ≤ homDensity graph178 W := by
    rw [homDensity_graph178]
    refine integral_mono hAη2 ?_ fun y ↦ ?_
    · refine integrable_of_bdd (μ := ν) (hAm.mul
        ((measurable_pageK W (measurable_degree W)).mul
          (measurable_pageK W measurable_const))) (C := 1) fun y ↦ ?_
      have h1 : 0 ≤ pageK W (degree W) (y 0) (y 1) (y 2) :=
        pageK_nonneg W (degree_nonneg W) _ _ _
      have h2 : 0 ≤ pageK W (fun _ ↦ 1) (y 0) (y 1) (y 2) :=
        pageK_nonneg W (fun _ ↦ zero_le_one) _ _ _
      rw [abs_of_nonneg (mul_nonneg (hA0 y) (mul_nonneg h1 h2))]
      exact mul_le_one₀ (hA1 y) (mul_nonneg h1 h2)
        (mul_le_one₀ (pageK_le_one W (measurable_degree W) (degree_nonneg W)
          (degree_le_one W) _ _ _) h2
          (pageK_le_one W measurable_const (fun _ ↦ zero_le_one)
            (fun _ ↦ le_refl 1) _ _ _))
    · have hpt := sq_pageK_half_le W (y 0) (y 1) (y 2)
      have := mul_le_mul_of_nonneg_left hpt (hA0 y)
      calc A y * η y ^ 2 ≤ A y * (pageK W (fun _ ↦ 1) (y 0) (y 1) (y 2) *
            pageK W (degree W) (y 0) (y 1) (y 2)) := this
        _ = spineA W (y 0) (y 1) (y 2) *
            (pageK W (degree W) (y 0) (y 1) (y 2) *
              pageK W (fun _ ↦ 1) (y 0) (y 1) (y 2)) := by rw [hA]; ring
  rw [hI4, hT] at hcs
  have hT0 : 0 ≤ cliqueDensity 3 W := by
    rw [← hT]; exact integral_nonneg hA0
  exact hcs.trans (mul_le_mul_of_nonneg_left hbound hT0)

end Taeyoung.Methods.Atlas178
