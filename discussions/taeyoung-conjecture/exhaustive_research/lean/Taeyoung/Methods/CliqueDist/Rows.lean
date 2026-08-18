import Taeyoung.Methods.CliqueDist.Bias
import Taeyoung.Methods.Peeling
import Taeyoung.Methods.ForestCone.Rows
import Taeyoung.Methods.BaseCone.Rows

/-!
# Atlas 134: `K₄` with one leaf on each of two clique vertices

`H₄(1,1,0,0)` in `notes/clique_distributed_leaves.tex`.  Peeling the two leaves
gives

```
t(H,W) = ∫_{Ω⁴} F(x)·d(x₀)d(x₁) dμ⁴,      F = the K₄ weight.
```

The note symmetrises over all `r!` clique permutations and applies AM–GM to the
resulting monomials.  At `(r,h) = (4,2)` that reduces to **one** exchange: the
graph with its leaves on `{0,1}` is isomorphic to the one with leaves on
`{2,3}`, so

```
2·t(H,W) = ∫ F·(d₀d₁ + d₂d₃) ≥ ∫ F·2√(d₀d₁d₂d₃) = 2∫ F·∏ᵢ√(d(xᵢ)),
```

by the two-term AM–GM `a + b ≥ 2√(ab)`.  No `r!`-fold average is needed, and the
geometric mean that appears is exactly `∏√d`, the `α = h/r = 1/2` weight.

`Methods/CliqueDist/Bias.lean` turns `∫F·∏√d` into `M⁴·t(K₄,W_ν)` on the
`√d`-biased space, and the two facts `M² ≤ p` and `M²·t(K₂,W_ν) ≥ p²` reduce the
note's Lemma 3.2 — `Ψ_r = A_r/s^{r/2}` increasing, proved there by logarithmic
differentiation — to the factorization

```
p(2s-1)(3s-2) - s(2p-1)(3p-2) = (s-p)(6ps-2) ≥ 0,
```

which needs no calculus at all.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.CliqueDist

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PureChordal Taeyoung.Methods.PawCone
  Taeyoung.Methods.BaseCone Taeyoung.Methods.ForestCone

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The `K₄` weight -/

lemma edgeFinset_top_fin_four :
    (⊤ : SimpleGraph (Fin 4)).edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

/-- The `K₄` weight as a function of four explicit coordinates. -/
noncomputable def k4w (W : Graphon Ω μ) (a0 a1 a2 a3 : Ω) : ℝ :=
  W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a2 a3

lemma graphWeight_top_fin_four (W : Graphon Ω μ) (x : Fin 4 → Ω) :
    graphWeight (⊤ : SimpleGraph (Fin 4)) W x = k4w W (x 0) (x 1) (x 2) (x 3) := by
  rw [graphWeight, edgeFinset_top_fin_four, k4w]
  simp
  ring

lemma k4w_nonneg (W : Graphon Ω μ) (a0 a1 a2 a3 : Ω) : 0 ≤ k4w W a0 a1 a2 a3 := by
  simp only [k4w]
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact W.nonneg _ _

lemma k4w_le_one (W : Graphon Ω μ) (a0 a1 a2 a3 : Ω) : k4w W a0 a1 a2 a3 ≤ 1 := by
  simp only [k4w]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (mul_le_one₀
    (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _)

lemma measurable_pair {n : ℕ} (W : Graphon Ω μ) (i j : Fin n) :
    Measurable fun y : Fin n → Ω ↦ W (y i) (y j) :=
  Measurable.comp (f := fun y : Fin n → Ω ↦ (y i, y j)) W.measurable
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j))

private lemma measurable_k4w {n : ℕ} (W : Graphon Ω μ) (i j k l : Fin n) :
    Measurable fun y : Fin n → Ω ↦ k4w W (y i) (y j) (y k) (y l) := by
  simp only [k4w]
  exact (((((measurable_pair W i j).mul (measurable_pair W i k)).mul
    (measurable_pair W i l)).mul (measurable_pair W j k)).mul
    (measurable_pair W j l)).mul (measurable_pair W k l)

/-! ### The two graphs -/

/-- `K₄` on `0,1,2,3`; leaf `4` on `0` and leaf `5` on `1`. -/
def cliqueDist01 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (0, 4), (1, 5)]

instance : DecidableRel cliqueDist01.Adj := graphFromEdges_decidableAdj _ _

/-- The same, with the leaves moved to `2` and `3`. -/
def cliqueDist23 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (2, 4), (3, 5)]

instance : DecidableRel cliqueDist23.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_cliqueDist01 :
    cliqueDist01.edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3), s(0, 4), s(1, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma edgeFinset_cliqueDist23 :
    cliqueDist23.edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3), s(2, 4), s(3, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_cliqueDist01 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight cliqueDist01 W x =
      k4w W (x 0) (x 1) (x 2) (x 3) * (W (x 0) (x 4) * W (x 1) (x 5)) := by
  rw [graphWeight, edgeFinset_cliqueDist01, k4w]
  simp
  ring

lemma graphWeight_cliqueDist23 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight cliqueDist23 W x =
      k4w W (x 0) (x 1) (x 2) (x 3) * (W (x 2) (x 4) * W (x 3) (x 5)) := by
  rw [graphWeight, edgeFinset_cliqueDist23, k4w]
  simp
  ring

/-! ### The two peelings

Both go through `Methods/Peeling.lean`, so only the collapse of the two leaf
integrals is written out. -/

section Peel

variable (W : Graphon Ω μ)

private lemma bdd_leafpair (i j : Fin 6) (x : Fin 6 → Ω) :
    |k4w W (x 0) (x 1) (x 2) (x 3) * (W (x i) (x 4) * W (x j) (x 5))| ≤ 1 := by
  have h0 : 0 ≤ k4w W (x 0) (x 1) (x 2) (x 3) * (W (x i) (x 4) * W (x j) (x 5)) :=
    mul_nonneg (k4w_nonneg W _ _ _ _)
      (mul_nonneg (W.nonneg _ _) (W.nonneg _ _))
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (k4w_le_one W _ _ _ _)
    (mul_nonneg (W.nonneg _ _) (W.nonneg _ _))
    (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))

private lemma meas_leafpair (i j : Fin 6) :
    Measurable fun y : Fin 6 → Ω ↦
      k4w W (y 0) (y 1) (y 2) (y 3) * (W (y i) (y 4) * W (y j) (y 5)) :=
  (measurable_k4w W 0 1 2 3).mul
    ((measurable_pair W i 4).mul (measurable_pair W j 5))

private lemma bdd_weighted (i j : Fin 4) (y : Fin 4 → Ω) :
    |degree W (y i) * degree W (y j) * k4w W (y 0) (y 1) (y 2) (y 3)| ≤ 1 := by
  have h0 : 0 ≤ degree W (y i) * degree W (y j) * k4w W (y 0) (y 1) (y 2) (y 3) :=
    mul_nonneg (mul_nonneg (degree_nonneg W _) (degree_nonneg W _))
      (k4w_nonneg W _ _ _ _)
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (degree_le_one W _) (degree_nonneg W _)
    (degree_le_one W _)) (k4w_nonneg W _ _ _ _) (k4w_le_one W _ _ _ _)

private lemma meas_weighted (i j : Fin 4) :
    Measurable fun y : Fin 4 → Ω ↦
      degree W (y i) * degree W (y j) * k4w W (y 0) (y 1) (y 2) (y 3) :=
  (((measurable_degree W).comp (measurable_pi_apply i)).mul
    ((measurable_degree W).comp (measurable_pi_apply j))).mul
    (measurable_k4w W 0 1 2 3)

/-- `t(H₀₁,W) = ∫ F·d₀d₁`. -/
theorem homDensity_cliqueDist01 :
    homDensity cliqueDist01 W =
      ∫ y : Fin 4 → Ω, degree W (y 0) * degree W (y 1) *
        k4w W (y 0) (y 1) (y 2) (y 3) ∂assignmentMeasure (Fin 4) μ := by
  rw [homDensity, integral_congr_ae (ae_of_all _ (graphWeight_cliqueDist01 W)),
    integral_assignment_fin_six
      (g := fun a0 a1 a2 a3 a4 a5 ↦ k4w W a0 a1 a2 a3 * (W a0 a4 * W a1 a5))
      (meas_leafpair W 0 1) (bdd_leafpair W 0 1),
    integral_assignment_fin_four
      (g := fun a0 a1 a2 a3 ↦ degree W a0 * degree W a1 * k4w W a0 a1 a2 a3)
      (meas_weighted W 0 1) (bdd_weighted W 0 1)]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
  simp only []
  have h5 : ∀ a4 : Ω,
      (∫ a5, k4w W a0 a1 a2 a3 * (W a0 a4 * W a1 a5) ∂μ) =
        (k4w W a0 a1 a2 a3 * W a0 a4) * degree W a1 := by
    intro a4
    have hre : ∀ a5 : Ω, k4w W a0 a1 a2 a3 * (W a0 a4 * W a1 a5) =
        (k4w W a0 a1 a2 a3 * W a0 a4) * W a1 a5 := fun a5 ↦ by ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
    rfl
  rw [integral_congr_ae (ae_of_all _ h5)]
  have h4 : ∀ a4 : Ω, (k4w W a0 a1 a2 a3 * W a0 a4) * degree W a1 =
      (k4w W a0 a1 a2 a3 * degree W a1) * W a0 a4 := fun a4 ↦ by ring
  rw [integral_congr_ae (ae_of_all _ h4), integral_const_mul]
  show k4w W a0 a1 a2 a3 * degree W a1 * degree W a0 =
    degree W a0 * degree W a1 * k4w W a0 a1 a2 a3
  ring

/-- `t(H₂₃,W) = ∫ F·d₂d₃`. -/
theorem homDensity_cliqueDist23 :
    homDensity cliqueDist23 W =
      ∫ y : Fin 4 → Ω, degree W (y 2) * degree W (y 3) *
        k4w W (y 0) (y 1) (y 2) (y 3) ∂assignmentMeasure (Fin 4) μ := by
  rw [homDensity, integral_congr_ae (ae_of_all _ (graphWeight_cliqueDist23 W)),
    integral_assignment_fin_six
      (g := fun a0 a1 a2 a3 a4 a5 ↦ k4w W a0 a1 a2 a3 * (W a2 a4 * W a3 a5))
      (meas_leafpair W 2 3) (bdd_leafpair W 2 3),
    integral_assignment_fin_four
      (g := fun a0 a1 a2 a3 ↦ degree W a2 * degree W a3 * k4w W a0 a1 a2 a3)
      (meas_weighted W 2 3) (bdd_weighted W 2 3)]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
  simp only []
  have h5 : ∀ a4 : Ω,
      (∫ a5, k4w W a0 a1 a2 a3 * (W a2 a4 * W a3 a5) ∂μ) =
        (k4w W a0 a1 a2 a3 * W a2 a4) * degree W a3 := by
    intro a4
    have hre : ∀ a5 : Ω, k4w W a0 a1 a2 a3 * (W a2 a4 * W a3 a5) =
        (k4w W a0 a1 a2 a3 * W a2 a4) * W a3 a5 := fun a5 ↦ by ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
    rfl
  rw [integral_congr_ae (ae_of_all _ h5)]
  have h4 : ∀ a4 : Ω, (k4w W a0 a1 a2 a3 * W a2 a4) * degree W a3 =
      (k4w W a0 a1 a2 a3 * degree W a3) * W a2 a4 := fun a4 ↦ by ring
  rw [integral_congr_ae (ae_of_all _ h4), integral_const_mul]
  show k4w W a0 a1 a2 a3 * degree W a3 * degree W a2 =
    degree W a2 * degree W a3 * k4w W a0 a1 a2 a3
  ring

end Peel

/-! ### The single exchange -/

/-- Moving the two leaves from `{0,1}` to `{2,3}` is a graph isomorphism. -/
def isoExchange : cliqueDist01 ≃g cliqueDist23 where
  toEquiv :=
    { toFun := ![2, 3, 0, 1, 4, 5]
      invFun := ![2, 3, 0, 1, 4, 5]
      left_inv := by decide
      right_inv := by decide }
  map_rel_iff' := by
    intro a b
    revert a b
    decide

/-! ### The bound -/

/-- **Atlas 134 dominates its target.** -/
theorem cliqueDist01_bound (W : Graphon Ω μ)
    (hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 3 * (2 * cliqueDensity 2 W - 1) *
        (3 * cliqueDensity 2 W - 2) ≤ homDensity cliqueDist01 W := by
  set p := cliqueDensity 2 W with hpdef
  have hppos : (0 : ℝ) < p := by linarith
  have hMpos : 0 < sqrtMean W := sqrtMean_pos W (by rw [← hpdef]; exact hppos)
  haveI := isProbabilityMeasure_sqrtMeasure W hMpos
  -- the two peelings and the exchange
  have hswap : (∫ y : Fin 4 → Ω, degree W (y 0) * degree W (y 1) *
      k4w W (y 0) (y 1) (y 2) (y 3) ∂assignmentMeasure (Fin 4) μ) =
      ∫ y : Fin 4 → Ω, degree W (y 2) * degree W (y 3) *
        k4w W (y 0) (y 1) (y 2) (y 3) ∂assignmentMeasure (Fin 4) μ := by
    rw [← homDensity_cliqueDist01 W, ← homDensity_cliqueDist23 W]
    exact homDensity_iso W isoExchange
  -- AM--GM, pointwise
  have hamgm : ∀ y : Fin 4 → Ω,
      2 * ((∏ i, sqrtDegree W (y i)) * k4w W (y 0) (y 1) (y 2) (y 3)) ≤
        degree W (y 0) * degree W (y 1) * k4w W (y 0) (y 1) (y 2) (y 3) +
          degree W (y 2) * degree W (y 3) * k4w W (y 0) (y 1) (y 2) (y 3) := by
    intro y
    have hprod : (∏ i, sqrtDegree W (y i)) =
        sqrtDegree W (y 0) * sqrtDegree W (y 1) * sqrtDegree W (y 2) *
          sqrtDegree W (y 3) := by
      rw [Fin.prod_univ_four]
    have e0 := sq_sqrtDegree W (y 0)
    have e1 := sq_sqrtDegree W (y 1)
    have e2 := sq_sqrtDegree W (y 2)
    have e3 := sq_sqrtDegree W (y 3)
    have hstep : 2 * (sqrtDegree W (y 0) * sqrtDegree W (y 1) *
        sqrtDegree W (y 2) * sqrtDegree W (y 3)) ≤
        degree W (y 0) * degree W (y 1) + degree W (y 2) * degree W (y 3) := by
      nlinarith [sq_nonneg (sqrtDegree W (y 0) * sqrtDegree W (y 1) -
        sqrtDegree W (y 2) * sqrtDegree W (y 3)), e0, e1, e2, e3]
    rw [hprod]
    nlinarith [hstep, k4w_nonneg W (y 0) (y 1) (y 2) (y 3)]
  -- integrate the AM--GM
  have hint01 : Integrable (fun y : Fin 4 → Ω ↦ degree W (y 0) * degree W (y 1) *
      k4w W (y 0) (y 1) (y 2) (y 3)) (assignmentMeasure (Fin 4) μ) :=
    integrable_of_bdd (meas_weighted W 0 1) (C := 1) (bdd_weighted W 0 1)
  have hint23 : Integrable (fun y : Fin 4 → Ω ↦ degree W (y 2) * degree W (y 3) *
      k4w W (y 0) (y 1) (y 2) (y 3)) (assignmentMeasure (Fin 4) μ) :=
    integrable_of_bdd (meas_weighted W 2 3) (C := 1) (bdd_weighted W 2 3)
  have hmeasS : Measurable fun y : Fin 4 → Ω ↦
      (∏ i, sqrtDegree W (y i)) * graphWeight (⊤ : SimpleGraph (Fin 4)) W y := by
    refine Measurable.mul ?_ (measurable_graphWeight _ W)
    exact Finset.measurable_prod _ fun i _ ↦
      (measurable_sqrtDegree W).comp (measurable_pi_apply i)
  have hbddS : ∀ y : Fin 4 → Ω,
      |(∏ i, sqrtDegree W (y i)) * graphWeight (⊤ : SimpleGraph (Fin 4)) W y| ≤ 1 := by
    intro y
    have hp0 : 0 ≤ ∏ i, sqrtDegree W (y i) :=
      Finset.prod_nonneg fun i _ ↦ sqrtDegree_nonneg W (y i)
    have hp1 : (∏ i, sqrtDegree W (y i)) ≤ 1 :=
      Finset.prod_le_one (fun i _ ↦ sqrtDegree_nonneg W (y i))
        fun i _ ↦ sqrtDegree_le_one W (y i)
    have h0 : 0 ≤ (∏ i, sqrtDegree W (y i)) *
        graphWeight (⊤ : SimpleGraph (Fin 4)) W y :=
      mul_nonneg hp0 (graphWeight_nonneg _ W y)
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ hp1 (graphWeight_nonneg _ W y) (graphWeight_le_one _ W y)
  have hintS : Integrable (fun y : Fin 4 → Ω ↦
      (∏ i, sqrtDegree W (y i)) * graphWeight (⊤ : SimpleGraph (Fin 4)) W y)
      (assignmentMeasure (Fin 4) μ) := integrable_of_bdd hmeasS (C := 1) hbddS
  have hmono : (∫ y : Fin 4 → Ω, 2 * ((∏ i, sqrtDegree W (y i)) *
      k4w W (y 0) (y 1) (y 2) (y 3)) ∂assignmentMeasure (Fin 4) μ) ≤
      ∫ y : Fin 4 → Ω, (degree W (y 0) * degree W (y 1) *
        k4w W (y 0) (y 1) (y 2) (y 3) +
        degree W (y 2) * degree W (y 3) *
          k4w W (y 0) (y 1) (y 2) (y 3)) ∂assignmentMeasure (Fin 4) μ := by
    refine integral_mono ?_ (hint01.add hint23) hamgm
    refine (hintS.const_mul 2).congr (ae_of_all _ fun y ↦ ?_)
    show 2 * ((∏ i, sqrtDegree W (y i)) *
        graphWeight (⊤ : SimpleGraph (Fin 4)) W y) =
      2 * ((∏ i, sqrtDegree W (y i)) * k4w W (y 0) (y 1) (y 2) (y 3))
    rw [graphWeight_top_fin_four]
  rw [integral_add hint01 hint23, ← hswap, integral_const_mul] at hmono
  -- the biased clique density
  have hbias := integral_sqrtDegree_prod 4 (⊤ : SimpleGraph (Fin 4)) W hMpos
  have hcongr : (∫ y : Fin 4 → Ω, (∏ i, sqrtDegree W (y i)) *
      k4w W (y 0) (y 1) (y 2) (y 3) ∂assignmentMeasure (Fin 4) μ) =
      sqrtMean W ^ 4 * cliqueDensity 4 (sqrtGraphon W) := by
    have h1 : (∫ y : Fin 4 → Ω, (∏ i, sqrtDegree W (y i)) *
        k4w W (y 0) (y 1) (y 2) (y 3) ∂assignmentMeasure (Fin 4) μ) =
        ∫ y : Fin 4 → Ω, (∏ i, sqrtDegree W (y i)) *
          graphWeight (⊤ : SimpleGraph (Fin 4)) W y
            ∂assignmentMeasure (Fin 4) μ := by
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      simp only []
      rw [graphWeight_top_fin_four]
    rw [h1]
    exact hbias
  rw [hcongr] at hmono
  have hkey : sqrtMean W ^ 4 * cliqueDensity 4 (sqrtGraphon W) ≤
      homDensity cliqueDist01 W := by
    rw [homDensity_cliqueDist01 W]
    linarith
  -- the scalar step
  set s := cliqueDensity 2 (sqrtGraphon W) with hsdef
  have hm2 : sqrtMean W ^ 2 ≤ p := by rw [hpdef]; exact sq_sqrtMean_le W
  have hms : p ^ 2 ≤ sqrtMean W ^ 2 * s := by
    rw [hpdef, hsdef]; exact sq_le_sq_sqrtMean_mul_cliqueDensity W hMpos
  have hs1 : s ≤ 1 := cliqueDensity_le_one 2 (sqrtGraphon W)
  have hMsq : 0 < sqrtMean W ^ 2 := by positivity
  have hsp : p ≤ s := by nlinarith [hms, hm2, hppos]
  have hspos : (0 : ℝ) < s := by linarith
  have hclique : cliquePoly 4 s ≤ cliqueDensity 4 (sqrtGraphon W) := by
    refine cliqueDensity_ge_cliquePoly (sqrtGraphon W) (r := 4) (by norm_num) ?_
      (le_refl 4)
    rw [← hsdef]
    norm_num
    linarith
  have hpoly : cliquePoly 4 s = s * (2 * s - 1) * (3 * s - 2) := by
    simp only [cliquePoly, Finset.prod_range_succ, Finset.prod_range_zero,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [hpoly] at hclique
  -- assemble
  refine le_trans ?_ hkey
  have hAB : p ^ 4 ≤ sqrtMean W ^ 2 * s * (sqrtMean W ^ 2 * s) := by
    nlinarith [hms, hppos, hMsq, hspos]
  have hs23 : (2 : ℝ) / 3 ≤ s := by linarith
  have hpos : 0 ≤ s * (2 * s - 1) * (3 * s - 2) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hfac : 0 ≤ p ^ 3 * s * ((s - p) * (6 * p * s - 2)) := by
    have h1 : (0 : ℝ) ≤ s - p := by linarith
    have h2 : (0 : ℝ) ≤ 6 * p * s - 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsp (by linarith : (0:ℝ) ≤ 6 * p),
        sq_nonneg (p - 2 / 3), hp, hppos]
    positivity
  have hstep : s ^ 2 * (p ^ 3 * (2 * p - 1) * (3 * p - 2)) ≤
      s ^ 2 * (sqrtMean W ^ 4 * (s * (2 * s - 1) * (3 * s - 2))) := by
    nlinarith [hAB, hpos, hfac, hspos, hppos]
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hfinal : p ^ 3 * (2 * p - 1) * (3 * p - 2) ≤
      sqrtMean W ^ 4 * (s * (2 * s - 1) * (3 * s - 2)) :=
    le_of_mul_le_mul_left hstep hs2
  nlinarith [hfinal, hclique, pow_nonneg hMpos.le 4]

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_134 (z : ℝ) :
    affineProd [0, 1, 1, 1, 2, 3] z = z ^ 3 * (2 * z - 1) * (3 * z - 2) := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₄` on `{0,1,2,3}`, then the leaf `4` on `{0}`, then the leaf `5` on
`{1}`. -/
def equiv134 : Option (Option (Fin 4)) ≃ Fin 6 where
  toFun a := match a with
    | none => 5
    | some none => 4
    | some (some i) => ![0, 1, 2, 3] i
  invFun j := ![some (some 0), some (some 1), some (some 2), some (some 3),
    some none, none] j
  left_inv := by decide
  right_inv := by decide

def iso134 :
    attachVertex (attachVertex (⊤ : SimpleGraph (Fin 4)) {0}) {some 1} ≃g
      cliqueDist01 where
  toEquiv := equiv134
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom134 : IsChromaticPolynomial cliqueDist01
    ((([0, 1, 1, 1, 2, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := cliqueDist01) iso134
    (isClique_singleton _ (some 1))
    (isChromaticPolynomial_attachVertex (isCliqueTop _)
      (isChromaticPolynomial_top 4))
  rw [show (({0} : Finset (Fin 4)).card) = 1 from by decide,
    Finset.card_singleton] at h
  have hpoly :
      ((([0, 1, 1, 1, 2, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((1 : ℕ) : ℝ)) * ∏ i ∈ range 4, ((X : ℝ[X]) - C (i : ℝ))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count134 (k : ℕ) :
    properAssignmentCount cliqueDist01 k =
      (k - 1) * ((k - 1) * k.descFactorial 4) := by
  rw [properAssignmentCount_of_attachIso (H' := cliqueDist01) iso134
      (isClique_singleton _ (some 1)) k,
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0} : Finset (Fin 4)).card) = 1 from by decide, Finset.card_singleton]

theorem num134 : IsChromaticNumber cliqueDist01 4 where
  positive := by rw [count134]; decide
  zero_below k hk := by
    rw [count134, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero]

/-- **Atlas 134 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_134 : Taeyoung.SatisfiesLowerBound cliqueDist01 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 1, 2, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := cliqueDist01) hP chrom134
  have hreq : r = 4 := IsChromaticNumber.unique (H := cliqueDist01) hr num134
  subst hPeq
  subst hreq
  have hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := cliqueDist01_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 2, 3] (by norm_num) hone,
      affineProd_134]
    exact hkey

end Taeyoung.Methods.CliqueDist
