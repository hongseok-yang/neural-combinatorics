import Taeyoung.Methods.CliqueDist.Rows

/-!
# Atlas 113: the diamond with one leaf in each automorphism orbit

`notes/diamond_orbit_balanced_leaves.tex` at `k = 1`.  The diamond
`D = K₄ - e` has two vertex orbits of size two — the endpoints `0,1` of the
shared triangle edge, and the two page vertices `2,3` — and the row attaches one
pendant leaf inside each.  Peeling both leaves gives

```
t(H,W) = ∫_{Ω⁴} F(x)·d(x₀)d(x₂) dμ⁴,      F = the diamond weight.
```

This is the same argument as `Methods/CliqueDist/Rows.lean` with `K₄` replaced
by the diamond, and it reuses every piece of it:

* the orbit average is again **one** exchange — swapping `0↔1` and `2↔3`
  simultaneously is an automorphism of `D` carrying the leaves from `{0,2}` to
  `{1,3}` — so `d₀d₂ + d₁d₃ ≥ 2√(d₀d₁d₂d₃)` is the two-term AM–GM;
* the `√d`-biased measure and `M² ≤ p`, `M²·t(K₂,W_ν) ≥ p²` are `Bias.lean`;
* the core input is the *already verified* `BaseCone.base_diamond`,
  `t(D,V) ≥ z(2z-1)²`, rather than a clique bound;
* the note's Lemma 3.2 (`A_D(s)/s²` increasing, by differentiation) becomes the
  `ring` identity `p(2s-1)² - s(2p-1)² = (s-p)(4ps-1) ≥ 0`.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.CliqueDist

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PureChordal Taeyoung.Methods.PawCone
  Taeyoung.Methods.BaseCone Taeyoung.Methods.ForestCone

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The diamond weight -/

lemma edgeFinset_diamond :
    diamond.edgeFinset = {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

/-- The diamond weight as a function of four explicit coordinates. -/
noncomputable def dmw (W : Graphon Ω μ) (a0 a1 a2 a3 : Ω) : ℝ :=
  W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3

lemma graphWeight_diamond (W : Graphon Ω μ) (x : Fin 4 → Ω) :
    graphWeight diamond W x = dmw W (x 0) (x 1) (x 2) (x 3) := by
  rw [graphWeight, edgeFinset_diamond, dmw]
  simp
  ring

lemma dmw_nonneg (W : Graphon Ω μ) (a0 a1 a2 a3 : Ω) : 0 ≤ dmw W a0 a1 a2 a3 := by
  simp only [dmw]
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_ <;>
    exact W.nonneg _ _

lemma dmw_le_one (W : Graphon Ω μ) (a0 a1 a2 a3 : Ω) : dmw W a0 a1 a2 a3 ≤ 1 := by
  simp only [dmw]
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀
    (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)) (W.nonneg _ _) (W.le_one _ _))
    (W.nonneg _ _) (W.le_one _ _)

private lemma measurable_dmw {n : ℕ} (W : Graphon Ω μ) (i j k l : Fin n) :
    Measurable fun y : Fin n → Ω ↦ dmw W (y i) (y j) (y k) (y l) := by
  simp only [dmw]
  exact ((((measurable_pair W i j).mul (measurable_pair W i k)).mul
    (measurable_pair W i l)).mul (measurable_pair W j k)).mul
    (measurable_pair W j l)

/-! ### The two graphs -/

/-- The diamond `0,1` – `2,3`; leaf `4` on `0` and leaf `5` on `2`. -/
def diamondLeaf02 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (0, 4), (2, 5)]

instance : DecidableRel diamondLeaf02.Adj := graphFromEdges_decidableAdj _ _

/-- The same after the orbit exchange `0↔1`, `2↔3`. -/
def diamondLeaf13 : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4), (3, 5)]

instance : DecidableRel diamondLeaf13.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_diamondLeaf02 :
    diamondLeaf02.edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(0, 4), s(2, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma edgeFinset_diamondLeaf13 :
    diamondLeaf13.edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(1, 4), s(3, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_diamondLeaf02 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight diamondLeaf02 W x =
      dmw W (x 0) (x 1) (x 2) (x 3) * (W (x 0) (x 4) * W (x 2) (x 5)) := by
  rw [graphWeight, edgeFinset_diamondLeaf02, dmw]
  simp
  ring

lemma graphWeight_diamondLeaf13 (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight diamondLeaf13 W x =
      dmw W (x 0) (x 1) (x 2) (x 3) * (W (x 1) (x 4) * W (x 3) (x 5)) := by
  rw [graphWeight, edgeFinset_diamondLeaf13, dmw]
  simp
  ring

/-! ### The two peelings -/

section Peel

variable (W : Graphon Ω μ)

private lemma bdd_dleaf (i j : Fin 6) (x : Fin 6 → Ω) :
    |dmw W (x 0) (x 1) (x 2) (x 3) * (W (x i) (x 4) * W (x j) (x 5))| ≤ 1 := by
  have h0 : 0 ≤ dmw W (x 0) (x 1) (x 2) (x 3) * (W (x i) (x 4) * W (x j) (x 5)) :=
    mul_nonneg (dmw_nonneg W _ _ _ _)
      (mul_nonneg (W.nonneg _ _) (W.nonneg _ _))
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (dmw_le_one W _ _ _ _)
    (mul_nonneg (W.nonneg _ _) (W.nonneg _ _))
    (mul_le_one₀ (W.le_one _ _) (W.nonneg _ _) (W.le_one _ _))

private lemma meas_dleaf (i j : Fin 6) :
    Measurable fun y : Fin 6 → Ω ↦
      dmw W (y 0) (y 1) (y 2) (y 3) * (W (y i) (y 4) * W (y j) (y 5)) :=
  (measurable_dmw W 0 1 2 3).mul
    ((measurable_pair W i 4).mul (measurable_pair W j 5))

private lemma bdd_dweighted (i j : Fin 4) (y : Fin 4 → Ω) :
    |degree W (y i) * degree W (y j) * dmw W (y 0) (y 1) (y 2) (y 3)| ≤ 1 := by
  have h0 : 0 ≤ degree W (y i) * degree W (y j) * dmw W (y 0) (y 1) (y 2) (y 3) :=
    mul_nonneg (mul_nonneg (degree_nonneg W _) (degree_nonneg W _))
      (dmw_nonneg W _ _ _ _)
  rw [abs_of_nonneg h0]
  exact mul_le_one₀ (mul_le_one₀ (degree_le_one W _) (degree_nonneg W _)
    (degree_le_one W _)) (dmw_nonneg W _ _ _ _) (dmw_le_one W _ _ _ _)

private lemma meas_dweighted (i j : Fin 4) :
    Measurable fun y : Fin 4 → Ω ↦
      degree W (y i) * degree W (y j) * dmw W (y 0) (y 1) (y 2) (y 3) :=
  (((measurable_degree W).comp (measurable_pi_apply i)).mul
    ((measurable_degree W).comp (measurable_pi_apply j))).mul
    (measurable_dmw W 0 1 2 3)

theorem homDensity_diamondLeaf02 :
    homDensity diamondLeaf02 W =
      ∫ y : Fin 4 → Ω, degree W (y 0) * degree W (y 2) *
        dmw W (y 0) (y 1) (y 2) (y 3) ∂assignmentMeasure (Fin 4) μ := by
  rw [homDensity, integral_congr_ae (ae_of_all _ (graphWeight_diamondLeaf02 W)),
    integral_assignment_fin_six
      (g := fun a0 a1 a2 a3 a4 a5 ↦ dmw W a0 a1 a2 a3 * (W a0 a4 * W a2 a5))
      (meas_dleaf W 0 2) (bdd_dleaf W 0 2),
    integral_assignment_fin_four
      (g := fun a0 a1 a2 a3 ↦ degree W a0 * degree W a2 * dmw W a0 a1 a2 a3)
      (meas_dweighted W 0 2) (bdd_dweighted W 0 2)]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
  simp only []
  have h5 : ∀ a4 : Ω,
      (∫ a5, dmw W a0 a1 a2 a3 * (W a0 a4 * W a2 a5) ∂μ) =
        (dmw W a0 a1 a2 a3 * W a0 a4) * degree W a2 := by
    intro a4
    have hre : ∀ a5 : Ω, dmw W a0 a1 a2 a3 * (W a0 a4 * W a2 a5) =
        (dmw W a0 a1 a2 a3 * W a0 a4) * W a2 a5 := fun a5 ↦ by ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
    rfl
  rw [integral_congr_ae (ae_of_all _ h5)]
  have h4 : ∀ a4 : Ω, (dmw W a0 a1 a2 a3 * W a0 a4) * degree W a2 =
      (dmw W a0 a1 a2 a3 * degree W a2) * W a0 a4 := fun a4 ↦ by ring
  rw [integral_congr_ae (ae_of_all _ h4), integral_const_mul]
  show dmw W a0 a1 a2 a3 * degree W a2 * degree W a0 =
    degree W a0 * degree W a2 * dmw W a0 a1 a2 a3
  ring

theorem homDensity_diamondLeaf13 :
    homDensity diamondLeaf13 W =
      ∫ y : Fin 4 → Ω, degree W (y 1) * degree W (y 3) *
        dmw W (y 0) (y 1) (y 2) (y 3) ∂assignmentMeasure (Fin 4) μ := by
  rw [homDensity, integral_congr_ae (ae_of_all _ (graphWeight_diamondLeaf13 W)),
    integral_assignment_fin_six
      (g := fun a0 a1 a2 a3 a4 a5 ↦ dmw W a0 a1 a2 a3 * (W a1 a4 * W a3 a5))
      (meas_dleaf W 1 3) (bdd_dleaf W 1 3),
    integral_assignment_fin_four
      (g := fun a0 a1 a2 a3 ↦ degree W a1 * degree W a3 * dmw W a0 a1 a2 a3)
      (meas_dweighted W 1 3) (bdd_dweighted W 1 3)]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a1 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
  simp only []
  refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
  simp only []
  have h5 : ∀ a4 : Ω,
      (∫ a5, dmw W a0 a1 a2 a3 * (W a1 a4 * W a3 a5) ∂μ) =
        (dmw W a0 a1 a2 a3 * W a1 a4) * degree W a3 := by
    intro a4
    have hre : ∀ a5 : Ω, dmw W a0 a1 a2 a3 * (W a1 a4 * W a3 a5) =
        (dmw W a0 a1 a2 a3 * W a1 a4) * W a3 a5 := fun a5 ↦ by ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
    rfl
  rw [integral_congr_ae (ae_of_all _ h5)]
  have h4 : ∀ a4 : Ω, (dmw W a0 a1 a2 a3 * W a1 a4) * degree W a3 =
      (dmw W a0 a1 a2 a3 * degree W a3) * W a1 a4 := fun a4 ↦ by ring
  rw [integral_congr_ae (ae_of_all _ h4), integral_const_mul]
  show dmw W a0 a1 a2 a3 * degree W a3 * degree W a1 =
    degree W a1 * degree W a3 * dmw W a0 a1 a2 a3
  ring

end Peel

/-- The orbit exchange `0↔1`, `2↔3`. -/
def isoOrbit : diamondLeaf02 ≃g diamondLeaf13 where
  toEquiv :=
    { toFun := ![1, 0, 3, 2, 4, 5]
      invFun := ![1, 0, 3, 2, 4, 5]
      left_inv := by decide
      right_inv := by decide }
  map_rel_iff' := by
    intro a b
    revert a b
    decide

/-! ### The bound -/

/-- **Atlas 113 dominates its target.** -/
theorem diamondLeaf02_bound {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 3 * (2 * cliqueDensity 2 W - 1) ^ 2 ≤
      homDensity diamondLeaf02 W := by
  set p := cliqueDensity 2 W with hpdef
  have hppos : (0 : ℝ) < p := by linarith
  have hMpos : 0 < sqrtMean W := sqrtMean_pos W (by rw [← hpdef]; exact hppos)
  haveI := isProbabilityMeasure_sqrtMeasure W hMpos
  have hswap : (∫ y : Fin 4 → Ω, degree W (y 0) * degree W (y 2) *
      dmw W (y 0) (y 1) (y 2) (y 3) ∂assignmentMeasure (Fin 4) μ) =
      ∫ y : Fin 4 → Ω, degree W (y 1) * degree W (y 3) *
        dmw W (y 0) (y 1) (y 2) (y 3) ∂assignmentMeasure (Fin 4) μ := by
    rw [← homDensity_diamondLeaf02 W, ← homDensity_diamondLeaf13 W]
    exact homDensity_iso W isoOrbit
  have hamgm : ∀ y : Fin 4 → Ω,
      2 * ((∏ i, sqrtDegree W (y i)) * dmw W (y 0) (y 1) (y 2) (y 3)) ≤
        degree W (y 0) * degree W (y 2) * dmw W (y 0) (y 1) (y 2) (y 3) +
          degree W (y 1) * degree W (y 3) * dmw W (y 0) (y 1) (y 2) (y 3) := by
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
        degree W (y 0) * degree W (y 2) + degree W (y 1) * degree W (y 3) := by
      nlinarith [sq_nonneg (sqrtDegree W (y 0) * sqrtDegree W (y 2) -
        sqrtDegree W (y 1) * sqrtDegree W (y 3)), e0, e1, e2, e3]
    rw [hprod]
    nlinarith [hstep, dmw_nonneg W (y 0) (y 1) (y 2) (y 3)]
  have hint02 : Integrable (fun y : Fin 4 → Ω ↦ degree W (y 0) * degree W (y 2) *
      dmw W (y 0) (y 1) (y 2) (y 3)) (assignmentMeasure (Fin 4) μ) :=
    integrable_of_bdd (meas_dweighted W 0 2) (C := 1) (bdd_dweighted W 0 2)
  have hint13 : Integrable (fun y : Fin 4 → Ω ↦ degree W (y 1) * degree W (y 3) *
      dmw W (y 0) (y 1) (y 2) (y 3)) (assignmentMeasure (Fin 4) μ) :=
    integrable_of_bdd (meas_dweighted W 1 3) (C := 1) (bdd_dweighted W 1 3)
  have hmeasS : Measurable fun y : Fin 4 → Ω ↦
      (∏ i, sqrtDegree W (y i)) * graphWeight diamond W y := by
    refine Measurable.mul ?_ (measurable_graphWeight _ W)
    exact Finset.measurable_prod _ fun i _ ↦
      (measurable_sqrtDegree W).comp (measurable_pi_apply i)
  have hbddS : ∀ y : Fin 4 → Ω,
      |(∏ i, sqrtDegree W (y i)) * graphWeight diamond W y| ≤ 1 := by
    intro y
    have hp0 : 0 ≤ ∏ i, sqrtDegree W (y i) :=
      Finset.prod_nonneg fun i _ ↦ sqrtDegree_nonneg W (y i)
    have hp1 : (∏ i, sqrtDegree W (y i)) ≤ 1 :=
      Finset.prod_le_one (fun i _ ↦ sqrtDegree_nonneg W (y i))
        fun i _ ↦ sqrtDegree_le_one W (y i)
    have h0 : 0 ≤ (∏ i, sqrtDegree W (y i)) * graphWeight diamond W y :=
      mul_nonneg hp0 (graphWeight_nonneg _ W y)
    rw [abs_of_nonneg h0]
    exact mul_le_one₀ hp1 (graphWeight_nonneg _ W y) (graphWeight_le_one _ W y)
  have hintS : Integrable (fun y : Fin 4 → Ω ↦
      (∏ i, sqrtDegree W (y i)) * graphWeight diamond W y)
      (assignmentMeasure (Fin 4) μ) := integrable_of_bdd hmeasS (C := 1) hbddS
  have hmono : (∫ y : Fin 4 → Ω, 2 * ((∏ i, sqrtDegree W (y i)) *
      dmw W (y 0) (y 1) (y 2) (y 3)) ∂assignmentMeasure (Fin 4) μ) ≤
      ∫ y : Fin 4 → Ω, (degree W (y 0) * degree W (y 2) *
        dmw W (y 0) (y 1) (y 2) (y 3) +
        degree W (y 1) * degree W (y 3) *
          dmw W (y 0) (y 1) (y 2) (y 3)) ∂assignmentMeasure (Fin 4) μ := by
    refine integral_mono ?_ (hint02.add hint13) hamgm
    refine (hintS.const_mul 2).congr (ae_of_all _ fun y ↦ ?_)
    show 2 * ((∏ i, sqrtDegree W (y i)) * graphWeight diamond W y) =
      2 * ((∏ i, sqrtDegree W (y i)) * dmw W (y 0) (y 1) (y 2) (y 3))
    rw [graphWeight_diamond]
  rw [integral_add hint02 hint13, ← hswap, integral_const_mul] at hmono
  have hbias := integral_sqrtDegree_prod 4 diamond W hMpos
  have hcongr : (∫ y : Fin 4 → Ω, (∏ i, sqrtDegree W (y i)) *
      dmw W (y 0) (y 1) (y 2) (y 3) ∂assignmentMeasure (Fin 4) μ) =
      sqrtMean W ^ 4 * homDensity diamond (sqrtGraphon W) := by
    have h1 : (∫ y : Fin 4 → Ω, (∏ i, sqrtDegree W (y i)) *
        dmw W (y 0) (y 1) (y 2) (y 3) ∂assignmentMeasure (Fin 4) μ) =
        ∫ y : Fin 4 → Ω, (∏ i, sqrtDegree W (y i)) *
          graphWeight diamond W y ∂assignmentMeasure (Fin 4) μ := by
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      simp only []
      rw [graphWeight_diamond]
    rw [h1]
    exact hbias
  rw [hcongr] at hmono
  have hkey : sqrtMean W ^ 4 * homDensity diamond (sqrtGraphon W) ≤
      homDensity diamondLeaf02 W := by
    rw [homDensity_diamondLeaf02 W]
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
  have hs12 : (1 : ℝ) / 2 ≤ s := by linarith
  have hdia : s * (2 * s - 1) ^ 2 ≤ homDensity diamond (sqrtGraphon W) := by
    have h := base_diamond (sqrtGraphon W) (by rw [← hsdef]; norm_num; linarith)
    rwa [affineProd_diamond, ← hsdef] at h
  refine le_trans ?_ hkey
  have hAB : p ^ 4 ≤ sqrtMean W ^ 2 * s * (sqrtMean W ^ 2 * s) := by
    nlinarith [hms, hppos, hMsq, hspos]
  have hpos : 0 ≤ s * (2 * s - 1) ^ 2 := by positivity
  have hfac : 0 ≤ p ^ 3 * s * ((s - p) * (4 * p * s - 1)) := by
    have h1 : (0 : ℝ) ≤ s - p := by linarith
    have h2 : (0 : ℝ) ≤ 4 * p * s - 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hsp (by linarith : (0:ℝ) ≤ 4 * p),
        sq_nonneg (p - 1 / 2), hp, hppos]
    positivity
  have hstep : s ^ 2 * (p ^ 3 * (2 * p - 1) ^ 2) ≤
      s ^ 2 * (sqrtMean W ^ 4 * (s * (2 * s - 1) ^ 2)) := by
    nlinarith [hAB, hpos, hfac, hspos, hppos]
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hfinal : p ^ 3 * (2 * p - 1) ^ 2 ≤
      sqrtMean W ^ 4 * (s * (2 * s - 1) ^ 2) :=
    le_of_mul_le_mul_left hstep hs2
  nlinarith [hfinal, hdia, pow_nonneg hMpos.le 4]

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_113 (z : ℝ) :
    affineProd [0, 1, 1, 1, 2, 2] z = z ^ 3 * (2 * z - 1) ^ 2 := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₃` on `{0,1,2}`, the fourth diamond vertex on the edge `{0,1}`, then the
leaf on `0` and the leaf on `2`. -/
def iso113 :
    attachVertex (attachVertex
      (attachVertex (⊤ : SimpleGraph (Fin 3)) {0, 1}) {some 0})
      {some (some 2)} ≃g diamondLeaf02 where
  toEquiv := equivTriple
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom113 : IsChromaticPolynomial diamondLeaf02
    ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := diamondLeaf02) iso113
    (isClique_singleton _ (some (some 2)))
    (isChromaticPolynomial_attachVertex (isClique_singleton _ (some 0))
      (isChromaticPolynomial_attachVertex (isCliqueTop _)
        (isChromaticPolynomial_top 3)))
  rw [show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    Finset.card_singleton, Finset.card_singleton] at h
  have hpoly :
      ((([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) =
      (X - C ((1 : ℕ) : ℝ)) * ((X - C ((1 : ℕ) : ℝ)) *
        ((X - C ((2 : ℕ) : ℝ)) * ∏ i ∈ range 3, ((X : ℝ[X]) - C (i : ℝ)))) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, map_zero, sub_zero, one_mul, mul_one]
    ring
  rw [hpoly]
  exact h

theorem count113 (k : ℕ) :
    properAssignmentCount diamondLeaf02 k =
      (k - 1) * ((k - 1) * ((k - 2) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso (H' := diamondLeaf02) iso113
      (isClique_singleton _ (some (some 2))) k,
    properAssignmentCount_attachVertex (isClique_singleton _ (some 0)),
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0, 1} : Finset (Fin 3)).card) = 2 from by decide,
    Finset.card_singleton, Finset.card_singleton]

theorem num113 : IsChromaticNumber diamondLeaf02 3 where
  positive := by rw [count113]; decide
  zero_below k hk := by
    rw [count113, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-- **Atlas 113 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_113 : Taeyoung.SatisfiesLowerBound diamondLeaf02 := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 1, 2, 2] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := diamondLeaf02) hP chrom113
  have hreq : r = 3 := IsChromaticNumber.unique (H := diamondLeaf02) hr num113
  subst hPeq
  subst hreq
  have hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := diamondLeaf02_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 2, 2] (by norm_num) hone,
      affineProd_113]
    exact hkey

end Taeyoung.Methods.CliqueDist
