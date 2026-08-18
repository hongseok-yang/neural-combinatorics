import Taeyoung.Methods.Link.WeightedGoodman
import Taeyoung.Foundation

/-!
# Path Sidorenko: `t(P₄,W) ≥ p³`

This file has two halves.

The **structural** half is the rooted factorization

```
t(P₄,W) = ∫ d(x)·(T_W d)(x) dμ(x) = ∫∫ W(x,y)d(x)d(y) dμ(x)dμ(y),
```

obtained by integrating out the two endpoints of the path.  It is what makes
the inequality an inequality about the degree function alone, and it is also
what `notes/whiskering.tex` and `notes/mixed_rooted_triangle_branches.tex` need.

The **analytic** half is `notes/whiskering.tex` Lemma 2.1: three-factor Hölder
applied to the almost-everywhere factorization

```
W(x,y) = (W·d(x)d(y))^{1/3}·(W/d(x))^{1/3}·(W/d(y))^{1/3},
```

whose second and third factors integrate to `μ{d>0} ≤ 1`.

The path is presented with its *second* vertex first, as `1 – 0 – 2 – 3`, so
that coordinate peeling — which always removes coordinate `0` — meets an
interior vertex first and the two leaves collapse to degrees on the way in.
-/

open MeasureTheory Finset

open scoped ENNReal

namespace Taeyoung.Methods.PathSidorenko

open Taeyoung Taeyoung.Methods.Link

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The three-edge path, rooted at an interior vertex -/

/-- The path `1 – 0 – 2 – 3`. -/
def p4Rooted : SimpleGraph (Fin 4) := graphFromEdges 4 [(0, 1), (0, 2), (2, 3)]

instance : DecidableRel p4Rooted.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_p4Rooted :
    p4Rooted.edgeFinset = {s(0, 1), s(0, 2), s(2, 3)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_p4Rooted (W : Graphon Ω μ) (x : Fin 4 → Ω) :
    graphWeight p4Rooted W x = W (x 0) (x 1) * W (x 0) (x 2) * W (x 2) (x 3) := by
  rw [graphWeight, edgeFinset_p4Rooted]
  simp
  ring

lemma graphWeight_p4Rooted_cons (W : Graphon Ω μ) (a0 a1 a2 a3 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight p4Rooted W
        (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))) =
      W a0 a1 * W a0 a2 * W a2 a3 := by
  rw [graphWeight_p4Rooted]
  rfl

/-- **The rooted factorization.**  Integrating out the two endpoints leaves the
degree function paired against the graphon operator applied to it. -/
theorem homDensity_p4Rooted (W : Graphon Ω μ) :
    homDensity p4Rooted W = ∫ a, degree W a * pathOp W a ∂μ := by
  have hm : Measurable (graphWeight p4Rooted W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight p4Rooted W x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 => ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 3 → Ω => graphWeight p4Rooted W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) (fun y => hb _)]
  -- the leaf `a1` integrates to `d a0`
  have hstep : ∀ a1 : Ω,
      (∫ y : Fin 2 → Ω,
          graphWeight p4Rooted W (Fin.cons a0 (Fin.cons a1 y))
        ∂assignmentMeasure (Fin 2) μ) =
        ∫ a2, W a0 a1 * (W a0 a2 * degree W a2) ∂μ := by
    intro a1
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 2 → Ω =>
        graphWeight p4Rooted W (Fin.cons a0 (Fin.cons a1 y)))
      (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
      (fun y => hb _)]
    refine integral_congr_ae (ae_of_all _ fun a2 => ?_)
    simp only []
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 1 → Ω =>
        graphWeight p4Rooted W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      (fun y => hb _)]
    -- the other leaf `a3` integrates to `d a2`
    have hlast : (∫ a3, (∫ y : Fin 0 → Ω,
        graphWeight p4Rooted W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 0) μ) ∂μ) =
        ∫ a3, (W a0 a1 * W a0 a2) * W a2 a3 ∂μ := by
      refine integral_congr_ae (ae_of_all _ fun a3 => ?_)
      simp only []
      rw [show (∫ y : Fin 0 → Ω,
          graphWeight p4Rooted W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
            ∂assignmentMeasure (Fin 0) μ) =
          W a0 a1 * W a0 a2 * W a2 a3 by
        simp [graphWeight_p4Rooted_cons]]
    rw [hlast, integral_const_mul]
    show W a0 a1 * W a0 a2 * degree W a2 = _
    ring
  rw [integral_congr_ae (ae_of_all _ hstep)]
  -- what is left is `d(a0)·(T_W d)(a0)`
  have hpull : (∫ a1, ∫ a2, W a0 a1 * (W a0 a2 * degree W a2) ∂μ ∂μ) =
      degree W a0 * pathOp W a0 := by
    have h2 : ∀ a1 : Ω,
        (∫ a2, W a0 a1 * (W a0 a2 * degree W a2) ∂μ) = W a0 a1 * pathOp W a0 := by
      intro a1
      rw [integral_const_mul]
      rfl
    rw [integral_congr_ae (ae_of_all _ h2), integral_mul_const]
    rfl
  exact hpull

/-! ### The Atlas labelling -/

/-- The relabelling swapping the root with the leaf hanging off it. -/
def p4RootedEquiv : Fin 4 ≃ Fin 4 where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide
  right_inv := by decide

/-- The path on its Atlas labelling `0 – 1 – 2 – 3`. -/
def p4Graph : SimpleGraph (Fin 4) := graphFromEdges 4 [(0, 1), (1, 2), (2, 3)]

instance : DecidableRel p4Graph.Adj := graphFromEdges_decidableAdj _ _

theorem p4Rooted_adj (a b : Fin 4) :
    p4Graph.Adj (p4RootedEquiv a) (p4RootedEquiv b) ↔ p4Rooted.Adj a b := by
  revert a b
  decide

def p4RootedIso : p4Rooted ≃g p4Graph where
  toEquiv := p4RootedEquiv
  map_rel_iff' := by intro a b; exact p4Rooted_adj a b

/-- The factorization, on the Atlas labelling. -/
theorem homDensity_p4Graph (W : Graphon Ω μ) :
    homDensity p4Graph W = ∫ a, degree W a * pathOp W a ∂μ := by
  rw [← homDensity_iso W p4RootedIso, homDensity_p4Rooted]

/-! ### The analytic half: three-factor Hölder

Everything below is in `ℝ≥0∞`.  That is what makes the unbounded factor `W/d`
harmless: it needs no integrability hypothesis, and the convention `0/0 = 0` is
already in force.
-/

section Holder

variable (W : Graphon Ω μ)

/-- The graphon, pushed into `ℝ≥0∞`. -/
noncomputable def edgeE (q : Ω × Ω) : ℝ≥0∞ := ENNReal.ofReal (W q.1 q.2)

/-- The degree function, pushed into `ℝ≥0∞`. -/
noncomputable def degE (x : Ω) : ℝ≥0∞ := ENNReal.ofReal (degree W x)

lemma measurable_edgeE : Measurable (edgeE W) := W.measurable.ennreal_ofReal

lemma measurable_degE : Measurable (degE W) :=
  (measurable_degree W).ennreal_ofReal

lemma measurable_edgeE_row (x : Ω) : Measurable fun y ↦ edgeE W (x, y) :=
  (measurable_edgeE W).comp (measurable_const.prodMk measurable_id)

lemma measurable_edgeE_col (y : Ω) : Measurable fun x ↦ edgeE W (x, y) :=
  (measurable_edgeE W).comp (measurable_id.prodMk measurable_const)

/-- Integrating a row gives the degree. -/
lemma lintegral_row (x : Ω) : ∫⁻ y, edgeE W (x, y) ∂μ = degE W x := by
  have hint : Integrable (fun y ↦ W x y) μ :=
    integrable_of_bdd (measurable_row W.measurable x) (C := 1) fun y ↦ by
      rw [abs_of_nonneg (W.nonneg x y)]; exact W.le_one x y
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun y ↦ W.nonneg x y)).symm

/-- The total mass is the edge density. -/
lemma lintegral_edgeE :
    ∫⁻ q, edgeE W q ∂(μ.prod μ) = ENNReal.ofReal (cliqueDensity 2 W) := by
  rw [lintegral_prod _ (measurable_edgeE W).aemeasurable]
  simp only [lintegral_row W]
  rw [← integral_degree W]
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_degree W)
    (ae_of_all _ fun x ↦ degree_nonneg W x)).symm

/-- The degree-weighted mass is the path density. -/
lemma lintegral_edgeE_mul :
    ∫⁻ q, edgeE W q * degE W q.1 * degE W q.2 ∂(μ.prod μ) =
      ENNReal.ofReal (∫ x, degree W x * pathOp W x ∂μ) := by
  have hmeas : Measurable fun q : Ω × Ω ↦ edgeE W q * degE W q.1 * degE W q.2 :=
    ((measurable_edgeE W).mul ((measurable_degE W).comp measurable_fst)).mul
      ((measurable_degE W).comp measurable_snd)
  rw [lintegral_prod _ hmeas.aemeasurable]
  have hinner : ∀ x : Ω,
      (∫⁻ y, edgeE W (x, y) * degE W x * degE W y ∂μ) =
        degE W x * ENNReal.ofReal (pathOp W x) := by
    intro x
    have hstep : (∫⁻ y, edgeE W (x, y) * degE W x * degE W y ∂μ) =
        degE W x * ∫⁻ y, edgeE W (x, y) * degE W y ∂μ := by
      rw [← lintegral_const_mul _
        ((measurable_edgeE_row W x).mul (measurable_degE W))]
      exact lintegral_congr fun y ↦ by ring
    rw [hstep]
    congr 1
    have hcongr : (∫⁻ y, edgeE W (x, y) * degE W y ∂μ) =
        ∫⁻ y, ENNReal.ofReal (W x y * degree W y) ∂μ :=
      lintegral_congr fun y ↦ (ENNReal.ofReal_mul (W.nonneg x y)).symm
    rw [hcongr]
    have hint : Integrable (fun y ↦ W x y * degree W y) μ :=
      integrable_of_bdd ((measurable_row W.measurable x).mul (measurable_degree W))
        (C := 1) fun y ↦ by
          rw [abs_of_nonneg (mul_nonneg (W.nonneg x y) (degree_nonneg W y))]
          exact mul_le_one₀ (W.le_one x y) (degree_nonneg W y) (degree_le_one W y)
    exact (ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun y ↦ mul_nonneg (W.nonneg x y) (degree_nonneg W y))).symm
  simp only [hinner]
  have hcongr : (∫⁻ x, degE W x * ENNReal.ofReal (pathOp W x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (degree W x * pathOp W x) ∂μ :=
    lintegral_congr fun x ↦ (ENNReal.ofReal_mul (degree_nonneg W x)).symm
  rw [hcongr]
  have hint : Integrable (fun x ↦ degree W x * pathOp W x) μ :=
    integrable_of_bdd ((measurable_degree W).mul (measurable_pathOp W))
      (C := 1) fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (degree_nonneg W x) (pathOp_nonneg W x))]
        exact mul_le_one₀ (degree_le_one W x) (pathOp_nonneg W x)
          (pathOp_le_one W x)
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x ↦ mul_nonneg (degree_nonneg W x) (pathOp_nonneg W x))).symm

/-- `∫∫ W(x,y)/d(x) = μ{d > 0} ≤ 1`. -/
lemma lintegral_edgeE_div_fst :
    ∫⁻ q, edgeE W q / degE W q.1 ∂(μ.prod μ) ≤ 1 := by
  have hmeas : Measurable fun q : Ω × Ω ↦ edgeE W q / degE W q.1 :=
    (measurable_edgeE W).div ((measurable_degE W).comp measurable_fst)
  rw [lintegral_prod _ hmeas.aemeasurable]
  calc (∫⁻ x, ∫⁻ y, edgeE W (x, y) / degE W x ∂μ ∂μ)
      = ∫⁻ x, degE W x / degE W x ∂μ := by
        refine lintegral_congr fun x ↦ ?_
        simp only [div_eq_mul_inv]
        rw [lintegral_mul_const _ (measurable_edgeE_row W x), lintegral_row W]
    _ ≤ ∫⁻ _x : Ω, 1 ∂μ := lintegral_mono fun x ↦ ENNReal.div_self_le_one
    _ = 1 := by simp

/-- `∫∫ W(x,y)/d(y) ≤ 1`, by symmetry of `W`. -/
lemma lintegral_edgeE_div_snd :
    ∫⁻ q, edgeE W q / degE W q.2 ∂(μ.prod μ) ≤ 1 := by
  have hmeas : Measurable fun q : Ω × Ω ↦ edgeE W q / degE W q.2 :=
    (measurable_edgeE W).div ((measurable_degE W).comp measurable_snd)
  rw [lintegral_prod_symm _ hmeas.aemeasurable]
  calc (∫⁻ y, ∫⁻ x, edgeE W (x, y) / degE W y ∂μ ∂μ)
      = ∫⁻ y, degE W y / degE W y ∂μ := by
        refine lintegral_congr fun y ↦ ?_
        simp only [div_eq_mul_inv]
        rw [lintegral_mul_const _ (measurable_edgeE_col W y)]
        congr 1
        rw [← lintegral_row W y]
        exact lintegral_congr fun x ↦ by rw [edgeE, edgeE, W.symm x y]
    _ ≤ ∫⁻ _y : Ω, 1 ∂μ := lintegral_mono fun y ↦ ENNReal.div_self_le_one
    _ = 1 := by simp

/-! ### The null set where the factorization breaks

At a point with `d(x) = 0 < W(x,y)` the first Hölder factor is `0` and the
second `∞`, so their product is `0` and the factorization fails — not only the
identity but the inequality.  That set is null because a vertex of degree zero
has a vanishing row. -/

lemma measurableSet_degE_ne_zero :
    MeasurableSet {q : Ω × Ω | edgeE W q ≠ 0 → degE W q.1 ≠ 0} := by
  have h1 : MeasurableSet {q : Ω × Ω | edgeE W q = 0} :=
    (measurable_edgeE W) (measurableSet_singleton 0)
  have h2 : MeasurableSet {q : Ω × Ω | degE W q.1 = 0} :=
    ((measurable_degE W).comp measurable_fst) (measurableSet_singleton 0)
  have hEq : {q : Ω × Ω | edgeE W q ≠ 0 → degE W q.1 ≠ 0} =
      {q : Ω × Ω | edgeE W q = 0} ∪ {q : Ω × Ω | degE W q.1 = 0}ᶜ := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
    tauto
  rw [hEq]
  exact h1.union h2.compl

lemma ae_degE_ne_zero :
    ∀ᵐ q ∂(μ.prod μ), edgeE W q ≠ 0 → degE W q.1 ≠ 0 := by
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_degE_ne_zero W)]
  filter_upwards with x
  by_cases hx : degE W x = 0
  · have hz : ∫⁻ y, edgeE W (x, y) ∂μ = 0 := by rw [lintegral_row W, hx]
    have hae := (lintegral_eq_zero_iff (measurable_edgeE_row W x)).mp hz
    filter_upwards [hae] with y hy
    exact fun hne ↦ absurd hy hne
  · exact ae_of_all _ fun _ _ ↦ hx

lemma ae_degE_ne_zero_snd :
    ∀ᵐ q ∂(μ.prod μ), edgeE W q ≠ 0 → degE W q.2 ≠ 0 := by
  have h0 : ∀ᵐ q ∂((μ.prod μ).map Prod.swap),
      edgeE W q ≠ 0 → degE W q.1 ≠ 0 := by
    rw [Measure.prod_swap]; exact ae_degE_ne_zero W
  rw [ae_map_iff measurable_swap.aemeasurable
    (measurableSet_degE_ne_zero W)] at h0
  filter_upwards [h0] with q hq
  intro hne
  refine hq ?_
  show ENNReal.ofReal (W q.2 q.1) ≠ 0
  rw [W.symm q.2 q.1]
  exact hne

/-! ### The inequality -/

/-- **Path Sidorenko.**  `notes/whiskering.tex` Lemma 2.1: three-factor Hölder
on `W = (W·d(x)d(y))^{1/3}·(W/d(x))^{1/3}·(W/d(y))^{1/3}`, whose last two
factors integrate to `μ{d>0} ≤ 1`. -/
theorem pow_three_le_pathIntegral :
    cliqueDensity 2 W ^ 3 ≤ ∫ x, degree W x * pathOp W x ∂μ := by
  have hI0 : 0 ≤ ∫ x, degree W x * pathOp W x ∂μ :=
    integral_nonneg fun x ↦ mul_nonneg (degree_nonneg W x) (pathOp_nonneg W x)
  have hp0 : 0 ≤ cliqueDensity 2 W := cliqueDensity_nonneg 2 W
  set g₀ : (Ω × Ω) → ℝ≥0∞ := fun q ↦ edgeE W q * degE W q.1 * degE W q.2 with hg₀
  set g₁ : (Ω × Ω) → ℝ≥0∞ := fun q ↦ edgeE W q / degE W q.1 with hg₁
  set g₂ : (Ω × Ω) → ℝ≥0∞ := fun q ↦ edgeE W q / degE W q.2 with hg₂
  set f : Fin 3 → (Ω × Ω) → ℝ≥0∞ :=
    fun i ↦ if i = 0 then g₀ else if i = 1 then g₁ else g₂ with hfdef
  have hf0 : f 0 = g₀ := rfl
  have hf1 : f 1 = g₁ := rfl
  have hf2 : f 2 = g₂ := rfl
  have hm₀ : AEMeasurable g₀ (μ.prod μ) :=
    (((measurable_edgeE W).mul ((measurable_degE W).comp measurable_fst)).mul
      ((measurable_degE W).comp measurable_snd)).aemeasurable
  have hm₁ : AEMeasurable g₁ (μ.prod μ) :=
    ((measurable_edgeE W).div ((measurable_degE W).comp measurable_fst)).aemeasurable
  have hm₂ : AEMeasurable g₂ (μ.prod μ) :=
    ((measurable_edgeE W).div ((measurable_degE W).comp measurable_snd)).aemeasurable
  have hmeas : ∀ i ∈ (univ : Finset (Fin 3)), AEMeasurable (f i) (μ.prod μ) := by
    intro i _
    rw [hfdef]
    dsimp only
    split_ifs <;> assumption
  have hholder := ENNReal.lintegral_prod_norm_pow_le (μ := μ.prod μ)
    (univ : Finset (Fin 3)) hmeas
    (p := fun _ ↦ (1 / 3 : ℝ)) (by norm_num) (fun i _ ↦ by norm_num)
  -- the left side is the edge density
  have hpt : ∀ᵐ q ∂(μ.prod μ),
      ∏ i : Fin 3, f i q ^ (1 / 3 : ℝ) = edgeE W q := by
    filter_upwards [ae_degE_ne_zero W, ae_degE_ne_zero_snd W] with q h1 h2
    rw [Fin.prod_univ_three, hf0, hf1, hf2]
    simp only [hg₀, hg₁, hg₂]
    rcases eq_or_ne (edgeE W q) 0 with h0 | h0
    · rw [h0, zero_mul, zero_mul, ENNReal.zero_div, ENNReal.zero_div,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 3), zero_mul,
        zero_mul]
    · have hb : degE W q.1 ≠ 0 := h1 h0
      have hc : degE W q.2 ≠ 0 := h2 h0
      have hbt : degE W q.1 ≠ ⊤ := ENNReal.ofReal_ne_top
      have hct : degE W q.2 ≠ ⊤ := ENNReal.ofReal_ne_top
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3),
        ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3)]
      have hprod : edgeE W q * degE W q.1 * degE W q.2 *
          (edgeE W q / degE W q.1) * (edgeE W q / degE W q.2) =
            edgeE W q ^ (3 : ℕ) := by
        simp only [div_eq_mul_inv]
        have hre : edgeE W q * degE W q.1 * degE W q.2 *
            (edgeE W q * (degE W q.1)⁻¹) * (edgeE W q * (degE W q.2)⁻¹) =
              edgeE W q ^ (3 : ℕ) * (degE W q.1 * (degE W q.1)⁻¹) *
                (degE W q.2 * (degE W q.2)⁻¹) := by ring
        rw [hre, ENNReal.mul_inv_cancel hb hbt, ENNReal.mul_inv_cancel hc hct,
          mul_one, mul_one]
      rw [hprod, ← ENNReal.rpow_natCast (edgeE W q) 3, ← ENNReal.rpow_mul]
      norm_num
  have hLHS : (∫⁻ q, ∏ i : Fin 3, f i q ^ (1 / 3 : ℝ) ∂(μ.prod μ)) =
      ENNReal.ofReal (cliqueDensity 2 W) := by
    rw [lintegral_congr_ae hpt, lintegral_edgeE]
  -- the right side collapses to the path density
  have hone₁ : (∫⁻ q, f 1 q ∂(μ.prod μ)) ^ (1 / 3 : ℝ) ≤ 1 := by
    rw [hf1, hg₁]
    calc (∫⁻ q, edgeE W q / degE W q.1 ∂(μ.prod μ)) ^ (1 / 3 : ℝ)
        ≤ (1 : ℝ≥0∞) ^ (1 / 3 : ℝ) :=
          ENNReal.rpow_le_rpow (lintegral_edgeE_div_fst W) (by norm_num)
      _ = 1 := ENNReal.one_rpow _
  have hone₂ : (∫⁻ q, f 2 q ∂(μ.prod μ)) ^ (1 / 3 : ℝ) ≤ 1 := by
    rw [hf2, hg₂]
    calc (∫⁻ q, edgeE W q / degE W q.2 ∂(μ.prod μ)) ^ (1 / 3 : ℝ)
        ≤ (1 : ℝ≥0∞) ^ (1 / 3 : ℝ) :=
          ENNReal.rpow_le_rpow (lintegral_edgeE_div_snd W) (by norm_num)
      _ = 1 := ENNReal.one_rpow _
  have hRHS : (∏ i : Fin 3, (∫⁻ q, f i q ∂(μ.prod μ)) ^ (1 / 3 : ℝ)) ≤
      (ENNReal.ofReal (∫ x, degree W x * pathOp W x ∂μ)) ^ (1 / 3 : ℝ) := by
    rw [Fin.prod_univ_three]
    calc (∫⁻ q, f 0 q ∂(μ.prod μ)) ^ (1 / 3 : ℝ) *
          (∫⁻ q, f 1 q ∂(μ.prod μ)) ^ (1 / 3 : ℝ) *
          (∫⁻ q, f 2 q ∂(μ.prod μ)) ^ (1 / 3 : ℝ)
        ≤ (∫⁻ q, f 0 q ∂(μ.prod μ)) ^ (1 / 3 : ℝ) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' le_rfl hone₁) hone₂
      _ = (∫⁻ q, f 0 q ∂(μ.prod μ)) ^ (1 / 3 : ℝ) := by rw [mul_one, mul_one]
      _ = _ := by rw [hf0, hg₀, lintegral_edgeE_mul]
  have hkey : ENNReal.ofReal (cliqueDensity 2 W) ≤
      (ENNReal.ofReal (∫ x, degree W x * pathOp W x ∂μ)) ^ (1 / 3 : ℝ) := by
    rw [← hLHS]
    exact le_trans hholder hRHS
  -- undo the cube root
  have hcube : ENNReal.ofReal (cliqueDensity 2 W) ^ (3 : ℝ) ≤
      ENNReal.ofReal (∫ x, degree W x * pathOp W x ∂μ) := by
    calc ENNReal.ofReal (cliqueDensity 2 W) ^ (3 : ℝ)
        ≤ ((ENNReal.ofReal (∫ x, degree W x * pathOp W x ∂μ)) ^ (1 / 3 : ℝ)) ^ (3 : ℝ) :=
          ENNReal.rpow_le_rpow hkey (by norm_num)
      _ = _ := by rw [← ENNReal.rpow_mul]; norm_num
  have hnat : ENNReal.ofReal (cliqueDensity 2 W ^ 3) ≤
      ENNReal.ofReal (∫ x, degree W x * pathOp W x ∂μ) := by
    rw [ENNReal.ofReal_pow hp0]
    have h3 : ENNReal.ofReal (cliqueDensity 2 W) ^ (3 : ℕ) =
        ENNReal.ofReal (cliqueDensity 2 W) ^ (3 : ℝ) := by
      rw [← ENNReal.rpow_natCast (ENNReal.ofReal (cliqueDensity 2 W)) 3]
      norm_num
    rw [h3]
    exact hcube
  exact (ENNReal.ofReal_le_ofReal_iff hI0).mp hnat

end Holder

end Taeyoung.Methods.PathSidorenko
