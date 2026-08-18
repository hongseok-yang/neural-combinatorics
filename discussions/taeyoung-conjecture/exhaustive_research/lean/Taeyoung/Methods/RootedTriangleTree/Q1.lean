import Taeyoung.Methods.RootedTriangleTree.L3

/-!
# `Q₁`: a triangle with one two-edge tail (Atlas 36)

The last member of the rooted triangle–tree family, and the one that does *not*
factor as `∫ dʳ·τ`.  Conditioning on the root gives

```
t(Q₁, W) = ∫ τ(x) · A(x) dμ(x),      A = T_W d = pathOp
```

The note bounds this with a piecewise-convex Jensen argument.  We avoid the
piecewise function entirely: the pointwise Goodman bound `τ ≥ 2A - p` and
`A ≥ 0` give

```
∫ τ·A  ≥  2∫A² - p∫A  =  2M₂² - p·M₂ + (∫A² - M₂²) ≥ 2M₂² - p·M₂,
```

and `m ↦ 2m² - pm` is increasing beyond `m = p²` when `p ≥ 1/2`, so the bound
descends to `2p⁴ - p³ = p³(2p-1)`.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedTriangleTree

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.Chromatic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### `∫ A = M₂`, and Jensen for `A` -/

/-- The mean of the two-edge path density is the second degree moment. -/
theorem integral_pathOp (W : Graphon Ω μ) :
    ∫ x, pathOp W x ∂μ = moment W 2 := by
  have hker : Measurable (Function.uncurry fun x y ↦ W x y * degree W y) :=
    W.measurable.mul ((measurable_degree W).comp measurable_snd)
  have hbdd : ∀ x y, |W x y * degree W y| ≤ 1 := by
    intro x y
    rw [abs_of_nonneg (mul_nonneg (W.nonneg x y) (degree_nonneg W y))]
    exact mul_le_one₀ (W.le_one x y) (degree_nonneg W y) (degree_le_one W y)
  have hint : Integrable (Function.uncurry fun x y ↦ W x y * degree W y)
      (μ.prod μ) := integrable_uncurry_of_bdd hker hbdd
  show (∫ x, ∫ y, W x y * degree W y ∂μ ∂μ) = moment W 2
  rw [integral_integral_swap hint]
  have hinner : ∀ y : Ω, (∫ x, W x y * degree W y ∂μ) = degree W y ^ 2 := by
    intro y
    have hre : (fun x ↦ W x y * degree W y) = fun x ↦ degree W y * W x y := by
      funext x; ring
    rw [hre, integral_const_mul]
    have hsym : (∫ x, W x y ∂μ) = degree W y :=
      integral_congr_ae (ae_of_all _ fun x ↦ W.symm x y)
    rw [hsym, sq]
  rw [integral_congr_ae (ae_of_all _ hinner)]
  rfl

/-- `∫ A² ≥ (∫ A)²`. -/
theorem sq_integral_pathOp_le (W : Graphon Ω μ) :
    (∫ x, pathOp W x ∂μ) ^ 2 ≤ ∫ x, pathOp W x ^ 2 ∂μ := by
  have hint : Integrable (pathOp W) μ :=
    integrable_of_bdd (measurable_pathOp W) (C := 1) fun x ↦ by
      rw [abs_of_nonneg (pathOp_nonneg W x)]
      exact pathOp_le_one W x
  have hint2 : Integrable (fun x ↦ pathOp W x ^ 2) μ :=
    integrable_of_bdd ((measurable_pathOp W).pow_const 2) (C := 1) fun x ↦ by
      rw [abs_of_nonneg (pow_nonneg (pathOp_nonneg W x) 2)]
      exact pow_le_one₀ (pathOp_nonneg W x) (pathOp_le_one W x)
  exact ConvexOn.map_integral_le (μ := μ) (s := Set.Ici 0)
    (g := fun t : ℝ ↦ t ^ 2) (f := pathOp W)
    (convexOn_pow (𝕜 := ℝ) 2) ((continuous_pow 2).continuousOn) isClosed_Ici
    (ae_of_all _ fun x ↦ pathOp_nonneg W x) hint hint2

/-! ### The tail bound -/

/-- **The two-edge-tail bound.**  No piecewise convexity is needed. -/
theorem tail_bound (W : Graphon Ω μ)
    (hp : (1 : ℝ) / 2 ≤ cliqueDensity 2 W) :
    cliqueDensity 2 W ^ 3 * (2 * cliqueDensity 2 W - 1) ≤
      ∫ x, rootedTriangle W x * pathOp W x ∂μ := by
  set p := cliqueDensity 2 W with hpdef
  -- integrability
  have hiA : Integrable (pathOp W) μ :=
    integrable_of_bdd (measurable_pathOp W) (C := 1) fun x ↦ by
      rw [abs_of_nonneg (pathOp_nonneg W x)]; exact pathOp_le_one W x
  have hiA2 : Integrable (fun x ↦ pathOp W x ^ 2) μ :=
    integrable_of_bdd ((measurable_pathOp W).pow_const 2) (C := 1) fun x ↦ by
      rw [abs_of_nonneg (pow_nonneg (pathOp_nonneg W x) 2)]
      exact pow_le_one₀ (pathOp_nonneg W x) (pathOp_le_one W x)
  have hitA : Integrable (fun x ↦ rootedTriangle W x * pathOp W x) μ :=
    integrable_of_bdd
      ((measurable_rootedTriangle W).mul (measurable_pathOp W)) (C := 1)
      fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (rootedTriangle_nonneg W x)
          (pathOp_nonneg W x))]
        exact mul_le_one₀ (rootedTriangle_le_one W x) (pathOp_nonneg W x)
          (pathOp_le_one W x)
  have hilin : Integrable (fun x ↦ 2 * pathOp W x ^ 2 - p * pathOp W x) μ :=
    (hiA2.const_mul 2).sub (hiA.const_mul p)
  -- pointwise: `(2A - p)·A ≤ τ·A`
  have hpt : ∀ x, 2 * pathOp W x ^ 2 - p * pathOp W x ≤
      rootedTriangle W x * pathOp W x := by
    intro x
    have h := rootedTriangle_ge W x
    have hA := pathOp_nonneg W x
    nlinarith [h, hA]
  have hmono : (∫ x, (2 * pathOp W x ^ 2 - p * pathOp W x) ∂μ) ≤
      ∫ x, rootedTriangle W x * pathOp W x ∂μ :=
    integral_mono hilin hitA hpt
  -- evaluate the left side
  have hsplit : (∫ x, (2 * pathOp W x ^ 2 - p * pathOp W x) ∂μ) =
      2 * (∫ x, pathOp W x ^ 2 ∂μ) - p * moment W 2 := by
    have e := integral_sub (hiA2.const_mul 2) (hiA.const_mul p)
    rw [e, integral_const_mul, integral_const_mul, integral_pathOp]
  rw [hsplit] at hmono
  -- and bound it below
  have hAsq : (moment W 2) ^ 2 ≤ ∫ x, pathOp W x ^ 2 ∂μ := by
    have := sq_integral_pathOp_le W
    rwa [integral_pathOp] at this
  have hM2 : p ^ 2 ≤ moment W 2 := pow_le_moment W 2
  have hM2nn : (0 : ℝ) ≤ moment W 2 := le_trans (by positivity) hM2
  have hkey : 0 ≤ (moment W 2 - p ^ 2) * (2 * (moment W 2 + p ^ 2) - p) := by
    refine mul_nonneg (by linarith) ?_
    nlinarith [hM2, hp]
  nlinarith [hmono, hAsq, hkey]


/-! ### The rooted `Q₁`, with the root at coordinate `0` -/

/-- Atlas 36: triangle `{1,2,3}` with the tail `3–4–0`. -/
def q1Graph : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 4), (1, 2), (1, 3), (2, 3), (3, 4)]

instance : DecidableRel q1Graph.Adj := graphFromEdges_decidableAdj _ _

/-- The same graph with the root at coordinate `0`: triangle `{0,1,2}`, tail
`0–3–4`. -/
def q1Rooted : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]

instance : DecidableRel q1Rooted.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_q1Rooted :
    q1Rooted.edgeFinset = {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(3, 4)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_q1Rooted (W : Graphon Ω μ) (x : Fin 5 → Ω) :
    graphWeight q1Rooted W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 0) (x 3) * W (x 1) (x 2) *
        W (x 3) (x 4) := by
  rw [graphWeight, edgeFinset_q1Rooted]
  simp
  ring

lemma graphWeight_q1Rooted_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight q1Rooted W
        (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y))))) =
      W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a3 a4 := by
  rw [graphWeight_q1Rooted]
  rfl

/-- Conditioning on the root: the tail gives `A = T_W d`, the triangle `τ`. -/
theorem homDensity_q1Rooted (W : Graphon Ω μ) :
    homDensity q1Rooted W = ∫ a, rootedTriangle W a * pathOp W a ∂μ := by
  have hm : Measurable (graphWeight q1Rooted W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight q1Rooted W x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 => ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω => graphWeight q1Rooted W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) (fun y => hb _)]
  have hstep : ∀ a1 : Ω,
      (∫ y : Fin 3 → Ω, graphWeight q1Rooted W (Fin.cons a0 (Fin.cons a1 y))
        ∂assignmentMeasure (Fin 3) μ) =
        ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 * pathOp W a0 ∂μ := by
    intro a1
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω => graphWeight q1Rooted W (Fin.cons a0 (Fin.cons a1 y)))
      (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
      (fun y => hb _)]
    refine integral_congr_ae (ae_of_all _ fun a2 => ?_)
    simp only []
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 2 → Ω =>
        graphWeight q1Rooted W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      (fun y => hb _)]
    have hinner : ∀ a3 : Ω,
        (∫ y : Fin 1 → Ω, graphWeight q1Rooted W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 1) μ) =
          (W a0 a1 * W a0 a2 * W a1 a2) * (W a0 a3 * degree W a3) := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 1 → Ω => graphWeight q1Rooted W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp
          ((measurable_fin_cons a1).comp
            ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        (fun y => hb _)]
      have hlast : (∫ a4, (∫ y : Fin 0 → Ω, graphWeight q1Rooted W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 0) μ) ∂μ) =
          ∫ a4, ((W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3) * W a3 a4 ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun a4 => ?_)
        simp only []
        rw [show (∫ y : Fin 0 → Ω, graphWeight q1Rooted W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y)))))
              ∂assignmentMeasure (Fin 0) μ) =
            W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a3 a4 by
          simp [graphWeight_q1Rooted_cons]]
        ring
      rw [hlast, integral_const_mul]
      show (W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3 * degree W a3 = _
      ring
    rw [integral_congr_ae (ae_of_all _ hinner), integral_const_mul]
    rfl
  rw [integral_congr_ae (ae_of_all _ hstep)]
  have hpull : (∫ a1, ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 * pathOp W a0 ∂μ ∂μ) =
      rootedTriangle W a0 * pathOp W a0 := by
    have h2 : ∀ a1 : Ω,
        (∫ a2, W a0 a1 * W a0 a2 * W a1 a2 * pathOp W a0 ∂μ) =
          pathOp W a0 * ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂μ := by
      intro a1
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun a2 => by ring)
    rw [integral_congr_ae (ae_of_all _ h2), integral_const_mul]
    show pathOp W a0 * rootedTriangle W a0 = _
    ring
  exact hpull

/-! ### Chromatic data: `K₃`, a leaf, then a leaf on that leaf -/

/-- `K₃` with a two-edge tail at vertex `0`. -/
abbrev q1Built : SimpleGraph (Option (Option (Fin 3))) :=
  attachVertex pawBuilt {none}

def q1Equiv : Option (Option (Fin 3)) ≃ Fin 5 where
  toFun a := match a with
    | none => 0
    | some none => 4
    | some (some i) => ![3, 1, 2] i
  invFun j := ![none, some (some 1), some (some 2), some (some 0), some none] j
  left_inv := by decide
  right_inv := by decide

theorem q1_adj (a b : Option (Option (Fin 3))) :
    q1Graph.Adj (q1Equiv a) (q1Equiv b) ↔ q1Built.Adj a b := by
  revert a b
  decide

def q1Iso : q1Built ≃g q1Graph where
  toEquiv := q1Equiv
  map_rel_iff' := by intro a b; exact q1_adj a b

private lemma singleton_clique_none :
    pawBuilt.IsClique ((({none} : Finset (Option (Fin 3)))) :
      Set (Option (Fin 3))) := by
  intro u hu v hv huv
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
  exact absurd (hu.trans hv.symm) huv

theorem q1_chromatic :
    IsChromaticPolynomial q1Graph
      ((X : ℝ[X]) * (X - C 1) ^ (2 + 1) * (X - C 2)) := by
  have hbase : IsChromaticPolynomial pawBuilt
      ((X - C ((({0} : Finset (Fin 3))).card : ℝ)) *
        ∏ i ∈ range 3, (X - C (i : ℝ))) :=
    isChromaticPolynomial_attachVertex singleton_isClique
      (isChromaticPolynomial_top 3)
  have h := isChromaticPolynomial_of_attachIso q1Iso singleton_clique_none hbase
  simp only [Finset.card_singleton, Nat.cast_one, Finset.prod_range_succ,
    Finset.prod_range_zero, Nat.cast_zero, Nat.cast_ofNat, map_zero, sub_zero,
    one_mul] at h
  have hpoly : (X : ℝ[X]) * (X - C 1) ^ (2 + 1) * (X - C 2) =
      (X - C 1) * ((X - C 1) * (X * (X - C 1) * (X - C 2))) := by ring
  rw [hpoly]
  exact h

theorem q1_count (k : ℕ) :
    properAssignmentCount q1Graph k = (k - 1) * ((k - 1) * k.descFactorial 3) := by
  rw [properAssignmentCount_of_attachIso q1Iso singleton_clique_none k,
    properAssignmentCount_attachVertex singleton_isClique k,
    properAssignmentCount_top]
  simp

theorem q1_chromaticNumber : IsChromaticNumber q1Graph 3 where
  positive := by
    rw [q1_count]
    decide
  zero_below k hk := by
    rw [q1_count, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero]

/-! ### The catalogue proposition -/

def q1RootedEquiv : Fin 5 ≃ Fin 5 where
  toFun := ![3, 1, 2, 4, 0]
  invFun := ![4, 1, 2, 0, 3]
  left_inv := by decide
  right_inv := by decide

theorem q1Rooted_adj (a b : Fin 5) :
    q1Graph.Adj (q1RootedEquiv a) (q1RootedEquiv b) ↔ q1Rooted.Adj a b := by
  revert a b
  decide

def q1RootedIso : q1Rooted ≃g q1Graph where
  toEquiv := q1RootedEquiv
  map_rel_iff' := by intro a b; exact q1Rooted_adj a b

/-- **Atlas 36 satisfies the common catalogue proposition.** -/
theorem q1_satisfiesLowerBound : Taeyoung.SatisfiesLowerBound q1Graph :=
  satisfiesLowerBound_of_target (r := 2) q1Graph q1_chromatic q1_chromaticNumber
    (fun W hp => by
      rw [← homDensity_iso W q1RootedIso, homDensity_q1Rooted]
      exact tail_bound W hp)


end Taeyoung.Methods.RootedTriangleTree
