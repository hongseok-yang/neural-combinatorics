import Taeyoung.Methods.K4Tail.Link
import Taeyoung.Methods.ForestCone.Rows
import Taeyoung.Methods.BaseCone.Rows

/-!
# Atlas 142: `K₄` with a two-edge tail

Clique vertices `0,1,2,3`, tail `0–4–5`.  Conditioning at the tail-bearing
clique vertex gives

```
t(H,W) = ∫ κ₄(x)·A(x) dμ(x),      A = T_W d,
```

and `Methods/K4Tail/Link.lean` bounds the integrand below pointwise by the
supporting plane `L_p(d(x), A(x))`.  That plane integrates to `T_p` *exactly*,
because `∫d = p` and `∫A = ∫d²` — the two zero-mean corrections it is built
from.  So the row needs no analytic step beyond the pointwise one; only the
peeling and the two moment identities.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.K4Tail

open Taeyoung Taeyoung.Methods Taeyoung.Methods.Link
  Taeyoung.Methods.PureChordal Taeyoung.Methods.PawCone
  Taeyoung.Methods.BaseCone Taeyoung.Methods.ForestCone
  Taeyoung.Methods.CliqueLeaf Taeyoung.Methods.BookTail

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The rooted `K₄` density as a triple integral -/

lemma edgeFinset_top_fin_three :
    (⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_top_fin_three (W : Graphon Ω μ) (x : Fin 3 → Ω) :
    graphWeight (⊤ : SimpleGraph (Fin 3)) W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) := by
  rw [graphWeight, edgeFinset_top_fin_three]
  simp
  ring

lemma rooted_integrand_top_three (W : Graphon Ω μ) (a : Ω) (y : Fin 3 → Ω) :
    (∏ i, W a (y i)) * graphWeight (⊤ : SimpleGraph (Fin 3)) W y =
      W a (y 0) * W a (y 1) * W a (y 2) *
        (W (y 0) (y 1) * W (y 0) (y 2) * W (y 1) (y 2)) := by
  rw [graphWeight_top_fin_three, Fin.prod_univ_three]

/-- `κ₄(a)` written out. -/
theorem rootedK4_eq (W : Graphon Ω μ) (a : Ω) :
    rootedK4 W a =
      ∫ y0, ∫ y1, ∫ y2, W a y0 * W a y1 * W a y2 *
        (W y0 y1 * W y0 y2 * W y1 y2) ∂μ ∂μ ∂μ := by
  have hm := measurable_rooted_integrand (⊤ : SimpleGraph (Fin 3)) W a
  have hb := abs_rooted_integrand_le_one (⊤ : SimpleGraph (Fin 3)) W a
  rw [rootedK4, rootedDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun y0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 2 → Ω ↦ (∏ i, W a ((Fin.cons y0 y : Fin 3 → Ω) i)) *
      graphWeight (⊤ : SimpleGraph (Fin 3)) W (Fin.cons y0 y))
    (hm.comp (measurable_fin_cons y0)) fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun y1 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 1 → Ω ↦
      (∏ i, W a ((Fin.cons y0 (Fin.cons y1 y) : Fin 3 → Ω) i)) *
        graphWeight (⊤ : SimpleGraph (Fin 3)) W (Fin.cons y0 (Fin.cons y1 y)))
    (hm.comp ((measurable_fin_cons y0).comp (measurable_fin_cons y1)))
    fun y ↦ hb _]
  refine integral_congr_ae (ae_of_all _ fun y2 ↦ ?_)
  simp only []
  have hval : ∀ z : Fin 0 → Ω,
      (∏ i, W a ((Fin.cons y0 (Fin.cons y1 (Fin.cons y2 z)) : Fin 3 → Ω) i)) *
          graphWeight (⊤ : SimpleGraph (Fin 3)) W
            (Fin.cons y0 (Fin.cons y1 (Fin.cons y2 z))) =
        W a y0 * W a y1 * W a y2 * (W y0 y1 * W y0 y2 * W y1 y2) := fun z ↦
    rooted_integrand_top_three W a (Fin.cons y0 (Fin.cons y1 (Fin.cons y2 z)))
  rw [integral_congr_ae (ae_of_all _ hval)]
  simp

/-! ### The graph -/

/-- `K₄` on `0,1,2,3`, with the two-edge tail `0–4–5`. -/
def k4tail : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (0, 4), (4, 5)]

instance : DecidableRel k4tail.Adj := graphFromEdges_decidableAdj _ _

lemma edgeFinset_k4tail :
    k4tail.edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3), s(0, 4), s(4, 5)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_k4tail (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight k4tail W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 0) (x 3) * W (x 1) (x 2) *
        W (x 1) (x 3) * W (x 2) (x 3) * W (x 0) (x 4) * W (x 4) (x 5) := by
  rw [graphWeight, edgeFinset_k4tail]
  simp
  ring

lemma graphWeight_k4tail_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight k4tail W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
        (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a2 a3 * W a0 a4 *
        W a4 a5 := by
  rw [graphWeight_k4tail]
  rfl

/-! ### The density identity -/

/-- **The density of Atlas 142 is `∫ κ₄·A`.** -/
theorem homDensity_k4tail (W : Graphon Ω μ) :
    homDensity k4tail W = ∫ a0, rootedK4 W a0 * pathOp W a0 ∂μ := by
  have hm : Measurable (graphWeight k4tail W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight k4tail W x| ≤ 1 := fun x ↦ by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 ↦ ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω ↦ graphWeight k4tail W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) fun y ↦ hb _]
  have hstep1 : ∀ a1 : Ω,
      (∫ y : Fin 4 → Ω, graphWeight k4tail W (Fin.cons a0 (Fin.cons a1 y))
        ∂assignmentMeasure (Fin 4) μ) =
        ∫ a2, ∫ a3, W a0 a1 * W a0 a2 * W a0 a3 *
          (W a1 a2 * W a1 a3 * W a2 a3) * pathOp W a0 ∂μ ∂μ := by
    intro a1
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 4 → Ω ↦ graphWeight k4tail W (Fin.cons a0 (Fin.cons a1 y)))
      (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
      fun y ↦ hb _]
    refine integral_congr_ae (ae_of_all _ fun a2 ↦ ?_)
    simp only []
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω ↦
        graphWeight k4tail W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      fun y ↦ hb _]
    refine integral_congr_ae (ae_of_all _ fun a3 ↦ ?_)
    simp only []
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 2 → Ω ↦ graphWeight k4tail W
        (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
      (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
        ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
      fun y ↦ hb _]
    have hstep4 : ∀ a4 : Ω,
        (∫ y : Fin 1 → Ω, graphWeight k4tail W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
              (Fin.cons a4 y)))))
          ∂assignmentMeasure (Fin 1) μ) =
          (W a0 a1 * W a0 a2 * W a0 a3 * (W a1 a2 * W a1 a3 * W a2 a3)) *
            (W a0 a4 * degree W a4) := by
      intro a4
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 1 → Ω ↦ graphWeight k4tail W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
            (Fin.cons a4 y))))))
        (hm.comp ((measurable_fin_cons a0).comp ((measurable_fin_cons a1).comp
          ((measurable_fin_cons a2).comp ((measurable_fin_cons a3).comp
            (measurable_fin_cons a4))))))
        fun y ↦ hb _]
      have hval : ∀ a5 : Ω,
          (∫ y : Fin 0 → Ω, graphWeight k4tail W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
                (Fin.cons a4 (Fin.cons a5 y))))))
            ∂assignmentMeasure (Fin 0) μ) =
            (W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a2 a3 *
              W a0 a4) * W a4 a5 := by
        intro a5
        rw [show (∫ y : Fin 0 → Ω, graphWeight k4tail W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3
              (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) =
            W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a2 a3 *
              W a0 a4 * W a4 a5 by simp [graphWeight_k4tail_cons]]
      rw [integral_congr_ae (ae_of_all _ hval), integral_const_mul]
      show (W a0 a1 * W a0 a2 * W a0 a3 * W a1 a2 * W a1 a3 * W a2 a3 * W a0 a4) *
          degree W a4 =
        (W a0 a1 * W a0 a2 * W a0 a3 * (W a1 a2 * W a1 a3 * W a2 a3)) *
          (W a0 a4 * degree W a4)
      ring
    rw [integral_congr_ae (ae_of_all _ hstep4), integral_const_mul, ← pathOp]
  rw [integral_congr_ae (ae_of_all _ hstep1)]
  -- pull the tail factor out of the three clique integrals
  have hpull : (∫ a1, ∫ a2, ∫ a3, W a0 a1 * W a0 a2 * W a0 a3 *
      (W a1 a2 * W a1 a3 * W a2 a3) * pathOp W a0 ∂μ ∂μ ∂μ) =
      rootedK4 W a0 * pathOp W a0 := by
    have h3 : ∀ a1 a2 : Ω,
        (∫ a3, W a0 a1 * W a0 a2 * W a0 a3 *
            (W a1 a2 * W a1 a3 * W a2 a3) * pathOp W a0 ∂μ) =
          pathOp W a0 * ∫ a3, W a0 a1 * W a0 a2 * W a0 a3 *
            (W a1 a2 * W a1 a3 * W a2 a3) ∂μ := by
      intro a1 a2
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun a3 ↦ by ring)
    have h2 : ∀ a1 : Ω,
        (∫ a2, ∫ a3, W a0 a1 * W a0 a2 * W a0 a3 *
            (W a1 a2 * W a1 a3 * W a2 a3) * pathOp W a0 ∂μ ∂μ) =
          pathOp W a0 * ∫ a2, ∫ a3, W a0 a1 * W a0 a2 * W a0 a3 *
            (W a1 a2 * W a1 a3 * W a2 a3) ∂μ ∂μ := by
      intro a1
      rw [integral_congr_ae (ae_of_all _ (h3 a1)), integral_const_mul]
    rw [integral_congr_ae (ae_of_all _ h2), integral_const_mul, rootedK4_eq]
    ring
  exact hpull

/-! ### Integrating the supporting plane -/

/-- `∫ L_p(d,A) = T_p`: the two corrections have mean zero. -/
theorem integral_plane (W : Graphon Ω μ) :
    (∫ x, plane (cliqueDensity 2 W) (degree W x) (pathOp W x) ∂μ) =
      targetT (cliqueDensity 2 W) := by
  have hd := integrable_degree W
  have hA := integrable_pathOp W
  have hd2 := integrable_degree_pow W 2
  have i0 : Integrable (fun _ : Ω ↦ targetT (cliqueDensity 2 W) -
      cliqueDensity 2 W ^ 2 *
        (30 * cliqueDensity 2 W ^ 2 - 21 * cliqueDensity 2 W + 2) *
        cliqueDensity 2 W) μ := integrable_const _
  have i1 : Integrable (fun x : Ω ↦ cliqueDensity 2 W ^ 2 *
      (30 * cliqueDensity 2 W ^ 2 - 21 * cliqueDensity 2 W + 2) * degree W x) μ :=
    hd.const_mul _
  have i2 : Integrable (fun x : Ω ↦ cliqueDensity 2 W *
      (20 * cliqueDensity 2 W ^ 2 - 15 * cliqueDensity 2 W + 2) * pathOp W x) μ :=
    hA.const_mul _
  have i3 : Integrable (fun x : Ω ↦ cliqueDensity 2 W *
      (20 * cliqueDensity 2 W ^ 2 - 15 * cliqueDensity 2 W + 2) *
      degree W x ^ 2) μ := hd2.const_mul _
  have hfun : ∀ x : Ω, plane (cliqueDensity 2 W) (degree W x) (pathOp W x) =
      (targetT (cliqueDensity 2 W) - cliqueDensity 2 W ^ 2 *
          (30 * cliqueDensity 2 W ^ 2 - 21 * cliqueDensity 2 W + 2) *
          cliqueDensity 2 W) +
        cliqueDensity 2 W ^ 2 *
          (30 * cliqueDensity 2 W ^ 2 - 21 * cliqueDensity 2 W + 2) * degree W x +
        cliqueDensity 2 W *
          (20 * cliqueDensity 2 W ^ 2 - 15 * cliqueDensity 2 W + 2) * pathOp W x -
        cliqueDensity 2 W *
          (20 * cliqueDensity 2 W ^ 2 - 15 * cliqueDensity 2 W + 2) *
          degree W x ^ 2 := by
    intro x
    simp only [plane]
    ring
  have e1 := integral_sub ((i0.add i1).add i2) i3
  have e2 := integral_add (i0.add i1) i2
  have e3 := integral_add i0 i1
  simp only [Pi.add_apply] at e1 e2 e3
  rw [integral_congr_ae (ae_of_all _ hfun), e1, e2, e3, integral_const,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_degree, integral_pathOp, moment]
  simp

/-! ### The bound -/

/-- **Atlas 142 dominates its target.** -/
theorem k4tail_bound (W : Graphon Ω μ)
    (hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W) :
    targetT (cliqueDensity 2 W) ≤ homDensity k4tail W := by
  set p := cliqueDensity 2 W with hpdef
  have hint1 : Integrable (fun x ↦ plane p (degree W x) (pathOp W x)) μ := by
    have hsplit : ∀ x : Ω, plane p (degree W x) (pathOp W x) =
        targetT p + p ^ 2 * (30 * p ^ 2 - 21 * p + 2) * degree W x +
          p * (20 * p ^ 2 - 15 * p + 2) * pathOp W x -
          p * (20 * p ^ 2 - 15 * p + 2) * degree W x ^ 2 -
          p ^ 2 * (30 * p ^ 2 - 21 * p + 2) * p := by
      intro x; simp only [plane]; ring
    refine Integrable.congr ?_ (ae_of_all _ fun x ↦ (hsplit x).symm)
    exact ((((integrable_const _).add ((integrable_degree W).const_mul _)).add
      ((integrable_pathOp W).const_mul _)).sub
      ((integrable_degree_pow W 2).const_mul _)).sub (integrable_const _)
  have hint2 : Integrable (fun x ↦ rootedK4 W x * pathOp W x) μ :=
    integrable_of_bdd ((measurable_rootedK4 W).mul (measurable_pathOp W))
      (C := 1) fun x ↦ by
        rw [abs_of_nonneg (mul_nonneg (rootedK4_nonneg W x) (pathOp_nonneg W x))]
        exact mul_le_one₀ (rootedK4_le_one W x) (pathOp_nonneg W x)
          (pathOp_le_one W x)
  have hmono : (∫ x, plane p (degree W x) (pathOp W x) ∂μ) ≤
      ∫ x, rootedK4 W x * pathOp W x ∂μ :=
    integral_mono hint1 hint2 fun x ↦ by
      have := plane_le_rootedK4 W (by rw [← hpdef] at *; exact hp) x
      rw [← hpdef] at this
      calc plane p (degree W x) (pathOp W x) ≤ pathOp W x * rootedK4 W x := this
        _ = rootedK4 W x * pathOp W x := by ring
  rw [homDensity_k4tail]
  rw [integral_plane W, ← hpdef] at hmono
  exact hmono

/-! ### Chromatic data and the catalogue proposition -/

lemma affineProd_142 (z : ℝ) :
    affineProd [0, 1, 1, 1, 2, 3] z = z ^ 3 * (2 * z - 1) * (3 * z - 2) := by
  rw [affineProd_cons, affineProd_cons, affineProd_cons, affineProd_cons,
    affineProd_cons, affineProd_cons, affineProd_nil]
  ring

/-- `K₄` on `{0,1,2,3}`, then `4` on `{0}`, then `5` on `{4}`. -/
def equiv142 : Option (Option (Fin 4)) ≃ Fin 6 where
  toFun a := match a with
    | none => 5
    | some none => 4
    | some (some i) => ![0, 1, 2, 3] i
  invFun j := ![some (some 0), some (some 1), some (some 2), some (some 3),
    some none, none] j
  left_inv := by decide
  right_inv := by decide

def iso142 :
    attachVertex (attachVertex (⊤ : SimpleGraph (Fin 4)) {0}) {none} ≃g
      k4tail where
  toEquiv := equiv142
  map_rel_iff' := by
    intro a b
    revert a b
    decide

theorem chrom142 : IsChromaticPolynomial k4tail
    ((([0, 1, 1, 1, 2, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod) := by
  have h := isChromaticPolynomial_of_attachIso (H' := k4tail) iso142
    (isClique_singleton _ none)
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

theorem count142 (k : ℕ) :
    properAssignmentCount k4tail k = (k - 1) * ((k - 1) * k.descFactorial 4) := by
  rw [properAssignmentCount_of_attachIso (H' := k4tail) iso142
      (isClique_singleton _ none) k,
    properAssignmentCount_attachVertex (isCliqueTop _), properAssignmentCount_top,
    show (({0} : Finset (Fin 4)).card) = 1 from by decide, Finset.card_singleton]

theorem num142 : IsChromaticNumber k4tail 4 where
  positive := by rw [count142]; decide
  zero_below k hk := by
    rw [count142, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero]

/-- **Atlas 142 satisfies the catalogue proposition.** -/
theorem satisfiesLowerBound_142 : Taeyoung.SatisfiesLowerBound k4tail := by
  intro P r hP hr Ω instM μ instP W hadm
  have hPeq : P =
      (([0, 1, 1, 1, 2, 3] : List ℝ).map fun k ↦ (X : ℝ[X]) - C k).prod :=
    IsChromaticPolynomial.unique (H := k4tail) hP chrom142
  have hreq : r = 4 := IsChromaticNumber.unique (H := k4tail) hr num142
  subst hPeq
  subst hreq
  have hp : (2 : ℝ) / 3 ≤ cliqueDensity 2 W := by
    have h := hadm
    norm_num [admissibleDensity, edgeDensity] at h
    linarith
  have hkey := k4tail_bound W hp
  change Taeyoung.chromaticTarget (V := Fin 6) _ (cliqueDensity 2 W) ≤ _
  by_cases hone : cliqueDensity 2 W = 1
  · rw [hone, chromaticTarget_at_one]
    rw [hone] at hkey
    simp only [targetT] at hkey
    norm_num at hkey
    exact hkey
  · rw [chromaticTarget_affineProd [0, 1, 1, 1, 2, 3] (by norm_num) hone,
      affineProd_142]
    simpa only [targetT] using hkey

end Taeyoung.Methods.K4Tail
