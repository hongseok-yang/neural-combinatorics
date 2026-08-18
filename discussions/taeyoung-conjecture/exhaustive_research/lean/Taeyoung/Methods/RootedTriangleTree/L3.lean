import Taeyoung.Methods.RootedTriangleTree.L2

/-!
# `L₃`: a triangle with three leaves at one vertex (Atlas 92)

The third member of the rooted triangle–tree family.  Same shape as `L₂`, one
nesting level deeper: three clique-attachments over `K₃` on the chromatic side,
and six coordinate peels on the analytic side.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedTriangleTree

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.Chromatic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Atlas 92: root `5`, triangle `{3,4,5}`, leaves `0,1,2`. -/
def l3Graph : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 5), (1, 5), (2, 5), (3, 4), (3, 5), (4, 5)]

instance : DecidableRel l3Graph.Adj := graphFromEdges_decidableAdj _ _

/-- The same graph with the root at coordinate `0`. -/
def l3Rooted : SimpleGraph (Fin 6) :=
  graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2)]

instance : DecidableRel l3Rooted.Adj := graphFromEdges_decidableAdj _ _

/-! ### The rooted factorization -/

lemma edgeFinset_l3Rooted :
    l3Rooted.edgeFinset =
      {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(0, 5), s(1, 2)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_l3Rooted (W : Graphon Ω μ) (x : Fin 6 → Ω) :
    graphWeight l3Rooted W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 0) (x 3) * W (x 0) (x 4) *
        W (x 0) (x 5) * W (x 1) (x 2) := by
  rw [graphWeight, edgeFinset_l3Rooted]
  simp
  ring

lemma graphWeight_l3Rooted_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 a5 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight l3Rooted W
        (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
          (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y)))))) =
      W a0 a1 * W a0 a2 * W a0 a3 * W a0 a4 * W a0 a5 * W a1 a2 := by
  rw [graphWeight_l3Rooted]
  rfl

/-- Conditioning on the root: three leaves give `d³`, the triangle gives `τ`. -/
theorem homDensity_l3Rooted (W : Graphon Ω μ) :
    homDensity l3Rooted W = ∫ a, degree W a ^ 3 * rootedTriangle W a ∂μ := by
  have hm : Measurable (graphWeight l3Rooted W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight l3Rooted W x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 => ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 5 → Ω => graphWeight l3Rooted W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) (fun y => hb _)]
  have hstep : ∀ a1 : Ω,
      (∫ y : Fin 4 → Ω, graphWeight l3Rooted W (Fin.cons a0 (Fin.cons a1 y))
        ∂assignmentMeasure (Fin 4) μ) =
        ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 * degree W a0 ^ 3 ∂μ := by
    intro a1
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 4 → Ω => graphWeight l3Rooted W (Fin.cons a0 (Fin.cons a1 y)))
      (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
      (fun y => hb _)]
    refine integral_congr_ae (ae_of_all _ fun a2 => ?_)
    simp only []
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω =>
        graphWeight l3Rooted W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      (fun y => hb _)]
    -- three leaf coordinates remain
    have h3 : ∀ a3 : Ω,
        (∫ y : Fin 2 → Ω, graphWeight l3Rooted W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 2) μ) =
          (W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3 * degree W a0 ^ 2 := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 2 → Ω => graphWeight l3Rooted W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp
          ((measurable_fin_cons a1).comp
            ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        (fun y => hb _)]
      have h4 : ∀ a4 : Ω,
          (∫ y : Fin 1 → Ω, graphWeight l3Rooted W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
                (Fin.cons a3 (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 1) μ) =
            ((W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3) * W a0 a4 *
              degree W a0 := by
        intro a4
        rw [integral_assignmentMeasure_succ
          (fun y : Fin 1 → Ω => graphWeight l3Rooted W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
              (Fin.cons a3 (Fin.cons a4 y))))))
          (hm.comp ((measurable_fin_cons a0).comp
            ((measurable_fin_cons a1).comp
              ((measurable_fin_cons a2).comp
                ((measurable_fin_cons a3).comp (measurable_fin_cons a4))))))
          (fun y => hb _)]
        have hlast : (∫ a5, (∫ y : Fin 0 → Ω, graphWeight l3Rooted W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
              (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y))))))
              ∂assignmentMeasure (Fin 0) μ) ∂μ) =
            ∫ a5, (((W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3) * W a0 a4) *
              W a0 a5 ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun a5 => ?_)
          simp only []
          rw [show (∫ y : Fin 0 → Ω, graphWeight l3Rooted W
              (Fin.cons a0 (Fin.cons a1 (Fin.cons a2
                (Fin.cons a3 (Fin.cons a4 (Fin.cons a5 y))))))
                ∂assignmentMeasure (Fin 0) μ) =
              W a0 a1 * W a0 a2 * W a0 a3 * W a0 a4 * W a0 a5 * W a1 a2 by
            simp [graphWeight_l3Rooted_cons]]
          ring
        rw [hlast, integral_const_mul]
        rfl
      rw [integral_congr_ae (ae_of_all _ h4)]
      have hre : ∀ a4 : Ω,
          ((W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3) * W a0 a4 * degree W a0 =
            (((W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3) * degree W a0) *
              W a0 a4 := by
        intro a4; ring
      rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
      show ((W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3) * degree W a0 *
        degree W a0 = _
      ring
    rw [integral_congr_ae (ae_of_all _ h3)]
    have hre : ∀ a3 : Ω,
        (W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3 * degree W a0 ^ 2 =
          ((W a0 a1 * W a0 a2 * W a1 a2) * degree W a0 ^ 2) * W a0 a3 := by
      intro a3; ring
    rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
    show (W a0 a1 * W a0 a2 * W a1 a2) * degree W a0 ^ 2 * degree W a0 = _
    ring
  rw [integral_congr_ae (ae_of_all _ hstep)]
  have hpull : (∫ a1, ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 * degree W a0 ^ 3 ∂μ ∂μ) =
      degree W a0 ^ 3 * rootedTriangle W a0 := by
    have h2 : ∀ a1 : Ω,
        (∫ a2, W a0 a1 * W a0 a2 * W a1 a2 * degree W a0 ^ 3 ∂μ) =
          degree W a0 ^ 3 * ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂μ := by
      intro a1
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun a2 => by ring)
    rw [integral_congr_ae (ae_of_all _ h2), integral_const_mul]
    rfl
  exact hpull

/-! ### Chromatic data, by three attachments over `K₃` -/

/-- `K₃` with three leaves at vertex `0`. -/
abbrev l3Built : SimpleGraph (Option (Option (Option (Fin 3)))) :=
  attachVertex l2Built {some (some 0)}

def l3Equiv : Option (Option (Option (Fin 3))) ≃ Fin 6 where
  toFun a := match a with
    | none => 0
    | some none => 1
    | some (some none) => 2
    | some (some (some i)) => ![5, 3, 4] i
  invFun j :=
    ![none, some none, some (some none), some (some (some 1)),
      some (some (some 2)), some (some (some 0))] j
  left_inv := by decide
  right_inv := by decide

theorem l3_adj (a b : Option (Option (Option (Fin 3)))) :
    l3Graph.Adj (l3Equiv a) (l3Equiv b) ↔ l3Built.Adj a b := by
  revert a b
  decide

def l3Iso : l3Built ≃g l3Graph where
  toEquiv := l3Equiv
  map_rel_iff' := by intro a b; exact l3_adj a b

private lemma singleton_clique_l2 :
    l2Built.IsClique ((({some (some 0)} :
      Finset (Option (Option (Fin 3))))) : Set (Option (Option (Fin 3)))) := by
  intro u hu v hv huv
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
  exact absurd (hu.trans hv.symm) huv

private lemma singleton_clique_paw :
    pawBuilt.IsClique ((({some 0} : Finset (Option (Fin 3)))) :
      Set (Option (Fin 3))) := by
  intro u hu v hv huv
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
  exact absurd (hu.trans hv.symm) huv

theorem l3_chromatic :
    IsChromaticPolynomial l3Graph
      ((X : ℝ[X]) * (X - C 1) ^ (3 + 1) * (X - C 2)) := by
  have hbase : IsChromaticPolynomial pawBuilt
      ((X - C ((({0} : Finset (Fin 3))).card : ℝ)) *
        ∏ i ∈ range 3, (X - C (i : ℝ))) :=
    isChromaticPolynomial_attachVertex singleton_isClique
      (isChromaticPolynomial_top 3)
  have h2 := isChromaticPolynomial_attachVertex singleton_clique_paw hbase
  have h := isChromaticPolynomial_of_attachIso l3Iso singleton_clique_l2 h2
  simp only [Finset.card_singleton, Nat.cast_one, Finset.prod_range_succ,
    Finset.prod_range_zero, Nat.cast_zero, Nat.cast_ofNat, map_zero, sub_zero,
    one_mul] at h
  have hpoly : (X : ℝ[X]) * (X - C 1) ^ (3 + 1) * (X - C 2) =
      (X - C 1) * ((X - C 1) * ((X - C 1) * (X * (X - C 1) * (X - C 2)))) := by
    ring
  rw [hpoly]
  exact h

theorem l3_count (k : ℕ) :
    properAssignmentCount l3Graph k =
      (k - 1) * ((k - 1) * ((k - 1) * k.descFactorial 3)) := by
  rw [properAssignmentCount_of_attachIso l3Iso singleton_clique_l2 k,
    properAssignmentCount_attachVertex singleton_clique_paw k,
    properAssignmentCount_attachVertex singleton_isClique k,
    properAssignmentCount_top]
  simp

theorem l3_chromaticNumber : IsChromaticNumber l3Graph 3 where
  positive := by
    rw [l3_count]
    decide
  zero_below k hk := by
    rw [l3_count, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero, Nat.mul_zero]

/-! ### The catalogue proposition -/

def l3RootedEquiv : Fin 6 ≃ Fin 6 where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by decide
  right_inv := by decide

theorem l3Rooted_adj (a b : Fin 6) :
    l3Graph.Adj (l3RootedEquiv a) (l3RootedEquiv b) ↔ l3Rooted.Adj a b := by
  revert a b
  decide

def l3RootedIso : l3Rooted ≃g l3Graph where
  toEquiv := l3RootedEquiv
  map_rel_iff' := by intro a b; exact l3Rooted_adj a b

theorem l3_factorization {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    homDensity l3Graph W = ∫ x, degree W x ^ 3 * rootedTriangle W x ∂μ := by
  rw [← homDensity_iso W l3RootedIso, homDensity_l3Rooted]

/-- **Atlas 92 satisfies the common catalogue proposition.** -/
theorem l3_satisfiesLowerBound : Taeyoung.SatisfiesLowerBound l3Graph :=
  satisfiesLowerBound_of_rootedTree (r := 3) l3Graph l3_chromatic
    l3_chromaticNumber (fun W => l3_factorization W)

end Taeyoung.Methods.RootedTriangleTree
