import Taeyoung.Methods.RootedTriangleTree.Paw

/-!
# `L₂`: a triangle with two leaves at one vertex (Atlas 34)

The second member of the rooted triangle–tree family.  Everything except the
rooted factorization comes from the shared packaging in `Paw.lean`; the
chromatic polynomial is two clique-attachments over `K₃`.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Methods.RootedTriangleTree

open Taeyoung Taeyoung.Methods.Link Taeyoung.Methods.Chromatic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Atlas 34, on its own edge list: root `4`, triangle `{2,3,4}`, leaves `0,1`. -/
def l2Graph : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 4), (1, 4), (2, 3), (2, 4), (3, 4)]

instance : DecidableRel l2Graph.Adj := graphFromEdges_decidableAdj _ _

/-- The same graph with the root at coordinate `0`. -/
def l2Rooted : SimpleGraph (Fin 5) :=
  graphFromEdges 5 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2)]

instance : DecidableRel l2Rooted.Adj := graphFromEdges_decidableAdj _ _

/-! ### The rooted factorization -/

lemma edgeFinset_l2Rooted :
    l2Rooted.edgeFinset = {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(1, 2)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    revert u v
    decide

lemma graphWeight_l2Rooted (W : Graphon Ω μ) (x : Fin 5 → Ω) :
    graphWeight l2Rooted W x =
      W (x 0) (x 1) * W (x 0) (x 2) * W (x 0) (x 3) * W (x 0) (x 4) *
        W (x 1) (x 2) := by
  rw [graphWeight, edgeFinset_l2Rooted]
  simp
  ring

lemma graphWeight_l2Rooted_cons (W : Graphon Ω μ) (a0 a1 a2 a3 a4 : Ω)
    (y : Fin 0 → Ω) :
    graphWeight l2Rooted W
        (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y))))) =
      W a0 a1 * W a0 a2 * W a0 a3 * W a0 a4 * W a1 a2 := by
  rw [graphWeight_l2Rooted]
  rfl

/-- Conditioning on the root: two leaves give `d²`, the triangle gives `τ`. -/
theorem homDensity_l2Rooted (W : Graphon Ω μ) :
    homDensity l2Rooted W = ∫ a, degree W a ^ 2 * rootedTriangle W a ∂μ := by
  have hm : Measurable (graphWeight l2Rooted W) := measurable_graphWeight _ W
  have hb : ∀ x, |graphWeight l2Rooted W x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (graphWeight_nonneg _ W x)]
    exact graphWeight_le_one _ W x
  rw [homDensity, integral_assignmentMeasure_succ _ hm hb]
  refine integral_congr_ae (ae_of_all _ fun a0 => ?_)
  simp only []
  rw [integral_assignmentMeasure_succ
    (fun y : Fin 4 → Ω => graphWeight l2Rooted W (Fin.cons a0 y))
    (hm.comp (measurable_fin_cons a0)) (fun y => hb _)]
  have hstep : ∀ a1 : Ω,
      (∫ y : Fin 3 → Ω, graphWeight l2Rooted W (Fin.cons a0 (Fin.cons a1 y))
        ∂assignmentMeasure (Fin 3) μ) =
        ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 * degree W a0 ^ 2 ∂μ := by
    intro a1
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 3 → Ω => graphWeight l2Rooted W (Fin.cons a0 (Fin.cons a1 y)))
      (hm.comp ((measurable_fin_cons a0).comp (measurable_fin_cons a1)))
      (fun y => hb _)]
    refine integral_congr_ae (ae_of_all _ fun a2 => ?_)
    simp only []
    rw [integral_assignmentMeasure_succ
      (fun y : Fin 2 → Ω =>
        graphWeight l2Rooted W (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 y))))
      (hm.comp ((measurable_fin_cons a0).comp
        ((measurable_fin_cons a1).comp (measurable_fin_cons a2))))
      (fun y => hb _)]
    have hinner : ∀ a3 : Ω,
        (∫ y : Fin 1 → Ω, graphWeight l2Rooted W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y))))
          ∂assignmentMeasure (Fin 1) μ) =
          (W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3 * degree W a0 := by
      intro a3
      rw [integral_assignmentMeasure_succ
        (fun y : Fin 1 → Ω => graphWeight l2Rooted W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 y)))))
        (hm.comp ((measurable_fin_cons a0).comp
          ((measurable_fin_cons a1).comp
            ((measurable_fin_cons a2).comp (measurable_fin_cons a3)))))
        (fun y => hb _)]
      have hlast : (∫ a4, (∫ y : Fin 0 → Ω, graphWeight l2Rooted W
          (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y)))))
            ∂assignmentMeasure (Fin 0) μ) ∂μ) =
          ∫ a4, ((W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3) * W a0 a4 ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun a4 => ?_)
        simp only []
        rw [show (∫ y : Fin 0 → Ω, graphWeight l2Rooted W
            (Fin.cons a0 (Fin.cons a1 (Fin.cons a2 (Fin.cons a3 (Fin.cons a4 y)))))
              ∂assignmentMeasure (Fin 0) μ) =
            W a0 a1 * W a0 a2 * W a0 a3 * W a0 a4 * W a1 a2 by
          simp [graphWeight_l2Rooted_cons]]
        ring
      rw [hlast, integral_const_mul]
      rfl
    rw [integral_congr_ae (ae_of_all _ hinner)]
    have hpull : (∫ a3, (W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3 * degree W a0 ∂μ) =
        W a0 a1 * W a0 a2 * W a1 a2 * degree W a0 ^ 2 := by
      have hre : ∀ a3 : Ω,
          (W a0 a1 * W a0 a2 * W a1 a2) * W a0 a3 * degree W a0 =
            ((W a0 a1 * W a0 a2 * W a1 a2) * degree W a0) * W a0 a3 := by
        intro a3; ring
      rw [integral_congr_ae (ae_of_all _ hre), integral_const_mul]
      show (W a0 a1 * W a0 a2 * W a1 a2) * degree W a0 * degree W a0 = _
      ring
    exact hpull
  rw [integral_congr_ae (ae_of_all _ hstep)]
  have hpull2 : (∫ a1, ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 * degree W a0 ^ 2 ∂μ ∂μ) =
      degree W a0 ^ 2 * rootedTriangle W a0 := by
    have h2 : ∀ a1 : Ω,
        (∫ a2, W a0 a1 * W a0 a2 * W a1 a2 * degree W a0 ^ 2 ∂μ) =
          degree W a0 ^ 2 * ∫ a2, W a0 a1 * W a0 a2 * W a1 a2 ∂μ := by
      intro a1
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun a2 => by ring)
    rw [integral_congr_ae (ae_of_all _ h2), integral_const_mul]
    rfl
  exact hpull2

/-! ### Chromatic data, by two attachments over `K₃` -/

/-- `K₃` with two leaves at vertex `0`. -/
abbrev l2Built : SimpleGraph (Option (Option (Fin 3))) :=
  attachVertex pawBuilt {some 0}

def l2Equiv : Option (Option (Fin 3)) ≃ Fin 5 where
  toFun a := match a with
    | none => 0
    | some none => 1
    | some (some i) => ![4, 2, 3] i
  invFun j := ![none, some none, some (some 1), some (some 2), some (some 0)] j
  left_inv := by decide
  right_inv := by decide

theorem l2_adj (a b : Option (Option (Fin 3))) :
    l2Graph.Adj (l2Equiv a) (l2Equiv b) ↔ l2Built.Adj a b := by
  revert a b
  decide

def l2Iso : l2Built ≃g l2Graph where
  toEquiv := l2Equiv
  map_rel_iff' := by intro a b; exact l2_adj a b

theorem l2_chromatic :
    IsChromaticPolynomial l2Graph
      ((X : ℝ[X]) * (X - C 1) ^ (2 + 1) * (X - C 2)) := by
  have hbase : IsChromaticPolynomial pawBuilt
      ((X - C ((({0} : Finset (Fin 3))).card : ℝ)) *
        ∏ i ∈ range 3, (X - C (i : ℝ))) :=
    isChromaticPolynomial_attachVertex singleton_isClique
      (isChromaticPolynomial_top 3)
  have hS : pawBuilt.IsClique ((({some 0} : Finset (Option (Fin 3)))) :
      Set (Option (Fin 3))) := by
    intro u hu v hv huv
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
    exact absurd (hu.trans hv.symm) huv
  have h := isChromaticPolynomial_of_attachIso l2Iso hS hbase
  simp only [Finset.card_singleton, Nat.cast_one, Finset.prod_range_succ,
    Finset.prod_range_zero, Nat.cast_zero, Nat.cast_ofNat, map_zero, sub_zero,
    one_mul] at h
  have hpoly : (X : ℝ[X]) * (X - C 1) ^ (2 + 1) * (X - C 2) =
      (X - C 1) * ((X - C 1) * (X * (X - C 1) * (X - C 2))) := by ring
  rw [hpoly]
  exact h

theorem l2_count (k : ℕ) :
    properAssignmentCount l2Graph k = (k - 1) * ((k - 1) * k.descFactorial 3) := by
  have hS : pawBuilt.IsClique ((({some 0} : Finset (Option (Fin 3)))) :
      Set (Option (Fin 3))) := by
    intro u hu v hv huv
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
    exact absurd (hu.trans hv.symm) huv
  rw [properAssignmentCount_of_attachIso l2Iso hS k,
    properAssignmentCount_attachVertex singleton_isClique k,
    properAssignmentCount_top]
  simp

theorem l2_chromaticNumber : IsChromaticNumber l2Graph 3 where
  positive := by
    rw [l2_count]
    decide
  zero_below k hk := by
    rw [l2_count, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.mul_zero,
      Nat.mul_zero]

/-! ### The catalogue proposition -/

def l2RootedEquiv : Fin 5 ≃ Fin 5 where
  toFun := ![4, 2, 3, 0, 1]
  invFun := ![3, 4, 1, 2, 0]
  left_inv := by decide
  right_inv := by decide

theorem l2Rooted_adj (a b : Fin 5) :
    l2Graph.Adj (l2RootedEquiv a) (l2RootedEquiv b) ↔ l2Rooted.Adj a b := by
  revert a b
  decide

def l2RootedIso : l2Rooted ≃g l2Graph where
  toEquiv := l2RootedEquiv
  map_rel_iff' := by intro a b; exact l2Rooted_adj a b

theorem l2_factorization {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    homDensity l2Graph W = ∫ x, degree W x ^ 2 * rootedTriangle W x ∂μ := by
  rw [← homDensity_iso W l2RootedIso, homDensity_l2Rooted]

/-- **Atlas 34 satisfies the common catalogue proposition.** -/
theorem l2_satisfiesLowerBound : Taeyoung.SatisfiesLowerBound l2Graph :=
  satisfiesLowerBound_of_rootedTree (r := 2) l2Graph l2_chromatic
    l2_chromaticNumber (fun W => l2_factorization W)

end Taeyoung.Methods.RootedTriangleTree
