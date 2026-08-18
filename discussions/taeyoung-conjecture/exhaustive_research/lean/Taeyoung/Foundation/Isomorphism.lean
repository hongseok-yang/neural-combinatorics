import Taeyoung.Foundation.Relabeling
import Taeyoung.Foundation.Status

/-!
# Transporting the status predicates along a graph isomorphism

Every proof methodology establishes its bound for one convenient representative
of an isomorphism class — a clique tree, a rooted triangle, a cone over a named
base.  An Atlas module, by contrast, defines its graph by a transparent edge
list.  This file supplies the bridge, so an Atlas row never has to be *restated*
on the representative's vertex labelling.

The two ingredients are `homDensity_iso` (`Foundation/Relabeling.lean`) and the
isomorphism invariance of `properAssignmentCount` proved here, which carries
both chromatic specifications across.
-/

open MeasureTheory

namespace Taeyoung

variable {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
variable {H : SimpleGraph V} {H' : SimpleGraph V'}

/-- Proper `k`-assignments correspond under a graph isomorphism. -/
def properAssignmentEquiv (φ : H ≃g H') (k : ℕ) :
    {x : V → Fin k // IsProperAssignment H x} ≃
      {y : V' → Fin k // IsProperAssignment H' y} where
  toFun x := ⟨fun v' ↦ x.1 (φ.symm v'), by
    intro u' v' huv
    exact x.2 (φ.symm.map_rel_iff.mpr huv)⟩
  invFun y := ⟨fun v ↦ y.1 (φ v), by
    intro u v huv
    exact y.2 (φ.map_rel_iff.mpr huv)⟩
  left_inv x := by
    ext v
    simp
  right_inv y := by
    ext v'
    simp

/-- The number of proper `k`-colour assignments is an isomorphism invariant. -/
theorem properAssignmentCount_iso (φ : H ≃g H') (k : ℕ) :
    properAssignmentCount H k = properAssignmentCount H' k := by
  classical
  have hV : properAssignmentCount H k =
      Fintype.card {x : V → Fin k // IsProperAssignment H x} := by
    rw [properAssignmentCount, Fintype.card_subtype]
  have hV' : properAssignmentCount H' k =
      Fintype.card {y : V' → Fin k // IsProperAssignment H' y} := by
    rw [properAssignmentCount, Fintype.card_subtype]
  rw [hV, hV', Fintype.card_congr (properAssignmentEquiv φ k)]

/-- A chromatic polynomial of `H'` is one of `H` whenever `H ≃g H'`. -/
theorem IsChromaticPolynomial.of_iso {P : Polynomial ℝ} (φ : H ≃g H')
    (h : IsChromaticPolynomial H' P) : IsChromaticPolynomial H P := by
  intro k
  rw [properAssignmentCount_iso φ k]
  exact h k

/-- The chromatic number is an isomorphism invariant. -/
theorem IsChromaticNumber.of_iso {r : ℕ} (φ : H ≃g H')
    (h : IsChromaticNumber H' r) : IsChromaticNumber H r where
  positive := by
    rw [properAssignmentCount_iso φ]
    exact h.positive
  zero_below k hk := by
    rw [properAssignmentCount_iso φ]
    exact h.zero_below k hk

/-- The chromatic target depends on the vertex type only through its
cardinality, so it too transports. -/
theorem chromaticTarget_congr_card (hcard : Fintype.card V = Fintype.card V')
    (P : Polynomial ℝ) (p : ℝ) :
    chromaticTarget (V := V) P p = chromaticTarget (V := V') P p := by
  unfold chromaticTarget
  rw [hcard]

/-- **The common bound transports along an isomorphism.**

This is what lets an Atlas module keep its own edge-list definition while its
proof is supplied by a differently-labelled representative. -/
theorem SatisfiesLowerBound.of_iso [DecidableRel H.Adj] [DecidableRel H'.Adj]
    (φ : H ≃g H') (h : SatisfiesLowerBound H) : SatisfiesLowerBound H' := by
  intro P r hP hr Ω _ μ _ W hp
  have hcard : Fintype.card V = Fintype.card V' := Fintype.card_congr φ.toEquiv
  have hbase := h P r (hP.of_iso φ) (hr.of_iso φ) W hp
  rw [homDensity_iso W φ] at hbase
  rwa [← chromaticTarget_congr_card hcard]

/-- The negative classification transports as well. -/
theorem ViolatesLowerBound.of_iso [DecidableRel H.Adj] [DecidableRel H'.Adj]
    (φ : H ≃g H') (h : ViolatesLowerBound H) : ViolatesLowerBound H' :=
  fun hsat ↦ h (SatisfiesLowerBound.of_iso φ.symm hsat)

end Taeyoung
