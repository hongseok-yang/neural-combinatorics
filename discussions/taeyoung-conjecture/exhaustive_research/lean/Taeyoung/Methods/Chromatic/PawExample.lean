import Taeyoung.Foundation

/-!
# Worked example: the chromatic polynomial of the paw

This is the intended usage pattern for `Foundation/ChromaticExtension.lean`, and
the smoke test that the whole chain composes.  It also produces a result the
`rooted_triangle_tree_extensions` methodology needs: the paw is Atlas 15.

The recipe, which a generator can follow for any graph built by attachment:

1. build the graph as a tower of `attachVertex`s over a clique;
2. give the explicit `Equiv` onto the Atlas labelling and discharge the
   adjacency correspondence by `decide` — this works because `attachVertex`
   goes through `SimpleGraph.fromRel`, whose adjacency is computable;
3. apply `isChromaticPolynomial_of_attachIso` once per attached vertex, with
   `isChromaticPolynomial_top` at the bottom.

No step needs a bespoke counting argument.
-/

open Taeyoung Finset Polynomial

namespace Taeyoung.Methods.Chromatic

/-- Atlas 15, the paw, on its own transparent edge list. -/
def pawGraph : SimpleGraph (Fin 4) :=
  graphFromEdges 4 [(0, 3), (1, 2), (1, 3), (2, 3)]

instance : DecidableRel pawGraph.Adj := graphFromEdges_decidableAdj _ _

/-- `K₃` with one leaf attached at vertex `0`. -/
abbrev pawBuilt : SimpleGraph (Option (Fin 3)) :=
  attachVertex (⊤ : SimpleGraph (Fin 3)) {0}

/-- The relabelling: the new leaf becomes Atlas vertex `0`, and the attachment
point becomes Atlas vertex `3`. -/
def pawEquiv : Option (Fin 3) ≃ Fin 4 where
  toFun a := match a with
    | none => 0
    | some i => ![3, 1, 2] i
  invFun j := ![none, some 1, some 2, some 0] j
  left_inv := by decide
  right_inv := by decide

theorem paw_adj (a b : Option (Fin 3)) :
    pawGraph.Adj (pawEquiv a) (pawEquiv b) ↔ pawBuilt.Adj a b := by
  revert a b
  decide

def pawIso : pawBuilt ≃g pawGraph where
  toEquiv := pawEquiv
  map_rel_iff' := by intro a b; exact paw_adj a b

lemma singleton_isClique :
    (⊤ : SimpleGraph (Fin 3)).IsClique (({0} : Finset (Fin 3)) : Set (Fin 3)) := by
  intro u hu v hv huv
  simpa using huv

/-- The chromatic polynomial of the paw, obtained purely by attachment. -/
theorem paw_chromatic_raw :
    IsChromaticPolynomial pawGraph
      ((X - C ((({0} : Finset (Fin 3))).card : ℝ)) *
        ∏ i ∈ range 3, (X - C (i : ℝ))) :=
  isChromaticPolynomial_of_attachIso pawIso singleton_isClique
    (isChromaticPolynomial_top 3)

/-- **The paw has chromatic polynomial `x(x-1)²(x-2)`.** -/
theorem paw_chromatic :
    IsChromaticPolynomial pawGraph (X * (X - C 1) ^ 2 * (X - C 2)) := by
  have h := paw_chromatic_raw
  simp only [Finset.card_singleton, Nat.cast_one, Finset.prod_range_succ,
    Finset.prod_range_zero, Nat.cast_zero, Nat.cast_ofNat, map_zero, sub_zero,
    one_mul] at h
  have hpoly : (X : ℝ[X]) * (X - C 1) ^ 2 * (X - C 2) =
      (X - C 1) * (X * (X - C 1) * (X - C 2)) := by ring
  rw [hpoly]
  exact h

end Taeyoung.Methods.Chromatic
