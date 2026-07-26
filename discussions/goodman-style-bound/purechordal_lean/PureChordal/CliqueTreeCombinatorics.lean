import PureChordal.Certificate
import PureChordal.HomDensity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite edge bookkeeping for a rooted clique tree
-/

open scoped BigOperators

namespace PureChordal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Unordered non-diagonal pairs whose two endpoints lie in `A`. -/
def pairsIn (A : Finset V) : Finset (Sym2 V) :=
  (⊤ : SimpleGraph V).edgeFinset.filter
    (fun e => ∀ v ∈ e, v ∈ A)

lemma mk_mem_pairsIn {A : Finset V} {u v : V} :
    s(u, v) ∈ pairsIn A ↔ u ≠ v ∧ u ∈ A ∧ v ∈ A := by
  simp [pairsIn, SimpleGraph.mem_edgeFinset, Sym2.mem_iff, and_assoc]

namespace PureCliqueTreeDecomp

variable {H : SimpleGraph V} [DecidableRel H.Adj] {r m : ℕ}
  (D : PureCliqueTreeDecomp H r m)

/-- All unordered pairs already present together in an earlier bag. -/
def previousPairs (i : Fin m) : Finset (Sym2 V) :=
  (Finset.univ.filter fun j : Fin m => j.val < i.val).biUnion
    (fun j => pairsIn (D.bag j))

/-- The overlap between the pairs in the current bag and all earlier bag
pairs is exactly the complete pair set of the parent separator. -/
theorem pairsIn_bag_inter_previousPairs (i : Fin m) :
    pairsIn (D.bag i) ∩ D.previousPairs i =
      pairsIn (D.separator i) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [Finset.mem_inter, mk_mem_pairsIn]
      constructor
      · rintro ⟨⟨huv, hui, hvi⟩, heprev⟩
        rw [previousPairs, Finset.mem_biUnion] at heprev
        rcases heprev with ⟨j, hj, heij⟩
        have hjlt : j.val < i.val := (Finset.mem_filter.mp hj).2
        rw [mk_mem_pairsIn] at heij
        have huPrev : u ∈ D.previousVertices i := by
          rw [previousVertices, Finset.mem_biUnion]
          exact ⟨j, hj, heij.2.1⟩
        have hvPrev : v ∈ D.previousVertices i := by
          rw [previousVertices, Finset.mem_biUnion]
          exact ⟨j, hj, heij.2.2⟩
        have huSep : u ∈ D.separator i := by
          rw [← D.bag_inter_previous_eq_separator i]
          exact Finset.mem_inter.mpr ⟨hui, huPrev⟩
        have hvSep : v ∈ D.separator i := by
          rw [← D.bag_inter_previous_eq_separator i]
          exact Finset.mem_inter.mpr ⟨hvi, hvPrev⟩
        exact ⟨huv, huSep, hvSep⟩
      · rintro ⟨huv, huSep, hvSep⟩
        have hui := D.separator_subset_bag i huSep
        have hvi := D.separator_subset_bag i hvSep
        refine ⟨⟨huv, hui, hvi⟩, ?_⟩
        by_cases hi : i = D.root
        · subst i
          simpa using huSep
        · rw [previousPairs, Finset.mem_biUnion]
          refine ⟨D.parent i, ?_, ?_⟩
          · exact Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, D.parent_lt i hi⟩
          · rw [mk_mem_pairsIn]
            rw [D.separator_of_ne_root hi] at huSep hvSep
            exact ⟨huv, (Finset.mem_inter.mp huSep).2,
              (Finset.mem_inter.mp hvSep).2⟩

/-- The union of complete pair sets of all bags is exactly the edge set of
the graph certified by the decomposition. -/
theorem biUnion_pairsIn_bag :
    (Finset.univ : Finset (Fin m)).biUnion
        (fun i => pairsIn (D.bag i)) =
      H.edgeFinset := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      constructor
      · intro he
        rw [Finset.mem_biUnion] at he
        rcases he with ⟨i, hi, hebag⟩
        rw [mk_mem_pairsIn] at hebag
        rw [SimpleGraph.mem_edgeFinset]
        exact D.bag_clique i hebag.2.1 hebag.2.2 hebag.1
      · intro he
        have hadj : H.Adj u v := by
          simpa [SimpleGraph.mem_edgeFinset] using he
        rcases D.edge_cover hadj with ⟨i, hui, hvi⟩
        rw [Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ _, mk_mem_pairsIn.mpr
          ⟨hadj.ne, hui, hvi⟩⟩

private def bagIndicesBefore
    (D : PureCliqueTreeDecomp H r m) (n : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => i.val < n

private def accumulatedPairs
    (D : PureCliqueTreeDecomp H r m) (n : ℕ) : Finset (Sym2 V) :=
  (D.bagIndicesBefore n).biUnion fun i => pairsIn (D.bag i)

private lemma bagIndicesBefore_succ
    {n : ℕ} (hn : n < m) :
    D.bagIndicesBefore (n + 1) =
      insert (⟨n, hn⟩ : Fin m) (D.bagIndicesBefore n) := by
  ext j
  simp only [bagIndicesBefore, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · intro hj
    by_cases heq : j.val = n
    · exact Or.inl (Fin.ext heq)
    · exact Or.inr (by omega)
  · rintro (hji | hj)
    · subst j
      simp
    · omega

private lemma index_not_mem_before {n : ℕ} (hn : n < m) :
    (⟨n, hn⟩ : Fin m) ∉ D.bagIndicesBefore n := by
  simp [bagIndicesBefore]

private lemma accumulatedPairs_succ
    {n : ℕ} (hn : n < m) :
    D.accumulatedPairs (n + 1) =
      pairsIn (D.bag ⟨n, hn⟩) ∪ D.accumulatedPairs n := by
  unfold accumulatedPairs
  rw [D.bagIndicesBefore_succ hn]
  simp

private lemma previousPairs_eq_accumulated
    (i : Fin m) :
    D.previousPairs i = D.accumulatedPairs i.val := by
  rfl

private theorem prod_pairsIn_bags_before
    {M : Type*} [CommMonoid M] (f : Sym2 V → M)
    (n : ℕ) (hn : n ≤ m) :
    (∏ i ∈ D.bagIndicesBefore n,
        ∏ e ∈ pairsIn (D.bag i), f e) =
      (∏ e ∈ D.accumulatedPairs n, f e) *
        ∏ i ∈ D.bagIndicesBefore n,
          ∏ e ∈ pairsIn (D.separator i), f e := by
  induction n with
  | zero =>
      simp [bagIndicesBefore, accumulatedPairs]
  | succ n ih =>
      have hnlt : n < m := by omega
      let i : Fin m := ⟨n, hnlt⟩
      have hindex :
          D.bagIndicesBefore (n + 1) =
            insert i (D.bagIndicesBefore n) :=
        D.bagIndicesBefore_succ hnlt
      have hinot : i ∉ D.bagIndicesBefore n :=
        D.index_not_mem_before hnlt
      have hacc :
          D.accumulatedPairs (n + 1) =
            pairsIn (D.bag i) ∪ D.accumulatedPairs n :=
        D.accumulatedPairs_succ hnlt
      have hinter :
          pairsIn (D.bag i) ∩ D.accumulatedPairs n =
            pairsIn (D.separator i) := by
        rw [← D.previousPairs_eq_accumulated i]
        exact D.pairsIn_bag_inter_previousPairs i
      have hih := ih (by omega)
      rw [hindex, Finset.prod_insert hinot, Finset.prod_insert hinot,
        hacc, hih]
      have hui := Finset.prod_union_inter
        (s₁ := pairsIn (D.bag i))
        (s₂ := D.accumulatedPairs n) (f := f)
      rw [hinter] at hui
      calc
        (∏ e ∈ pairsIn (D.bag i), f e) *
            ((∏ e ∈ D.accumulatedPairs n, f e) *
              ∏ j ∈ D.bagIndicesBefore n,
                ∏ e ∈ pairsIn (D.separator j), f e) =
            ((∏ e ∈ D.accumulatedPairs n, f e) *
              ∏ e ∈ pairsIn (D.bag i), f e) *
              ∏ j ∈ D.bagIndicesBefore n,
                ∏ e ∈ pairsIn (D.separator j), f e := by
          ac_rfl
        _ = ((∏ e ∈ pairsIn (D.bag i) ∪ D.accumulatedPairs n, f e) *
              ∏ e ∈ pairsIn (D.separator i), f e) *
              ∏ j ∈ D.bagIndicesBefore n,
                ∏ e ∈ pairsIn (D.separator j), f e := by
          rw [hui]
          ac_rfl
        _ = (∏ e ∈ pairsIn (D.bag i) ∪ D.accumulatedPairs n, f e) *
              ((∏ e ∈ pairsIn (D.separator i), f e) *
                ∏ j ∈ D.bagIndicesBefore n,
                  ∏ e ∈ pairsIn (D.separator j), f e) := by
          ac_rfl

/-- Abstract multiplicity identity for any commutative family of edge
weights. -/
theorem prod_pairsIn_bags
    {M : Type*} [CommMonoid M] (f : Sym2 V → M) :
    (∏ i : Fin m, ∏ e ∈ pairsIn (D.bag i), f e) =
      (∏ e ∈ H.edgeFinset, f e) *
        ∏ i : Fin m, ∏ e ∈ pairsIn (D.separator i), f e := by
  have h :=
    D.prod_pairsIn_bags_before f m (le_refl m)
  have hindex :
      D.bagIndicesBefore m = (Finset.univ : Finset (Fin m)) := by
    ext i
    simp [bagIndicesBefore, i.isLt]
  have hacc :
      D.accumulatedPairs m = H.edgeFinset := by
    unfold accumulatedPairs
    rw [hindex]
    exact D.biUnion_pairsIn_bag
  simpa [hindex, hacc] using h

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]

/-- Complete-pair weight on an arbitrary finite vertex set. -/
def cliqueWeightOn (A : Finset V) (W : Graphon Ω μ) (x : V → Ω) : ℝ :=
  ∏ e ∈ pairsIn A, edgeValue W x e

/-- Pointwise edge-weight multiplicity identity `(EW)`. -/
theorem prod_cliqueWeightOn_bags
    (W : Graphon Ω μ) (x : V → Ω) :
    (∏ i : Fin m, cliqueWeightOn (D.bag i) W x) =
      graphWeight H W x *
        ∏ i : Fin m, cliqueWeightOn (D.separator i) W x := by
  simpa [cliqueWeightOn, graphWeight] using
    D.prod_pairsIn_bags (fun e => edgeValue W x e)

end PureCliqueTreeDecomp

end PureChordal
