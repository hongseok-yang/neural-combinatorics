import Taeyoung.Methods.PureChordal.CliqueMoments
import Taeyoung.Methods.PureChordal.IntegratedCube
import Taeyoung.Foundation.Relabeling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-!
# The graphon Moon--Moser recurrence

The general integrated cube inequality becomes the classical clique recurrence
after using the transitivity of the complete graph on vertices and edges.
-/

open MeasureTheory
open scoped BigOperators

namespace Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Relabel a complete graph with one isolated vertex. -/
def topDeleteIncidenceIso
    {V V' : Type*} (q : V ≃ V') (v : V) :
    (⊤ : SimpleGraph V).deleteIncidenceSet v ≃g
      (⊤ : SimpleGraph V').deleteIncidenceSet (q v) where
  __ := q
  map_rel_iff' := by
    intro a b
    simp [SimpleGraph.deleteIncidenceSet_adj]

/-- Relabel a complete graph with one edge deleted. -/
def topDeleteOneEdgeIso
    {V V' : Type*} [DecidableEq V] [DecidableEq V']
    (q : V ≃ V') (e : Sym2 V) :
    deleteOneEdge (⊤ : SimpleGraph V) e ≃g
      deleteOneEdge (⊤ : SimpleGraph V') (e.map q) where
  __ := q
  map_rel_iff' := by
    intro a b
    simp only [deleteOneEdge, SimpleGraph.deleteEdges_adj,
      SimpleGraph.top_adj, ne_eq, Finset.coe_singleton,
      Set.mem_singleton_iff]
    change
      (q a ≠ q b ∧ s(q a, q b) ≠ e.map q) ↔
        (a ≠ b ∧ s(a, b) ≠ e)
    constructor
    · rintro ⟨hab, hedge⟩
      refine ⟨fun h => hab (congrArg q h), ?_⟩
      intro h
      apply hedge
      calc
        s(q a, q b) = s(a, b).map q := by simp
        _ = e.map q := congrArg (Sym2.map q) h
    · rintro ⟨hab, hedge⟩
      refine ⟨fun h => hab (q.injective h), ?_⟩
      intro h
      apply hedge
      apply Sym2.map.injective q.injective
      simpa using h

/-- The standard decomposition of `Fin (s+2)` into two distinguished
vertices and the remaining `Fin s`. -/
def finTwoEquiv (s : ℕ) :
    Fin (s + 2) ≃ Option (Option (Fin s)) :=
  (finSuccEquiv (s + 1)).trans
    (Equiv.optionCongr (finSuccEquiv s))

@[simp] lemma finTwoEquiv_zero (s : ℕ) :
    finTwoEquiv s (0 : Fin (s + 2)) = none := by
  simp [finTwoEquiv]

@[simp] lemma finTwoEquiv_one (s : ℕ) :
    finTwoEquiv s (1 : Fin (s + 2)) = some none := by
  change finTwoEquiv s (Fin.succ (0 : Fin (s + 1))) = some none
  simp [finTwoEquiv]

/-- A permutation sending a prescribed ordered pair of distinct vertices to
`0,1`. -/
def pairToZeroOnePerm (s : ℕ) (u v : Fin (s + 2)) :
    Equiv.Perm (Fin (s + 2)) :=
  (Equiv.swap u 0).trans
    (Equiv.swap (Equiv.swap u 0 v) 1)

lemma pairToZeroOnePerm_apply_left
    (s : ℕ) {u v : Fin (s + 2)} (huv : u ≠ v) :
    pairToZeroOnePerm s u v u = 0 := by
  have hw0 : Equiv.swap u 0 v ≠ (0 : Fin (s + 2)) := by
    intro h
    have huv' : v = u := (Equiv.swap u 0).injective <| by
      rw [h, Equiv.swap_apply_left]
    exact huv huv'.symm
  rw [pairToZeroOnePerm, Equiv.trans_apply, Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne hw0.symm (by norm_num)

@[simp] lemma pairToZeroOnePerm_apply_right
    (s : ℕ) (u v : Fin (s + 2)) :
    pairToZeroOnePerm s u v v = 1 := by
  rw [pairToZeroOnePerm, Equiv.trans_apply]
  exact Equiv.swap_apply_left _ _

/-- Every vertex-deleted term in the complete graph has the preceding clique
density. -/
theorem homDensity_top_deleteIncidence_fin
    (s : ℕ) (W : Graphon Ω μ) (v : Fin (s + 2)) :
    homDensity ((⊤ : SimpleGraph (Fin (s + 2))).deleteIncidenceSet v) W =
      cliqueDensity (s + 1) W := by
  let q : Fin (s + 2) ≃ Option (Fin (s + 1)) :=
    (Equiv.swap v 0).trans (finSuccEquiv (s + 1))
  have hq : q v = none := by
    simp [q]
  calc
    homDensity ((⊤ : SimpleGraph (Fin (s + 2))).deleteIncidenceSet v) W =
        homDensity
          ((⊤ : SimpleGraph (Option (Fin (s + 1)))).deleteIncidenceSet
            (q v)) W :=
      homDensity_iso W (topDeleteIncidenceIso q v)
    _ = homDensity
          ((⊤ : SimpleGraph (Option (Fin (s + 1)))).deleteIncidenceSet none) W := by
      rw [hq]
    _ = homDensity (⊤ : SimpleGraph (Fin (s + 1))) W :=
      homDensity_top_deleteIncidence_option W
    _ = cliqueDensity (s + 1) W := rfl

/-- Every edge-deleted term in `K_{s+2}` is the same conditional second
moment. -/
theorem homDensity_top_deleteOneEdge_fin
    (s : ℕ) (W : Graphon Ω μ)
    (e : Sym2 (Fin (s + 2)))
    (he : e ∈ (⊤ : SimpleGraph (Fin (s + 2))).edgeFinset) :
    homDensity (deleteOneEdge (⊤ : SimpleGraph (Fin (s + 2))) e) W =
      cliqueExtensionSecondMoment (α := Fin s) W := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : u ≠ v := by
        simpa [SimpleGraph.mem_edgeFinset] using he
      let p := pairToZeroOnePerm s u v
      let q : Fin (s + 2) ≃ Option (Option (Fin s)) :=
        p.trans (finTwoEquiv s)
      have hqu : q u = none := by
        simp [q, p, pairToZeroOnePerm_apply_left s huv]
      have hqv : q v = some none := by
        simp [q, p]
      have hedge : s(u, v).map q = s(none, some none) := by
        simp [hqu, hqv]
      calc
        homDensity
            (deleteOneEdge (⊤ : SimpleGraph (Fin (s + 2))) s(u, v)) W =
          homDensity
            (deleteOneEdge (⊤ : SimpleGraph (Option (Option (Fin s))))
              (s(u, v).map q)) W :=
          homDensity_iso W (topDeleteOneEdgeIso q s(u, v))
        _ = homDensity (twoExtensionGraph (Fin s)) W := by
          rw [hedge]
        _ = cliqueExtensionSecondMoment (α := Fin s) W :=
          homDensity_twoExtension_eq_secondMoment W

/-- The integrated cube inequality for a clique, after all symmetric terms
have been collected. -/
theorem clique_secondMoment_cube_bound
    (s : ℕ) (W : Graphon Ω μ) :
    (s + 1 : ℝ) * cliqueExtensionSecondMoment (α := Fin s) W ≤
      cliqueDensity (s + 1) W +
        s * cliqueDensity (s + 2) W := by
  let K : SimpleGraph (Fin (s + 2)) := ⊤
  have h := integrated_graph_edge_cube_inequality K W
  have hedge :
      ∑ e ∈ K.edgeFinset, homDensity (deleteOneEdge K e) W =
        K.edgeFinset.card *
          cliqueExtensionSecondMoment (α := Fin s) W := by
    calc
      ∑ e ∈ K.edgeFinset, homDensity (deleteOneEdge K e) W =
          ∑ _e ∈ K.edgeFinset,
            cliqueExtensionSecondMoment (α := Fin s) W := by
        apply Finset.sum_congr rfl
        intro e he
        exact homDensity_top_deleteOneEdge_fin s W e
          (by simpa [K] using he)
      _ = K.edgeFinset.card *
          cliqueExtensionSecondMoment (α := Fin s) W := by simp
  have hvertex :
      ∑ v : Fin (s + 2), homDensity (K.deleteIncidenceSet v) W =
        (s + 2) * cliqueDensity (s + 1) W := by
    simp_rw [show ∀ v : Fin (s + 2),
        homDensity (K.deleteIncidenceSet v) W =
          cliqueDensity (s + 1) W by
      intro v
      simpa [K] using homDensity_top_deleteIncidence_fin s W v]
    simp
  have hcomplete :
      homDensity K W = cliqueDensity (s + 2) W := by
    rfl
  rw [hedge, hvertex, hcomplete] at h
  have hcard :
      (K.edgeFinset.card : ℝ) =
        ((s + 2 : ℝ) * (s + 1 : ℝ)) / 2 := by
    rw [show K.edgeFinset.card = (s + 2).choose 2 by
      simpa [K] using
        (SimpleGraph.card_edgeFinset_top_eq_card_choose_two
          (V := Fin (s + 2)))]
    rw [Nat.cast_choose_two (K := ℝ)]
    push_cast
    ring
  have hvertices : (Fintype.card (Fin (s + 2)) : ℝ) = s + 2 := by
    simp
  rw [hcard, hvertices] at h
  have hs2 : (0 : ℝ) < s + 2 := by positivity
  nlinarith

/-- Moon--Moser's clique-density recurrence, indexed so that the middle
clique has `s+1` vertices. -/
theorem cliqueDensity_moonMoser_succ
    (s : ℕ) (W : Graphon Ω μ) :
    (s + 1 : ℝ) * cliqueDensity (s + 1) W ^ 2 ≤
      cliqueDensity s W * cliqueDensity (s + 1) W +
        s * cliqueDensity s W * cliqueDensity (s + 2) W := by
  have hcs :=
    cliqueDensity_sq_le_cliqueDensity_mul_secondMoment s W
  have hcube := clique_secondMoment_cube_bound s W
  calc
    (s + 1 : ℝ) * cliqueDensity (s + 1) W ^ 2 ≤
        (s + 1 : ℝ) *
          (cliqueDensity s W *
            cliqueExtensionSecondMoment (α := Fin s) W) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = cliqueDensity s W *
        ((s + 1 : ℝ) *
          cliqueExtensionSecondMoment (α := Fin s) W) := by ring
    _ ≤ cliqueDensity s W *
        (cliqueDensity (s + 1) W +
          s * cliqueDensity (s + 2) W) :=
      mul_le_mul_of_nonneg_left hcube (cliqueDensity_nonneg s W)
    _ = cliqueDensity s W * cliqueDensity (s + 1) W +
        s * cliqueDensity s W * cliqueDensity (s + 2) W := by ring

end Taeyoung.Methods.PureChordal
