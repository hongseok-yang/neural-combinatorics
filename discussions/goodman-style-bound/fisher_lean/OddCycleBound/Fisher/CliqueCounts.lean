import Mathlib

/-!
# Module 1 — Finite graphs and clique counts

Corresponds to `fisher.tex`, §"Graph-theoretic and polynomial preliminaries",
and Module 1 of the Lean blueprint.

We work with `SimpleGraph V` on a `Fintype V` with `DecidableRel G.Adj`.

Objects to define / port from Mathlib:
* `cliqueCount G k := (G.cliqueFinset k).card`  (Mathlib: `SimpleGraph.cliqueFinset`);
  so `c₀ = 1`, `c₁ = n`, `c₂ = e`, `c₃ = T`.
* the complement `Gᶜ` (Mathlib: `SimpleGraph.compl`);
* the induced subgraph on the common neighbourhood of a clique `S`
  (`SimpleGraph.induce` on `⋂_{v∈S} N_G(v) \ S`).

All statements here are pure finite combinatorics.
-/

namespace Fisher

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Number of `k`-cliques of `G` (the empty clique counts, so `cliqueCount 0 = 1`). -/
noncomputable def cliqueCount (k : ℕ) : ℕ := (G.cliqueFinset k).card

/-- The empty vertex set is the unique zero-clique. -/
theorem cliqueCount_zero : cliqueCount G 0 = 1 := by
  classical
  change (G.cliqueFinset 0).card = 1
  rw [show G.cliqueFinset 0 = {∅} by ext s; simp]
  simp

/-- There are no cliques larger than the vertex set. -/
theorem cliqueCount_eq_zero_of_card_lt {k : ℕ} (hk : Fintype.card V < k) :
    cliqueCount G k = 0 := by
  have hle := SimpleGraph.card_cliqueFinset_le (G := G) (n := k)
  rw [Nat.choose_eq_zero_of_lt hk] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- Clique counts are invariant under graph isomorphism. -/
theorem cliqueCount_iso {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (f : G ≃g H) (k : ℕ) :
    cliqueCount G k = cliqueCount H k := by
  classical
  have forward {S : Finset V} (hS : G.IsNClique k S) :
      H.IsNClique k (S.map f.toEquiv.toEmbedding) := by
    refine ⟨?_, (Finset.card_map _).trans hS.card_eq⟩
    intro x hx y hy hxy
    change x ∈ S.map f.toEquiv.toEmbedding at hx
    change y ∈ S.map f.toEquiv.toEmbedding at hy
    rw [Finset.mem_map] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact (SimpleGraph.Iso.map_adj_iff f).2
      (hS.isClique ha hb (fun hab => hxy (congrArg f hab)))
  have backward {S : Finset V}
      (hS : H.IsNClique k (S.map f.toEquiv.toEmbedding)) : G.IsNClique k S := by
    have hback : G.IsNClique k
        ((S.map f.toEquiv.toEmbedding).map f.symm.toEquiv.toEmbedding) := by
      refine ⟨?_, (Finset.card_map _).trans hS.card_eq⟩
      intro x hx y hy hxy
      change x ∈ (S.map f.toEquiv.toEmbedding).map
        f.symm.toEquiv.toEmbedding at hx
      change y ∈ (S.map f.toEquiv.toEmbedding).map
        f.symm.toEquiv.toEmbedding at hy
      rw [Finset.mem_map] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact (SimpleGraph.Iso.map_adj_iff f.symm).2
        (hS.isClique ha hb (fun hab => hxy (congrArg f.symm hab)))
    have hfin : (S.map f.toEquiv.toEmbedding).map
        f.symm.toEquiv.toEmbedding = S := by
      change f.toEquiv.finsetCongr.symm (f.toEquiv.finsetCongr S) = S
      exact f.toEquiv.finsetCongr.symm_apply_apply S
    rw [hfin] at hback
    exact hback
  let eFin : Finset V ≃ Finset W := f.toEquiv.finsetCongr
  let e : {S // S ∈ G.cliqueFinset k} ≃ {T // T ∈ H.cliqueFinset k} :=
    eFin.subtypeEquiv (fun S => by
      simp only [eFin, Equiv.finsetCongr_apply,
        SimpleGraph.mem_cliqueFinset_iff]
      exact ⟨forward, backward⟩)
  change (G.cliqueFinset k).card = (H.cliqueFinset k).card
  calc
    (G.cliqueFinset k).card = Fintype.card {S // S ∈ G.cliqueFinset k} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card {T // T ∈ H.cliqueFinset k} := Fintype.card_congr e
    _ = (H.cliqueFinset k).card := Fintype.card_coe _

/-- Nested induced graphs are canonically isomorphic to induction on the
smaller vertex set directly. -/
def induceSubsetIso {T S : Finset V} (hTS : T ⊆ S) :
    G.induce (↑T : Set V) ≃g
      (G.induce (↑S : Set V)).induce
        (↑(T.subtype fun x => x ∈ S) : Set (↑S : Set V)) where
  toFun x := ⟨⟨x.1, hTS x.2⟩, Finset.mem_subtype.mpr x.2⟩
  invFun x := ⟨x.1.1, Finset.mem_subtype.mp x.2⟩
  left_inv x := rfl
  right_inv x := rfl
  map_rel_iff' := Iff.rfl

/-- Cliques in an induced graph are exactly the ambient cliques contained in
the inducing vertex set. -/
theorem cliqueCount_induce (S : Finset V) (k : ℕ) :
    cliqueCount (G.induce (↑S : Set V)) k =
      ((G.cliqueFinset k).filter fun T ↦ ∀ v ∈ T, v ∈ S).card := by
  classical
  let valEmb : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let emb : Finset S ↪ Finset V :=
    ⟨fun T ↦ T.map valEmb, Finset.map_injective valEmb⟩
  change ((G.induce (↑S : Set V)).cliqueFinset k).card = _
  rw [← Finset.card_map emb]
  congr 1
  ext T
  simp only [Finset.mem_map, SimpleGraph.mem_cliqueFinset_iff, Finset.mem_filter]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(SimpleGraph.isNClique_induce_iff (↑S : Set V) t k).mp ht, ?_⟩
    intro v hv
    exact Finset.map_subtype_subset t hv
  · rintro ⟨hT, hsub⟩
    let t : Finset S := T.subtype (fun v ↦ v ∈ S)
    have htmap : t.map valEmb = T := by
      dsimp [t, valEmb]
      exact Finset.subtype_map_of_mem hsub
    have htmap' : t.map (.subtype fun v ↦ v ∈ (↑S : Set V)) = T := by
      rw [← htmap]
      ext v
      simp [valEmb]
    refine ⟨t, ?_, ?_⟩
    · apply (SimpleGraph.isNClique_induce_iff (↑S : Set V) t k).mpr
      rw [htmap']
      exact hT
    · exact htmap

/-- Removing a distinguished vertex identifies `(k+1)`-cliques containing it
with `k`-cliques in its open neighborhood. -/
theorem cliqueCount_neighbor_eq_filter (v : V) (k : ℕ) :
    cliqueCount (G.induce (↑(G.neighborFinset v) : Set V)) k =
      ((G.cliqueFinset (k + 1)).filter fun T ↦ v ∈ T).card := by
  classical
  rw [cliqueCount_induce]
  apply Finset.card_bij (fun S _ ↦ insert v S)
  · intro S hS
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hS ⊢
    refine ⟨?_, Finset.mem_insert_self v S⟩
    apply hS.1.insert
    intro w hw
    exact (G.mem_neighborFinset v w).mp (hS.2 w hw)
  · intro A hA B hB hAB
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hA hB
    have hvA : v ∉ A := fun hv ↦ G.notMem_neighborFinset_self v (hA.2 v hv)
    have hvB : v ∉ B := fun hv ↦ G.notMem_neighborFinset_self v (hB.2 v hv)
    have := congrArg (fun T : Finset V ↦ T.erase v) hAB
    simpa [hvA, hvB] using this
  · intro T hT
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hT
    refine ⟨T.erase v, ?_, ?_⟩
    · rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
      refine ⟨?_, ?_⟩
      · have herase := hT.1.erase_of_mem hT.2
        simpa using herase
      · intro w hw
        rw [G.mem_neighborFinset]
        exact hT.1.isClique hT.2 (Finset.mem_of_mem_erase hw)
          (Finset.ne_of_mem_erase hw).symm
    · exact Finset.insert_erase hT.2

/-- Incidence double count: summing `k`-cliques over all vertex links counts
each `(k+1)`-clique once for each of its vertices. -/
theorem sum_cliqueCount_neighbor (k : ℕ) :
    ∑ v : V, cliqueCount (G.induce (↑(G.neighborFinset v) : Set V)) k =
      (k + 1) * cliqueCount G (k + 1) := by
  classical
  simp_rw [cliqueCount_neighbor_eq_filter]
  calc
    ∑ v : V, ((G.cliqueFinset (k + 1)).filter fun T ↦ v ∈ T).card =
        ∑ v : V, ∑ T ∈ G.cliqueFinset (k + 1), if v ∈ T then 1 else 0 := by
          congr 1
          funext v
          simp
    _ = ∑ T ∈ G.cliqueFinset (k + 1), ∑ v : V, if v ∈ T then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ T ∈ G.cliqueFinset (k + 1), T.card := by
          apply Finset.sum_congr rfl
          intro T hT
          simp
    _ = ∑ _T ∈ G.cliqueFinset (k + 1), (k + 1) := by
          apply Finset.sum_congr rfl
          intro T hT
          exact (SimpleGraph.mem_cliqueFinset_iff.mp hT).card_eq
    _ = (k + 1) * cliqueCount G (k + 1) := by
          simp [cliqueCount, Nat.mul_comm]

/-- `c₁ = |V|`. -/
theorem cliqueCount_one : cliqueCount G 1 = Fintype.card V := by
  classical
  have hcliques :
      G.cliqueFinset 1 = Finset.univ.image (fun v : V ↦ ({v} : Finset V)) := by
    ext s
    simp only [SimpleGraph.mem_cliqueFinset_iff, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · intro hs
      obtain ⟨v, rfl⟩ := SimpleGraph.isNClique_one.mp hs
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact SimpleGraph.isNClique_one.mpr ⟨v, rfl⟩
  rw [cliqueCount, hcliques,
    Finset.card_image_of_injective _ Finset.singleton_injective, Finset.card_univ]

/-- `c₂ = e`, the edge count. -/
theorem cliqueCount_two : cliqueCount G 2 = G.edgeFinset.card := by
  classical
  have htoFinset : Function.Injective (fun e : Sym2 V ↦ e.toFinset) := by
    intro e f hef
    change e.toFinset = f.toFinset at hef
    apply Sym2.ext
    intro v
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hef]
  have hcliques :
      G.cliqueFinset 2 = G.edgeFinset.image (fun e : Sym2 V ↦ e.toFinset) := by
    ext s
    simp only [SimpleGraph.mem_cliqueFinset_iff, Finset.mem_image]
    constructor
    · intro hs
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs.card_eq
      refine ⟨s(a, b), ?_, Sym2.toFinset_mk_eq⟩
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hs.isClique (by simp) (by simp) hab
    · rintro ⟨e, he, rfl⟩
      induction e using Sym2.inductionOn with
      | _ a b =>
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
          rw [Sym2.toFinset_mk_eq]
          refine ⟨?_, Finset.card_pair he.ne⟩
          simpa [he.ne] using he
  rw [cliqueCount, hcliques, Finset.card_image_of_injective _ htoFinset]

/-- `c₃ = T`, the triangle count. -/
theorem cliqueCount_three : cliqueCount G 3 = (G.cliqueFinset 3).card := rfl

/-- Common neighbourhood of a clique `S` (vertices adjacent to every element of `S`,
excluding `S` itself), as the vertex set of an induced subgraph. -/
noncomputable def commonNbhd (S : Finset V) : Finset V :=
  Finset.univ.filter (fun v => v ∉ S ∧ ∀ w ∈ S, G.Adj v w)

/-- A clique and its common open neighborhood are disjoint. -/
theorem disjoint_commonNbhd (S : Finset V) : Disjoint S (commonNbhd G S) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvS hvN
  rw [commonNbhd, Finset.mem_filter] at hvN
  exact G.loopless.irrefl v (hvN.2.2 v hvS)

/-- For a fixed `j`-clique `S`, adjoining `S` identifies `m`-cliques in
its common neighborhood with `(m+j)`-cliques containing `S`. -/
theorem cliqueCount_commonNbhd_eq_filter {S : Finset V} {j : ℕ}
    (hS : G.IsNClique j S) (m : ℕ) :
    cliqueCount (G.induce (↑(commonNbhd G S) : Set V)) m =
      ((G.cliqueFinset (m + j)).filter fun T ↦ S ⊆ T).card := by
  classical
  rw [cliqueCount_induce]
  apply Finset.card_bij (fun R _ ↦ S ∪ R)
  · intro R hR
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hR ⊢
    refine ⟨?_, Finset.subset_union_left⟩
    have hdis : Disjoint S R :=
      (disjoint_commonNbhd G S).mono_right hR.2
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      rcases Finset.mem_union.mp hx with hxS | hxR <;>
        rcases Finset.mem_union.mp hy with hyS | hyR
      · exact hS.isClique hxS hyS hxy
      · have hyN := hR.2 y hyR
        rw [commonNbhd, Finset.mem_filter] at hyN
        exact (hyN.2.2 x hxS).symm
      · have hxN := hR.2 x hxR
        rw [commonNbhd, Finset.mem_filter] at hxN
        exact hxN.2.2 y hyS
      · exact hR.1.isClique hxR hyR hxy
    · rw [Finset.card_union_of_disjoint hdis, hS.card_eq, hR.1.card_eq]
      omega
  · intro A hA B hB hAB
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hA hB
    have hdisA : Disjoint S A :=
      (disjoint_commonNbhd G S).mono_right hA.2
    have hdisB : Disjoint S B :=
      (disjoint_commonNbhd G S).mono_right hB.2
    have heq := congrArg (fun T : Finset V ↦ T \ S) hAB
    simpa [Finset.union_sdiff_cancel_left hdisA,
      Finset.union_sdiff_cancel_left hdisB] using heq
  · intro T hT
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hT
    refine ⟨T \ S, ?_, ?_⟩
    · rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
      refine ⟨?_, ?_⟩
      · refine ⟨hT.1.isClique.subset (Finset.sdiff_subset), ?_⟩
        rw [Finset.card_sdiff_of_subset hT.2, hT.1.card_eq, hS.card_eq]
        omega
      · intro w hw
        rw [commonNbhd, Finset.mem_filter]
        refine ⟨Finset.mem_univ w, (Finset.mem_sdiff.mp hw).2, ?_⟩
        intro s hs
        have hws : w ≠ s := fun h ↦ (Finset.mem_sdiff.mp hw).2 (h ▸ hs)
        exact hT.1.isClique (Finset.mem_sdiff.mp hw).1
          (Finset.mem_of_subset hT.2 hs) hws
    · exact Finset.union_sdiff_of_subset hT.2

/-- General clique-link incidence count.  A pair consisting of a `j`-clique
and an `m`-clique in its common neighborhood is equivalently an
`(m+j)`-clique together with a choice of `j` of its vertices. -/
theorem sum_cliqueCount_commonNbhd (j m : ℕ) :
    ∑ S ∈ G.cliqueFinset j,
        cliqueCount (G.induce (↑(commonNbhd G S) : Set V)) m =
      (m + j).choose j * cliqueCount G (m + j) := by
  classical
  calc
    ∑ S ∈ G.cliqueFinset j,
        cliqueCount (G.induce (↑(commonNbhd G S) : Set V)) m =
        ∑ S ∈ G.cliqueFinset j,
          ((G.cliqueFinset (m + j)).filter fun T ↦ S ⊆ T).card := by
            apply Finset.sum_congr rfl
            intro S hS
            exact cliqueCount_commonNbhd_eq_filter G
              (SimpleGraph.mem_cliqueFinset_iff.mp hS) m
    _ = ∑ S ∈ G.cliqueFinset j,
          ∑ T ∈ G.cliqueFinset (m + j), (if S ⊆ T then (1 : ℕ) else 0) := by
            apply Finset.sum_congr rfl
            intro S hS
            simp
    _ = ∑ T ∈ G.cliqueFinset (m + j),
          ∑ S ∈ G.cliqueFinset j, (if S ⊆ T then (1 : ℕ) else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ _T ∈ G.cliqueFinset (m + j), (m + j).choose j := by
            apply Finset.sum_congr rfl
            intro T hT
            have hTclique := SimpleGraph.mem_cliqueFinset_iff.mp hT
            have hfilter :
                (G.cliqueFinset j).filter (fun S ↦ S ⊆ T) = T.powersetCard j := by
              ext S
              rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff,
                Finset.mem_powersetCard]
              constructor
              · rintro ⟨hS, hST⟩
                exact ⟨hST, hS.card_eq⟩
              · rintro ⟨hST, hcard⟩
                exact ⟨⟨hTclique.isClique.subset hST, hcard⟩, hST⟩
            calc
              (∑ S ∈ G.cliqueFinset j, (if S ⊆ T then (1 : ℕ) else 0)) =
                  ((G.cliqueFinset j).filter fun S ↦ S ⊆ T).card := by simp
              _ = (T.powersetCard j).card := by rw [hfilter]
              _ = T.card.choose j := Finset.card_powersetCard j T
              _ = (m + j).choose j := by rw [hTclique.card_eq]
    _ = (m + j).choose j * cliqueCount G (m + j) := by
          simp [cliqueCount, Nat.mul_comm]

end Fisher
