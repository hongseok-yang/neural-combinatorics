import Taeyoung.Methods.RootedSOS.GraphCanonical
import Taeyoung.Foundation.DisjointUnion
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.List.GetD

/-!
# Removing isolated edge components at fixed edge density

The exact rooted certificates group an ordinary graph together with any
isolated `K₂` components.  This file gives the executable normalization used
for five-vertex products.  A permutation puts zero, one, or two isolated edge
components at the end; deleting those standard edges leaves a canonical core.
-/

open Finset

namespace Taeyoung.Methods.RootedSOS

open Taeyoung

/-- Executable degree on a five-vertex graph.  This deliberately scans the
five possible neighbours instead of going through `SimpleGraph.edgeFinset`;
the direct representation kernel-reduces well in the certificate audits. -/
def degreeFin5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (v : Fin 5) : ℕ :=
  (Finset.univ.filter fun w ↦ G.Adj v w).card

/-- An ordered pair `u < v` represents an isolated `K₂` component when its
two vertices are adjacent and both have degree one. -/
def isIsolatedEdgePairFin5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (u v : Fin 5) : Bool :=
  decide (u < v) && decide (G.Adj u v) &&
    decide (degreeFin5 G u = 1) && decide (degreeFin5 G v = 1)

/-- Number of isolated `K₂` components of a five-vertex graph.  Each edge is
counted exactly once by orienting its endpoints with `u < v`. -/
def isolatedEdgeCountFin5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] : ℕ :=
  ((Finset.univ.product Finset.univ).filter fun uv ↦
    isIsolatedEdgePairFin5 G uv.1 uv.2 = true).card

/-- The graph induced on the first three vertices. -/
def frontGraph3 (R : SimpleGraph (Fin 5)) [DecidableRel R.Adj] :
    SimpleGraph (Fin 3) :=
  R.comap (Fin.castAdd 2)

instance frontGraph3_decidableAdj (R : SimpleGraph (Fin 5))
    [DecidableRel R.Adj] : DecidableRel (frontGraph3 R).Adj := by
  unfold frontGraph3
  infer_instance

/-- The graph induced on the first vertex. -/
def frontGraph1 (R : SimpleGraph (Fin 5)) [DecidableRel R.Adj] :
    SimpleGraph (Fin 1) :=
  R.comap (Fin.castAdd 4)

instance frontGraph1_decidableAdj (R : SimpleGraph (Fin 5))
    [DecidableRel R.Adj] : DecidableRel (frontGraph1 R).Adj := by
  unfold frontGraph1
  infer_instance

/-- Standard decomposition with one final isolated edge. -/
def standardOneEdge (R : SimpleGraph (Fin 5)) [DecidableRel R.Adj] :
    SimpleGraph (Fin 5) :=
  disjointUnion (frontGraph3 R) (⊤ : SimpleGraph (Fin 2))

instance standardOneEdge_decidableAdj (R : SimpleGraph (Fin 5))
    [DecidableRel R.Adj] : DecidableRel (standardOneEdge R).Adj := by
  unfold standardOneEdge
  infer_instance

/-- Standard decomposition with two final isolated edges. -/
def standardTwoEdges (R : SimpleGraph (Fin 5)) [DecidableRel R.Adj] :
    SimpleGraph (Fin 5) :=
  disjointUnion
    (disjointUnion (frontGraph1 R) (⊤ : SimpleGraph (Fin 2)))
    (⊤ : SimpleGraph (Fin 2))

instance standardTwoEdges_decidableAdj (R : SimpleGraph (Fin 5))
    [DecidableRel R.Adj] : DecidableRel (standardTwoEdges R).Adj := by
  unfold standardTwoEdges
  infer_instance

/-- Whether a relabelled graph has the requested standard decomposition. -/
def isStandardDecomposition (R : SimpleGraph (Fin 5)) [DecidableRel R.Adj]
    (m : ℕ) : Bool :=
  match m with
  | 0 => true
  | 1 => adjacencyCode R == adjacencyCode (standardOneEdge R)
  | 2 => adjacencyCode R == adjacencyCode (standardTwoEdges R)
  | _ => false

/-- Relabel a graph by reading old vertices from a five-entry list.  Lists
coming from `List.permutations` are genuine permutations; the fallback is only
used to keep this evaluator total on arbitrary input. -/
def relabelCodeByList (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (l : List (Fin 5)) : AdjacencyCode 5 :=
  List.ofFn fun i ↦ List.ofFn fun j ↦
    decide (G.Adj (l.getD i.1 i) (l.getD j.1 j))

/-- The five vertices in their natural order, represented without a finite-set
quotient so that closed certificate checks kernel-reduce. -/
def vertexListFin5 : List (Fin 5) :=
  List.ofFn fun i : Fin 5 ↦ i

/-- Isolated edges, oriented by their naturally ordered endpoints. -/
def isolatedEdgePairsFin5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] :
    List (Fin 5 × Fin 5) :=
  vertexListFin5.flatMap fun u ↦
    (vertexListFin5.filter fun v ↦ isIsolatedEdgePairFin5 G u v).map
      fun v ↦ (u, v)

/-- The vertices lying in isolated-edge components. -/
def isolatedEdgeVerticesFin5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] :
    List (Fin 5) :=
  (isolatedEdgePairsFin5 G).flatMap fun uv ↦ [uv.1, uv.2]

/-- Deterministic relabelling order: all core vertices first, followed by the
two endpoints of each isolated edge. -/
def decompositionVerticesFin5 (G : SimpleGraph (Fin 5))
    [DecidableRel G.Adj] : List (Fin 5) :=
  (vertexListFin5.filter fun v ↦ !(isolatedEdgeVerticesFin5 G).contains v) ++
    isolatedEdgeVerticesFin5 G

/-- The deterministic relabelled code displaying all isolated edges at the
end of the vertex order. -/
def decompositionCode (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (_m : ℕ) : AdjacencyCode 5 :=
  relabelCodeByList G (decompositionVerticesFin5 G)

/-- Relabelled representative selected by `decompositionCode`. -/
def decomposedGraph (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (m : ℕ) : SimpleGraph (Fin 5) :=
  graphOfCode (decompositionCode G m)

instance decomposedGraph_decidableAdj (G : SimpleGraph (Fin 5))
    [DecidableRel G.Adj] (m : ℕ) : DecidableRel (decomposedGraph G m).Adj := by
  unfold decomposedGraph
  infer_instance

/-- The relabelled core after deleting the standardized isolated edges. -/
def strippedGraphFin5 (R : SimpleGraph (Fin 5)) [DecidableRel R.Adj]
    (m : ℕ) : SimpleGraph (Fin 5) :=
  match m with
  | 0 => R
  | 1 => R.deleteEdges ↑({s(3, 4)} : Finset (Sym2 (Fin 5)))
  | 2 => R.deleteEdges ↑({s(1, 2), s(3, 4)} : Finset (Sym2 (Fin 5)))
  | _ => R

instance strippedGraphFin5_decidableAdj (R : SimpleGraph (Fin 5))
    [DecidableRel R.Adj] (m : ℕ) : DecidableRel (strippedGraphFin5 R m).Adj := by
  cases m with
  | zero =>
      change DecidableRel R.Adj
      infer_instance
  | succ m =>
      cases m with
      | zero =>
          change DecidableRel (R.deleteEdges
            ↑({s(3, 4)} : Finset (Sym2 (Fin 5)))).Adj
          infer_instance
      | succ m =>
          cases m with
          | zero =>
              change DecidableRel (R.deleteEdges
                ↑({s(1, 2), s(3, 4)} : Finset (Sym2 (Fin 5)))).Adj
              infer_instance
          | succ m =>
              change DecidableRel R.Adj
              infer_instance

def fixedCoreGraphFin5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] :
    SimpleGraph (Fin 5) :=
  let m := isolatedEdgeCountFin5 G
  let R := decomposedGraph G m
  graphOfCode (adjacencyCode (strippedGraphFin5 R m))

instance fixedCoreGraphFin5_decidableAdj (G : SimpleGraph (Fin 5))
    [DecidableRel G.Adj] : DecidableRel (fixedCoreGraphFin5 G).Adj := by
  unfold fixedCoreGraphFin5
  infer_instance

/-- Fixed-density key: canonical core plus the number of removed `K₂`s. -/
def fixedDensityKeyFin5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] :
    AdjacencyCode 5 × ℕ :=
  (canonicalCode (fixedCoreGraphFin5 G), isolatedEdgeCountFin5 G)

/-- The selected permutation really displays the requested decomposition. -/
def decompositionValid (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] : Bool :=
  let m := isolatedEdgeCountFin5 G
  let l := decompositionVerticesFin5 G
  decide (l.length = 5) && decide l.Nodup &&
    decide (m ≤ 2) && isStandardDecomposition (decomposedGraph G m) m

private theorem edgeSet_disjointUnion {m n : ℕ}
    (H₁ : SimpleGraph (Fin m)) (H₂ : SimpleGraph (Fin n)) :
    (disjointUnion H₁ H₂).edgeSet =
      (Sym2.map (Fin.castAdd n) '' H₁.edgeSet) ∪
        (Sym2.map (Fin.natAdd m) '' H₂.edgeSet) := by
  rw [disjointUnion, SimpleGraph.edgeSet_sup]
  change
    (H₁.map (⟨Fin.castAdd n, Fin.castAdd_injective m n⟩ :
      Fin m ↪ Fin (m + n))).edgeSet ∪
      (H₂.map (⟨Fin.natAdd m, Fin.natAdd_injective n m⟩ :
        Fin n ↪ Fin (m + n))).edgeSet = _
  rw [
    SimpleGraph.edgeSet_map
      ⟨Fin.castAdd n, Fin.castAdd_injective m n⟩,
    SimpleGraph.edgeSet_map
      ⟨Fin.natAdd m, Fin.natAdd_injective n m⟩]
  rfl

private theorem strippedGraphFin5_one_of_standard
    (R : SimpleGraph (Fin 5)) [DecidableRel R.Adj]
    (h : isStandardDecomposition R 1 = true) :
    strippedGraphFin5 R 1 = (frontGraph3 R).map (Fin.castAdd 2) := by
  have hR : R = standardOneEdge R := by
    apply (adjacencyCode_eq_iff R (standardOneEdge R)).mp
    simpa [isStandardDecomposition] using h
  let A := (frontGraph3 R).map (Fin.castAdd 2)
  let E := (⊤ : SimpleGraph (Fin 2)).map (Fin.natAdd 3)
  let s₀ : Set (Sym2 (Fin 5)) :=
    ↑({s(3, 4)} : Finset (Sym2 (Fin 5)))
  have hEfin : E.edgeFinset = {s(3, 4)} := by
    dsimp [E]
    rw [edgeFinset_map_eq_image (⊤ : SimpleGraph (Fin 2))
      (Fin.natAdd_injective 2 3)]
    decide +kernel
  have hs : s₀ = E.edgeSet := by
    ext e
    simp only [s₀, Finset.mem_coe, Finset.mem_singleton]
    rw [← SimpleGraph.mem_edgeFinset, hEfin]
    simp
  have hdisj : Disjoint A E := by
    rw [← SimpleGraph.disjoint_edgeFinset]
    dsimp [A, E]
    rw [edgeFinset_map_eq_image (frontGraph3 R)
      (Fin.castAdd_injective 3 2),
      edgeFinset_map_eq_image (⊤ : SimpleGraph (Fin 2))
        (Fin.natAdd_injective 2 3)]
    exact disjoint_blocks (frontGraph3 R) (⊤ : SimpleGraph (Fin 2))
  have hA : A.deleteEdges s₀ = A := by
    rw [SimpleGraph.deleteEdges_eq_self, hs,
      SimpleGraph.disjoint_edgeSet]
    exact hdisj
  have hE : E.deleteEdges s₀ = ⊥ := by
    rw [hs, SimpleGraph.deleteEdges_edgeSet]
    exact sdiff_self
  simp only [strippedGraphFin5]
  change R.deleteEdges s₀ = A
  unfold standardOneEdge at hR
  change R = A ⊔ E at hR
  rw [hR, SimpleGraph.deleteEdges_sup, hA, hE, sup_bot_eq]

private theorem standardTwoEdges_edgeSet (R : SimpleGraph (Fin 5))
    [DecidableRel R.Adj] :
    (standardTwoEdges R).edgeSet =
      (↑({s(1, 2), s(3, 4)} : Finset (Sym2 (Fin 5))) :
        Set (Sym2 (Fin 5))) := by
  have hfront : frontGraph1 R = ⊥ := by
    ext i j
    fin_cases i
    fin_cases j
    simp [frontGraph1]
  have htopFin : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by
    decide +kernel
  have htop : (⊤ : SimpleGraph (Fin 2)).edgeSet = {s(0, 1)} := by
    ext e
    rw [← SimpleGraph.mem_edgeFinset, htopFin]
    simp
  unfold standardTwoEdges
  rw [edgeSet_disjointUnion, edgeSet_disjointUnion, hfront, htop]
  ext e
  simp [Sym2.map_mk, or_comm]

private theorem strippedGraphFin5_two_of_standard
    (R : SimpleGraph (Fin 5)) [DecidableRel R.Adj]
    (h : isStandardDecomposition R 2 = true) :
    strippedGraphFin5 R 2 = ⊥ := by
  have hR : R = standardTwoEdges R := by
    apply (adjacencyCode_eq_iff R (standardTwoEdges R)).mp
    simpa [isStandardDecomposition] using h
  let s₀ : Set (Sym2 (Fin 5)) :=
    ↑({s(1, 2), s(3, 4)} : Finset (Sym2 (Fin 5)))
  have hs : s₀ = (standardTwoEdges R).edgeSet :=
    (standardTwoEdges_edgeSet R).symm
  simp only [strippedGraphFin5]
  change R.deleteEdges s₀ = ⊥
  rw [hR, hs, SimpleGraph.deleteEdges_edgeSet]
  exact sdiff_self

/-- Adding only isolated vertices and no edges has density one. -/
theorem homDensity_bot_fin
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (W : Graphon Ω μ) :
    homDensity (⊥ : SimpleGraph (Fin n)) W = 1 := by
  have hweight : ∀ x : Fin n → Ω,
      graphWeight (⊥ : SimpleGraph (Fin n)) W x = 1 := by
    intro x
    rw [graphWeight]
    apply Finset.prod_eq_one
    intro e he
    exfalso
    simpa using he
  rw [homDensity, MeasureTheory.integral_congr_ae
    (MeasureTheory.ae_of_all _ hweight)]
  simp

private theorem homDensity_graph_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (H K : SimpleGraph (Fin n)) [dH : DecidableRel H.Adj]
    [dK : DecidableRel K.Adj]
    (W : Graphon Ω μ) (h : H = K) :
    homDensity H W = homDensity K W := by
  subst K
  have hd : dH = dK := Subsingleton.elim _ _
  subst dK
  rfl

private theorem homDensity_standardOneEdge
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (R : SimpleGraph (Fin 5)) [DecidableRel R.Adj] (W : Graphon Ω μ) :
    homDensity (standardOneEdge R) W =
      homDensity (frontGraph3 R) W * cliqueDensity 2 W := by
  change homDensity (disjointUnion (frontGraph3 R)
    (⊤ : SimpleGraph (Fin 2))) W = _
  exact homDensity_disjointUnion (frontGraph3 R)
    (⊤ : SimpleGraph (Fin 2)) W

private theorem homDensity_standardTwoEdges
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (R : SimpleGraph (Fin 5)) [DecidableRel R.Adj] (W : Graphon Ω μ) :
    homDensity (standardTwoEdges R) W = cliqueDensity 2 W ^ 2 := by
  have hfront : frontGraph1 R = (⊤ : SimpleGraph (Fin 1)) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [frontGraph1]
  change homDensity (disjointUnion
    (disjointUnion (frontGraph1 R) (⊤ : SimpleGraph (Fin 2)))
    (⊤ : SimpleGraph (Fin 2))) W = _
  rw [homDensity_disjointUnion, homDensity_disjointUnion]
  have hdfront : homDensity (frontGraph1 R) W = 1 := by
    simpa [hfront, cliqueDensity] using cliqueDensity_one W
  rw [hdfront]
  simp only [cliqueDensity]
  ring

private theorem list_ofFn_getD_eq (l : List (Fin 5)) (hlen : l.length = 5) :
    List.ofFn (fun i : Fin 5 ↦ l.getD i.1 i) = l := by
  apply List.ext_get
  · simp [hlen]
  · intro n hn₁ hn₂
    rw [List.get_ofFn, List.getD_eq_getElem]
    · simp
    · omega

/-- Reading the old vertices from any five-entry duplicate-free list is a
vertex relabelling, so decoding its adjacency code preserves density. -/
theorem homDensity_relabelCodeByList
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (l : List (Fin 5)) (hlen : l.length = 5) (hnodup : l.Nodup)
    (W : Graphon Ω μ) :
    homDensity G W = homDensity (graphOfCode (relabelCodeByList G l)) W := by
  let f : Fin 5 → Fin 5 := fun i ↦ l.getD i.1 i
  have hlf : List.ofFn f = l := list_ofFn_getD_eq l hlen
  have hfnodup : (List.ofFn f).Nodup := by
    rw [hlf]
    exact hnodup
  have hf : Function.Injective f := List.nodup_ofFn.mp hfnodup
  let e : Fin 5 ≃ Fin 5 := Equiv.ofBijective f hf.bijective_of_finite
  have hgraph : graphOfCode (relabelCodeByList G l) = G.comap f := by
    change graphOfCode (adjacencyCode (G.comap f)) = G.comap f
    exact graphOfCode_adjacencyCode _
  have he : (e : Fin 5 → Fin 5) = f := rfl
  simpa only [hgraph, he] using
    homDensity_iso W (SimpleGraph.Iso.comap e G).symm

/-- A successful decomposition check certifies that the deterministic vertex
list is a genuine permutation of `Fin 5`. -/
theorem decompositionValid_vertices (G : SimpleGraph (Fin 5))
    [DecidableRel G.Adj] (h : decompositionValid G = true) :
    (decompositionVerticesFin5 G).length = 5 ∧
      (decompositionVerticesFin5 G).Nodup := by
  simp only [decompositionValid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- The deterministic decomposition is only a vertex relabelling, so it
preserves homomorphism density. -/
theorem homDensity_decomposedGraph_of_valid
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (W : Graphon Ω μ) (h : decompositionValid G = true) :
    homDensity G W =
      homDensity (decomposedGraph G (isolatedEdgeCountFin5 G)) W := by
  let l := decompositionVerticesFin5 G
  let f : Fin 5 → Fin 5 := fun i ↦ l.getD i.1 i
  have hl := decompositionValid_vertices G h
  have hlf : List.ofFn f = l := by
    exact list_ofFn_getD_eq l hl.1
  have hfnodup : (List.ofFn f).Nodup := by
    rw [hlf]
    exact hl.2
  have hf : Function.Injective f := List.nodup_ofFn.mp hfnodup
  let e : Fin 5 ≃ Fin 5 := Equiv.ofBijective f hf.bijective_of_finite
  have hgraph : decomposedGraph G (isolatedEdgeCountFin5 G) = G.comap f := by
    change graphOfCode (relabelCodeByList G l) = G.comap f
    change graphOfCode (adjacencyCode (G.comap f)) = G.comap f
    exact graphOfCode_adjacencyCode _
  have he : (e : Fin 5 → Fin 5) = f := rfl
  simpa only [hgraph, he] using
    homDensity_iso W (SimpleGraph.Iso.comap e G).symm

/-- Fixed-density normalization: every isolated `K₂` component contributes
one factor of the ambient edge density, and the remaining graph is the
canonical five-vertex core used by the coefficient tables. -/
theorem homDensity_fixedCore_of_valid
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (W : Graphon Ω μ) (h : decompositionValid G = true) :
    homDensity G W =
      cliqueDensity 2 W ^ isolatedEdgeCountFin5 G *
        homDensity (fixedCoreGraphFin5 G) W := by
  have hv := h
  simp only [decompositionValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  have hmle : isolatedEdgeCountFin5 G ≤ 2 := hv.1.2
  have hcases : isolatedEdgeCountFin5 G = 0 ∨
      isolatedEdgeCountFin5 G = 1 ∨ isolatedEdgeCountFin5 G = 2 := by
    omega
  have hrel := homDensity_decomposedGraph_of_valid G W h
  rcases hcases with hm | hm | hm
  · let R := decomposedGraph G 0
    have hrel₀ : homDensity G W = homDensity R W := by
      simpa only [hm] using hrel
    have hcore : fixedCoreGraphFin5 G = R := by
      unfold fixedCoreGraphFin5
      simp only [hm]
      change graphOfCode (adjacencyCode (strippedGraphFin5 R 0)) = R
      simpa only [strippedGraphFin5] using graphOfCode_adjacencyCode R
    calc
      homDensity G W = homDensity R W := hrel₀
      _ = cliqueDensity 2 W ^ isolatedEdgeCountFin5 G *
          homDensity (fixedCoreGraphFin5 G) W := by
        simp only [hm, pow_zero, one_mul, hcore]
  · let R := decomposedGraph G 1
    have hrel₁ : homDensity G W = homDensity R W := by
      simpa only [hm] using hrel
    have hstd : isStandardDecomposition R 1 = true := by
      simpa only [hm] using hv.2
    have hReq : R = standardOneEdge R := by
      apply (adjacencyCode_eq_iff R (standardOneEdge R)).mp
      simpa [isStandardDecomposition] using hstd
    have hdR : homDensity R W =
        homDensity (frontGraph3 R) W * cliqueDensity 2 W := by
      exact (homDensity_graph_eq R (standardOneEdge R) W hReq).trans
        (homDensity_standardOneEdge R W)
    have hcore : fixedCoreGraphFin5 G =
        (frontGraph3 R).map (Fin.castAdd 2) := by
      unfold fixedCoreGraphFin5
      simp only [hm]
      change graphOfCode (adjacencyCode (strippedGraphFin5 R 1)) =
        (frontGraph3 R).map (Fin.castAdd 2)
      exact (graphOfCode_adjacencyCode
        (strippedGraphFin5 R 1)).trans
          (strippedGraphFin5_one_of_standard R hstd)
    have hdcore : homDensity (fixedCoreGraphFin5 G) W =
        homDensity (frontGraph3 R) W := by
      simpa only [hcore] using
        homDensity_map_castAdd (frontGraph3 R) 2 W
    calc
      homDensity G W = homDensity R W := hrel₁
      _ = homDensity (frontGraph3 R) W * cliqueDensity 2 W := hdR
      _ = cliqueDensity 2 W ^ isolatedEdgeCountFin5 G *
          homDensity (fixedCoreGraphFin5 G) W := by
        rw [hm, pow_one, hdcore]
        ring
  · let R := decomposedGraph G 2
    have hrel₂ : homDensity G W = homDensity R W := by
      simpa only [hm] using hrel
    have hstd : isStandardDecomposition R 2 = true := by
      simpa only [hm] using hv.2
    have hReq : R = standardTwoEdges R := by
      apply (adjacencyCode_eq_iff R (standardTwoEdges R)).mp
      simpa [isStandardDecomposition] using hstd
    have hdR : homDensity R W = cliqueDensity 2 W ^ 2 := by
      exact (homDensity_graph_eq R (standardTwoEdges R) W hReq).trans
        (homDensity_standardTwoEdges R W)
    have hcore : fixedCoreGraphFin5 G = (⊥ : SimpleGraph (Fin 5)) := by
      unfold fixedCoreGraphFin5
      simp only [hm]
      change graphOfCode (adjacencyCode (strippedGraphFin5 R 2)) = ⊥
      exact (graphOfCode_adjacencyCode
        (strippedGraphFin5 R 2)).trans
          (strippedGraphFin5_two_of_standard R hstd)
    have hdcore : homDensity (fixedCoreGraphFin5 G) W = 1 := by
      simpa only [hcore] using homDensity_bot_fin 5 W
    calc
      homDensity G W = homDensity R W := hrel₂
      _ = cliqueDensity 2 W ^ 2 := hdR
      _ = cliqueDensity 2 W ^ isolatedEdgeCountFin5 G *
          homDensity (fixedCoreGraphFin5 G) W := by
        rw [hm, hdcore, mul_one]

end Taeyoung.Methods.RootedSOS
