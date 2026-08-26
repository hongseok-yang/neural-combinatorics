import Taeyoung.Foundation.Relabeling
import Mathlib.Data.List.GetD

/-!
# Canonical finite-graph codes

Certificate coefficient tables must identify relabelled copies of the same
ordinary graph.  `AdjacencyCode n` is the finite Boolean adjacency matrix on
`Fin n`, equipped with lexicographic order.  The canonical code of a graph is
the least adjacency matrix among all vertex permutations.

The construction is executable, while `homDensity_canonicalCode` proves that
replacing a graph by the graph decoded from its canonical code preserves its
homomorphism density.
-/

namespace Taeyoung.Methods.RootedSOS

open Taeyoung

/-- A finite Boolean adjacency matrix, stored row by row so that the standard
lexicographic list order can be used by the executable canonicalizer. -/
abbrev AdjacencyCode (_n : ℕ) := List (List Bool)

/-- The adjacency code of a labelled graph. -/
def adjacencyCode {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    AdjacencyCode n :=
  List.ofFn fun i ↦ List.ofFn fun j ↦ decide (H.Adj i j)

private def adjacencyCodeEntry {n : ℕ} (c : AdjacencyCode n)
    (i j : Fin n) : Bool :=
  ((c[i.1]?).bind fun row ↦ row[j.1]?).getD false

/-- Decode a Boolean matrix, symmetrizing it and deleting its diagonal. -/
def graphOfCode {n : ℕ} (c : AdjacencyCode n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j ↦ adjacencyCodeEntry c i j = true

instance graphOfCode_decidableAdj {n : ℕ} (c : AdjacencyCode n) :
    DecidableRel (graphOfCode c).Adj := by
  unfold graphOfCode
  infer_instance

/-- Encoding and then decoding a simple graph is the identity. -/
theorem graphOfCode_adjacencyCode {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] : graphOfCode (adjacencyCode H) = H := by
  ext i j
  simp [graphOfCode, adjacencyCode, adjacencyCodeEntry, H.adj_comm]
  intro h hij
  subst j
  exact H.loopless.irrefl i h

theorem adjacencyCode_eq_iff {n : ℕ} (H K : SimpleGraph (Fin n))
    [DecidableRel H.Adj] [DecidableRel K.Adj] :
    adjacencyCode H = adjacencyCode K ↔ H = K := by
  constructor
  · intro h
    exact (graphOfCode_adjacencyCode H).symm.trans
      ((congrArg graphOfCode h).trans (graphOfCode_adjacencyCode K))
  · intro h
    subst K
    exact congrArg (fun d : DecidableRel H.Adj ↦ @adjacencyCode n H d)
      (Subsingleton.elim _ _)

/-- All adjacency codes obtained by permuting the vertices. -/
def relabelGraph {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (σ : Equiv.Perm (Fin n)) : SimpleGraph (Fin n) :=
  H.comap σ.symm

instance relabelGraph_decidableAdj {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (σ : Equiv.Perm (Fin n)) :
    DecidableRel (relabelGraph H σ).Adj := by
  unfold relabelGraph
  infer_instance

def permutedCodes {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    Finset (AdjacencyCode n) :=
  Finset.univ.image fun σ : Equiv.Perm (Fin n) ↦
    adjacencyCode (relabelGraph H σ)

private theorem permutedCodes_nonempty {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] :
    (permutedCodes H).Nonempty := by
  classical
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

/-- Lexicographically least adjacency code in the isomorphism class. -/
def canonicalCode {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    AdjacencyCode n :=
  (permutedCodes H).min' (permutedCodes_nonempty H)

theorem canonicalCode_mem_permutedCodes {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] :
    canonicalCode H ∈ permutedCodes H :=
  Finset.min'_mem _ _

theorem homDensity_graphOfCode_of_mem_permutedCodes {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (c : AdjacencyCode n) (hc : c ∈ permutedCodes H) (W : Graphon Ω μ) :
    homDensity H W = homDensity (graphOfCode c) W := by
  rw [permutedCodes, Finset.mem_image] at hc
  obtain ⟨σ, -, hσ⟩ := hc
  have hg : graphOfCode c = relabelGraph H σ := by
    rw [← hσ, graphOfCode_adjacencyCode]
  exact homDensity_iso W (by
    rw [hg]
    exact (SimpleGraph.Iso.comap σ.symm H).symm)

/-- A graph and the graph decoded from its canonical code have the same
homomorphism density. -/
theorem homDensity_canonicalCode {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (W : Graphon Ω μ) :
    homDensity H W = homDensity (graphOfCode (canonicalCode H)) W := by
  classical
  have hmem := canonicalCode_mem_permutedCodes H
  rw [permutedCodes, Finset.mem_image] at hmem
  obtain ⟨σ, -, hσ⟩ := hmem
  have hg : graphOfCode (canonicalCode H) = relabelGraph H σ := by
    rw [← hσ, graphOfCode_adjacencyCode]
  exact homDensity_iso W (by
    rw [hg]
    exact (SimpleGraph.Iso.comap σ.symm H).symm)

/-! ## Explicit relabelling witnesses

Certificate generators often already know a concrete vertex permutation.
Reading that permutation from a short list avoids enumerating every
permutation inside Lean while retaining a fully checked density identity. -/

/-- Relabel a finite graph by reading old vertices from a list.  The fallback
keeps the executable definition total; certificate checks separately prove
that the list has the expected length and no duplicates. -/
def relabelCodeByListFin {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (l : List (Fin n)) : AdjacencyCode n :=
  List.ofFn fun i ↦ List.ofFn fun j ↦
    decide (G.Adj (l.getD i.1 i) (l.getD j.1 j))

private theorem list_ofFn_getD_eq_fin {n : ℕ} (l : List (Fin n))
    (hlen : l.length = n) :
    List.ofFn (fun i : Fin n ↦ l.getD i.1 i) = l := by
  apply List.ext_get
  · simp [hlen]
  · intro k hk₁ hk₂
    rw [List.get_ofFn, List.getD_eq_getElem]
    · simp
    · omega

/-- A length-`n`, duplicate-free list is a vertex relabelling, so decoding
its checked adjacency code preserves homomorphism density. -/
theorem homDensity_relabelCodeByListFin
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (l : List (Fin n)) (hlen : l.length = n) (hnodup : l.Nodup)
    (W : Graphon Ω μ) :
    homDensity G W = homDensity (graphOfCode (relabelCodeByListFin G l)) W := by
  let f : Fin n → Fin n := fun i ↦ l.getD i.1 i
  have hlf : List.ofFn f = l := list_ofFn_getD_eq_fin l hlen
  have hfnodup : (List.ofFn f).Nodup := by
    rw [hlf]
    exact hnodup
  have hf : Function.Injective f := List.nodup_ofFn.mp hfnodup
  let e : Fin n ≃ Fin n := Equiv.ofBijective f hf.bijective_of_finite
  have hgraph : graphOfCode (relabelCodeByListFin G l) = G.comap f := by
    change graphOfCode (adjacencyCode (G.comap f)) = G.comap f
    exact graphOfCode_adjacencyCode _
  have he : (e : Fin n → Fin n) = f := rfl
  simpa only [hgraph, he] using
    homDensity_iso W (SimpleGraph.Iso.comap e G).symm

end Taeyoung.Methods.RootedSOS
