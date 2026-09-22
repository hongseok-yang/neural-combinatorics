import Taeyoung.Methods.RootedSOS.Induced.Six.Base
import Taeyoung.Methods.RootedSOS.Induced.Gluing
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
namespace Taeyoung.Methods.RootedSOS.Induced.Six.Config02
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset
abbrev Root := Fin 2
abbrev Branch := Fin 2
abbrev Vertex := Root ⊕ (Branch ⊕ Branch)
abbrev RootEdge := Fin 1
abbrev BranchEdge := Fin 5
abbrev CrossEdge := Fin 4
abbrev Edge := (RootEdge ⊕ (BranchEdge ⊕ BranchEdge)) ⊕ CrossEdge
def rootPairs : RootEdge → Root × Root := ![(0,1)]
def branchPairs : BranchEdge → (Root ⊕ Branch) × (Root ⊕ Branch) := ![((Sum.inl 0),(Sum.inr 0)), ((Sum.inl 0),(Sum.inr 1)), ((Sum.inl 1),(Sum.inr 0)), ((Sum.inl 1),(Sum.inr 1)), ((Sum.inr 0),(Sum.inr 1))]
def crossPairs : CrossEdge → Branch × Branch := ![(0,0), (0,1), (1,0), (1,1)]
def allPairs : Edge → Vertex × Vertex := gluedPairs rootPairs branchPairs crossPairs
def vertexMap : Vertex → Fin 6 := Sum.elim (fun i => ⟨i.1, by omega⟩)
  (Sum.elim (fun i => ⟨2+i.1, by omega⟩) (fun i => ⟨4+i.1, by omega⟩))
def vertexInv (i : Fin 6) : Vertex :=
  if h : i.1 < 2 then Sum.inl ⟨i.1,h⟩ else
  if h' : i.1 < 4 then Sum.inr (Sum.inl ⟨i.1-2,by omega⟩)
  else Sum.inr (Sum.inr ⟨i.1-4,by omega⟩)
def rootIndex : RootEdge → Fin 15 := ![0]
def firstIndex : BranchEdge → Fin 15 := ![1, 2, 5, 6, 9]
def secondIndex : BranchEdge → Fin 15 := ![3, 4, 7, 8, 14]
def crossIndex : CrossEdge → Fin 15 := ![10, 11, 12, 13]
def edgeMap : Edge → Fin 15 := Sum.elim (Sum.elim rootIndex (Sum.elim firstIndex secondIndex)) crossIndex
def edgeInv : Fin 15 → Edge := ![Sum.inl (Sum.inl 0), Sum.inl (Sum.inr (Sum.inl 0)), Sum.inl (Sum.inr (Sum.inl 1)), Sum.inl (Sum.inr (Sum.inr 0)), Sum.inl (Sum.inr (Sum.inr 1)), Sum.inl (Sum.inr (Sum.inl 2)), Sum.inl (Sum.inr (Sum.inl 3)), Sum.inl (Sum.inr (Sum.inr 2)), Sum.inl (Sum.inr (Sum.inr 3)), Sum.inl (Sum.inr (Sum.inl 4)), Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl (Sum.inr (Sum.inr 4))]
private theorem vertex_left : ∀ v, vertexInv (vertexMap v) = v := by decide +kernel
private theorem vertex_right : ∀ v, vertexMap (vertexInv v) = v := by decide +kernel
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def vertexEquiv : Vertex ≃ Fin 6 := ⟨vertexMap,vertexInv,vertex_left,vertex_right⟩
def edgeEquiv : Edge ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
@[simp] theorem edgeEquiv_apply (e : Edge) : edgeEquiv e = edgeMap e := rfl
theorem pairs_exact : ∀ e, vertexMap (allPairs e).1 = (pairs (edgeMap e)).1 ∧
    vertexMap (allPairs e).2 = (pairs (edgeMap e)).2 := by decide +kernel
def rootBits (a : Fin 2) : RootEdge → Fin 2 := finFunctionFinEquiv.symm a
def branchBits (a : Fin 32) : BranchEdge → Fin 2 := finFunctionFinEquiv.symm a
def crossBits (a : Fin 16) : CrossEdge → Fin 2 := finFunctionFinEquiv.symm a

private def rootPlacementData : PackedTable := (.node 1 (.leaf (0))
(.leaf (1)))
def rootPlacement (a : Fin 2) : Nat := (rootPlacementData.get a).toNat
theorem rootPlacement_exact : ∀ a, rootPlacement a = ∑ i, (rootBits a i).1 * 2^(rootIndex i).1 := by decide +kernel

private def firstPlacementData : PackedTable := (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (2)))
(.node 1 (.leaf (4))
(.leaf (6))))
(.node 2 (.node 1 (.leaf (32))
(.leaf (34)))
(.node 1 (.leaf (36))
(.leaf (38)))))
(.node 4 (.node 2 (.node 1 (.leaf (64))
(.leaf (66)))
(.node 1 (.leaf (68))
(.leaf (70))))
(.node 2 (.node 1 (.leaf (96))
(.leaf (98)))
(.node 1 (.leaf (100))
(.leaf (102))))))
(.node 8 (.node 4 (.node 2 (.node 1 (.leaf (512))
(.leaf (514)))
(.node 1 (.leaf (516))
(.leaf (518))))
(.node 2 (.node 1 (.leaf (544))
(.leaf (546)))
(.node 1 (.leaf (548))
(.leaf (550)))))
(.node 4 (.node 2 (.node 1 (.leaf (576))
(.leaf (578)))
(.node 1 (.leaf (580))
(.leaf (582))))
(.node 2 (.node 1 (.leaf (608))
(.leaf (610)))
(.node 1 (.leaf (612))
(.leaf (614)))))))
def firstPlacement (a : Fin 32) : Nat := (firstPlacementData.get a).toNat
theorem firstPlacement_exact : ∀ a, firstPlacement a = ∑ i, (branchBits a i).1 * 2^(firstIndex i).1 := by decide +kernel

private def secondPlacementData : PackedTable := (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (8)))
(.node 1 (.leaf (16))
(.leaf (24))))
(.node 2 (.node 1 (.leaf (128))
(.leaf (136)))
(.node 1 (.leaf (144))
(.leaf (152)))))
(.node 4 (.node 2 (.node 1 (.leaf (256))
(.leaf (264)))
(.node 1 (.leaf (272))
(.leaf (280))))
(.node 2 (.node 1 (.leaf (384))
(.leaf (392)))
(.node 1 (.leaf (400))
(.leaf (408))))))
(.node 8 (.node 4 (.node 2 (.node 1 (.leaf (16384))
(.leaf (16392)))
(.node 1 (.leaf (16400))
(.leaf (16408))))
(.node 2 (.node 1 (.leaf (16512))
(.leaf (16520)))
(.node 1 (.leaf (16528))
(.leaf (16536)))))
(.node 4 (.node 2 (.node 1 (.leaf (16640))
(.leaf (16648)))
(.node 1 (.leaf (16656))
(.leaf (16664))))
(.node 2 (.node 1 (.leaf (16768))
(.leaf (16776)))
(.node 1 (.leaf (16784))
(.leaf (16792)))))))
def secondPlacement (a : Fin 32) : Nat := (secondPlacementData.get a).toNat
theorem secondPlacement_exact : ∀ a, secondPlacement a = ∑ i, (branchBits a i).1 * 2^(secondIndex i).1 := by decide +kernel

private def crossPlacementData : PackedTable := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (1024)))
(.node 1 (.leaf (2048))
(.leaf (3072))))
(.node 2 (.node 1 (.leaf (4096))
(.leaf (5120)))
(.node 1 (.leaf (6144))
(.leaf (7168)))))
(.node 4 (.node 2 (.node 1 (.leaf (8192))
(.leaf (9216)))
(.node 1 (.leaf (10240))
(.leaf (11264))))
(.node 2 (.node 1 (.leaf (12288))
(.leaf (13312)))
(.node 1 (.leaf (14336))
(.leaf (15360))))))
def crossPlacement (a : Fin 16) : Nat := (crossPlacementData.get a).toNat
theorem crossPlacement_exact : ∀ a, crossPlacement a = ∑ i, (crossBits a i).1 * 2^(crossIndex i).1 := by decide +kernel

def completion (p : Fin 2) (a b : Fin 32) (c : Fin 16) : Fin 32768 :=
  ⟨(rootPlacement p+(firstPlacement a+secondPlacement b)+crossPlacement c)%32768,
    Nat.mod_lt _ (by decide)⟩
theorem completion_exact (p : Fin 2) (a b : Fin 32) (c : Fin 16) :
    completion p a b c = patternCode edgeEquiv (gluedPattern (rootBits p) (branchBits a) (branchBits b) (crossBits c)) := by
  have h := patternCode_val edgeEquiv
    (gluedPattern (rootBits p) (branchBits a) (branchBits b) (crossBits c))
  simp only [gluedPattern, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    edgeEquiv_apply, edgeMap] at h
  rw [← rootPlacement_exact, ← firstPlacement_exact, ← secondPlacement_exact, ← crossPlacement_exact] at h
  apply Fin.ext
  change (rootPlacement p+(firstPlacement a+secondPlacement b)+crossPlacement c)%32768 = _
  rw [← h]
  exact Nat.mod_eq_of_lt (patternCode _ _).isLt
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem completion_density (p : Fin 2) (a b : Fin 32) (c : Fin 16) (W : Taeyoung.Graphon Ω μ) :
    inducedDensity allPairs (gluedPattern (rootBits p) (branchBits a) (branchBits b) (crossBits c)) W =
      inducedDensity pairs (bits (completion p a b c)) W := by
  apply inducedDensity_relabel allPairs pairs _ _ vertexEquiv edgeEquiv
  · intro i
    rw [completion_exact]
    exact (bits_patternCode edgeEquiv _ i).symm
  · intro i
    exact Or.inl (pairs_exact i)
end Taeyoung.Methods.RootedSOS.Induced.Six.Config02
