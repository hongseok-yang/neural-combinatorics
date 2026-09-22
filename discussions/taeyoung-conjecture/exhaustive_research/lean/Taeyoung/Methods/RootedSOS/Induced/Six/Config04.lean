import Taeyoung.Methods.RootedSOS.Induced.Six.Base
import Taeyoung.Methods.RootedSOS.Induced.Gluing
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
namespace Taeyoung.Methods.RootedSOS.Induced.Six.Config04
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset
abbrev Root := Fin 4
abbrev Branch := Fin 1
abbrev Vertex := Root ⊕ (Branch ⊕ Branch)
abbrev RootEdge := Fin 6
abbrev BranchEdge := Fin 4
abbrev CrossEdge := Fin 1
abbrev Edge := (RootEdge ⊕ (BranchEdge ⊕ BranchEdge)) ⊕ CrossEdge
def rootPairs : RootEdge → Root × Root := ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]
def branchPairs : BranchEdge → (Root ⊕ Branch) × (Root ⊕ Branch) := ![((Sum.inl 0),(Sum.inr 0)), ((Sum.inl 1),(Sum.inr 0)), ((Sum.inl 2),(Sum.inr 0)), ((Sum.inl 3),(Sum.inr 0))]
def crossPairs : CrossEdge → Branch × Branch := ![(0,0)]
def allPairs : Edge → Vertex × Vertex := gluedPairs rootPairs branchPairs crossPairs
def vertexMap : Vertex → Fin 6 := Sum.elim (fun i => ⟨i.1, by omega⟩)
  (Sum.elim (fun i => ⟨4+i.1, by omega⟩) (fun i => ⟨5+i.1, by omega⟩))
def vertexInv (i : Fin 6) : Vertex :=
  if h : i.1 < 4 then Sum.inl ⟨i.1,h⟩ else
  if h' : i.1 < 5 then Sum.inr (Sum.inl ⟨i.1-4,by omega⟩)
  else Sum.inr (Sum.inr ⟨i.1-5,by omega⟩)
def rootIndex : RootEdge → Fin 15 := ![0, 1, 2, 5, 6, 9]
def firstIndex : BranchEdge → Fin 15 := ![3, 7, 10, 12]
def secondIndex : BranchEdge → Fin 15 := ![4, 8, 11, 13]
def crossIndex : CrossEdge → Fin 15 := ![14]
def edgeMap : Edge → Fin 15 := Sum.elim (Sum.elim rootIndex (Sum.elim firstIndex secondIndex)) crossIndex
def edgeInv : Fin 15 → Edge := ![Sum.inl (Sum.inl 0), Sum.inl (Sum.inl 1), Sum.inl (Sum.inl 2), Sum.inl (Sum.inr (Sum.inl 0)), Sum.inl (Sum.inr (Sum.inr 0)), Sum.inl (Sum.inl 3), Sum.inl (Sum.inl 4), Sum.inl (Sum.inr (Sum.inl 1)), Sum.inl (Sum.inr (Sum.inr 1)), Sum.inl (Sum.inl 5), Sum.inl (Sum.inr (Sum.inl 2)), Sum.inl (Sum.inr (Sum.inr 2)), Sum.inl (Sum.inr (Sum.inl 3)), Sum.inl (Sum.inr (Sum.inr 3)), Sum.inr 0]
private theorem vertex_left : ∀ v, vertexInv (vertexMap v) = v := by decide +kernel
private theorem vertex_right : ∀ v, vertexMap (vertexInv v) = v := by decide +kernel
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def vertexEquiv : Vertex ≃ Fin 6 := ⟨vertexMap,vertexInv,vertex_left,vertex_right⟩
def edgeEquiv : Edge ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
@[simp] theorem edgeEquiv_apply (e : Edge) : edgeEquiv e = edgeMap e := rfl
theorem pairs_exact : ∀ e, vertexMap (allPairs e).1 = (pairs (edgeMap e)).1 ∧
    vertexMap (allPairs e).2 = (pairs (edgeMap e)).2 := by decide +kernel
def rootBits (a : Fin 64) : RootEdge → Fin 2 := finFunctionFinEquiv.symm a
def branchBits (a : Fin 16) : BranchEdge → Fin 2 := finFunctionFinEquiv.symm a
def crossBits (a : Fin 2) : CrossEdge → Fin 2 := finFunctionFinEquiv.symm a

private def rootPlacementData : PackedTable := (.node 32 (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (1)))
(.node 1 (.leaf (2))
(.leaf (3))))
(.node 2 (.node 1 (.leaf (4))
(.leaf (5)))
(.node 1 (.leaf (6))
(.leaf (7)))))
(.node 4 (.node 2 (.node 1 (.leaf (32))
(.leaf (33)))
(.node 1 (.leaf (34))
(.leaf (35))))
(.node 2 (.node 1 (.leaf (36))
(.leaf (37)))
(.node 1 (.leaf (38))
(.leaf (39))))))
(.node 8 (.node 4 (.node 2 (.node 1 (.leaf (64))
(.leaf (65)))
(.node 1 (.leaf (66))
(.leaf (67))))
(.node 2 (.node 1 (.leaf (68))
(.leaf (69)))
(.node 1 (.leaf (70))
(.leaf (71)))))
(.node 4 (.node 2 (.node 1 (.leaf (96))
(.leaf (97)))
(.node 1 (.leaf (98))
(.leaf (99))))
(.node 2 (.node 1 (.leaf (100))
(.leaf (101)))
(.node 1 (.leaf (102))
(.leaf (103)))))))
(.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (512))
(.leaf (513)))
(.node 1 (.leaf (514))
(.leaf (515))))
(.node 2 (.node 1 (.leaf (516))
(.leaf (517)))
(.node 1 (.leaf (518))
(.leaf (519)))))
(.node 4 (.node 2 (.node 1 (.leaf (544))
(.leaf (545)))
(.node 1 (.leaf (546))
(.leaf (547))))
(.node 2 (.node 1 (.leaf (548))
(.leaf (549)))
(.node 1 (.leaf (550))
(.leaf (551))))))
(.node 8 (.node 4 (.node 2 (.node 1 (.leaf (576))
(.leaf (577)))
(.node 1 (.leaf (578))
(.leaf (579))))
(.node 2 (.node 1 (.leaf (580))
(.leaf (581)))
(.node 1 (.leaf (582))
(.leaf (583)))))
(.node 4 (.node 2 (.node 1 (.leaf (608))
(.leaf (609)))
(.node 1 (.leaf (610))
(.leaf (611))))
(.node 2 (.node 1 (.leaf (612))
(.leaf (613)))
(.node 1 (.leaf (614))
(.leaf (615))))))))
def rootPlacement (a : Fin 64) : Nat := (rootPlacementData.get a).toNat
theorem rootPlacement_exact : ∀ a, rootPlacement a = ∑ i, (rootBits a i).1 * 2^(rootIndex i).1 := by decide +kernel

private def firstPlacementData : PackedTable := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (8)))
(.node 1 (.leaf (128))
(.leaf (136))))
(.node 2 (.node 1 (.leaf (1024))
(.leaf (1032)))
(.node 1 (.leaf (1152))
(.leaf (1160)))))
(.node 4 (.node 2 (.node 1 (.leaf (4096))
(.leaf (4104)))
(.node 1 (.leaf (4224))
(.leaf (4232))))
(.node 2 (.node 1 (.leaf (5120))
(.leaf (5128)))
(.node 1 (.leaf (5248))
(.leaf (5256))))))
def firstPlacement (a : Fin 16) : Nat := (firstPlacementData.get a).toNat
theorem firstPlacement_exact : ∀ a, firstPlacement a = ∑ i, (branchBits a i).1 * 2^(firstIndex i).1 := by decide +kernel

private def secondPlacementData : PackedTable := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (16)))
(.node 1 (.leaf (256))
(.leaf (272))))
(.node 2 (.node 1 (.leaf (2048))
(.leaf (2064)))
(.node 1 (.leaf (2304))
(.leaf (2320)))))
(.node 4 (.node 2 (.node 1 (.leaf (8192))
(.leaf (8208)))
(.node 1 (.leaf (8448))
(.leaf (8464))))
(.node 2 (.node 1 (.leaf (10240))
(.leaf (10256)))
(.node 1 (.leaf (10496))
(.leaf (10512))))))
def secondPlacement (a : Fin 16) : Nat := (secondPlacementData.get a).toNat
theorem secondPlacement_exact : ∀ a, secondPlacement a = ∑ i, (branchBits a i).1 * 2^(secondIndex i).1 := by decide +kernel

private def crossPlacementData : PackedTable := (.node 1 (.leaf (0))
(.leaf (16384)))
def crossPlacement (a : Fin 2) : Nat := (crossPlacementData.get a).toNat
theorem crossPlacement_exact : ∀ a, crossPlacement a = ∑ i, (crossBits a i).1 * 2^(crossIndex i).1 := by decide +kernel

def completion (p : Fin 64) (a b : Fin 16) (c : Fin 2) : Fin 32768 :=
  ⟨(rootPlacement p+(firstPlacement a+secondPlacement b)+crossPlacement c)%32768,
    Nat.mod_lt _ (by decide)⟩
theorem completion_exact (p : Fin 64) (a b : Fin 16) (c : Fin 2) :
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
theorem completion_density (p : Fin 64) (a b : Fin 16) (c : Fin 2) (W : Taeyoung.Graphon Ω μ) :
    inducedDensity allPairs (gluedPattern (rootBits p) (branchBits a) (branchBits b) (crossBits c)) W =
      inducedDensity pairs (bits (completion p a b c)) W := by
  apply inducedDensity_relabel allPairs pairs _ _ vertexEquiv edgeEquiv
  · intro i
    rw [completion_exact]
    exact (bits_patternCode edgeEquiv _ i).symm
  · intro i
    exact Or.inl (pairs_exact i)
end Taeyoung.Methods.RootedSOS.Induced.Six.Config04
