"""Emit three shared root/branch layouts and fast, proved completion codes."""

import itertools as it
import json
from pathlib import Path

from generate_compact_s4_psd import table


NS = 'Taeyoung.Methods.RootedSOS.Induced.Six'
ROOT = Path('lean/Taeyoung/Methods/RootedSOS/Induced/Six')


def main():
    common = json.loads(Path('experiments/induced_six_common.json').read_text(encoding='utf-8'))
    for m in (0,2,4):
        t = next(t for t in common['types'] if t['roots'] == m)
        r = t['branches']
        nr,nb,nc = math_choose(m,2),len(t['branch_pairs']),len(t['cross_indices'])
        root_indices = [common['pairs'].index(list(e)) for e in it.combinations(range(m),2)]
        root_codes = [sum(1 << j for k,j in enumerate(root_indices) if a >> k & 1) for a in range(2**nr)]
        root_pairs = ', '.join(f'({i},{j})' for i,j in it.combinations(range(m),2))
        branch_v = lambda i: f'(Sum.inl {i})' if i < m else f'(Sum.inr {i-m})'
        branch_pairs = ', '.join(f'({branch_v(i)},{branch_v(j)})' for i,j in t['branch_pairs'])
        cross_pairs = ', '.join(f'({i},{j})' for i in range(r) for j in range(r))
        embed_edge = lambda part,i: [f'Sum.inl (Sum.inl {i})', f'Sum.inl (Sum.inr (Sum.inl {i}))',
                                    f'Sum.inl (Sum.inr (Sum.inr {i}))', f'Sum.inr {i}'][part]
        edge_inv = ['']*15
        for part,indices in enumerate([root_indices,t['first_indices'],t['second_indices'],t['cross_indices']]):
            for i,j in enumerate(indices):
                edge_inv[j] = embed_edge(part,i)
        v = lambda values: '!['+', '.join(map(str,values))+']'
        ns = f'{NS}.Config{m:02d}'
        body = f'''import {NS}.Base
import Taeyoung.Methods.RootedSOS.Induced.Gluing
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
namespace {ns}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset
abbrev Root := Fin {m}
abbrev Branch := Fin {r}
abbrev Vertex := Root ⊕ (Branch ⊕ Branch)
abbrev RootEdge := Fin {nr}
abbrev BranchEdge := Fin {nb}
abbrev CrossEdge := Fin {nc}
abbrev Edge := (RootEdge ⊕ (BranchEdge ⊕ BranchEdge)) ⊕ CrossEdge
def rootPairs : RootEdge → Root × Root := ![{root_pairs}]
def branchPairs : BranchEdge → (Root ⊕ Branch) × (Root ⊕ Branch) := ![{branch_pairs}]
def crossPairs : CrossEdge → Branch × Branch := ![{cross_pairs}]
def allPairs : Edge → Vertex × Vertex := gluedPairs rootPairs branchPairs crossPairs
def vertexMap : Vertex → Fin 6 := Sum.elim (fun i => ⟨i.1, by omega⟩)
  (Sum.elim (fun i => ⟨{m}+i.1, by omega⟩) (fun i => ⟨{m+r}+i.1, by omega⟩))
def vertexInv (i : Fin 6) : Vertex :=
  if h : i.1 < {m} then Sum.inl ⟨i.1,h⟩ else
  if h' : i.1 < {m+r} then Sum.inr (Sum.inl ⟨i.1-{m},by omega⟩)
  else Sum.inr (Sum.inr ⟨i.1-{m+r},by omega⟩)
def rootIndex : RootEdge → Fin 15 := {v(root_indices)}
def firstIndex : BranchEdge → Fin 15 := {v(t['first_indices'])}
def secondIndex : BranchEdge → Fin 15 := {v(t['second_indices'])}
def crossIndex : CrossEdge → Fin 15 := {v(t['cross_indices'])}
def edgeMap : Edge → Fin 15 := Sum.elim (Sum.elim rootIndex (Sum.elim firstIndex secondIndex)) crossIndex
def edgeInv : Fin 15 → Edge := ![{', '.join(edge_inv)}]
private theorem vertex_left : ∀ v, vertexInv (vertexMap v) = v := by decide +kernel
private theorem vertex_right : ∀ v, vertexMap (vertexInv v) = v := by decide +kernel
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def vertexEquiv : Vertex ≃ Fin 6 := ⟨vertexMap,vertexInv,vertex_left,vertex_right⟩
def edgeEquiv : Edge ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
@[simp] theorem edgeEquiv_apply (e : Edge) : edgeEquiv e = edgeMap e := rfl
theorem pairs_exact : ∀ e, vertexMap (allPairs e).1 = (pairs (edgeMap e)).1 ∧
    vertexMap (allPairs e).2 = (pairs (edgeMap e)).2 := by decide +kernel
def rootBits (a : Fin {2**nr}) : RootEdge → Fin 2 := finFunctionFinEquiv.symm a
def branchBits (a : Fin {2**nb}) : BranchEdge → Fin 2 := finFunctionFinEquiv.symm a
def crossBits (a : Fin {2**nc}) : CrossEdge → Fin 2 := finFunctionFinEquiv.symm a
'''
        for name,values,indices,bits in [
            ('rootPlacement',root_codes,root_indices,'rootBits'),
            ('firstPlacement',t['first_codes'],t['first_indices'],'branchBits'),
            ('secondPlacement',t['second_codes'],t['second_indices'],'branchBits'),
            ('crossPlacement',t['cross_codes'],t['cross_indices'],'crossBits')]:
            idx = name.replace('Placement','Index')
            body += f'''
private def {name}Data : PackedTable := {table(values)}
def {name} (a : Fin {len(values)}) : Nat := ({name}Data.get a).toNat
theorem {name}_exact : ∀ a, {name} a = ∑ i, ({bits} a i).1 * 2^({idx} i).1 := by decide +kernel
'''
        body += f'''
def completion (p : Fin {2**nr}) (a b : Fin {2**nb}) (c : Fin {2**nc}) : Fin 32768 :=
  ⟨(rootPlacement p+(firstPlacement a+secondPlacement b)+crossPlacement c)%32768,
    Nat.mod_lt _ (by decide)⟩
theorem completion_exact (p : Fin {2**nr}) (a b : Fin {2**nb}) (c : Fin {2**nc}) :
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
variable {{Ω : Type*}} [MeasurableSpace Ω] {{μ : Measure Ω}} [IsProbabilityMeasure μ]
theorem completion_density (p : Fin {2**nr}) (a b : Fin {2**nb}) (c : Fin {2**nc}) (W : Taeyoung.Graphon Ω μ) :
    inducedDensity allPairs (gluedPattern (rootBits p) (branchBits a) (branchBits b) (crossBits c)) W =
      inducedDensity pairs (bits (completion p a b c)) W := by
  apply inducedDensity_relabel allPairs pairs _ _ vertexEquiv edgeEquiv
  · intro i
    rw [completion_exact]
    exact (bits_patternCode edgeEquiv _ i).symm
  · intro i
    exact Or.inl (pairs_exact i)
end {ns}
'''
        path = ROOT/f'Config{m:02d}.lean'
        path.write_text(body,encoding='utf-8')
        print(path,path.stat().st_size,flush=True)


def math_choose(n,k):
    import math
    return math.comb(n,k)


if __name__ == '__main__':
    main()
