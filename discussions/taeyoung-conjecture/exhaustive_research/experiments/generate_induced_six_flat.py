"""Generate one shared finite-sum reindexing for the 14 induced Gram blocks."""

import json
from pathlib import Path


def plus(values):
    return values[0] if len(values)==1 else f'({values[0]}+{plus(values[1:])})'


def embedding(i, squares, term):
    if i<len(squares)-1:
        term=f'Fin.castAdd ({plus(squares[i+1:])}) ({term})'
    for size in reversed(squares[:i]):
        term=f'Fin.natAdd ({size}) ({term})'
    return term


def main():
    common=json.loads(Path('experiments/induced_six_common.json').read_text(encoding='utf-8'))
    dims=[t['flag_count'] for t in common['types']]
    squares=[f'd{i}*d{i}' for i in range(14)]
    ns='Taeyoung.Methods.RootedSOS.Induced.Six'
    text=f'''import {ns}.SparseBase
namespace {ns}
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
theorem sum_square {{M : Type*}} [AddCommMonoid M] (d : Nat) (f : Fin (d*d) → M) :
    (∑ k, f k) = ∑ i : Fin d, ∑ j : Fin d, f (finProdFinEquiv (i,j)) := by
  rw [← finProdFinEquiv.sum_comp f]
  exact Fintype.sum_prod_type _
theorem sum_fourteen_squares {{M : Type*}} [AddCommMonoid M]
    ({' '.join('d'+str(i) for i in range(14))} : Nat) (f : Fin {plus(squares)} → M) :
    (∑ k, f k) =
'''
    terms=[]
    for i in range(14):
        terms.append(f'      (∑ a : Fin d{i}, ∑ b : Fin d{i}, f ({embedding(i,squares,"finProdFinEquiv (a,b)")}))')
    text+=' +\n'.join(terms)+' := by\n'
    for i in range(13):
        text+=f'  rw [Fin.sum_univ_add (a := {squares[i]}) (b := {plus(squares[i+1:])})]\n'
    for i in range(14):
        text+=f'  rw [sum_square d{i} (fun k => f ({embedding(i,squares,"k")}))]\n'
    text+='  simp only [add_assoc]\n\n'
    concrete=list(map(str,(d*d for d in dims)))
    offset=0
    total=sum(d*d for d in dims)
    for i,d in enumerate(dims):
        text+=f'''def blockIndex{i:02d} (a b : Fin {d}) : Fin {total} :=
  {embedding(i,concrete,'finProdFinEquiv (a,b)')}
@[simp] theorem blockIndex{i:02d}_val (a b : Fin {d}) :
    (blockIndex{i:02d} a b).1 = {offset}+b.1+{d}*a.1 := by
  simp [blockIndex{i:02d}, finProdFinEquiv, Nat.add_assoc] <;> omega
theorem blockCode{i:02d} (a b : Fin {d}) :
    Sparse.flatCode (blockIndex{i:02d} a b) = Family{i:02d}.countCode a b := by
  unfold Sparse.flatCode
'''
        for j in range(i):
            stop=sum(x*x for x in dims[:j+1])
            text+=f'''  have h{j} : ¬ (blockIndex{i:02d} a b).1 < {stop} := by rw [blockIndex{i:02d}_val]; omega
  rw [if_neg h{j}]
'''
        if i<13:
            stop=sum(x*x for x in dims[:i+1])
            text+=f'''  have hi : (blockIndex{i:02d} a b).1 < {stop} := by rw [blockIndex{i:02d}_val]; omega
  rw [if_pos hi]
'''
        text+=f'''  apply congrArg₂ Family{i:02d}.countCode <;> apply Fin.ext <;>
    simp only [blockIndex{i:02d}_val] <;> omega
theorem blockPulled{i:02d} (g : Fin 156) (a b : Fin {d}) :
    Sparse.pulled g (blockIndex{i:02d} a b) = Family{i:02d}.coefficient a b g := by
  simp only [Sparse.pulled, Family{i:02d}.coefficient, blockCode{i:02d}]
'''
        offset+=d*d
    text+=f'''theorem sum_all_blocks {{M : Type*}} [AddCommMonoid M] (f : Fin {total} → M) :
    (∑ k, f k) =
'''
    text+=' +\n'.join(f'      (∑ a : Fin {d}, ∑ b : Fin {d}, f (blockIndex{i:02d} a b))' for i,d in enumerate(dims))+' := by\n'
    text+='  simpa only ['+', '.join(f'blockIndex{i:02d}' for i in range(14))+'] using\n'
    text+='    sum_fourteen_squares '+' '.join(map(str,dims))+' f\n'
    text+=f'#print axioms sum_all_blocks\nend {ns}\n'
    path=Path('lean/Taeyoung/Methods/RootedSOS/Induced/Six/FlatBlocks.lean')
    path.write_text(text,encoding='utf-8')
    print(path,path.stat().st_size,flush=True)


if __name__=='__main__':
    main()
