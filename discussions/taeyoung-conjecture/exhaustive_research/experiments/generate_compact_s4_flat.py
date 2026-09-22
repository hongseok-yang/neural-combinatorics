"""Finite reindexing lemmas connecting the five Young blocks to one vector."""

from pathlib import Path

from generate_compact_s4_psd import PREFIX


def main():
    ns=f'{PREFIX}.CompactS4'
    source=f'''import {ns}.SparseBase
namespace {ns}
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

theorem sum_square {{M : Type*}} [AddCommMonoid M] (d : Nat) (f : Fin (d*d) → M) :
    (∑ k, f k) = ∑ i : Fin d, ∑ j : Fin d, f (finProdFinEquiv (i,j)) := by
  rw [← (finProdFinEquiv.sum_comp f)]
  exact Fintype.sum_prod_type _

theorem sum_five_squares {{M : Type*}} [AddCommMonoid M]
    (a b c d e : Nat) (f : Fin (a*a+(b*b+(c*c+(d*d+e*e)))) → M) :
    (∑ k, f k) =
      (∑ i : Fin a, ∑ j : Fin a, f (Fin.castAdd _ (finProdFinEquiv (i,j)))) +
      (∑ i : Fin b, ∑ j : Fin b, f (Fin.natAdd (a*a) (Fin.castAdd _ (finProdFinEquiv (i,j))))) +
      (∑ i : Fin c, ∑ j : Fin c, f (Fin.natAdd (a*a) (Fin.natAdd (b*b) (Fin.castAdd _ (finProdFinEquiv (i,j)))))) +
      (∑ i : Fin d, ∑ j : Fin d, f (Fin.natAdd (a*a) (Fin.natAdd (b*b) (Fin.natAdd (c*c) (Fin.castAdd _ (finProdFinEquiv (i,j))))))) +
      (∑ i : Fin e, ∑ j : Fin e, f (Fin.natAdd (a*a) (Fin.natAdd (b*b) (Fin.natAdd (c*c) (Fin.natAdd (d*d) (finProdFinEquiv (i,j))))))) := by
  rw [Fin.sum_univ_add (a := a*a) (b := b*b+(c*c+(d*d+e*e)))]
  rw [Fin.sum_univ_add (a := b*b) (b := c*c+(d*d+e*e))]
  rw [Fin.sum_univ_add (a := c*c) (b := d*d+e*e)]
  rw [Fin.sum_univ_add (a := d*d) (b := e*e)]
  rw [sum_square a (fun k => f (Fin.castAdd _ k))]
  rw [sum_square b (fun k => f (Fin.natAdd (a*a) (Fin.castAdd _ k)))]
  rw [sum_square c (fun k => f (Fin.natAdd (a*a) (Fin.natAdd (b*b) (Fin.castAdd _ k))))]
  rw [sum_square d (fun k => f (Fin.natAdd (a*a) (Fin.natAdd (b*b) (Fin.natAdd (c*c) (Fin.castAdd _ k)))))]
  rw [sum_square e (fun k => f (Fin.natAdd (a*a) (Fin.natAdd (b*b) (Fin.natAdd (c*c) (Fin.natAdd (d*d) k)))))]
  simp only [add_assoc]

#print axioms sum_five_squares

'''
    ds=[32,52,34,30,6]
    offsets=[0,1024,3728,4884,5784]
    tags=['4','31','22','211','1111']
    embeddings=[
        'Fin.castAdd 4796 (finProdFinEquiv (i,j))',
        'Fin.natAdd 1024 (Fin.castAdd 2092 (finProdFinEquiv (i,j)))',
        'Fin.natAdd 1024 (Fin.natAdd 2704 (Fin.castAdd 936 (finProdFinEquiv (i,j))))',
        'Fin.natAdd 1024 (Fin.natAdd 2704 (Fin.natAdd 1156 (Fin.castAdd 36 (finProdFinEquiv (i,j)))))',
        'Fin.natAdd 1024 (Fin.natAdd 2704 (Fin.natAdd 1156 (Fin.natAdd 900 (finProdFinEquiv (i,j)))))',
    ]
    for b,(d,offset,tag) in enumerate(zip(ds,offsets,tags)):
        source+=f'''def blockIndex{b} (i j : Fin {d}) : Fin 5820 :=
  {embeddings[b]}

@[simp] theorem blockIndex{b}_val (i j : Fin {d}) :
    (blockIndex{b} i j).1 = {offset}+j.1+{d}*i.1 := by
  simp [blockIndex{b}, finProdFinEquiv, Nat.add_assoc] <;> omega

theorem blockCode{b} (i j : Fin {d}) :
    Sparse.flatCode (blockIndex{b} i j) = Young{tag}.code i j := by
  unfold Sparse.flatCode
  split_ifs
  all_goals try (exfalso; simp only [blockIndex{b}_val] at *; omega)
  apply congrArg₂ Young{tag}.code <;> apply Fin.ext <;>
    simp only [blockIndex{b}_val] <;> omega

#print axioms blockCode{b}

theorem blockPulled{b} (g : Fin 143) (i j : Fin {d}) :
    Sparse.pulled g (blockIndex{b} i j) = Young{tag}.pulled g i j := by
  simp only [Sparse.pulled, Young{tag}.pulled, blockCode{b}]

'''
    source+='''theorem sum_five_blocks {M : Type*} [AddCommMonoid M] (f : Fin 5820 → M) :
    (∑ k, f k) =
      (∑ i : Fin 32, ∑ j : Fin 32, f (blockIndex0 i j)) +
      (∑ i : Fin 52, ∑ j : Fin 52, f (blockIndex1 i j)) +
      (∑ i : Fin 34, ∑ j : Fin 34, f (blockIndex2 i j)) +
      (∑ i : Fin 30, ∑ j : Fin 30, f (blockIndex3 i j)) +
      (∑ i : Fin 6, ∑ j : Fin 6, f (blockIndex4 i j)) := by
  exact sum_five_squares 32 52 34 30 6 f

#print axioms sum_five_blocks

'''
    source+=f'end {ns}\n'
    Path('lean/Taeyoung/Methods/RootedSOS/CompactS4/FlatBlocks.lean').write_text(source,encoding='utf-8')


if __name__=='__main__':
    main()
