"""Join matching constant and interval-weighted Gram blocks."""

import argparse
from pathlib import Path
from generate_compact_s4_psd import PREFIX, row_tag


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--atlas',required=True,type=int)
    parser.add_argument('--namespace-suffix', default='')
    args=parser.parse_args()
    atlas=args.atlas
    ns=PREFIX+'.'+row_tag(dict(atlas=atlas, lean_namespace_suffix=args.namespace_suffix))
    root=Path('lean')/Path(*ns.split('.'))
    for b,(d,offset,tag) in enumerate(zip([32,52,34,30,6],[0,1024,3728,4884,5784],['4','31','22','211','1111'])):
        source=f'''import {ns}.Block{b:02d}Density
import {ns}.Block{b+5:02d}Density
import {ns}.Right
import {PREFIX}.CompactS4.FlatBlocks

namespace {ns}
open Finset MeasureTheory
variable {{Ω : Type*}} [MeasurableSpace Ω] {{μ : Measure Ω}} [IsProbabilityMeasure μ]

theorem blockRight{b} (i j : Fin {d}) (u : Fin 4) :
    right (blockIndex{b} i j) u =
      if u.1 = 0 then 24*Block{b:02d}.H i j
      else if u.1 = 1 then 24*(Block{b:02d}.H i ({d}+j)+Block{b:02d}.H ({d}+i) j)
      else if u.1 = 2 then 24*Block{b:02d}.H ({d}+i) ({d}+j)
      else 24*Block{b+5:02d}.H i j := by
  rw [((rightCheck_all (blockIndex{b} i j)).1 u).2]
  unfold expandedRight
'''
        for t,stop in enumerate([1024,3728,4884,5784]):
            if t>b: break
            sign='' if t==b else '¬ '
            source+=f'''  have h{t} : {sign}(blockIndex{b} i j).1 < {stop} := by rw [blockIndex{b}_val]; omega
  rw [if_{'pos' if t==b else 'neg'} h{t}]
'''
        source+=f'''  have hi : ((blockIndex{b} i j).1-{offset})/{d} = i.1 := by rw [blockIndex{b}_val]; omega
  have hj : ((blockIndex{b} i j).1-{offset})%{d} = j.1 := by rw [blockIndex{b}_val]; omega
  dsimp only
  rw [hi,hj]

theorem blockSum{b}_nonneg (W : Taeyoung.Graphon Ω μ) (s : Real)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ∑ i : Fin {d}, ∑ j : Fin {d},
      ((right (blockIndex{b} i j) 0 : Real)+(right (blockIndex{b} i j) 1 : Real)*s+
        (right (blockIndex{b} i j) 2 : Real)*s^2+
        (right (blockIndex{b} i j) 3 : Real)*s*(1-s)) *
      (∑ g : Fin 143, (Sparse.pulled g (blockIndex{b} i j) : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W)) := by
  have he : (∑ i : Fin {d}, ∑ j : Fin {d},
      ((right (blockIndex{b} i j) 0 : Real)+(right (blockIndex{b} i j) 1 : Real)*s+
        (right (blockIndex{b} i j) 2 : Real)*s^2+
        (right (blockIndex{b} i j) 3 : Real)*s*(1-s)) *
      (∑ g : Fin 143, (Sparse.pulled g (blockIndex{b} i j) : Real) *
        (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
          Taeyoung.homDensity (S4Classification.coreGraph6 g) W))) =
      24*Block{b:02d}.density W s + 24*s*(1-s)*Block{b+5:02d}.density W s := by
    simp only [Block{b:02d}.density, Block{b+5:02d}.density, Finset.mul_sum,
      ← Finset.sum_add_distrib, blockPulled{b}]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro g _
    have h0 := blockRight{b} i j 0
    have h1 := blockRight{b} i j 1
    have h2 := blockRight{b} i j 2
    have h3 := blockRight{b} i j 3
    norm_num at h0 h1 h2 h3 ⊢
    rw [h0,h1,h2,h3]
    push_cast
    ring
  rw [he]
  have h0 := Block{b:02d}.density_nonneg W s
  have h1 := Block{b+5:02d}.density_nonneg W s
  have hc : 0 ≤ 1-s := by linarith
  positivity

#print axioms blockSum{b}_nonneg
end {ns}
'''
        (root/f'BlockSum{b}.lean').write_text(source,encoding='utf-8')
    print(f'Generated five Atlas{atlas} block-sum modules')


if __name__=='__main__':
    main()
