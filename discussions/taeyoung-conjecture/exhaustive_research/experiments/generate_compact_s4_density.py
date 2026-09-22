"""Interpret each of the ten checked integer Gram blocks as a graphon bound."""

import argparse
import json
from pathlib import Path

from generate_compact_s4_psd import PREFIX, row_tag


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('certificate')
    args=parser.parse_args()
    c=json.loads(Path(args.certificate).read_text(encoding='utf-8'))
    atlas=c['atlas']
    row_ns=PREFIX+'.'+row_tag(c)
    root=Path('lean')/Path(*row_ns.split('.'))
    for b,G in enumerate(c['gram_scaled']):
        d=[32,52,34,30,6][b%5]
        tag=['4','31','22','211','1111'][b%5]
        order=2 if b<5 else 1
        n=len(G)
        ns=f'{row_ns}.Block{b:02d}'
        pol=(f'(H i j : Real) + ((H i ({d}+j) : Real)+(H ({d}+i) j : Real))*s + '
             f'(H ({d}+i) ({d}+j) : Real)*s^2') if b<5 else '(H i j : Real)'
        source=f'''import {row_ns}.Block{b:02d}PSD
import {row_ns}.Block{b:02d}Expansion
import {PREFIX}.CompactS4.Young{tag}
import {PREFIX}.MatrixFlagDensity

namespace {ns}
open Finset MeasureTheory
variable {{Ω : Type*}} [MeasurableSpace Ω] {{μ : Measure Ω}} [IsProbabilityMeasure μ]

noncomputable def density (W : Taeyoung.Graphon Ω μ) (s : Real) : Real :=
  ∑ i : Fin {d}, ∑ j : Fin {d}, ({pol}) *
    (∑ g : Fin 143, (Young{tag}.pulled g i j : Real) *
      (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Taeyoung.homDensity (S4Classification.coreGraph6 g) W))

theorem density_nonneg (W : Taeyoung.Graphon Ω μ) (s : Real) : 0 ≤ density W s := by
  have h := integer_flag_density_nonneg (order := {order}) (n := {n})
    S4Flags.flagLabelGraph S4Flags.flagBranchNeighbors
    (fun a i => (Young{tag}.TInt a i : Real))
    (fun ui k => N (finProdFinEquiv ui) k) (fun i j => G i j)
    (fun ui vj => H (finProdFinEquiv ui) (finProdFinEquiv vj))
    gram_nonneg (fun a b => expanded_entries_exact (finProdFinEquiv a) (finProdFinEquiv b)) W s
  change 0 ≤ ∑ ui : Fin {order} × Fin {d}, ∑ vj : Fin {order} × Fin {d},
    (H (finProdFinEquiv ui) (finProdFinEquiv vj) : Real) * s^(ui.1.1+vj.1.1) *
      (∑ a : Fin 352, ∑ b : Fin 352,
        (Young{tag}.TInt a ui.2 : Real)*(Young{tag}.TInt b vj.2 : Real)*
          Taeyoung.homDensity (S4Flags.gluedGraph a b) W) at h
  simp_rw [Young{tag}.pair_basis_density] at h
  rw [{'two_layer_sum' if b<5 else 'one_layer_sum'} H
    (fun i j : Fin {d} => ∑ g : Fin 143, (Young{tag}.pulled g i j : Real) *
      (Taeyoung.cliqueDensity 2 W ^ (S4Classification.groupKey g).2 *
        Taeyoung.homDensity (S4Classification.coreGraph6 g) W)) s] at h
  exact h

#print axioms density_nonneg
end {ns}
'''
        (root/f'Block{b:02d}Density.lean').write_text(source,encoding='utf-8')
    print(f'Generated ten Atlas{atlas} density interpretation modules')


if __name__=='__main__':
    main()
