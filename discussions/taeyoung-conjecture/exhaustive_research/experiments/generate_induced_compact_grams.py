"""Emit 28 exact PSD and expansion checks in seven row-specific Lean files."""

import argparse
import json
from pathlib import Path

from generate_compact_s4_psd import PREFIX, matrix, packed_product


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('candidate')
    args = parser.parse_args()
    c = json.loads(Path(args.candidate).read_text(encoding='utf-8'))
    atlas = c['atlas']
    root = Path(f'lean/Taeyoung/Methods/RootedSOS/CompactS4/Atlas{atlas}')
    root.mkdir(parents=True,exist_ok=True)
    ns = f'{PREFIX}.CompactS4.Atlas{atlas}.Lower'
    for first in range(0,28,4):
        text = f'''import {PREFIX}.PackedMatrix
import {PREFIX}.CongruenceDiagonalDominance
import {PREFIX}.Induced.PositiveCombinations
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
'''
        for block in range(first,first+4):
            G = c['gram_scaled'][block]
            n = len(G)
            witness = c['positivity'][block]
            P,K,B = [witness[key] for key in ('preconditioner','intermediate','dominant')]
            N,NG,H = [c['expansions'][block][key] for key in ('N','NG','H')]
            m = len(N)
            Pt,Nt = list(map(list,zip(*P))),list(map(list,zip(*N)))
            bns = f'{ns}.Block{block:02d}'
            text += f'\nnamespace {bns}\nopen Finset\n'
            text += '\n'.join(matrix(name,values) for name,values in
                              [('G',G),('P',P),('K',K),('B',B),('N',N),('NG',NG),('H',H)])
            text += '\ndef Pt (i j : Nat) : Int := P j i\ndef Nt (i j : Nat) : Int := N j i\n'
            text += packed_product('GP','G','P','K',G,P,K,n)
            text += packed_product('PK','Pt','K','B',Pt,K,B,n)
            text += f'''
private theorem upper : ∀ i j : Fin {n}, j < i → P i j = 0 := by decide +kernel
private theorem diagonal : ∀ i : Fin {n}, P i i ≠ 0 := by decide +kernel
private theorem symm : ∀ i j : Fin {n}, B i j = B j i := by decide +kernel
private theorem dominant : ∀ i : Fin {n},
  (∑ j : Fin {n}, if i = j then 0 else (B i j).natAbs : Nat) ≤ (B i i).toNat := by decide +kernel
private theorem positive : ∀ i : Fin {n}, 0 ≤ B i i := by decide +kernel
theorem gram_nonneg (x : Fin {n} → Real) : 0 ≤ matrixQuadratic (fun i j => (G i j : Real)) x :=
  matrixQuadratic_nonneg_of_integer_congruence
    (fun i j => G i j) (fun i j => P i j) (fun i j => K i j) (fun i j => B i j)
    upper diagonal GP_exact PK_exact symm dominant positive x
'''
            text += packed_product('NGProduct','N','G','NG',N,G,NG,n)
            text += packed_product('FullProduct','NG','Nt','H',NG,Nt,H,n)
            text += f'''
theorem expanded_entries_exact (i j : Fin {m}) :
    H i j = ∑ k : Fin {n}, (∑ l : Fin {n}, N i l * G l k) * N j k := by
  rw [FullProduct_exact]
  apply Finset.sum_congr rfl
  intro k _
  rw [NGProduct_exact]
  rfl
theorem pulled_nonneg (x : Fin {m} → Real) :
    0 ≤ matrixQuadratic (fun i j => (H i j : Real)) x :=
  Induced.integer_rectangular_pullback_nonneg (fun i j => G i j) (fun i j => N i j)
    (fun i j => H i j) gram_nonneg expanded_entries_exact x
#print axioms pulled_nonneg
end {bns}
'''
        for ti in range(first//2,first//2+2):
            b0,b1 = 2*ti,2*ti+1
            nf = len(c['expansions'][b1]['H'])
            text += f'''
namespace {ns}.Type{ti:02d}
def matrix (s : Real) : Fin {nf} → Fin {nf} → Real :=
  Induced.intervalMatrix (fun i j => (Block{b0:02d}.H i j : Real)) (fun i j => (Block{b1:02d}.H i j : Real)) s
theorem matrix_nonneg {{s : Real}} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : Fin {nf} → Real) :
    0 ≤ matrixQuadratic (matrix s) x :=
  Induced.intervalMatrix_nonneg _ _ Block{b0:02d}.pulled_nonneg Block{b1:02d}.pulled_nonneg hs0 hs1 x
end {ns}.Type{ti:02d}
'''
        path = root/f'LowerGrams{first//4:02d}.lean'
        path.write_text(text,encoding='utf-8')
        print(path.name,path.stat().st_size,flush=True)


if __name__ == '__main__':
    main()
