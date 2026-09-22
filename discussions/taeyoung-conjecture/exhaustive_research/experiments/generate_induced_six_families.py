"""Generate induced flag families with exact completion histograms and semantics."""

import itertools as it
import json
from pathlib import Path

from generate_compact_s4_psd import table


NS = 'Taeyoung.Methods.RootedSOS.Induced.Six'
ROOT = Path('lean/Taeyoung/Methods/RootedSOS/Induced/Six')


def main():
    c = json.loads(Path('experiments/induced_six_common.json').read_text(encoding='utf-8'))
    base,bound = c['histogram_base'],c['histogram_bound']
    offset = bound*sum(base**j for j in range(156))
    (ROOT/'Powers.lean').write_text(f'''import Taeyoung.Methods.RootedSOS.PackedMatrix
namespace {NS}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
private def powerData : PackedTable := {table([base**j for j in range(156)])}
def groupPower (j : Fin 156) : Int := powerData.get j
theorem groupPower_exact : ∀ j, groupPower j = ({base} : Int)^j.1 := by decide +kernel
theorem histogram_offset : ({bound} : Int)*geometricEncoding {base} 156 = {offset} := by decide +kernel
end {NS}
''',encoding='utf-8')
    for ti,t in enumerate(c['types']):
        m,nf = t['roots'],t['flag_count']
        nb,nc = len(t['branch_pairs']),len(t['cross_indices'])
        root_indices = [c['pairs'].index(list(e)) for e in it.combinations(range(m),2)]
        root_code = sum(1 << k for k,e in enumerate(root_indices) if t['root_code'] >> e & 1)
        sizes = list(map(len,t['members']))
        width = max(sizes)
        members = [v for row in t['members'] for v in row+[0]*(width-len(row))]
        codes = [offset+int(v) for row in t['encoded_counts'] for v in row]
        ns,config = f'{NS}.Family{ti:02d}',f'{NS}.Config{m:02d}'
        text = f'''import {NS}.Classification
import {NS}.Config{m:02d}
import {NS}.Powers
import Taeyoung.Methods.RootedSOS.Induced.Family
import Taeyoung.Methods.RootedSOS.Induced.Counts
namespace {ns}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory
def size : Fin {nf} → Nat := ![{', '.join(map(str,sizes))}]
private def memberData : PackedTable := {table(members)}
def memberCode (i : Fin {nf}) (a : Fin (size i)) : Fin {2**nb} :=
  ⟨(memberData.get (i.1*{width}+a.1)).toNat%{2**nb}, Nat.mod_lt _ (by decide)⟩
def member (i : Fin {nf}) (a : Fin (size i)) : {config}.BranchEdge → Fin 2 :=
  {config}.branchBits (memberCode i a)
private def countData : PackedTable := {table(codes)}
def countCode (i j : Fin {nf}) : Nat := (countData.get (i.1*{nf}+j.1)).toNat
def coefficient (i j : Fin {nf}) (g : Fin 156) : Int :=
  decodeSignedDigit {base} {bound} (countCode i j) g
def completedHost (i j : Fin {nf}) (a : Fin (size i)) (b : Fin (size j)) (c : Fin {2**nc}) : Fin 156 :=
  host ({config}.completion {root_code} (memberCode i a) (memberCode j b) c)
def pairEquation (i j : Fin {nf}) : Prop :=
  (countCode i j : Int) = {offset} +
    ∑ a : Fin (size i), ∑ b : Fin (size j), ∑ c : Fin {2**nc}, groupPower (completedHost i j a b c)
instance (i j : Fin {nf}) : Decidable (pairEquation i j) := by unfold pairEquation; infer_instance
theorem card_bound : ∀ i j : Fin {nf}, size i*(size j*{2**nc}) ≤ {bound} := by decide +kernel
'''
        for i in range(nf):
            for j in range(nf):
                text += f'private theorem check_{i:02d}_{j:02d} : pairEquation {i} {j} := by decide +kernel\n'
            text += f'private theorem row_{i:02d} (j : Fin {nf}) : pairEquation {i} j := by\n  fin_cases j\n'
            text += ''.join(f'  · exact check_{i:02d}_{j:02d}\n' for j in range(nf))
        text += f'theorem pairEquation_all (i j : Fin {nf}) : pairEquation i j := by\n  fin_cases i\n'
        text += ''.join(f'  · exact row_{i:02d} j\n' for i in range(nf))
        text += f'''
theorem code_exact (i j : Fin {nf}) :
    (countCode i j : Int) = ({bound} : Int)*geometricEncoding {base} 156 +
      ∑ q : Fin (size i) × (Fin (size j) × Fin {2**nc}),
        ({base} : Int)^(completedHost i j q.1 q.2.1 q.2.2).1 := by
  rw [histogram_offset]
  simpa only [pairEquation, Fintype.sum_prod_type, groupPower_exact] using pairEquation_all i j
variable {{Ω : Type*}} [MeasurableSpace Ω] {{μ : Measure Ω}} [IsProbabilityMeasure μ]
noncomputable def pair (W : Taeyoung.Graphon Ω μ) (i j : Fin {nf}) : Real :=
  familyPair {config}.rootPairs ({config}.rootBits {root_code}) {config}.branchPairs size member W i j
theorem pair_density (W : Taeyoung.Graphon Ω μ) (i j : Fin {nf}) :
    pair W i j = ∑ g : Fin 156, (coefficient i j g : Real)*density g W := by
  have hc := count_density_sum
    (fun q : Fin (size i) × (Fin (size j) × Fin {2**nc}) => completedHost i j q.1 q.2.1 q.2.2)
    (by decide : {base} = 2*{bound}+1)
    (by simpa only [Fintype.card_prod, Fintype.card_fin] using card_bound i j)
    (code_exact i j) (fun g => density g W)
  change pair W i j = ∑ g : Fin 156, (decodeSignedDigit {base} {bound} (countCode i j) g : Real)*density g W
  rw [← hc]
  simp only [Fintype.sum_prod_type]
  unfold pair
  rw [familyPair_expansion {config}.rootPairs ({config}.rootBits {root_code})
    {config}.branchPairs {config}.crossPairs size member W]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [← finFunctionFinEquiv.symm.sum_comp (fun c : {config}.CrossEdge → Fin 2 =>
    inducedDensity (gluedPairs {config}.rootPairs {config}.branchPairs {config}.crossPairs)
      (gluedPattern ({config}.rootBits {root_code}) (member i a) (member j b) c) W)]
  apply Finset.sum_congr rfl
  intro c _
  change inducedDensity {config}.allPairs
    (gluedPattern ({config}.rootBits {root_code})
      ({config}.branchBits (memberCode i a)) ({config}.branchBits (memberCode j b)) ({config}.crossBits c)) W = _
  rw [{config}.completion_density, inducedDensity_classification]
  rfl
theorem gram_nonneg (W : Taeyoung.Graphon Ω μ) (G : Fin {nf} → Fin {nf} → Real)
    (hG : ∀ x, 0 ≤ matrixQuadratic G x) :
    0 ≤ ∑ i, ∑ j, G i j * (∑ g : Fin 156, (coefficient i j g : Real)*density g W) := by
  have h := family_gram_nonneg {config}.rootPairs ({config}.rootBits {root_code})
    {config}.branchPairs size member W G hG
  change 0 ≤ ∑ i, ∑ j, G i j * pair W i j at h
  simp_rw [pair_density] at h
  exact h
#print axioms gram_nonneg
end {ns}
'''
        path = ROOT/f'Family{ti:02d}.lean'
        path.write_text(text,encoding='utf-8')
        print(path.name,path.stat().st_size,flush=True)


if __name__ == '__main__':
    main()
