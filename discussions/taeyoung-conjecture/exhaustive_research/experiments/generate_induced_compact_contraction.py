"""Generate eight row files for induced Gram coefficient contractions."""

import argparse
import json
from pathlib import Path

import generate_compact_s4_group_totals as chunks
from generate_compact_s4_psd import PREFIX,matrix,table


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('candidate')
    args=parser.parse_args()
    c=json.loads(Path(args.candidate).read_text(encoding='utf-8'))
    common=json.loads(Path('experiments/induced_six_sparse_witness.json').read_text(encoding='utf-8'))
    atlas=c['atlas'];count=common['column_count'];lb=common['histogram_bound']
    assert count==3632
    right=c['right'];totals=c['group_totals']
    rb=max(abs(v) for row in right for v in row)
    bound=count*lb*rb;base=2*bound+1
    encoded=[sum(v*base**u for u,v in enumerate(row)) for row in right]
    offset=bound*sum(base**u for u in range(3))
    for g,row in enumerate(common['rows']):
        assert all(totals[g][u]==sum(value*right[k][u] for k,value in row) for u in range(3))
    chunks.configure(atlas)
    parent=chunks.NS;ns=parent+'.Lower';write=chunks.write
    imports='\n'.join(f'import {parent}.LowerGrams{i:02d}' for i in range(7))
    expanded=''
    for ti,d in enumerate(common['block_dimensions']):
        start,stop=common['block_offsets'][ti:ti+2]
        if ti<13:expanded+=f'  if k.1 < {stop} then\n'
        expanded+=f'''    let i := (k.1-{start})/{d}
    let j := (k.1-{start})%{d}
    if u.1 = 0 then Block{2*ti:02d}.H i j
    else if u.1 = 1 then Block{2*ti:02d}.H i ({d}+j)+Block{2*ti:02d}.H ({d}+i) j+Block{2*ti+1:02d}.H i j
    else Block{2*ti:02d}.H ({d}+i) ({d}+j)'''+(' else\n' if ti<13 else '\n')
    write('LowerRightBase',imports+f'''
namespace {ns}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
{matrix('right',right)}
private def rightEncodedData : PackedTable := {table(encoded)}
def rightEncoded (k : Fin {count}) : Int := rightEncodedData.get k
def expandedRight (k : Fin {count}) (u : Fin 3) : Int :=
{expanded}
def rightCheck (k : Fin {count}) : Prop :=
  (∀ u : Fin 3, (right k u).natAbs ≤ {rb} ∧ right k u = expandedRight k u) ∧
  rightEncoded k = ∑ u : Fin 3, right k u*({base} : Int)^u.1
instance (k : Fin {count}) : Decidable (rightCheck k) := by unfold rightCheck; infer_instance
end {ns}
''')
    imports,thm=chunks.chunks('LowerRightChecks','LowerRightBase','Lower.rightCheck',count,2048,64)
    cs='Induced.Six.Sparse'
    write('LowerContractionBase',imports+f'''
import {PREFIX}.Induced.Six.Sparse
namespace {parent}
{thm}
end {parent}
namespace {ns}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
{matrix('groupTotal',totals)}
def contractionCheck (g : Fin 156) : Prop :=
  (∀ u : Fin 3, (groupTotal g u).natAbs ≤ {bound}) ∧
  shiftedEncoding {base} {bound} (List.ofFn fun u : Fin 3 => groupTotal g u) =
    {offset} + ∑ j : Fin ({cs}.rowSize g),
      {cs}.rowValue ⟨g,j⟩*rightEncoded ({cs}.rowColumn ⟨g,j⟩)
instance (g : Fin 156) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end {ns}
''')
    imports,thm=chunks.chunks('LowerContractionChecks','LowerContractionBase','Lower.contractionCheck',156,52,1)
    write('LowerContraction',imports+f'''
namespace {parent}
{thm}
end {parent}
namespace {ns}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
theorem groupTotal_exact (g : Fin 156) (u : Fin 3) :
    groupTotal g u = ∑ k : Fin {count}, {cs}.pulled g k*right k u := by
  have h := packed_rect_product_exact
    (fun i j => {cs}.pulled ⟨i%156,Nat.mod_lt _ (by decide)⟩ ⟨j%{count},Nat.mod_lt _ (by decide)⟩)
    right groupTotal {lb} {rb} {bound} {base} rightEncoded
    (by
      intro i j
      exact decodeSignedDigit_bound (by decide) ({cs}.flatCode _) _)
    (fun k u => ((rightCheck_all k).1 u).1)
    (fun g u => (contractionCheck_all g).1 u)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun k => (rightCheck_all k).2)
    (by
      intro g
      have hoff : ({bound} : Int)*geometricEncoding {base} 3 = {offset} := by decide +kernel
      simp only [Nat.cast_ofNat, Nat.mod_eq_of_lt g.isLt, Nat.mod_eq_of_lt (Fin.isLt _)]
      rw [hoff, {cs}.contraction]
      exact (contractionCheck_all g).2)
    g u
  simpa only [Nat.mod_eq_of_lt g.isLt, Nat.mod_eq_of_lt (Fin.isLt _)] using h
#print axioms groupTotal_exact
end {ns}
''')
    print(f'Generated eight lower-contraction files for Atlas{atlas}; right bound {rb}.',flush=True)


if __name__=='__main__':
    main()
