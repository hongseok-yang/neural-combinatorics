"""Generate row-specific checks of four-slot contractions, using shared sparsity."""

import argparse
import json
from pathlib import Path

from generate_compact_s4_psd import PREFIX, matrix, table, row_tag


NS=f'{PREFIX}.CompactS4.Atlas118'
ROOT=Path('lean/Taeyoung/Methods/RootedSOS/CompactS4/Atlas118')


def configure(atlas, suffix=''):
    global NS, ROOT
    NS=PREFIX+'.'+row_tag(dict(atlas=atlas, lean_namespace_suffix=suffix))
    ROOT=Path('lean')/Path(*NS.split('.'))
    ROOT.mkdir(parents=True,exist_ok=True)


def write(name, body):
    (ROOT/f'{name}.lean').write_text(body,encoding='utf-8')


def chunks(name, base, predicate, size, per_file, per_theorem):
    result=[]
    for start in range(0,size,per_file):
        stop=min(start+per_file,size)
        stem=f'{name}{start:04d}'
        body=f'import {NS}.{base}\nnamespace {NS}\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 40000000\n'
        cases=''
        for a in range(start,stop,per_theorem):
            z=min(a+per_theorem,stop)
            body+=f'''private theorem check_{a:04d} : ∀ i : Fin {z-a},
    {predicate} ⟨{a}+i.1, by omega⟩ := by decide +kernel
'''
            cases+=f'''  by_cases h : i.1 < {z-start}
  · let j : Fin {z-a} := ⟨i.1-{a-start}, by omega⟩
    have he : (⟨{a}+j.1, by omega⟩ : Fin {size}) = ⟨{start}+i.1, by omega⟩ := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using check_{a:04d} j
'''
        body+=f'''theorem {name}_{start:04d} (i : Fin {stop-start}) : {predicate} ⟨{start}+i.1, by omega⟩ := by
{cases}  omega
end {NS}
'''
        write(stem,body)
        result.append((start,stop,stem))
    imports='\n'.join(f'import {NS}.{stem}' for _,_,stem in result)
    cases=''
    for start,stop,_ in result:
        cases+=f'''  by_cases h : k.1 < {stop}
  · let j : Fin {stop-start} := ⟨k.1-{start}, by omega⟩
    have he : (⟨{start}+j.1, by omega⟩ : Fin {size}) = k := by
      apply Fin.ext
      dsimp only [j] <;> omega
    simpa only [he] using {name}_{start:04d} j
'''
    theorem=f'theorem {predicate}_all (k : Fin {size}) : {predicate} k := by\n{cases}  omega\n'
    return imports,theorem


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('witness')
    args=parser.parse_args()
    c=json.loads(Path(args.witness).read_text(encoding='utf-8'))
    configure(c['atlas'], c.get('lean_namespace_suffix', ''))
    sparse=json.loads(Path('experiments/s4_compact_sparse_witness.json').read_text())
    base,bound,rb=c['base'],c['bound'],c['right_bound']
    write('RightData',f'''import {PREFIX}.PackedMatrix
namespace {NS}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
{matrix('right',c['right'])}
private def rightEncodedData : PackedTable := {table(c['right_encoded'])}
def rightEncoded (k : Fin 5820) : Int := rightEncodedData.get k
end {NS}
''')
    write('GroupData',f'''import {PREFIX}.PackedMatrix
namespace {NS}
set_option maxRecDepth 1000000
{matrix('groupTotal',c['group_totals'])}
end {NS}
''')
    imports='\n'.join(f'import {NS}.Block{b:02d}ExpansionData' for b in range(10))
    expansion=''
    for b,d in enumerate(sparse['block_dimensions']):
        start,stop=sparse['block_offsets'][b:b+2]
        expansion+=f'''  {'if k.1 < '+str(stop)+' then' if b<4 else ''}
    let i := (k.1-{start})/{d}
    let j := (k.1-{start})%{d}
    if u.1 = 0 then 24*Block{b:02d}.H i j
    else if u.1 = 1 then 24*(Block{b:02d}.H i ({d}+j)+Block{b:02d}.H ({d}+i) j)
    else if u.1 = 2 then 24*Block{b:02d}.H ({d}+i) ({d}+j)
    else 24*Block{b+5:02d}.H i j{' else' if b<4 else ''}
'''
    write('RightBase',f'''import {NS}.RightData
{imports}
namespace {NS}
def expandedRight (k : Fin 5820) (u : Fin 4) : Int :=
{expansion}
def rightCheck (k : Fin 5820) : Prop :=
  (∀ u : Fin 4, (right k u).natAbs ≤ {rb} ∧ right k u = expandedRight k u) ∧
  rightEncoded k = ∑ u : Fin 4, right k u * ({base} : Int)^u.1
instance (k : Fin 5820) : Decidable (rightCheck k) := by unfold rightCheck; infer_instance
end {NS}
''')
    imports,thm=chunks('RightChecks','RightBase','rightCheck',5820,1024,64)
    write('Right',imports+f'\nnamespace {NS}\n'+thm+f'\nend {NS}\n')
    write('ContractionBase',f'''import {NS}.Right
import {NS}.GroupData
import {PREFIX}.CompactS4.Sparse
namespace {NS}
def contractionCheck (g : Fin 143) : Prop :=
  (∀ u : Fin 4, (groupTotal g u).natAbs ≤ {bound}) ∧
  shiftedEncoding {base} {bound} (List.ofFn fun u : Fin 4 => groupTotal g u) =
    {bound*sum(base**u for u in range(4))} +
      ∑ j : Fin (Sparse.rowSize g), Sparse.rowValue ⟨g,j⟩ * rightEncoded (Sparse.rowColumn ⟨g,j⟩)
instance (g : Fin 143) : Decidable (contractionCheck g) := by unfold contractionCheck; infer_instance
end {NS}
''')
    imports,thm=chunks('ContractionChecks','ContractionBase','contractionCheck',143,13,1)
    final=imports+f'''\nnamespace {NS}
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
{thm}
theorem groupTotal_exact (g : Fin 143) (u : Fin 4) :
    groupTotal g u = ∑ k : Fin 5820, Sparse.pulled g k * right k u := by
  apply packed_rect_product_exact
    (fun i j => Sparse.pulled ⟨i%143,Nat.mod_lt _ (by decide)⟩ ⟨j%5820,Nat.mod_lt _ (by decide)⟩)
    right groupTotal 576 {rb} {bound} {base} rightEncoded
    (by
      intro i j
      exact decodeSignedDigit_bound (by decide) (Sparse.flatCode _) _)
    (fun k u => ((rightCheck_all k).1 u).1)
    (fun g u => (contractionCheck_all g).1 u)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun k => (rightCheck_all k).2)
    (by
      intro g
      have hoff : ({bound} : Int) * geometricEncoding {base} 4 = {bound*sum(base**u for u in range(4))} := by decide +kernel
      simp only [Nat.cast_ofNat, Nat.mod_eq_of_lt g.isLt, Nat.mod_eq_of_lt (Fin.isLt _)]
      rw [hoff, Sparse.contraction]
      exact (contractionCheck_all g).2)
    g u

#print axioms groupTotal_exact
end {NS}
'''
    # Nat-indexed adapter on the left is propositionally equal at finite indices.
    final=final.replace('  apply packed_rect_product_exact','  have h := packed_rect_product_exact')
    final=final.replace('    g u\n','    g u\n  simpa only [Nat.mod_eq_of_lt g.isLt, Nat.mod_eq_of_lt (Fin.isLt _)] using h\n')
    write('Contraction',final)
    print(f"Generated 23 Atlas{c['atlas']} group-contraction files")


if __name__=='__main__':
    main()
